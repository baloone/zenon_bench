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

(declare-sort enum_STATUT 0)

(declare-fun enum_STATUT1 () ty)

(declare-fun mem (ty uni uni) Bool)

(declare-fun mem1 (Int (set Int)) Bool)

(declare-fun mem3 (enum_STATUT (set enum_STATUT)) Bool)

(declare-fun infix_eqeq (ty uni uni) Bool)

(declare-fun t2tb14 ((set enum_STATUT)) uni)

;; t2tb_sort
  (assert
  (forall ((x (set enum_STATUT))) (sort (set1 enum_STATUT1) (t2tb14 x))))

(declare-fun tb2t14 (uni) (set enum_STATUT))

;; BridgeL
  (assert
  (forall ((i (set enum_STATUT)))
  (! (= (tb2t14 (t2tb14 i)) i) :pattern ((t2tb14 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 enum_STATUT1) j) (= (t2tb14 (tb2t14 j)) j)) :pattern (
  (t2tb14 (tb2t14 j))) )))

;; infix ==_def
  (assert
  (forall ((s1 (set enum_STATUT)) (s2 (set enum_STATUT)))
  (= (infix_eqeq enum_STATUT1 (t2tb14 s1) (t2tb14 s2))
  (forall ((x enum_STATUT)) (= (mem3 x s1) (mem3 x s2))))))

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
  (forall ((s1 (set enum_STATUT)) (s2 (set enum_STATUT)))
  (= (subset enum_STATUT1 (t2tb14 s1) (t2tb14 s2))
  (forall ((x enum_STATUT)) (=> (mem3 x s1) (mem3 x s2))))))

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

(declare-sort tuple2 2)

(declare-fun tuple21 (ty ty) ty)

(declare-fun empty (ty) uni)

;; empty_sort
  (assert (forall ((a ty)) (sort (set1 a) (empty a))))

(declare-fun empty1 () (set Int))

(declare-fun empty2 () (set (tuple2 Int Int)))

(declare-fun empty4 () (set enum_STATUT))

(declare-fun is_empty (ty uni) Bool)

;; is_empty_def
  (assert
  (forall ((s (set enum_STATUT)))
  (= (is_empty enum_STATUT1 (t2tb14 s))
  (forall ((x enum_STATUT)) (not (mem3 x s))))))

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
  (assert (is_empty enum_STATUT1 (t2tb14 empty4)))

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
  (assert (is_empty (tuple21 int int) (t2tb5 empty2)))

;; empty_def1
  (assert (is_empty int (t2tb empty1)))

;; empty_def1
  (assert (forall ((a ty)) (is_empty a (empty a))))

;; mem_empty
  (assert (forall ((x enum_STATUT)) (not (mem3 x empty4))))

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
  (not (mem (tuple21 int int) (t2tb6 x) (t2tb5 empty2)))))

;; mem_empty
  (assert (forall ((x Int)) (not (mem1 x empty1))))

;; mem_empty
  (assert (forall ((a ty)) (forall ((x uni)) (not (mem a x (empty a))))))

(declare-fun add (ty uni uni) uni)

;; add_sort
  (assert
  (forall ((a ty)) (forall ((x uni) (x1 uni)) (sort (set1 a) (add a x x1)))))

(declare-fun add1 (Int (set Int)) (set Int))

(declare-fun add3 (enum_STATUT (set enum_STATUT)) (set enum_STATUT))

;; add_def1
  (assert
  (forall ((x enum_STATUT) (y enum_STATUT))
  (forall ((s (set enum_STATUT)))
  (= (mem3 x (add3 y s)) (or (= x y) (mem3 x s))))))

;; add_def1
  (assert
  (forall ((x Int) (y Int))
  (forall ((s (set Int))) (= (mem1 x (add1 y s)) (or (= x y) (mem1 x s))))))

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

(declare-fun t2tb15 (enum_STATUT) uni)

;; t2tb_sort
  (assert (forall ((x enum_STATUT)) (sort enum_STATUT1 (t2tb15 x))))

(declare-fun tb2t15 (uni) enum_STATUT)

;; BridgeL
  (assert
  (forall ((i enum_STATUT))
  (! (= (tb2t15 (t2tb15 i)) i) :pattern ((t2tb15 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort enum_STATUT1 j) (= (t2tb15 (tb2t15 j)) j)) :pattern ((t2tb15
                                                                    (tb2t15
                                                                    j))) )))

;; remove_def1
  (assert
  (forall ((x enum_STATUT) (y enum_STATUT) (s (set enum_STATUT)))
  (= (mem3 x (tb2t14 (remove enum_STATUT1 (t2tb15 y) (t2tb14 s))))
  (and (not (= x y)) (mem3 x s)))))

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
  (forall ((x enum_STATUT) (s (set enum_STATUT)))
  (=> (mem3 x s)
  (= (add3 x (tb2t14 (remove enum_STATUT1 (t2tb15 x) (t2tb14 s)))) s))))

;; add_remove
  (assert
  (forall ((x Int) (s (set Int)))
  (=> (mem1 x s) (= (add1 x (tb2t (remove int (t2tb1 x) (t2tb s)))) s))))

;; add_remove
  (assert
  (forall ((a ty))
  (forall ((x uni) (s uni))
  (=> (sort (set1 a) s) (=> (mem a x s) (= (add a x (remove a x s)) s))))))

;; remove_add
  (assert
  (forall ((x enum_STATUT) (s (set enum_STATUT)))
  (= (tb2t14 (remove enum_STATUT1 (t2tb15 x) (t2tb14 (add3 x s)))) (tb2t14
                                                                   (remove
                                                                   enum_STATUT1
                                                                   (t2tb15 x)
                                                                   (t2tb14 s))))))

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

(declare-fun union1 ((set Int) (set Int)) (set Int))

(declare-fun union2 ((set (tuple2 Int Int)) (set (tuple2 Int
  Int))) (set (tuple2 Int Int)))

(declare-fun union4 ((set enum_STATUT) (set enum_STATUT)) (set enum_STATUT))

;; union_def1
  (assert
  (forall ((s1 (set enum_STATUT)) (s2 (set enum_STATUT)) (x enum_STATUT))
  (= (mem3 x (union4 s1 s2)) (or (mem3 x s1) (mem3 x s2)))))

;; union_def1
  (assert
  (forall ((s1 (set (tuple2 Int Int))) (s2 (set (tuple2 Int Int)))
  (x (tuple2 Int Int)))
  (= (mem (tuple21 int int) (t2tb6 x) (t2tb5 (union2 s1 s2)))
  (or (mem (tuple21 int int) (t2tb6 x) (t2tb5 s1)) (mem (tuple21 int int)
  (t2tb6 x) (t2tb5 s2))))))

;; union_def1
  (assert
  (forall ((s1 (set Int)) (s2 (set Int)) (x Int))
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
  (forall ((s1 (set enum_STATUT)) (s2 (set enum_STATUT)) (x enum_STATUT))
  (= (mem3 x (tb2t14 (inter enum_STATUT1 (t2tb14 s1) (t2tb14 s2))))
  (and (mem3 x s1) (mem3 x s2)))))

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
  (forall ((s1 (set enum_STATUT)) (s2 (set enum_STATUT)) (x enum_STATUT))
  (= (mem3 x (tb2t14 (diff enum_STATUT1 (t2tb14 s1) (t2tb14 s2))))
  (and (mem3 x s1) (not (mem3 x s2))))))

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
  (forall ((s (set enum_STATUT)))
  (=> (not (is_empty enum_STATUT1 (t2tb14 s))) (mem3
  (tb2t15 (choose enum_STATUT1 (t2tb14 s))) s))))

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
  (assert (forall ((x enum_STATUT)) (mem3 x (tb2t14 (all enum_STATUT1)))))

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
  (assert (forall ((a Int) (b Int)) (=> (< b a) (= (mk a b) empty1))))

;; interval_add
  (assert
  (forall ((a Int) (b Int))
  (=> (<= a b) (= (mk a b) (add1 b (mk a (- b 1)))))))

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

(declare-fun t2tb41 ((set (set enum_STATUT))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set enum_STATUT)))) (sort (set1 (set1 enum_STATUT1))
  (t2tb41 x))))

(declare-fun tb2t41 (uni) (set (set enum_STATUT)))

;; BridgeL
  (assert
  (forall ((i (set (set enum_STATUT))))
  (! (= (tb2t41 (t2tb41 i)) i) :pattern ((t2tb41 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (set1 enum_STATUT1)) j) (= (t2tb41 (tb2t41 j)) j)) :pattern (
  (t2tb41 (tb2t41 j))) )))

;; mem_non_empty_power
  (assert
  (forall ((x (set enum_STATUT)) (y (set enum_STATUT)))
  (! (= (mem (set1 enum_STATUT1) (t2tb14 x)
     (non_empty_power enum_STATUT1 (t2tb14 y)))
     (and (subset enum_STATUT1 (t2tb14 x) (t2tb14 y)) (not (= x empty4)))) :pattern ((mem
  (set1 enum_STATUT1) (t2tb14 x)
  (non_empty_power enum_STATUT1 (t2tb14 y)))) )))

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
     (and (subset (tuple21 int int) (t2tb5 x) (t2tb5 y)) (not (= x empty2)))) :pattern ((mem
  (set1 (tuple21 int int)) (t2tb5 x)
  (non_empty_power (tuple21 int int) (t2tb5 y)))) )))

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
     (and (subset int (t2tb x) (t2tb y)) (not (= x empty1)))) :pattern ((mem
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
  (forall ((a ty))
  (forall ((f uni) (s uni) (t (set enum_STATUT)))
  (and
  (=> (mem (set1 (tuple21 a enum_STATUT1)) f
  (relation enum_STATUT1 a s (t2tb14 t)))
  (forall ((x uni) (y enum_STATUT))
  (=> (mem (tuple21 a enum_STATUT1) (Tuple2 a enum_STATUT1 x (t2tb15 y)) f)
  (and (mem a x s) (mem3 y t)))))
  (=>
  (forall ((x uni) (y enum_STATUT))
  (=> (sort a x)
  (=> (mem (tuple21 a enum_STATUT1) (Tuple2 a enum_STATUT1 x (t2tb15 y)) f)
  (and (mem a x s) (mem3 y t))))) (mem (set1 (tuple21 a enum_STATUT1)) f
  (relation enum_STATUT1 a s (t2tb14 t))))))))

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

(declare-fun t2tb42 ((set (set (tuple2 enum_STATUT enum_STATUT)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 enum_STATUT enum_STATUT))))) (sort
  (set1 (set1 (tuple21 enum_STATUT1 enum_STATUT1))) (t2tb42 x))))

(declare-fun tb2t42 (uni) (set (set (tuple2 enum_STATUT enum_STATUT))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 enum_STATUT enum_STATUT)))))
  (! (= (tb2t42 (t2tb42 i)) i) :pattern ((t2tb42 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (set1 (tuple21 enum_STATUT1 enum_STATUT1))) j)
     (= (t2tb42 (tb2t42 j)) j)) :pattern ((t2tb42 (tb2t42 j))) )))

(declare-fun t2tb43 ((set (tuple2 enum_STATUT enum_STATUT))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 enum_STATUT enum_STATUT)))) (sort
  (set1 (tuple21 enum_STATUT1 enum_STATUT1)) (t2tb43 x))))

(declare-fun tb2t43 (uni) (set (tuple2 enum_STATUT enum_STATUT)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 enum_STATUT enum_STATUT))))
  (! (= (tb2t43 (t2tb43 i)) i) :pattern ((t2tb43 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (tuple21 enum_STATUT1 enum_STATUT1)) j)
     (= (t2tb43 (tb2t43 j)) j)) :pattern ((t2tb43 (tb2t43 j))) )))

(declare-fun t2tb44 ((tuple2 enum_STATUT enum_STATUT)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 enum_STATUT enum_STATUT))) (sort
  (tuple21 enum_STATUT1 enum_STATUT1) (t2tb44 x))))

(declare-fun tb2t44 (uni) (tuple2 enum_STATUT enum_STATUT))

;; BridgeL
  (assert
  (forall ((i (tuple2 enum_STATUT enum_STATUT)))
  (! (= (tb2t44 (t2tb44 i)) i) :pattern ((t2tb44 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (tuple21 enum_STATUT1 enum_STATUT1) j)
     (= (t2tb44 (tb2t44 j)) j)) :pattern ((t2tb44 (tb2t44 j))) )))

;; mem_relation
  (assert
  (forall ((f (set (tuple2 enum_STATUT enum_STATUT))) (s (set enum_STATUT))
  (t (set enum_STATUT)))
  (= (mem (set1 (tuple21 enum_STATUT1 enum_STATUT1)) (t2tb43 f)
  (relation enum_STATUT1 enum_STATUT1 (t2tb14 s) (t2tb14 t)))
  (forall ((x enum_STATUT) (y enum_STATUT))
  (=> (mem (tuple21 enum_STATUT1 enum_STATUT1)
  (Tuple2 enum_STATUT1 enum_STATUT1 (t2tb15 x) (t2tb15 y)) (t2tb43 f))
  (and (mem3 x s) (mem3 y t)))))))

(declare-fun t2tb45 ((set (set (tuple2 enum_STATUT Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 enum_STATUT Int))))) (sort
  (set1 (set1 (tuple21 enum_STATUT1 int))) (t2tb45 x))))

(declare-fun tb2t45 (uni) (set (set (tuple2 enum_STATUT Int))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 enum_STATUT Int)))))
  (! (= (tb2t45 (t2tb45 i)) i) :pattern ((t2tb45 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb45 (tb2t45 j)) j) :pattern ((t2tb45 (tb2t45 j))) )))

(declare-fun t2tb46 ((set (tuple2 enum_STATUT Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 enum_STATUT Int)))) (sort
  (set1 (tuple21 enum_STATUT1 int)) (t2tb46 x))))

(declare-fun tb2t46 (uni) (set (tuple2 enum_STATUT Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 enum_STATUT Int))))
  (! (= (tb2t46 (t2tb46 i)) i) :pattern ((t2tb46 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb46 (tb2t46 j)) j) :pattern ((t2tb46 (tb2t46 j))) )))

(declare-fun t2tb47 ((tuple2 enum_STATUT Int)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 enum_STATUT Int))) (sort (tuple21 enum_STATUT1 int)
  (t2tb47 x))))

(declare-fun tb2t47 (uni) (tuple2 enum_STATUT Int))

;; BridgeL
  (assert
  (forall ((i (tuple2 enum_STATUT Int)))
  (! (= (tb2t47 (t2tb47 i)) i) :pattern ((t2tb47 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb47 (tb2t47 j)) j) :pattern ((t2tb47 (tb2t47 j))) )))

;; mem_relation
  (assert
  (forall ((f (set (tuple2 enum_STATUT Int))) (s (set enum_STATUT))
  (t (set Int)))
  (= (mem (set1 (tuple21 enum_STATUT1 int)) (t2tb46 f)
  (relation int enum_STATUT1 (t2tb14 s) (t2tb t)))
  (forall ((x enum_STATUT) (y Int))
  (=> (mem (tuple21 enum_STATUT1 int)
  (Tuple2 enum_STATUT1 int (t2tb15 x) (t2tb1 y)) (t2tb46 f))
  (and (mem3 x s) (mem1 y t)))))))

;; mem_relation
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set enum_STATUT)) (t uni))
  (and
  (=> (mem (set1 (tuple21 enum_STATUT1 b)) f
  (relation b enum_STATUT1 (t2tb14 s) t))
  (forall ((x enum_STATUT) (y uni))
  (=> (mem (tuple21 enum_STATUT1 b) (Tuple2 enum_STATUT1 b (t2tb15 x) y) f)
  (and (mem3 x s) (mem b y t)))))
  (=>
  (forall ((x enum_STATUT) (y uni))
  (=> (sort b y)
  (=> (mem (tuple21 enum_STATUT1 b) (Tuple2 enum_STATUT1 b (t2tb15 x) y) f)
  (and (mem3 x s) (mem b y t))))) (mem (set1 (tuple21 enum_STATUT1 b)) f
  (relation b enum_STATUT1 (t2tb14 s) t)))))))

(declare-fun t2tb48 ((set (set (tuple2 Int enum_STATUT)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Int enum_STATUT))))) (sort
  (set1 (set1 (tuple21 int enum_STATUT1))) (t2tb48 x))))

(declare-fun tb2t48 (uni) (set (set (tuple2 Int enum_STATUT))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Int enum_STATUT)))))
  (! (= (tb2t48 (t2tb48 i)) i) :pattern ((t2tb48 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb48 (tb2t48 j)) j) :pattern ((t2tb48 (tb2t48 j))) )))

(declare-fun t2tb49 ((set (tuple2 Int enum_STATUT))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int enum_STATUT)))) (sort
  (set1 (tuple21 int enum_STATUT1)) (t2tb49 x))))

(declare-fun tb2t49 (uni) (set (tuple2 Int enum_STATUT)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int enum_STATUT))))
  (! (= (tb2t49 (t2tb49 i)) i) :pattern ((t2tb49 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb49 (tb2t49 j)) j) :pattern ((t2tb49 (tb2t49 j))) )))

(declare-fun t2tb50 ((tuple2 Int enum_STATUT)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Int enum_STATUT))) (sort (tuple21 int enum_STATUT1)
  (t2tb50 x))))

(declare-fun tb2t50 (uni) (tuple2 Int enum_STATUT))

;; BridgeL
  (assert
  (forall ((i (tuple2 Int enum_STATUT)))
  (! (= (tb2t50 (t2tb50 i)) i) :pattern ((t2tb50 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb50 (tb2t50 j)) j) :pattern ((t2tb50 (tb2t50 j))) )))

;; mem_relation
  (assert
  (forall ((f (set (tuple2 Int enum_STATUT))) (s (set Int))
  (t (set enum_STATUT)))
  (= (mem (set1 (tuple21 int enum_STATUT1)) (t2tb49 f)
  (relation enum_STATUT1 int (t2tb s) (t2tb14 t)))
  (forall ((x Int) (y enum_STATUT))
  (=> (mem (tuple21 int enum_STATUT1)
  (Tuple2 int enum_STATUT1 (t2tb1 x) (t2tb15 y)) (t2tb49 f))
  (and (mem1 x s) (mem3 y t)))))))

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
  (forall ((r uni) (dom1 uni) (y enum_STATUT))
  (! (and
     (=> (mem3 y (tb2t14 (image enum_STATUT1 a r dom1)))
     (exists ((x uni))
     (and (sort a x)
     (and (mem a x dom1) (mem (tuple21 a enum_STATUT1)
     (Tuple2 a enum_STATUT1 x (t2tb15 y)) r)))))
     (=>
     (exists ((x uni))
     (and (mem a x dom1) (mem (tuple21 a enum_STATUT1)
     (Tuple2 a enum_STATUT1 x (t2tb15 y)) r))) (mem3 y
     (tb2t14 (image enum_STATUT1 a r dom1))))) :pattern ((mem3
  y (tb2t14 (image enum_STATUT1 a r dom1)))) ))))

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
  (forall ((r (set (tuple2 enum_STATUT enum_STATUT)))
  (dom1 (set enum_STATUT)) (y enum_STATUT))
  (! (= (mem3 y
     (tb2t14 (image enum_STATUT1 enum_STATUT1 (t2tb43 r) (t2tb14 dom1))))
     (exists ((x enum_STATUT))
     (and (mem3 x dom1) (mem (tuple21 enum_STATUT1 enum_STATUT1)
     (Tuple2 enum_STATUT1 enum_STATUT1 (t2tb15 x) (t2tb15 y)) (t2tb43 r))))) :pattern ((mem3
  y (tb2t14 (image enum_STATUT1 enum_STATUT1 (t2tb43 r) (t2tb14 dom1))))) )))

;; mem_image
  (assert
  (forall ((r (set (tuple2 enum_STATUT Int))) (dom1 (set enum_STATUT))
  (y Int))
  (! (= (mem1 y (tb2t (image int enum_STATUT1 (t2tb46 r) (t2tb14 dom1))))
     (exists ((x enum_STATUT))
     (and (mem3 x dom1) (mem (tuple21 enum_STATUT1 int)
     (Tuple2 enum_STATUT1 int (t2tb15 x) (t2tb1 y)) (t2tb46 r))))) :pattern ((mem1
  y (tb2t (image int enum_STATUT1 (t2tb46 r) (t2tb14 dom1))))) )))

;; mem_image
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom1 (set enum_STATUT)) (y uni))
  (! (= (mem b y (image b enum_STATUT1 r (t2tb14 dom1)))
     (exists ((x enum_STATUT))
     (and (mem3 x dom1) (mem (tuple21 enum_STATUT1 b)
     (Tuple2 enum_STATUT1 b (t2tb15 x) y) r)))) :pattern ((mem
  b y (image b enum_STATUT1 r (t2tb14 dom1)))) ))))

;; mem_image
  (assert
  (forall ((r (set (tuple2 Int enum_STATUT))) (dom1 (set Int))
  (y enum_STATUT))
  (! (= (mem3 y (tb2t14 (image enum_STATUT1 int (t2tb49 r) (t2tb dom1))))
     (exists ((x Int))
     (and (mem1 x dom1) (mem (tuple21 int enum_STATUT1)
     (Tuple2 int enum_STATUT1 (t2tb1 x) (t2tb15 y)) (t2tb49 r))))) :pattern ((mem3
  y (tb2t14 (image enum_STATUT1 int (t2tb49 r) (t2tb dom1))))) )))

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
  (forall ((a ty))
  (forall ((r uni) (s uni) (t uni))
  (= (tb2t14 (image enum_STATUT1 a r (union a s t))) (union4
                                                     (tb2t14
                                                     (image enum_STATUT1 a r
                                                     s))
                                                     (tb2t14
                                                     (image enum_STATUT1 a r
                                                     t)))))))

;; image_union
  (assert
  (forall ((a ty))
  (forall ((r uni) (s uni) (t uni))
  (= (tb2t5 (image (tuple21 int int) a r (union a s t))) (union2
                                                         (tb2t5
                                                         (image
                                                         (tuple21 int int) a
                                                         r s))
                                                         (tb2t5
                                                         (image
                                                         (tuple21 int int) a
                                                         r t)))))))

;; image_union
  (assert
  (forall ((a ty))
  (forall ((r uni) (s uni) (t uni))
  (= (tb2t (image int a r (union a s t))) (union1 (tb2t (image int a r s))
                                          (tb2t (image int a r t)))))))

;; image_union
  (assert
  (forall ((r (set (tuple2 enum_STATUT enum_STATUT))) (s (set enum_STATUT))
  (t (set enum_STATUT)))
  (= (tb2t14
     (image enum_STATUT1 enum_STATUT1 (t2tb43 r) (t2tb14 (union4 s t)))) 
  (union4 (tb2t14 (image enum_STATUT1 enum_STATUT1 (t2tb43 r) (t2tb14 s)))
  (tb2t14 (image enum_STATUT1 enum_STATUT1 (t2tb43 r) (t2tb14 t)))))))

(declare-fun t2tb51 ((set (tuple2 enum_STATUT (tuple2 Int Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 enum_STATUT (tuple2 Int Int))))) (sort
  (set1 (tuple21 enum_STATUT1 (tuple21 int int))) (t2tb51 x))))

(declare-fun tb2t51 (uni) (set (tuple2 enum_STATUT (tuple2 Int Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 enum_STATUT (tuple2 Int Int)))))
  (! (= (tb2t51 (t2tb51 i)) i) :pattern ((t2tb51 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb51 (tb2t51 j)) j) :pattern ((t2tb51 (tb2t51 j))) )))

;; image_union
  (assert
  (forall ((r (set (tuple2 enum_STATUT (tuple2 Int Int))))
  (s (set enum_STATUT)) (t (set enum_STATUT)))
  (= (tb2t5
     (image (tuple21 int int) enum_STATUT1 (t2tb51 r) (t2tb14 (union4 s t)))) 
  (union2
  (tb2t5 (image (tuple21 int int) enum_STATUT1 (t2tb51 r) (t2tb14 s)))
  (tb2t5 (image (tuple21 int int) enum_STATUT1 (t2tb51 r) (t2tb14 t)))))))

;; image_union
  (assert
  (forall ((r (set (tuple2 enum_STATUT Int))) (s (set enum_STATUT))
  (t (set enum_STATUT)))
  (= (tb2t (image int enum_STATUT1 (t2tb46 r) (t2tb14 (union4 s t)))) 
  (union1 (tb2t (image int enum_STATUT1 (t2tb46 r) (t2tb14 s)))
  (tb2t (image int enum_STATUT1 (t2tb46 r) (t2tb14 t)))))))

;; image_union
  (assert
  (forall ((b ty))
  (forall ((r uni) (s (set enum_STATUT)) (t (set enum_STATUT)))
  (= (image b enum_STATUT1 r (t2tb14 (union4 s t))) (union b
                                                    (image b enum_STATUT1 r
                                                    (t2tb14 s))
                                                    (image b enum_STATUT1 r
                                                    (t2tb14 t)))))))

(declare-fun t2tb52 ((set (tuple2 (tuple2 Int Int) enum_STATUT))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Int Int) enum_STATUT)))) (sort
  (set1 (tuple21 (tuple21 int int) enum_STATUT1)) (t2tb52 x))))

(declare-fun tb2t52 (uni) (set (tuple2 (tuple2 Int Int) enum_STATUT)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Int Int) enum_STATUT))))
  (! (= (tb2t52 (t2tb52 i)) i) :pattern ((t2tb52 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb52 (tb2t52 j)) j) :pattern ((t2tb52 (tb2t52 j))) )))

;; image_union
  (assert
  (forall ((r (set (tuple2 (tuple2 Int Int) enum_STATUT)))
  (s (set (tuple2 Int Int))) (t (set (tuple2 Int Int))))
  (= (tb2t14
     (image enum_STATUT1 (tuple21 int int) (t2tb52 r) (t2tb5 (union2 s t)))) 
  (union4
  (tb2t14 (image enum_STATUT1 (tuple21 int int) (t2tb52 r) (t2tb5 s)))
  (tb2t14 (image enum_STATUT1 (tuple21 int int) (t2tb52 r) (t2tb5 t)))))))

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

;; image_union
  (assert
  (forall ((r (set (tuple2 (tuple2 Int Int) (tuple2 Int Int))))
  (s (set (tuple2 Int Int))) (t (set (tuple2 Int Int))))
  (= (tb2t5
     (image (tuple21 int int) (tuple21 int int) (t2tb28 r)
     (t2tb5 (union2 s t)))) (union2
                            (tb2t5
                            (image (tuple21 int int) (tuple21 int int)
                            (t2tb28 r) (t2tb5 s)))
                            (tb2t5
                            (image (tuple21 int int) (tuple21 int int)
                            (t2tb28 r) (t2tb5 t)))))))

(declare-fun t2tb29 ((set (tuple2 (tuple2 Int Int) Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Int Int) Int)))) (sort
  (set1 (tuple21 (tuple21 int int) int)) (t2tb29 x))))

(declare-fun tb2t29 (uni) (set (tuple2 (tuple2 Int Int) Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Int Int) Int))))
  (! (= (tb2t29 (t2tb29 i)) i) :pattern ((t2tb29 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb29 (tb2t29 j)) j) :pattern ((t2tb29 (tb2t29 j))) )))

;; image_union
  (assert
  (forall ((r (set (tuple2 (tuple2 Int Int) Int))) (s (set (tuple2 Int Int)))
  (t (set (tuple2 Int Int))))
  (= (tb2t (image int (tuple21 int int) (t2tb29 r) (t2tb5 (union2 s t)))) 
  (union1 (tb2t (image int (tuple21 int int) (t2tb29 r) (t2tb5 s)))
  (tb2t (image int (tuple21 int int) (t2tb29 r) (t2tb5 t)))))))

;; image_union
  (assert
  (forall ((b ty))
  (forall ((r uni) (s (set (tuple2 Int Int))) (t (set (tuple2 Int Int))))
  (= (image b (tuple21 int int) r (t2tb5 (union2 s t))) (union b
                                                        (image b
                                                        (tuple21 int int) r
                                                        (t2tb5 s))
                                                        (image b
                                                        (tuple21 int int) r
                                                        (t2tb5 t)))))))

;; image_union
  (assert
  (forall ((r (set (tuple2 Int enum_STATUT))) (s (set Int)) (t (set Int)))
  (= (tb2t14 (image enum_STATUT1 int (t2tb49 r) (t2tb (union1 s t)))) 
  (union4 (tb2t14 (image enum_STATUT1 int (t2tb49 r) (t2tb s)))
  (tb2t14 (image enum_STATUT1 int (t2tb49 r) (t2tb t)))))))

(declare-fun t2tb30 ((set (tuple2 Int (tuple2 Int Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int (tuple2 Int Int))))) (sort
  (set1 (tuple21 int (tuple21 int int))) (t2tb30 x))))

(declare-fun tb2t30 (uni) (set (tuple2 Int (tuple2 Int Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int (tuple2 Int Int)))))
  (! (= (tb2t30 (t2tb30 i)) i) :pattern ((t2tb30 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb30 (tb2t30 j)) j) :pattern ((t2tb30 (tb2t30 j))) )))

;; image_union
  (assert
  (forall ((r (set (tuple2 Int (tuple2 Int Int)))) (s (set Int))
  (t (set Int)))
  (= (tb2t5 (image (tuple21 int int) int (t2tb30 r) (t2tb (union1 s t)))) 
  (union2 (tb2t5 (image (tuple21 int int) int (t2tb30 r) (t2tb s)))
  (tb2t5 (image (tuple21 int int) int (t2tb30 r) (t2tb t)))))))

;; image_union
  (assert
  (forall ((r (set (tuple2 Int Int))) (s (set Int)) (t (set Int)))
  (= (tb2t (image int int (t2tb5 r) (t2tb (union1 s t)))) (union1
                                                          (tb2t
                                                          (image int 
                                                          int (t2tb5 r)
                                                          (t2tb s)))
                                                          (tb2t
                                                          (image int 
                                                          int (t2tb5 r)
                                                          (t2tb t)))))))

;; image_union
  (assert
  (forall ((b ty))
  (forall ((r uni) (s (set Int)) (t (set Int)))
  (= (image b int r (t2tb (union1 s t))) (union b (image b int r (t2tb s))
                                         (image b int r (t2tb t)))))))

;; image_union
  (assert
  (forall ((a ty) (b ty))
  (forall ((r uni) (s uni) (t uni))
  (= (image b a r (union a s t)) (union b (image b a r s) (image b a r t))))))

;; image_add
  (assert
  (forall ((a ty))
  (forall ((r uni) (dom1 uni) (x uni))
  (= (tb2t14 (image enum_STATUT1 a r (add a x dom1))) (union4
                                                      (tb2t14
                                                      (image enum_STATUT1 a r
                                                      (add a x (empty a))))
                                                      (tb2t14
                                                      (image enum_STATUT1 a r
                                                      dom1)))))))

;; image_add
  (assert
  (forall ((a ty))
  (forall ((r uni) (dom1 uni) (x uni))
  (= (tb2t5 (image (tuple21 int int) a r (add a x dom1))) (union2
                                                          (tb2t5
                                                          (image
                                                          (tuple21 int int) a
                                                          r
                                                          (add a x (empty a))))
                                                          (tb2t5
                                                          (image
                                                          (tuple21 int int) a
                                                          r dom1)))))))

;; image_add
  (assert
  (forall ((a ty))
  (forall ((r uni) (dom1 uni) (x uni))
  (= (tb2t (image int a r (add a x dom1))) (union1
                                           (tb2t
                                           (image int a r
                                           (add a x (empty a))))
                                           (tb2t (image int a r dom1)))))))

;; image_add
  (assert
  (forall ((r (set (tuple2 enum_STATUT enum_STATUT)))
  (dom1 (set enum_STATUT)) (x enum_STATUT))
  (= (tb2t14
     (image enum_STATUT1 enum_STATUT1 (t2tb43 r) (t2tb14 (add3 x dom1)))) 
  (union4
  (tb2t14
  (image enum_STATUT1 enum_STATUT1 (t2tb43 r) (t2tb14 (add3 x empty4))))
  (tb2t14 (image enum_STATUT1 enum_STATUT1 (t2tb43 r) (t2tb14 dom1)))))))

;; image_add
  (assert
  (forall ((r (set (tuple2 enum_STATUT (tuple2 Int Int))))
  (dom1 (set enum_STATUT)) (x enum_STATUT))
  (= (tb2t5
     (image (tuple21 int int) enum_STATUT1 (t2tb51 r) (t2tb14 (add3 x dom1)))) 
  (union2
  (tb2t5
  (image (tuple21 int int) enum_STATUT1 (t2tb51 r) (t2tb14 (add3 x empty4))))
  (tb2t5 (image (tuple21 int int) enum_STATUT1 (t2tb51 r) (t2tb14 dom1)))))))

;; image_add
  (assert
  (forall ((r (set (tuple2 enum_STATUT Int))) (dom1 (set enum_STATUT))
  (x enum_STATUT))
  (= (tb2t (image int enum_STATUT1 (t2tb46 r) (t2tb14 (add3 x dom1)))) 
  (union1 (tb2t (image int enum_STATUT1 (t2tb46 r) (t2tb14 (add3 x empty4))))
  (tb2t (image int enum_STATUT1 (t2tb46 r) (t2tb14 dom1)))))))

;; image_add
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom1 (set enum_STATUT)) (x enum_STATUT))
  (= (image b enum_STATUT1 r (t2tb14 (add3 x dom1))) (union b
                                                     (image b enum_STATUT1 r
                                                     (t2tb14 (add3 x empty4)))
                                                     (image b enum_STATUT1 r
                                                     (t2tb14 dom1)))))))

;; image_add
  (assert
  (forall ((r (set (tuple2 (tuple2 Int Int) enum_STATUT)))
  (dom1 (set (tuple2 Int Int))) (x (tuple2 Int Int)))
  (= (tb2t14
     (image enum_STATUT1 (tuple21 int int) (t2tb52 r)
     (add (tuple21 int int) (t2tb6 x) (t2tb5 dom1)))) (union4
                                                      (tb2t14
                                                      (image enum_STATUT1
                                                      (tuple21 int int)
                                                      (t2tb52 r)
                                                      (add (tuple21 int int)
                                                      (t2tb6 x)
                                                      (t2tb5 empty2))))
                                                      (tb2t14
                                                      (image enum_STATUT1
                                                      (tuple21 int int)
                                                      (t2tb52 r)
                                                      (t2tb5 dom1)))))))

;; image_add
  (assert
  (forall ((r (set (tuple2 (tuple2 Int Int) (tuple2 Int Int))))
  (dom1 (set (tuple2 Int Int))) (x (tuple2 Int Int)))
  (= (tb2t5
     (image (tuple21 int int) (tuple21 int int) (t2tb28 r)
     (add (tuple21 int int) (t2tb6 x) (t2tb5 dom1)))) (union2
                                                      (tb2t5
                                                      (image
                                                      (tuple21 int int)
                                                      (tuple21 int int)
                                                      (t2tb28 r)
                                                      (add (tuple21 int int)
                                                      (t2tb6 x)
                                                      (t2tb5 empty2))))
                                                      (tb2t5
                                                      (image
                                                      (tuple21 int int)
                                                      (tuple21 int int)
                                                      (t2tb28 r)
                                                      (t2tb5 dom1)))))))

;; image_add
  (assert
  (forall ((r (set (tuple2 (tuple2 Int Int) Int))) (dom1 (set (tuple2 Int
  Int))) (x (tuple2 Int Int)))
  (= (tb2t
     (image int (tuple21 int int) (t2tb29 r)
     (add (tuple21 int int) (t2tb6 x) (t2tb5 dom1)))) (union1
                                                      (tb2t
                                                      (image int
                                                      (tuple21 int int)
                                                      (t2tb29 r)
                                                      (add (tuple21 int int)
                                                      (t2tb6 x)
                                                      (t2tb5 empty2))))
                                                      (tb2t
                                                      (image int
                                                      (tuple21 int int)
                                                      (t2tb29 r)
                                                      (t2tb5 dom1)))))))

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
                                                     (t2tb5 empty2)))
                                                     (image b
                                                     (tuple21 int int) r
                                                     (t2tb5 dom1)))))))

;; image_add
  (assert
  (forall ((r (set (tuple2 Int enum_STATUT))) (dom1 (set Int)) (x Int))
  (= (tb2t14 (image enum_STATUT1 int (t2tb49 r) (t2tb (add1 x dom1)))) 
  (union4 (tb2t14 (image enum_STATUT1 int (t2tb49 r) (t2tb (add1 x empty1))))
  (tb2t14 (image enum_STATUT1 int (t2tb49 r) (t2tb dom1)))))))

;; image_add
  (assert
  (forall ((r (set (tuple2 Int (tuple2 Int Int)))) (dom1 (set Int)) (x Int))
  (= (tb2t5 (image (tuple21 int int) int (t2tb30 r) (t2tb (add1 x dom1)))) 
  (union2
  (tb2t5 (image (tuple21 int int) int (t2tb30 r) (t2tb (add1 x empty1))))
  (tb2t5 (image (tuple21 int int) int (t2tb30 r) (t2tb dom1)))))))

;; image_add
  (assert
  (forall ((r (set (tuple2 Int Int))) (dom1 (set Int)) (x Int))
  (= (tb2t (image int int (t2tb5 r) (t2tb (add1 x dom1)))) (union1
                                                           (tb2t
                                                           (image int 
                                                           int (t2tb5 r)
                                                           (t2tb
                                                           (add1 x empty1))))
                                                           (tb2t
                                                           (image int 
                                                           int (t2tb5 r)
                                                           (t2tb dom1)))))))

;; image_add
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom1 (set Int)) (x Int))
  (= (image b int r (t2tb (add1 x dom1))) (union b
                                          (image b int r
                                          (t2tb (add1 x empty1)))
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
  (forall ((a ty))
  (forall ((f uni) (s uni) (t (set enum_STATUT)))
  (and
  (=> (mem (set1 (tuple21 a enum_STATUT1)) f
  (infix_plmngt enum_STATUT1 a s (t2tb14 t)))
  (and
  (forall ((x uni) (y enum_STATUT))
  (=> (mem (tuple21 a enum_STATUT1) (Tuple2 a enum_STATUT1 x (t2tb15 y)) f)
  (and (mem a x s) (mem3 y t))))
  (forall ((x uni) (y1 enum_STATUT) (y2 enum_STATUT))
  (=>
  (and (mem (tuple21 a enum_STATUT1) (Tuple2 a enum_STATUT1 x (t2tb15 y1)) f)
  (mem (tuple21 a enum_STATUT1) (Tuple2 a enum_STATUT1 x (t2tb15 y2)) f))
  (= y1 y2)))))
  (=>
  (and
  (forall ((x uni) (y enum_STATUT))
  (=> (sort a x)
  (=> (mem (tuple21 a enum_STATUT1) (Tuple2 a enum_STATUT1 x (t2tb15 y)) f)
  (and (mem a x s) (mem3 y t)))))
  (forall ((x uni) (y1 enum_STATUT) (y2 enum_STATUT))
  (=> (sort a x)
  (=>
  (and (mem (tuple21 a enum_STATUT1) (Tuple2 a enum_STATUT1 x (t2tb15 y1)) f)
  (mem (tuple21 a enum_STATUT1) (Tuple2 a enum_STATUT1 x (t2tb15 y2)) f))
  (= y1 y2))))) (mem (set1 (tuple21 a enum_STATUT1)) f
  (infix_plmngt enum_STATUT1 a s (t2tb14 t))))))))

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
  (forall ((f (set (tuple2 enum_STATUT enum_STATUT))) (s (set enum_STATUT))
  (t (set enum_STATUT)))
  (= (mem (set1 (tuple21 enum_STATUT1 enum_STATUT1)) (t2tb43 f)
  (infix_plmngt enum_STATUT1 enum_STATUT1 (t2tb14 s) (t2tb14 t)))
  (and
  (forall ((x enum_STATUT) (y enum_STATUT))
  (=> (mem (tuple21 enum_STATUT1 enum_STATUT1)
  (Tuple2 enum_STATUT1 enum_STATUT1 (t2tb15 x) (t2tb15 y)) (t2tb43 f))
  (and (mem3 x s) (mem3 y t))))
  (forall ((x enum_STATUT) (y1 enum_STATUT) (y2 enum_STATUT))
  (=>
  (and (mem (tuple21 enum_STATUT1 enum_STATUT1)
  (Tuple2 enum_STATUT1 enum_STATUT1 (t2tb15 x) (t2tb15 y1)) (t2tb43 f)) (mem
  (tuple21 enum_STATUT1 enum_STATUT1)
  (Tuple2 enum_STATUT1 enum_STATUT1 (t2tb15 x) (t2tb15 y2)) (t2tb43 f)))
  (= y1 y2)))))))

;; mem_function
  (assert
  (forall ((f (set (tuple2 enum_STATUT Int))) (s (set enum_STATUT))
  (t (set Int)))
  (= (mem (set1 (tuple21 enum_STATUT1 int)) (t2tb46 f)
  (infix_plmngt int enum_STATUT1 (t2tb14 s) (t2tb t)))
  (and
  (forall ((x enum_STATUT) (y Int))
  (=> (mem (tuple21 enum_STATUT1 int)
  (Tuple2 enum_STATUT1 int (t2tb15 x) (t2tb1 y)) (t2tb46 f))
  (and (mem3 x s) (mem1 y t))))
  (forall ((x enum_STATUT) (y1 Int) (y2 Int))
  (=>
  (and (mem (tuple21 enum_STATUT1 int)
  (Tuple2 enum_STATUT1 int (t2tb15 x) (t2tb1 y1)) (t2tb46 f)) (mem
  (tuple21 enum_STATUT1 int) (Tuple2 enum_STATUT1 int (t2tb15 x) (t2tb1 y2))
  (t2tb46 f))) (= y1 y2)))))))

;; mem_function
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set enum_STATUT)) (t uni))
  (and
  (=> (mem (set1 (tuple21 enum_STATUT1 b)) f
  (infix_plmngt b enum_STATUT1 (t2tb14 s) t))
  (and
  (forall ((x enum_STATUT) (y uni))
  (=> (mem (tuple21 enum_STATUT1 b) (Tuple2 enum_STATUT1 b (t2tb15 x) y) f)
  (and (mem3 x s) (mem b y t))))
  (forall ((x enum_STATUT) (y1 uni) (y2 uni))
  (=> (sort b y1)
  (=> (sort b y2)
  (=>
  (and (mem (tuple21 enum_STATUT1 b) (Tuple2 enum_STATUT1 b (t2tb15 x) y1) f)
  (mem (tuple21 enum_STATUT1 b) (Tuple2 enum_STATUT1 b (t2tb15 x) y2) f))
  (= y1 y2)))))))
  (=>
  (and
  (forall ((x enum_STATUT) (y uni))
  (=> (sort b y)
  (=> (mem (tuple21 enum_STATUT1 b) (Tuple2 enum_STATUT1 b (t2tb15 x) y) f)
  (and (mem3 x s) (mem b y t)))))
  (forall ((x enum_STATUT) (y1 uni) (y2 uni))
  (=> (sort b y1)
  (=> (sort b y2)
  (=>
  (and (mem (tuple21 enum_STATUT1 b) (Tuple2 enum_STATUT1 b (t2tb15 x) y1) f)
  (mem (tuple21 enum_STATUT1 b) (Tuple2 enum_STATUT1 b (t2tb15 x) y2) f))
  (= y1 y2)))))) (mem (set1 (tuple21 enum_STATUT1 b)) f
  (infix_plmngt b enum_STATUT1 (t2tb14 s) t)))))))

;; mem_function
  (assert
  (forall ((f (set (tuple2 Int enum_STATUT))) (s (set Int))
  (t (set enum_STATUT)))
  (= (mem (set1 (tuple21 int enum_STATUT1)) (t2tb49 f)
  (infix_plmngt enum_STATUT1 int (t2tb s) (t2tb14 t)))
  (and
  (forall ((x Int) (y enum_STATUT))
  (=> (mem (tuple21 int enum_STATUT1)
  (Tuple2 int enum_STATUT1 (t2tb1 x) (t2tb15 y)) (t2tb49 f))
  (and (mem1 x s) (mem3 y t))))
  (forall ((x Int) (y1 enum_STATUT) (y2 enum_STATUT))
  (=>
  (and (mem (tuple21 int enum_STATUT1)
  (Tuple2 int enum_STATUT1 (t2tb1 x) (t2tb15 y1)) (t2tb49 f)) (mem
  (tuple21 int enum_STATUT1) (Tuple2 int enum_STATUT1 (t2tb1 x) (t2tb15 y2))
  (t2tb49 f))) (= y1 y2)))))))

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
  (forall ((f uni) (s (set enum_STATUT)) (t uni) (x enum_STATUT) (y uni))
  (=> (mem (set1 (tuple21 enum_STATUT1 b)) f
  (infix_plmngt b enum_STATUT1 (t2tb14 s) t))
  (=> (mem (tuple21 enum_STATUT1 b) (Tuple2 enum_STATUT1 b (t2tb15 x) y) f)
  (mem3 x s))))))

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
  (forall ((f uni) (s uni) (t (set enum_STATUT)) (x uni) (y enum_STATUT))
  (=> (mem (set1 (tuple21 a enum_STATUT1)) f
  (infix_plmngt enum_STATUT1 a s (t2tb14 t)))
  (=> (mem (tuple21 a enum_STATUT1) (Tuple2 a enum_STATUT1 x (t2tb15 y)) f)
  (mem3 y t))))))

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
  (forall ((f uni) (s uni) (t (set enum_STATUT)) (u (set enum_STATUT)))
  (=> (subset enum_STATUT1 (t2tb14 u) (t2tb14 t))
  (=> (mem (set1 (tuple21 a enum_STATUT1)) f
  (infix_plmngt enum_STATUT1 a s (t2tb14 t)))
  (=>
  (forall ((x uni) (y enum_STATUT))
  (=> (sort a x)
  (=> (mem (tuple21 a enum_STATUT1) (Tuple2 a enum_STATUT1 x (t2tb15 y)) f)
  (mem3 y u)))) (mem (set1 (tuple21 a enum_STATUT1)) f
  (infix_plmngt enum_STATUT1 a s (t2tb14 u)))))))))

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
  (forall ((x enum_STATUT))
  (and
  (=> (mem3 x (tb2t14 (dom b enum_STATUT1 r)))
  (exists ((y uni))
  (and (sort b y) (mem (tuple21 enum_STATUT1 b)
  (Tuple2 enum_STATUT1 b (t2tb15 x) y) r))))
  (=>
  (exists ((y uni)) (mem (tuple21 enum_STATUT1 b)
  (Tuple2 enum_STATUT1 b (t2tb15 x) y) r)) (mem3 x
  (tb2t14 (dom b enum_STATUT1 r)))))))))

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
  (forall ((y enum_STATUT))
  (and
  (=> (mem3 y (tb2t14 (ran enum_STATUT1 a r)))
  (exists ((x uni))
  (and (sort a x) (mem (tuple21 a enum_STATUT1)
  (Tuple2 a enum_STATUT1 x (t2tb15 y)) r))))
  (=>
  (exists ((x uni)) (mem (tuple21 a enum_STATUT1)
  (Tuple2 a enum_STATUT1 x (t2tb15 y)) r)) (mem3 y
  (tb2t14 (ran enum_STATUT1 a r)))))))))

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
  (forall ((b ty))
  (= (tb2t14 (dom b enum_STATUT1 (empty (tuple21 enum_STATUT1 b)))) empty4)))

;; dom_empty
  (assert
  (forall ((b ty))
  (= (tb2t5 (dom b (tuple21 int int) (empty (tuple21 (tuple21 int int) b)))) 
  empty2)))

;; dom_empty
  (assert (= (tb2t (dom int int (t2tb5 empty2))) empty1))

;; dom_empty
  (assert
  (forall ((b ty)) (= (tb2t (dom b int (empty (tuple21 int b)))) empty1)))

;; dom_empty
  (assert
  (forall ((a ty) (b ty)) (= (dom b a (empty (tuple21 a b))) (empty a))))

;; dom_add
  (assert
  (forall ((b ty))
  (forall ((f uni) (x enum_STATUT) (y uni))
  (= (tb2t14
     (dom b enum_STATUT1
     (add (tuple21 enum_STATUT1 b) (Tuple2 enum_STATUT1 b (t2tb15 x) y) f))) 
  (add3 x (tb2t14 (dom b enum_STATUT1 f)))))))

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
  (forall ((x enum_STATUT) (y uni))
  (= (tb2t14
     (dom b enum_STATUT1
     (add (tuple21 enum_STATUT1 b) (Tuple2 enum_STATUT1 b (t2tb15 x) y)
     (empty (tuple21 enum_STATUT1 b))))) (add3 x empty4)))))

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
                                              (t2tb6 x) (t2tb5 empty2)))))))

;; dom_singleton
  (assert
  (forall ((x Int) (y Int))
  (= (tb2t
     (dom int int
     (add (tuple21 int int) (Tuple2 int int (t2tb1 x) (t2tb1 y))
     (t2tb5 empty2)))) (add1 x empty1))))

;; dom_singleton
  (assert
  (forall ((b ty))
  (forall ((x Int) (y uni))
  (= (tb2t
     (dom b int
     (add (tuple21 int b) (Tuple2 int b (t2tb1 x) y) (empty (tuple21 int b))))) 
  (add1 x empty1)))))

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
  (forall ((s uni) (t (set enum_STATUT)) (x uni) (y enum_STATUT))
  (=> (and (mem a x s) (mem3 y t)) (mem (set1 (tuple21 a enum_STATUT1))
  (add (tuple21 a enum_STATUT1) (Tuple2 a enum_STATUT1 x (t2tb15 y))
  (empty (tuple21 a enum_STATUT1)))
  (infix_plmngt enum_STATUT1 a s (t2tb14 t)))))))

;; singleton_is_partial_function
  (assert
  (forall ((a ty))
  (forall ((s uni) (t (set Int)) (x uni) (y Int))
  (=> (and (mem a x s) (mem1 y t)) (mem (set1 (tuple21 a int))
  (add (tuple21 a int) (Tuple2 a int x (t2tb1 y)) (empty (tuple21 a int)))
  (infix_plmngt int a s (t2tb t)))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set enum_STATUT)) (t (set enum_STATUT)) (x enum_STATUT)
  (y enum_STATUT))
  (=> (and (mem3 x s) (mem3 y t)) (mem
  (set1 (tuple21 enum_STATUT1 enum_STATUT1))
  (add (tuple21 enum_STATUT1 enum_STATUT1)
  (Tuple2 enum_STATUT1 enum_STATUT1 (t2tb15 x) (t2tb15 y))
  (empty (tuple21 enum_STATUT1 enum_STATUT1)))
  (infix_plmngt enum_STATUT1 enum_STATUT1 (t2tb14 s) (t2tb14 t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set enum_STATUT)) (t (set Int)) (x enum_STATUT) (y Int))
  (=> (and (mem3 x s) (mem1 y t)) (mem (set1 (tuple21 enum_STATUT1 int))
  (add (tuple21 enum_STATUT1 int)
  (Tuple2 enum_STATUT1 int (t2tb15 x) (t2tb1 y))
  (empty (tuple21 enum_STATUT1 int)))
  (infix_plmngt int enum_STATUT1 (t2tb14 s) (t2tb t))))))

;; singleton_is_partial_function
  (assert
  (forall ((b ty))
  (forall ((s (set enum_STATUT)) (t uni) (x enum_STATUT) (y uni))
  (=> (and (mem3 x s) (mem b y t)) (mem (set1 (tuple21 enum_STATUT1 b))
  (add (tuple21 enum_STATUT1 b) (Tuple2 enum_STATUT1 b (t2tb15 x) y)
  (empty (tuple21 enum_STATUT1 b)))
  (infix_plmngt b enum_STATUT1 (t2tb14 s) t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set Int)) (t (set enum_STATUT)) (x Int) (y enum_STATUT))
  (=> (and (mem1 x s) (mem3 y t)) (mem (set1 (tuple21 int enum_STATUT1))
  (add (tuple21 int enum_STATUT1)
  (Tuple2 int enum_STATUT1 (t2tb1 x) (t2tb15 y))
  (empty (tuple21 int enum_STATUT1)))
  (infix_plmngt enum_STATUT1 int (t2tb s) (t2tb14 t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set Int)) (t (set Int)) (x Int) (y Int))
  (=> (and (mem1 x s) (mem1 y t)) (mem (set1 (tuple21 int int))
  (add (tuple21 int int) (Tuple2 int int (t2tb1 x) (t2tb1 y)) (t2tb5 empty2))
  (infix_plmngt int int (t2tb s) (t2tb t))))))

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
  (forall ((a ty))
  (forall ((x uni) (y enum_STATUT)) (! (mem (set1 (tuple21 a enum_STATUT1))
  (add (tuple21 a enum_STATUT1) (Tuple2 a enum_STATUT1 x (t2tb15 y))
  (empty (tuple21 a enum_STATUT1)))
  (infix_mnmngt enum_STATUT1 a (add a x (empty a)) (t2tb14 (add3 y empty4)))) :pattern (
  (add (tuple21 a enum_STATUT1) (Tuple2 a enum_STATUT1 x (t2tb15 y))
  (empty (tuple21 a enum_STATUT1)))) ))))

;; singleton_is_function
  (assert
  (forall ((a ty))
  (forall ((x uni) (y (tuple2 Int Int))) (! (mem
  (set1 (tuple21 a (tuple21 int int)))
  (add (tuple21 a (tuple21 int int)) (Tuple2 a (tuple21 int int) x (t2tb6 y))
  (empty (tuple21 a (tuple21 int int))))
  (infix_mnmngt (tuple21 int int) a (add a x (empty a))
  (add (tuple21 int int) (t2tb6 y) (t2tb5 empty2)))) :pattern ((add
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
  (forall ((x uni) (y Int)) (! (mem (set1 (tuple21 a int))
  (add (tuple21 a int) (Tuple2 a int x (t2tb1 y)) (empty (tuple21 a int)))
  (infix_mnmngt int a (add a x (empty a)) (t2tb (add1 y empty1)))) :pattern (
  (add (tuple21 a int) (Tuple2 a int x (t2tb1 y)) (empty (tuple21 a int)))) ))))

;; singleton_is_function
  (assert
  (forall ((x enum_STATUT) (y enum_STATUT)) (! (mem
  (set1 (tuple21 enum_STATUT1 enum_STATUT1))
  (add (tuple21 enum_STATUT1 enum_STATUT1)
  (Tuple2 enum_STATUT1 enum_STATUT1 (t2tb15 x) (t2tb15 y))
  (empty (tuple21 enum_STATUT1 enum_STATUT1)))
  (infix_mnmngt enum_STATUT1 enum_STATUT1 (t2tb14 (add3 x empty4))
  (t2tb14 (add3 y empty4)))) :pattern ((tb2t43
                                       (add
                                       (tuple21 enum_STATUT1 enum_STATUT1)
                                       (Tuple2 enum_STATUT1 enum_STATUT1
                                       (t2tb15 x) (t2tb15 y))
                                       (empty
                                       (tuple21 enum_STATUT1 enum_STATUT1))))) )))

(declare-fun t2tb53 ((set (set (tuple2 enum_STATUT (tuple2 Int Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 enum_STATUT (tuple2 Int Int)))))) (sort
  (set1 (set1 (tuple21 enum_STATUT1 (tuple21 int int)))) (t2tb53 x))))

(declare-fun tb2t53 (uni) (set (set (tuple2 enum_STATUT (tuple2 Int Int)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 enum_STATUT (tuple2 Int Int))))))
  (! (= (tb2t53 (t2tb53 i)) i) :pattern ((t2tb53 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb53 (tb2t53 j)) j) :pattern ((t2tb53 (tb2t53 j))) )))

(declare-fun t2tb54 ((tuple2 enum_STATUT (tuple2 Int Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 enum_STATUT (tuple2 Int Int)))) (sort
  (tuple21 enum_STATUT1 (tuple21 int int)) (t2tb54 x))))

(declare-fun tb2t54 (uni) (tuple2 enum_STATUT (tuple2 Int Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 enum_STATUT (tuple2 Int Int))))
  (! (= (tb2t54 (t2tb54 i)) i) :pattern ((t2tb54 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb54 (tb2t54 j)) j) :pattern ((t2tb54 (tb2t54 j))) )))

;; singleton_is_function
  (assert
  (forall ((x enum_STATUT) (y (tuple2 Int Int))) (! (mem
  (set1 (tuple21 enum_STATUT1 (tuple21 int int)))
  (add (tuple21 enum_STATUT1 (tuple21 int int))
  (Tuple2 enum_STATUT1 (tuple21 int int) (t2tb15 x) (t2tb6 y))
  (empty (tuple21 enum_STATUT1 (tuple21 int int))))
  (infix_mnmngt (tuple21 int int) enum_STATUT1 (t2tb14 (add3 x empty4))
  (add (tuple21 int int) (t2tb6 y) (t2tb5 empty2)))) :pattern ((tb2t51
                                                               (add
                                                               (tuple21
                                                               enum_STATUT1
                                                               (tuple21 
                                                               int int))
                                                               (Tuple2
                                                               enum_STATUT1
                                                               (tuple21 
                                                               int int)
                                                               (t2tb15 x)
                                                               (t2tb6 y))
                                                               (empty
                                                               (tuple21
                                                               enum_STATUT1
                                                               (tuple21 
                                                               int int)))))) )))

;; singleton_is_function
  (assert
  (forall ((x enum_STATUT) (y Int)) (! (mem (set1 (tuple21 enum_STATUT1 int))
  (add (tuple21 enum_STATUT1 int)
  (Tuple2 enum_STATUT1 int (t2tb15 x) (t2tb1 y))
  (empty (tuple21 enum_STATUT1 int)))
  (infix_mnmngt int enum_STATUT1 (t2tb14 (add3 x empty4))
  (t2tb (add1 y empty1)))) :pattern ((tb2t46
                                     (add (tuple21 enum_STATUT1 int)
                                     (Tuple2 enum_STATUT1 int (t2tb15 x)
                                     (t2tb1 y))
                                     (empty (tuple21 enum_STATUT1 int))))) )))

;; singleton_is_function
  (assert
  (forall ((b ty))
  (forall ((x enum_STATUT) (y uni)) (! (mem (set1 (tuple21 enum_STATUT1 b))
  (add (tuple21 enum_STATUT1 b) (Tuple2 enum_STATUT1 b (t2tb15 x) y)
  (empty (tuple21 enum_STATUT1 b)))
  (infix_mnmngt b enum_STATUT1 (t2tb14 (add3 x empty4)) (add b y (empty b)))) :pattern (
  (add (tuple21 enum_STATUT1 b) (Tuple2 enum_STATUT1 b (t2tb15 x) y)
  (empty (tuple21 enum_STATUT1 b)))) ))))

(declare-fun t2tb55 ((set (set (tuple2 (tuple2 Int Int) enum_STATUT)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 Int Int) enum_STATUT))))) (sort
  (set1 (set1 (tuple21 (tuple21 int int) enum_STATUT1))) (t2tb55 x))))

(declare-fun tb2t55 (uni) (set (set (tuple2 (tuple2 Int Int) enum_STATUT))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 Int Int) enum_STATUT)))))
  (! (= (tb2t55 (t2tb55 i)) i) :pattern ((t2tb55 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb55 (tb2t55 j)) j) :pattern ((t2tb55 (tb2t55 j))) )))

(declare-fun t2tb56 ((tuple2 (tuple2 Int Int) enum_STATUT)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 Int Int) enum_STATUT))) (sort
  (tuple21 (tuple21 int int) enum_STATUT1) (t2tb56 x))))

(declare-fun tb2t56 (uni) (tuple2 (tuple2 Int Int) enum_STATUT))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 Int Int) enum_STATUT)))
  (! (= (tb2t56 (t2tb56 i)) i) :pattern ((t2tb56 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb56 (tb2t56 j)) j) :pattern ((t2tb56 (tb2t56 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 Int Int)) (y enum_STATUT)) (! (mem
  (set1 (tuple21 (tuple21 int int) enum_STATUT1))
  (add (tuple21 (tuple21 int int) enum_STATUT1)
  (Tuple2 (tuple21 int int) enum_STATUT1 (t2tb6 x) (t2tb15 y))
  (empty (tuple21 (tuple21 int int) enum_STATUT1)))
  (infix_mnmngt enum_STATUT1 (tuple21 int int)
  (add (tuple21 int int) (t2tb6 x) (t2tb5 empty2)) (t2tb14 (add3 y empty4)))) :pattern (
  (tb2t52
  (add (tuple21 (tuple21 int int) enum_STATUT1)
  (Tuple2 (tuple21 int int) enum_STATUT1 (t2tb6 x) (t2tb15 y))
  (empty (tuple21 (tuple21 int int) enum_STATUT1))))) )))

(declare-fun t2tb35 ((tuple2 (tuple2 Int Int) (tuple2 Int Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 Int Int) (tuple2 Int Int)))) (sort
  (tuple21 (tuple21 int int) (tuple21 int int)) (t2tb35 x))))

(declare-fun tb2t35 (uni) (tuple2 (tuple2 Int Int) (tuple2 Int Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 Int Int) (tuple2 Int Int))))
  (! (= (tb2t35 (t2tb35 i)) i) :pattern ((t2tb35 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb35 (tb2t35 j)) j) :pattern ((t2tb35 (tb2t35 j))) )))

(declare-fun t2tb36 ((set (set (tuple2 (tuple2 Int Int) (tuple2 Int
  Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 Int Int) (tuple2 Int Int)))))) (sort
  (set1 (set1 (tuple21 (tuple21 int int) (tuple21 int int)))) (t2tb36 x))))

(declare-fun tb2t36 (uni) (set (set (tuple2 (tuple2 Int Int) (tuple2 Int
  Int)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 Int Int) (tuple2 Int Int))))))
  (! (= (tb2t36 (t2tb36 i)) i) :pattern ((t2tb36 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb36 (tb2t36 j)) j) :pattern ((t2tb36 (tb2t36 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 Int Int)) (y (tuple2 Int Int))) (! (mem
  (set1 (tuple21 (tuple21 int int) (tuple21 int int)))
  (add (tuple21 (tuple21 int int) (tuple21 int int))
  (Tuple2 (tuple21 int int) (tuple21 int int) (t2tb6 x) (t2tb6 y))
  (empty (tuple21 (tuple21 int int) (tuple21 int int))))
  (infix_mnmngt (tuple21 int int) (tuple21 int int)
  (add (tuple21 int int) (t2tb6 x) (t2tb5 empty2))
  (add (tuple21 int int) (t2tb6 y) (t2tb5 empty2)))) :pattern ((tb2t28
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

(declare-fun t2tb37 ((tuple2 (tuple2 Int Int) Int)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 Int Int) Int))) (sort
  (tuple21 (tuple21 int int) int) (t2tb37 x))))

(declare-fun tb2t37 (uni) (tuple2 (tuple2 Int Int) Int))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 Int Int) Int)))
  (! (= (tb2t37 (t2tb37 i)) i) :pattern ((t2tb37 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb37 (tb2t37 j)) j) :pattern ((t2tb37 (tb2t37 j))) )))

(declare-fun t2tb38 ((set (set (tuple2 (tuple2 Int Int) Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 Int Int) Int))))) (sort
  (set1 (set1 (tuple21 (tuple21 int int) int))) (t2tb38 x))))

(declare-fun tb2t38 (uni) (set (set (tuple2 (tuple2 Int Int) Int))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 Int Int) Int)))))
  (! (= (tb2t38 (t2tb38 i)) i) :pattern ((t2tb38 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb38 (tb2t38 j)) j) :pattern ((t2tb38 (tb2t38 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 Int Int)) (y Int)) (! (mem
  (set1 (tuple21 (tuple21 int int) int))
  (add (tuple21 (tuple21 int int) int)
  (Tuple2 (tuple21 int int) int (t2tb6 x) (t2tb1 y))
  (empty (tuple21 (tuple21 int int) int)))
  (infix_mnmngt int (tuple21 int int)
  (add (tuple21 int int) (t2tb6 x) (t2tb5 empty2)) (t2tb (add1 y empty1)))) :pattern (
  (tb2t29
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
  (add (tuple21 int int) (t2tb6 x) (t2tb5 empty2)) (add b y (empty b)))) :pattern (
  (add (tuple21 (tuple21 int int) b) (Tuple2 (tuple21 int int) b (t2tb6 x) y)
  (empty (tuple21 (tuple21 int int) b)))) ))))

;; singleton_is_function
  (assert
  (forall ((x Int) (y enum_STATUT)) (! (mem (set1 (tuple21 int enum_STATUT1))
  (add (tuple21 int enum_STATUT1)
  (Tuple2 int enum_STATUT1 (t2tb1 x) (t2tb15 y))
  (empty (tuple21 int enum_STATUT1)))
  (infix_mnmngt enum_STATUT1 int (t2tb (add1 x empty1))
  (t2tb14 (add3 y empty4)))) :pattern ((tb2t49
                                       (add (tuple21 int enum_STATUT1)
                                       (Tuple2 int enum_STATUT1 (t2tb1 x)
                                       (t2tb15 y))
                                       (empty (tuple21 int enum_STATUT1))))) )))

(declare-fun t2tb39 ((tuple2 Int (tuple2 Int Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Int (tuple2 Int Int)))) (sort
  (tuple21 int (tuple21 int int)) (t2tb39 x))))

(declare-fun tb2t39 (uni) (tuple2 Int (tuple2 Int Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 Int (tuple2 Int Int))))
  (! (= (tb2t39 (t2tb39 i)) i) :pattern ((t2tb39 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb39 (tb2t39 j)) j) :pattern ((t2tb39 (tb2t39 j))) )))

(declare-fun t2tb40 ((set (set (tuple2 Int (tuple2 Int Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Int (tuple2 Int Int)))))) (sort
  (set1 (set1 (tuple21 int (tuple21 int int)))) (t2tb40 x))))

(declare-fun tb2t40 (uni) (set (set (tuple2 Int (tuple2 Int Int)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Int (tuple2 Int Int))))))
  (! (= (tb2t40 (t2tb40 i)) i) :pattern ((t2tb40 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb40 (tb2t40 j)) j) :pattern ((t2tb40 (tb2t40 j))) )))

;; singleton_is_function
  (assert
  (forall ((x Int) (y (tuple2 Int Int))) (! (mem
  (set1 (tuple21 int (tuple21 int int)))
  (add (tuple21 int (tuple21 int int))
  (Tuple2 int (tuple21 int int) (t2tb1 x) (t2tb6 y))
  (empty (tuple21 int (tuple21 int int))))
  (infix_mnmngt (tuple21 int int) int (t2tb (add1 x empty1))
  (add (tuple21 int int) (t2tb6 y) (t2tb5 empty2)))) :pattern ((tb2t30
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

;; singleton_is_function
  (assert
  (forall ((x Int) (y Int)) (! (mem (set1 (tuple21 int int))
  (add (tuple21 int int) (Tuple2 int int (t2tb1 x) (t2tb1 y)) (t2tb5 empty2))
  (infix_mnmngt int int (t2tb (add1 x empty1)) (t2tb (add1 y empty1)))) :pattern (
  (tb2t5
  (add (tuple21 int int) (Tuple2 int int (t2tb1 x) (t2tb1 y)) (t2tb5 empty2)))) )))

;; singleton_is_function
  (assert
  (forall ((b ty))
  (forall ((x Int) (y uni)) (! (mem (set1 (tuple21 int b))
  (add (tuple21 int b) (Tuple2 int b (t2tb1 x) y) (empty (tuple21 int b)))
  (infix_mnmngt b int (t2tb (add1 x empty1)) (add b y (empty b)))) :pattern (
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
  (forall ((b ty))
  (forall ((f uni) (s (set enum_STATUT)) (t uni) (a enum_STATUT))
  (=>
  (and (mem (set1 (tuple21 enum_STATUT1 b)) f
  (infix_plmngt b enum_STATUT1 (t2tb14 s) t)) (mem3 a
  (tb2t14 (dom b enum_STATUT1 f)))) (mem (tuple21 enum_STATUT1 b)
  (Tuple2 enum_STATUT1 b (t2tb15 a) (apply b enum_STATUT1 f (t2tb15 a))) f)))))

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
  (forall ((f uni) (s (set enum_STATUT)) (t uni) (a enum_STATUT))
  (=>
  (and (mem (set1 (tuple21 enum_STATUT1 b)) f
  (infix_mnmngt b enum_STATUT1 (t2tb14 s) t)) (mem3 a s)) (mem
  (tuple21 enum_STATUT1 b)
  (Tuple2 enum_STATUT1 b (t2tb15 a) (apply b enum_STATUT1 f (t2tb15 a))) f)))))

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
  (forall ((x Int) (y Int))
  (= (tb2t1
     (apply int int
     (add (tuple21 int int) (Tuple2 int int (t2tb1 x) (t2tb1 y))
     (t2tb5 empty2)) (t2tb1 x))) y)))

;; apply_singleton
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (y uni))
  (=> (sort b y)
  (= (apply b a (add (tuple21 a b) (Tuple2 a b x y) (empty (tuple21 a b))) x) y)))))

;; apply_range
  (assert
  (forall ((a ty))
  (forall ((x uni) (f uni) (s uni) (t (set enum_STATUT)))
  (! (=>
     (and (mem (set1 (tuple21 a enum_STATUT1)) f
     (infix_plmngt enum_STATUT1 a s (t2tb14 t))) (mem a x
     (dom enum_STATUT1 a f))) (mem3 (tb2t15 (apply enum_STATUT1 a f x)) t)) :pattern ((mem
  (set1 (tuple21 a enum_STATUT1)) f
  (infix_plmngt enum_STATUT1 a s (t2tb14 t)))
  (tb2t15 (apply enum_STATUT1 a f x))) ))))

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
  (forall ((x enum_STATUT) (f (set (tuple2 enum_STATUT enum_STATUT)))
  (s (set enum_STATUT)) (t (set enum_STATUT)))
  (! (=>
     (and (mem (set1 (tuple21 enum_STATUT1 enum_STATUT1)) (t2tb43 f)
     (infix_plmngt enum_STATUT1 enum_STATUT1 (t2tb14 s) (t2tb14 t))) (mem3 x
     (tb2t14 (dom enum_STATUT1 enum_STATUT1 (t2tb43 f))))) (mem3
     (tb2t15 (apply enum_STATUT1 enum_STATUT1 (t2tb43 f) (t2tb15 x))) t)) :pattern ((mem
  (set1 (tuple21 enum_STATUT1 enum_STATUT1)) (t2tb43 f)
  (infix_plmngt enum_STATUT1 enum_STATUT1 (t2tb14 s) (t2tb14 t)))
  (tb2t15 (apply enum_STATUT1 enum_STATUT1 (t2tb43 f) (t2tb15 x)))) )))

;; apply_range
  (assert
  (forall ((x enum_STATUT) (f (set (tuple2 enum_STATUT Int)))
  (s (set enum_STATUT)) (t (set Int)))
  (! (=>
     (and (mem (set1 (tuple21 enum_STATUT1 int)) (t2tb46 f)
     (infix_plmngt int enum_STATUT1 (t2tb14 s) (t2tb t))) (mem3 x
     (tb2t14 (dom int enum_STATUT1 (t2tb46 f))))) (mem1
     (tb2t1 (apply int enum_STATUT1 (t2tb46 f) (t2tb15 x))) t)) :pattern ((mem
  (set1 (tuple21 enum_STATUT1 int)) (t2tb46 f)
  (infix_plmngt int enum_STATUT1 (t2tb14 s) (t2tb t)))
  (tb2t1 (apply int enum_STATUT1 (t2tb46 f) (t2tb15 x)))) )))

;; apply_range
  (assert
  (forall ((b ty))
  (forall ((x enum_STATUT) (f uni) (s (set enum_STATUT)) (t uni))
  (! (=>
     (and (mem (set1 (tuple21 enum_STATUT1 b)) f
     (infix_plmngt b enum_STATUT1 (t2tb14 s) t)) (mem3 x
     (tb2t14 (dom b enum_STATUT1 f)))) (mem b
     (apply b enum_STATUT1 f (t2tb15 x)) t)) :pattern ((mem
  (set1 (tuple21 enum_STATUT1 b)) f
  (infix_plmngt b enum_STATUT1 (t2tb14 s) t))
  (apply b enum_STATUT1 f (t2tb15 x))) ))))

;; apply_range
  (assert
  (forall ((x Int) (f (set (tuple2 Int enum_STATUT))) (s (set Int))
  (t (set enum_STATUT)))
  (! (=>
     (and (mem (set1 (tuple21 int enum_STATUT1)) (t2tb49 f)
     (infix_plmngt enum_STATUT1 int (t2tb s) (t2tb14 t))) (mem1 x
     (tb2t (dom enum_STATUT1 int (t2tb49 f))))) (mem3
     (tb2t15 (apply enum_STATUT1 int (t2tb49 f) (t2tb1 x))) t)) :pattern ((mem
  (set1 (tuple21 int enum_STATUT1)) (t2tb49 f)
  (infix_plmngt enum_STATUT1 int (t2tb s) (t2tb14 t)))
  (tb2t15 (apply enum_STATUT1 int (t2tb49 f) (t2tb1 x)))) )))

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
  (forall ((x uni) (f uni) (g uni) (s uni) (t (set enum_STATUT)) (u uni))
  (=>
  (and (mem (set1 (tuple21 a enum_STATUT1)) f
  (infix_plmngt enum_STATUT1 a s (t2tb14 t)))
  (and (mem (set1 (tuple21 enum_STATUT1 c)) g
  (infix_plmngt c enum_STATUT1 (t2tb14 t) u))
  (and (mem a x (dom enum_STATUT1 a f)) (mem3
  (tb2t15 (apply enum_STATUT1 a f x)) (tb2t14 (dom c enum_STATUT1 g))))))
  (= (apply c a (semicolon c enum_STATUT1 a f g) x) (apply c enum_STATUT1 g
                                                    (apply enum_STATUT1 a f
                                                    x)))))))

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
  (forall ((x enum_STATUT) (f (set (tuple2 enum_STATUT enum_STATUT))) (g uni)
  (s (set enum_STATUT)) (t (set enum_STATUT)) (u uni))
  (=>
  (and (mem (set1 (tuple21 enum_STATUT1 enum_STATUT1)) (t2tb43 f)
  (infix_plmngt enum_STATUT1 enum_STATUT1 (t2tb14 s) (t2tb14 t)))
  (and (mem (set1 (tuple21 enum_STATUT1 c)) g
  (infix_plmngt c enum_STATUT1 (t2tb14 t) u))
  (and (mem3 x (tb2t14 (dom enum_STATUT1 enum_STATUT1 (t2tb43 f)))) (mem3
  (tb2t15 (apply enum_STATUT1 enum_STATUT1 (t2tb43 f) (t2tb15 x)))
  (tb2t14 (dom c enum_STATUT1 g))))))
  (= (apply c enum_STATUT1
     (semicolon c enum_STATUT1 enum_STATUT1 (t2tb43 f) g) (t2tb15 x)) 
  (apply c enum_STATUT1 g
  (apply enum_STATUT1 enum_STATUT1 (t2tb43 f) (t2tb15 x))))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x enum_STATUT) (f (set (tuple2 enum_STATUT Int))) (g uni)
  (s (set enum_STATUT)) (t (set Int)) (u uni))
  (=>
  (and (mem (set1 (tuple21 enum_STATUT1 int)) (t2tb46 f)
  (infix_plmngt int enum_STATUT1 (t2tb14 s) (t2tb t)))
  (and (mem (set1 (tuple21 int c)) g (infix_plmngt c int (t2tb t) u))
  (and (mem3 x (tb2t14 (dom int enum_STATUT1 (t2tb46 f)))) (mem1
  (tb2t1 (apply int enum_STATUT1 (t2tb46 f) (t2tb15 x)))
  (tb2t (dom c int g))))))
  (= (apply c enum_STATUT1 (semicolon c int enum_STATUT1 (t2tb46 f) g)
     (t2tb15 x)) (apply c int g
                 (apply int enum_STATUT1 (t2tb46 f) (t2tb15 x))))))))

;; apply_compose
  (assert
  (forall ((b ty) (c ty))
  (forall ((x enum_STATUT) (f uni) (g uni) (s (set enum_STATUT)) (t uni)
  (u uni))
  (=>
  (and (mem (set1 (tuple21 enum_STATUT1 b)) f
  (infix_plmngt b enum_STATUT1 (t2tb14 s) t))
  (and (mem (set1 (tuple21 b c)) g (infix_plmngt c b t u))
  (and (mem3 x (tb2t14 (dom b enum_STATUT1 f))) (mem b
  (apply b enum_STATUT1 f (t2tb15 x)) (dom c b g)))))
  (= (apply c enum_STATUT1 (semicolon c b enum_STATUT1 f g) (t2tb15 x)) 
  (apply c b g (apply b enum_STATUT1 f (t2tb15 x))))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x Int) (f (set (tuple2 Int enum_STATUT))) (g uni) (s (set Int))
  (t (set enum_STATUT)) (u uni))
  (=>
  (and (mem (set1 (tuple21 int enum_STATUT1)) (t2tb49 f)
  (infix_plmngt enum_STATUT1 int (t2tb s) (t2tb14 t)))
  (and (mem (set1 (tuple21 enum_STATUT1 c)) g
  (infix_plmngt c enum_STATUT1 (t2tb14 t) u))
  (and (mem1 x (tb2t (dom enum_STATUT1 int (t2tb49 f)))) (mem3
  (tb2t15 (apply enum_STATUT1 int (t2tb49 f) (t2tb1 x)))
  (tb2t14 (dom c enum_STATUT1 g))))))
  (= (apply c int (semicolon c enum_STATUT1 int (t2tb49 f) g) (t2tb1 x)) 
  (apply c enum_STATUT1 g (apply enum_STATUT1 int (t2tb49 f) (t2tb1 x))))))))

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
  (forall ((f uni) (s (set enum_STATUT)) (t uni))
  (forall ((x enum_STATUT) (y enum_STATUT))
  (=> (mem (set1 (tuple21 enum_STATUT1 b)) f
  (infix_gtmngt b enum_STATUT1 (t2tb14 s) t))
  (=> (mem3 x s)
  (=> (mem3 y s)
  (=>
  (= (apply b enum_STATUT1 f (t2tb15 x)) (apply b enum_STATUT1 f (t2tb15 y)))
  (= x y)))))))))

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
  (forall ((x enum_STATUT) (y enum_STATUT) (s (set enum_STATUT)))
  (= (mem (tuple21 enum_STATUT1 enum_STATUT1)
  (Tuple2 enum_STATUT1 enum_STATUT1 (t2tb15 x) (t2tb15 y))
  (id enum_STATUT1 (t2tb14 s))) (and (mem3 x s) (= x y)))))

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
  (forall ((s (set enum_STATUT))) (is_finite_subset enum_STATUT1
  (t2tb14 empty4) (t2tb14 s) 0)))

;; Empty
  (assert
  (forall ((s (set (tuple2 Int Int)))) (is_finite_subset (tuple21 int int)
  (t2tb5 empty2) (t2tb5 s) 0)))

;; Empty
  (assert
  (forall ((s (set Int))) (is_finite_subset int (t2tb empty1) (t2tb s) 0)))

;; Empty
  (assert
  (forall ((a ty)) (forall ((s uni)) (is_finite_subset a (empty a) s 0))))

;; Add_mem
  (assert
  (forall ((x enum_STATUT) (s1 (set enum_STATUT)) (s2 (set enum_STATUT))
  (c Int))
  (=> (is_finite_subset enum_STATUT1 (t2tb14 s1) (t2tb14 s2) c)
  (=> (mem3 x s2)
  (=> (mem3 x s1) (is_finite_subset enum_STATUT1 (t2tb14 (add3 x s1))
  (t2tb14 s2) c))))))

;; Add_mem
  (assert
  (forall ((x Int) (s1 (set Int)) (s2 (set Int)) (c Int))
  (=> (is_finite_subset int (t2tb s1) (t2tb s2) c)
  (=> (mem1 x s2)
  (=> (mem1 x s1) (is_finite_subset int (t2tb (add1 x s1)) (t2tb s2) c))))))

;; Add_mem
  (assert
  (forall ((a ty))
  (forall ((x uni) (s1 uni) (s2 uni) (c Int))
  (=> (is_finite_subset a s1 s2 c)
  (=> (mem a x s2) (=> (mem a x s1) (is_finite_subset a (add a x s1) s2 c)))))))

;; Add_notmem
  (assert
  (forall ((x enum_STATUT) (s1 (set enum_STATUT)) (s2 (set enum_STATUT))
  (c Int))
  (=> (is_finite_subset enum_STATUT1 (t2tb14 s1) (t2tb14 s2) c)
  (=> (mem3 x s2)
  (=> (not (mem3 x s1)) (is_finite_subset enum_STATUT1 (t2tb14 (add3 x s1))
  (t2tb14 s2) (+ c 1)))))))

;; Add_notmem
  (assert
  (forall ((x Int) (s1 (set Int)) (s2 (set Int)) (c Int))
  (=> (is_finite_subset int (t2tb s1) (t2tb s2) c)
  (=> (mem1 x s2)
  (=> (not (mem1 x s1)) (is_finite_subset int (t2tb (add1 x s1)) (t2tb s2)
  (+ c 1)))))))

;; Add_notmem
  (assert
  (forall ((a ty))
  (forall ((x uni) (s1 uni) (s2 uni) (c Int))
  (=> (is_finite_subset a s1 s2 c)
  (=> (mem a x s2)
  (=> (not (mem a x s1)) (is_finite_subset a (add a x s1) s2 (+ c 1))))))))

;; is_finite_subset_inversion
  (assert
  (forall ((z (set enum_STATUT)) (z1 (set enum_STATUT)) (z2 Int))
  (=> (is_finite_subset enum_STATUT1 (t2tb14 z) (t2tb14 z1) z2)
  (or
  (or
  (exists ((s (set enum_STATUT))) (and (and (= z empty4) (= z1 s)) (= z2 0)))
  (exists ((x enum_STATUT) (s1 (set enum_STATUT)) (s2 (set enum_STATUT))
  (c Int))
  (and (is_finite_subset enum_STATUT1 (t2tb14 s1) (t2tb14 s2) c)
  (and (mem3 x s2)
  (and (mem3 x s1) (and (and (= z (add3 x s1)) (= z1 s2)) (= z2 c)))))))
  (exists ((x enum_STATUT) (s1 (set enum_STATUT)) (s2 (set enum_STATUT))
  (c Int))
  (and (is_finite_subset enum_STATUT1 (t2tb14 s1) (t2tb14 s2) c)
  (and (mem3 x s2)
  (and (not (mem3 x s1))
  (and (and (= z (add3 x s1)) (= z1 s2)) (= z2 (+ c 1)))))))))))

;; is_finite_subset_inversion
  (assert
  (forall ((z (set (tuple2 Int Int))) (z1 (set (tuple2 Int Int))) (z2 Int))
  (=> (is_finite_subset (tuple21 int int) (t2tb5 z) (t2tb5 z1) z2)
  (or
  (or
  (exists ((s (set (tuple2 Int Int))))
  (and (and (= z empty2) (= z1 s)) (= z2 0)))
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
  (forall ((z (set Int)) (z1 (set Int)) (z2 Int))
  (=> (is_finite_subset int (t2tb z) (t2tb z1) z2)
  (or
  (or (exists ((s (set Int))) (and (and (= z empty1) (= z1 s)) (= z2 0)))
  (exists ((x Int) (s1 (set Int)) (s2 (set Int)) (c Int))
  (and (is_finite_subset int (t2tb s1) (t2tb s2) c)
  (and (mem1 x s2)
  (and (mem1 x s1) (and (and (= z (add1 x s1)) (= z1 s2)) (= z2 c)))))))
  (exists ((x Int) (s1 (set Int)) (s2 (set Int)) (c Int))
  (and (is_finite_subset int (t2tb s1) (t2tb s2) c)
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
  (forall ((s (set enum_STATUT))) (mem (set1 enum_STATUT1) (t2tb14 empty4)
  (finite_subsets enum_STATUT1 (t2tb14 s)))))

;; finite_Empty
  (assert
  (forall ((s (set (tuple2 Int Int)))) (mem (set1 (tuple21 int int))
  (t2tb5 empty2) (finite_subsets (tuple21 int int) (t2tb5 s)))))

;; finite_Empty
  (assert
  (forall ((s (set Int))) (mem (set1 int) (t2tb empty1)
  (finite_subsets int (t2tb s)))))

;; finite_Empty
  (assert
  (forall ((a ty))
  (forall ((s uni)) (mem (set1 a) (empty a) (finite_subsets a s)))))

;; finite_Add
  (assert
  (forall ((x enum_STATUT) (s1 (set enum_STATUT)) (s2 (set enum_STATUT)))
  (=> (mem (set1 enum_STATUT1) (t2tb14 s1)
  (finite_subsets enum_STATUT1 (t2tb14 s2)))
  (=> (mem3 x s2) (mem (set1 enum_STATUT1) (t2tb14 (add3 x s1))
  (finite_subsets enum_STATUT1 (t2tb14 s2)))))))

;; finite_Add
  (assert
  (forall ((x Int) (s1 (set Int)) (s2 (set Int)))
  (=> (mem (set1 int) (t2tb s1) (finite_subsets int (t2tb s2)))
  (=> (mem1 x s2) (mem (set1 int) (t2tb (add1 x s1))
  (finite_subsets int (t2tb s2)))))))

;; finite_Add
  (assert
  (forall ((a ty))
  (forall ((x uni) (s1 uni) (s2 uni))
  (=> (mem (set1 a) s1 (finite_subsets a s2))
  (=> (mem a x s2) (mem (set1 a) (add a x s1) (finite_subsets a s2)))))))

;; finite_Union
  (assert
  (forall ((s1 (set enum_STATUT)) (s2 (set enum_STATUT))
  (s3 (set enum_STATUT)))
  (=> (mem (set1 enum_STATUT1) (t2tb14 s1)
  (finite_subsets enum_STATUT1 (t2tb14 s3)))
  (=> (mem (set1 enum_STATUT1) (t2tb14 s2)
  (finite_subsets enum_STATUT1 (t2tb14 s3))) (mem (set1 enum_STATUT1)
  (t2tb14 (union4 s1 s2)) (finite_subsets enum_STATUT1 (t2tb14 s3)))))))

;; finite_Union
  (assert
  (forall ((s1 (set (tuple2 Int Int))) (s2 (set (tuple2 Int Int)))
  (s3 (set (tuple2 Int Int))))
  (=> (mem (set1 (tuple21 int int)) (t2tb5 s1)
  (finite_subsets (tuple21 int int) (t2tb5 s3)))
  (=> (mem (set1 (tuple21 int int)) (t2tb5 s2)
  (finite_subsets (tuple21 int int) (t2tb5 s3))) (mem
  (set1 (tuple21 int int)) (t2tb5 (union2 s1 s2))
  (finite_subsets (tuple21 int int) (t2tb5 s3)))))))

;; finite_Union
  (assert
  (forall ((s1 (set Int)) (s2 (set Int)) (s3 (set Int)))
  (=> (mem (set1 int) (t2tb s1) (finite_subsets int (t2tb s3)))
  (=> (mem (set1 int) (t2tb s2) (finite_subsets int (t2tb s3))) (mem
  (set1 int) (t2tb (union1 s1 s2)) (finite_subsets int (t2tb s3)))))))

;; finite_Union
  (assert
  (forall ((a ty))
  (forall ((s1 uni) (s2 uni) (s3 uni))
  (=> (mem (set1 a) s1 (finite_subsets a s3))
  (=> (mem (set1 a) s2 (finite_subsets a s3)) (mem (set1 a) (union a s1 s2)
  (finite_subsets a s3)))))))

;; finite_inversion
  (assert
  (forall ((s1 (set enum_STATUT)) (s2 (set enum_STATUT)))
  (=> (mem (set1 enum_STATUT1) (t2tb14 s1)
  (finite_subsets enum_STATUT1 (t2tb14 s2)))
  (or (= s1 empty4)
  (exists ((x enum_STATUT) (s3 (set enum_STATUT)))
  (and (= s1 (add3 x s3)) (mem (set1 enum_STATUT1) (t2tb14 s3)
  (finite_subsets enum_STATUT1 (t2tb14 s2)))))))))

;; finite_inversion
  (assert
  (forall ((s1 (set (tuple2 Int Int))) (s2 (set (tuple2 Int Int))))
  (=> (mem (set1 (tuple21 int int)) (t2tb5 s1)
  (finite_subsets (tuple21 int int) (t2tb5 s2)))
  (or (= s1 empty2)
  (exists ((x (tuple2 Int Int)) (s3 (set (tuple2 Int Int))))
  (and (= s1 (tb2t5 (add (tuple21 int int) (t2tb6 x) (t2tb5 s3)))) (mem
  (set1 (tuple21 int int)) (t2tb5 s3)
  (finite_subsets (tuple21 int int) (t2tb5 s2)))))))))

;; finite_inversion
  (assert
  (forall ((s1 (set Int)) (s2 (set Int)))
  (=> (mem (set1 int) (t2tb s1) (finite_subsets int (t2tb s2)))
  (or (= s1 empty1)
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
  (forall ((s (set enum_STATUT)) (x (set enum_STATUT)))
  (= (mem (set1 enum_STATUT1) (t2tb14 x)
  (non_empty_finite_subsets enum_STATUT1 (t2tb14 s)))
  (exists ((c Int))
  (and (is_finite_subset enum_STATUT1 (t2tb14 x) (t2tb14 s) c)
  (not (= x empty4)))))))

;; non_empty_finite_subsets_def
  (assert
  (forall ((s (set (tuple2 Int Int))) (x (set (tuple2 Int Int))))
  (= (mem (set1 (tuple21 int int)) (t2tb5 x)
  (non_empty_finite_subsets (tuple21 int int) (t2tb5 s)))
  (exists ((c Int))
  (and (is_finite_subset (tuple21 int int) (t2tb5 x) (t2tb5 s) c)
  (not (= x empty2)))))))

;; non_empty_finite_subsets_def
  (assert
  (forall ((s (set Int)) (x (set Int)))
  (= (mem (set1 int) (t2tb x) (non_empty_finite_subsets int (t2tb s)))
  (exists ((c Int))
  (and (is_finite_subset int (t2tb x) (t2tb s) c) (not (= x empty1)))))))

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
  (assert (= (card enum_STATUT1 (t2tb14 empty4)) 0))

;; card_Empty
  (assert (= (card (tuple21 int int) (t2tb5 empty2)) 0))

;; card_Empty
  (assert (= (card int (t2tb empty1)) 0))

;; card_Empty
  (assert (forall ((a ty)) (= (card a (empty a)) 0)))

;; card_Add_not_mem
  (assert
  (forall ((x enum_STATUT) (s1 (set enum_STATUT)) (s2 (set enum_STATUT)))
  (! (=> (mem (set1 enum_STATUT1) (t2tb14 s1)
     (finite_subsets enum_STATUT1 (t2tb14 s2)))
     (=> (not (mem3 x s1))
     (= (card enum_STATUT1 (t2tb14 (add3 x s1))) (+ (card enum_STATUT1
                                                    (t2tb14 s1)) 1)))) :pattern ((mem
  (set1 enum_STATUT1) (t2tb14 s1) (finite_subsets enum_STATUT1 (t2tb14 s2)))
  (card enum_STATUT1 (t2tb14 (add3 x s1)))) )))

;; card_Add_not_mem
  (assert
  (forall ((x Int) (s1 (set Int)) (s2 (set Int)))
  (! (=> (mem (set1 int) (t2tb s1) (finite_subsets int (t2tb s2)))
     (=> (not (mem1 x s1))
     (= (card int (t2tb (add1 x s1))) (+ (card int (t2tb s1)) 1)))) :pattern ((mem
  (set1 int) (t2tb s1) (finite_subsets int (t2tb s2)))
  (card int (t2tb (add1 x s1)))) )))

;; card_Add_not_mem
  (assert
  (forall ((a ty))
  (forall ((x uni) (s1 uni) (s2 uni))
  (! (=> (mem (set1 a) s1 (finite_subsets a s2))
     (=> (not (mem a x s1)) (= (card a (add a x s1)) (+ (card a s1) 1)))) :pattern ((mem
  (set1 a) s1 (finite_subsets a s2)) (card a (add a x s1))) ))))

;; card_Add_mem
  (assert
  (forall ((x enum_STATUT) (s1 (set enum_STATUT)) (s2 (set enum_STATUT)))
  (! (=> (mem (set1 enum_STATUT1) (t2tb14 s1)
     (finite_subsets enum_STATUT1 (t2tb14 s2)))
     (=> (mem3 x s1)
     (= (card enum_STATUT1 (t2tb14 (add3 x s1))) (card enum_STATUT1
                                                 (t2tb14 s1))))) :pattern ((mem
  (set1 enum_STATUT1) (t2tb14 s1) (finite_subsets enum_STATUT1 (t2tb14 s2)))
  (card enum_STATUT1 (t2tb14 (add3 x s1)))) )))

;; card_Add_mem
  (assert
  (forall ((x Int) (s1 (set Int)) (s2 (set Int)))
  (! (=> (mem (set1 int) (t2tb s1) (finite_subsets int (t2tb s2)))
     (=> (mem1 x s1) (= (card int (t2tb (add1 x s1))) (card int (t2tb s1))))) :pattern ((mem
  (set1 int) (t2tb s1) (finite_subsets int (t2tb s2)))
  (card int (t2tb (add1 x s1)))) )))

;; card_Add_mem
  (assert
  (forall ((a ty))
  (forall ((x uni) (s1 uni) (s2 uni))
  (! (=> (mem (set1 a) s1 (finite_subsets a s2))
     (=> (mem a x s1) (= (card a (add a x s1)) (card a s1)))) :pattern ((mem
  (set1 a) s1 (finite_subsets a s2)) (card a (add a x s1))) ))))

;; card_Union
  (assert
  (forall ((s1 (set enum_STATUT)) (s2 (set enum_STATUT))
  (s3 (set enum_STATUT)))
  (! (=> (mem (set1 enum_STATUT1) (t2tb14 s1)
     (finite_subsets enum_STATUT1 (t2tb14 s3)))
     (=> (mem (set1 enum_STATUT1) (t2tb14 s2)
     (finite_subsets enum_STATUT1 (t2tb14 s3)))
     (=> (is_empty enum_STATUT1 (inter enum_STATUT1 (t2tb14 s1) (t2tb14 s2)))
     (= (card enum_STATUT1 (t2tb14 (union4 s1 s2))) (+ (card enum_STATUT1
                                                       (t2tb14 s1)) (card
                                                                    enum_STATUT1
                                                                    (t2tb14
                                                                    s2))))))) :pattern ((mem
  (set1 enum_STATUT1) (t2tb14 s1) (finite_subsets enum_STATUT1 (t2tb14 s3)))
  (mem (set1 enum_STATUT1) (t2tb14 s2)
  (finite_subsets enum_STATUT1 (t2tb14 s3)))
  (card enum_STATUT1 (t2tb14 (union4 s1 s2)))) )))

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
     (= (card (tuple21 int int) (t2tb5 (union2 s1 s2))) (+ (card
                                                           (tuple21 int int)
                                                           (t2tb5 s1)) 
     (card (tuple21 int int) (t2tb5 s2))))))) :pattern ((mem
  (set1 (tuple21 int int)) (t2tb5 s1)
  (finite_subsets (tuple21 int int) (t2tb5 s3))) (mem
  (set1 (tuple21 int int)) (t2tb5 s2)
  (finite_subsets (tuple21 int int) (t2tb5 s3)))
  (card (tuple21 int int) (t2tb5 (union2 s1 s2)))) )))

;; card_Union
  (assert
  (forall ((s1 (set Int)) (s2 (set Int)) (s3 (set Int)))
  (! (=> (mem (set1 int) (t2tb s1) (finite_subsets int (t2tb s3)))
     (=> (mem (set1 int) (t2tb s2) (finite_subsets int (t2tb s3)))
     (=> (is_empty int (inter int (t2tb s1) (t2tb s2)))
     (= (card int (t2tb (union1 s1 s2))) (+ (card int (t2tb s1)) (card 
                                                                 int
                                                                 (t2tb s2))))))) :pattern ((mem
  (set1 int) (t2tb s1) (finite_subsets int (t2tb s3))) (mem (set1 int)
  (t2tb s2) (finite_subsets int (t2tb s3)))
  (card int (t2tb (union1 s1 s2)))) )))

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
  (forall ((a1 uni) (b (set enum_STATUT)) (x uni) (y enum_STATUT))
  (! (= (mem (tuple21 a enum_STATUT1) (Tuple2 a enum_STATUT1 x (t2tb15 y))
     (times enum_STATUT1 a a1 (t2tb14 b))) (and (mem a x a1) (mem3 y b))) :pattern ((mem
  (tuple21 a enum_STATUT1) (Tuple2 a enum_STATUT1 x (t2tb15 y))
  (times enum_STATUT1 a a1 (t2tb14 b)))) ))))

;; times_def
  (assert
  (forall ((a ty))
  (forall ((a1 uni) (b (set Int)) (x uni) (y Int))
  (! (= (mem (tuple21 a int) (Tuple2 a int x (t2tb1 y))
     (times int a a1 (t2tb b))) (and (mem a x a1) (mem1 y b))) :pattern ((mem
  (tuple21 a int) (Tuple2 a int x (t2tb1 y)) (times int a a1 (t2tb b)))) ))))

;; times_def
  (assert
  (forall ((a (set enum_STATUT)) (b (set enum_STATUT)) (x enum_STATUT)
  (y enum_STATUT))
  (! (= (mem (tuple21 enum_STATUT1 enum_STATUT1)
     (Tuple2 enum_STATUT1 enum_STATUT1 (t2tb15 x) (t2tb15 y))
     (times enum_STATUT1 enum_STATUT1 (t2tb14 a) (t2tb14 b)))
     (and (mem3 x a) (mem3 y b))) :pattern ((mem
  (tuple21 enum_STATUT1 enum_STATUT1)
  (Tuple2 enum_STATUT1 enum_STATUT1 (t2tb15 x) (t2tb15 y))
  (times enum_STATUT1 enum_STATUT1 (t2tb14 a) (t2tb14 b)))) )))

;; times_def
  (assert
  (forall ((a (set enum_STATUT)) (b (set Int)) (x enum_STATUT) (y Int))
  (! (= (mem (tuple21 enum_STATUT1 int)
     (Tuple2 enum_STATUT1 int (t2tb15 x) (t2tb1 y))
     (times int enum_STATUT1 (t2tb14 a) (t2tb b)))
     (and (mem3 x a) (mem1 y b))) :pattern ((mem
  (tuple21 enum_STATUT1 int) (Tuple2 enum_STATUT1 int (t2tb15 x) (t2tb1 y))
  (times int enum_STATUT1 (t2tb14 a) (t2tb b)))) )))

;; times_def
  (assert
  (forall ((b ty))
  (forall ((a (set enum_STATUT)) (b1 uni) (x enum_STATUT) (y uni))
  (! (= (mem (tuple21 enum_STATUT1 b) (Tuple2 enum_STATUT1 b (t2tb15 x) y)
     (times b enum_STATUT1 (t2tb14 a) b1)) (and (mem3 x a) (mem b y b1))) :pattern ((mem
  (tuple21 enum_STATUT1 b) (Tuple2 enum_STATUT1 b (t2tb15 x) y)
  (times b enum_STATUT1 (t2tb14 a) b1))) ))))

;; times_def
  (assert
  (forall ((a (set Int)) (b (set enum_STATUT)) (x Int) (y enum_STATUT))
  (! (= (mem (tuple21 int enum_STATUT1)
     (Tuple2 int enum_STATUT1 (t2tb1 x) (t2tb15 y))
     (times enum_STATUT1 int (t2tb a) (t2tb14 b)))
     (and (mem1 x a) (mem3 y b))) :pattern ((mem
  (tuple21 int enum_STATUT1) (Tuple2 int enum_STATUT1 (t2tb1 x) (t2tb15 y))
  (times enum_STATUT1 int (t2tb a) (t2tb14 b)))) )))

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
  (forall ((r uni) (u uni) (v (set enum_STATUT)))
  (and
  (=> (subset (tuple21 a enum_STATUT1) r (times enum_STATUT1 a u (t2tb14 v)))
  (forall ((x uni) (y enum_STATUT))
  (=> (mem (tuple21 a enum_STATUT1) (Tuple2 a enum_STATUT1 x (t2tb15 y)) r)
  (and (mem a x u) (mem3 y v)))))
  (=>
  (forall ((x uni) (y enum_STATUT))
  (=> (sort a x)
  (=> (mem (tuple21 a enum_STATUT1) (Tuple2 a enum_STATUT1 x (t2tb15 y)) r)
  (and (mem a x u) (mem3 y v))))) (subset (tuple21 a enum_STATUT1) r
  (times enum_STATUT1 a u (t2tb14 v))))))))

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
  (forall ((r (set (tuple2 enum_STATUT enum_STATUT))) (u (set enum_STATUT))
  (v (set enum_STATUT)))
  (= (subset (tuple21 enum_STATUT1 enum_STATUT1) (t2tb43 r)
  (times enum_STATUT1 enum_STATUT1 (t2tb14 u) (t2tb14 v)))
  (forall ((x enum_STATUT) (y enum_STATUT))
  (=> (mem (tuple21 enum_STATUT1 enum_STATUT1)
  (Tuple2 enum_STATUT1 enum_STATUT1 (t2tb15 x) (t2tb15 y)) (t2tb43 r))
  (and (mem3 x u) (mem3 y v)))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 enum_STATUT Int))) (u (set enum_STATUT))
  (v (set Int)))
  (= (subset (tuple21 enum_STATUT1 int) (t2tb46 r)
  (times int enum_STATUT1 (t2tb14 u) (t2tb v)))
  (forall ((x enum_STATUT) (y Int))
  (=> (mem (tuple21 enum_STATUT1 int)
  (Tuple2 enum_STATUT1 int (t2tb15 x) (t2tb1 y)) (t2tb46 r))
  (and (mem3 x u) (mem1 y v)))))))

;; subset_of_times
  (assert
  (forall ((b ty))
  (forall ((r uni) (u (set enum_STATUT)) (v uni))
  (and
  (=> (subset (tuple21 enum_STATUT1 b) r (times b enum_STATUT1 (t2tb14 u) v))
  (forall ((x enum_STATUT) (y uni))
  (=> (mem (tuple21 enum_STATUT1 b) (Tuple2 enum_STATUT1 b (t2tb15 x) y) r)
  (and (mem3 x u) (mem b y v)))))
  (=>
  (forall ((x enum_STATUT) (y uni))
  (=> (sort b y)
  (=> (mem (tuple21 enum_STATUT1 b) (Tuple2 enum_STATUT1 b (t2tb15 x) y) r)
  (and (mem3 x u) (mem b y v))))) (subset (tuple21 enum_STATUT1 b) r
  (times b enum_STATUT1 (t2tb14 u) v)))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 Int enum_STATUT))) (u (set Int))
  (v (set enum_STATUT)))
  (= (subset (tuple21 int enum_STATUT1) (t2tb49 r)
  (times enum_STATUT1 int (t2tb u) (t2tb14 v)))
  (forall ((x Int) (y enum_STATUT))
  (=> (mem (tuple21 int enum_STATUT1)
  (Tuple2 int enum_STATUT1 (t2tb1 x) (t2tb15 y)) (t2tb49 r))
  (and (mem1 x u) (mem3 y v)))))))

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
  (forall ((a ty))
  (forall ((s uni) (x uni) (y enum_STATUT))
  (! (=> (mem a x s)
     (= (tb2t15
        (apply enum_STATUT1 a
        (times enum_STATUT1 a s (t2tb14 (add3 y empty4))) x)) y)) :pattern (
  (tb2t15
  (apply enum_STATUT1 a (times enum_STATUT1 a s (t2tb14 (add3 y empty4))) x))) ))))

;; apply_times
  (assert
  (forall ((a ty))
  (forall ((s uni) (x uni) (y (tuple2 Int Int)))
  (! (=> (mem a x s)
     (= (tb2t6
        (apply (tuple21 int int) a
        (times (tuple21 int int) a s
        (add (tuple21 int int) (t2tb6 y) (t2tb5 empty2))) x)) y)) :pattern (
  (tb2t6
  (apply (tuple21 int int) a
  (times (tuple21 int int) a s
  (add (tuple21 int int) (t2tb6 y) (t2tb5 empty2))) x))) ))))

;; apply_times
  (assert
  (forall ((a ty))
  (forall ((s uni) (x uni) (y Int))
  (! (=> (mem a x s)
     (= (tb2t1 (apply int a (times int a s (t2tb (add1 y empty1))) x)) y)) :pattern (
  (tb2t1 (apply int a (times int a s (t2tb (add1 y empty1))) x))) ))))

;; apply_times
  (assert
  (forall ((s (set enum_STATUT)) (x enum_STATUT) (y enum_STATUT))
  (! (=> (mem3 x s)
     (= (tb2t15
        (apply enum_STATUT1 enum_STATUT1
        (times enum_STATUT1 enum_STATUT1 (t2tb14 s) (t2tb14 (add3 y empty4)))
        (t2tb15 x))) y)) :pattern ((tb2t15
                                   (apply enum_STATUT1 enum_STATUT1
                                   (times enum_STATUT1 enum_STATUT1
                                   (t2tb14 s) (t2tb14 (add3 y empty4)))
                                   (t2tb15 x)))) )))

;; apply_times
  (assert
  (forall ((s (set enum_STATUT)) (x enum_STATUT) (y (tuple2 Int Int)))
  (! (=> (mem3 x s)
     (= (tb2t6
        (apply (tuple21 int int) enum_STATUT1
        (times (tuple21 int int) enum_STATUT1 (t2tb14 s)
        (add (tuple21 int int) (t2tb6 y) (t2tb5 empty2))) (t2tb15 x))) y)) :pattern (
  (tb2t6
  (apply (tuple21 int int) enum_STATUT1
  (times (tuple21 int int) enum_STATUT1 (t2tb14 s)
  (add (tuple21 int int) (t2tb6 y) (t2tb5 empty2))) (t2tb15 x)))) )))

;; apply_times
  (assert
  (forall ((s (set enum_STATUT)) (x enum_STATUT) (y Int))
  (! (=> (mem3 x s)
     (= (tb2t1
        (apply int enum_STATUT1
        (times int enum_STATUT1 (t2tb14 s) (t2tb (add1 y empty1)))
        (t2tb15 x))) y)) :pattern ((tb2t1
                                   (apply int enum_STATUT1
                                   (times int enum_STATUT1 (t2tb14 s)
                                   (t2tb (add1 y empty1))) (t2tb15 x)))) )))

;; apply_times
  (assert
  (forall ((b ty))
  (forall ((s (set enum_STATUT)) (x enum_STATUT) (y uni))
  (! (=> (sort b y)
     (=> (mem3 x s)
     (= (apply b enum_STATUT1
        (times b enum_STATUT1 (t2tb14 s) (add b y (empty b))) (t2tb15 x)) y))) :pattern (
  (apply b enum_STATUT1 (times b enum_STATUT1 (t2tb14 s) (add b y (empty b)))
  (t2tb15 x))) ))))

;; apply_times
  (assert
  (forall ((s (set Int)) (x Int) (y enum_STATUT))
  (! (=> (mem1 x s)
     (= (tb2t15
        (apply enum_STATUT1 int
        (times enum_STATUT1 int (t2tb s) (t2tb14 (add3 y empty4))) (t2tb1 x))) y)) :pattern (
  (tb2t15
  (apply enum_STATUT1 int
  (times enum_STATUT1 int (t2tb s) (t2tb14 (add3 y empty4))) (t2tb1 x)))) )))

;; apply_times
  (assert
  (forall ((s (set Int)) (x Int) (y (tuple2 Int Int)))
  (! (=> (mem1 x s)
     (= (tb2t6
        (apply (tuple21 int int) int
        (times (tuple21 int int) int (t2tb s)
        (add (tuple21 int int) (t2tb6 y) (t2tb5 empty2))) (t2tb1 x))) y)) :pattern (
  (tb2t6
  (apply (tuple21 int int) int
  (times (tuple21 int int) int (t2tb s)
  (add (tuple21 int int) (t2tb6 y) (t2tb5 empty2))) (t2tb1 x)))) )))

;; apply_times
  (assert
  (forall ((s (set Int)) (x Int) (y Int))
  (! (=> (mem1 x s)
     (= (tb2t1
        (apply int int (times int int (t2tb s) (t2tb (add1 y empty1)))
        (t2tb1 x))) y)) :pattern ((tb2t1
                                  (apply int int
                                  (times int int (t2tb s)
                                  (t2tb (add1 y empty1))) (t2tb1 x)))) )))

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

(declare-fun infix_lspl (ty ty uni uni) uni)

;; infix <+_sort
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (x1 uni)) (sort (set1 (tuple21 a b))
  (infix_lspl b a x x1)))))

;; overriding_def
  (assert
  (forall ((b ty))
  (forall ((x enum_STATUT) (y uni) (q uni) (r uni))
  (= (mem (tuple21 enum_STATUT1 b) (Tuple2 enum_STATUT1 b (t2tb15 x) y)
  (infix_lspl b enum_STATUT1 q r))
  (ite (mem3 x (tb2t14 (dom b enum_STATUT1 r))) (mem (tuple21 enum_STATUT1 b)
  (Tuple2 enum_STATUT1 b (t2tb15 x) y) r) (mem (tuple21 enum_STATUT1 b)
  (Tuple2 enum_STATUT1 b (t2tb15 x) y) q))))))

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
  (forall ((b ty))
  (forall ((f uni) (g uni))
  (! (= (tb2t14 (dom b enum_STATUT1 (infix_lspl b enum_STATUT1 f g))) 
  (union4 (tb2t14 (dom b enum_STATUT1 f)) (tb2t14 (dom b enum_STATUT1 g)))) :pattern (
  (tb2t14 (dom b enum_STATUT1 (infix_lspl b enum_STATUT1 f g)))) ))))

;; dom_overriding
  (assert
  (forall ((b ty))
  (forall ((f uni) (g uni))
  (! (= (tb2t5
        (dom b (tuple21 int int) (infix_lspl b (tuple21 int int) f g))) 
  (union2 (tb2t5 (dom b (tuple21 int int) f))
  (tb2t5 (dom b (tuple21 int int) g)))) :pattern ((tb2t5
                                                  (dom b (tuple21 int int)
                                                  (infix_lspl b
                                                  (tuple21 int int) f g)))) ))))

;; dom_overriding
  (assert
  (forall ((b ty))
  (forall ((f uni) (g uni))
  (! (= (tb2t (dom b int (infix_lspl b int f g))) (union1
                                                  (tb2t (dom b int f))
                                                  (tb2t (dom b int g)))) :pattern (
  (tb2t (dom b int (infix_lspl b int f g)))) ))))

;; dom_overriding
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (g uni))
  (! (= (dom b a (infix_lspl b a f g)) (union a (dom b a f) (dom b a g))) :pattern (
  (dom b a (infix_lspl b a f g))) ))))

;; apply_overriding_1
  (assert
  (forall ((b ty))
  (forall ((s (set enum_STATUT)) (t uni) (f uni) (g uni) (x enum_STATUT))
  (! (=>
     (and (mem (set1 (tuple21 enum_STATUT1 b)) f
     (infix_plmngt b enum_STATUT1 (t2tb14 s) t)) (mem
     (set1 (tuple21 enum_STATUT1 b)) g
     (infix_plmngt b enum_STATUT1 (t2tb14 s) t)))
     (=> (mem3 x (tb2t14 (dom b enum_STATUT1 g)))
     (= (apply b enum_STATUT1 (infix_lspl b enum_STATUT1 f g) (t2tb15 x)) 
     (apply b enum_STATUT1 g (t2tb15 x))))) :pattern ((mem
  (set1 (tuple21 enum_STATUT1 b)) f
  (infix_plmngt b enum_STATUT1 (t2tb14 s) t)) (mem
  (set1 (tuple21 enum_STATUT1 b)) g
  (infix_plmngt b enum_STATUT1 (t2tb14 s) t))
  (apply b enum_STATUT1 (infix_lspl b enum_STATUT1 f g) (t2tb15 x))) ))))

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
  (forall ((s (set enum_STATUT)) (t uni) (f uni) (g uni) (x enum_STATUT))
  (! (=>
     (and (mem (set1 (tuple21 enum_STATUT1 b)) f
     (infix_plmngt b enum_STATUT1 (t2tb14 s) t)) (mem
     (set1 (tuple21 enum_STATUT1 b)) g
     (infix_plmngt b enum_STATUT1 (t2tb14 s) t)))
     (=> (not (mem3 x (tb2t14 (dom b enum_STATUT1 g))))
     (=> (mem3 x (tb2t14 (dom b enum_STATUT1 f)))
     (= (apply b enum_STATUT1 (infix_lspl b enum_STATUT1 f g) (t2tb15 x)) 
     (apply b enum_STATUT1 f (t2tb15 x)))))) :pattern ((mem
  (set1 (tuple21 enum_STATUT1 b)) f
  (infix_plmngt b enum_STATUT1 (t2tb14 s) t))
  (apply b enum_STATUT1 (infix_lspl b enum_STATUT1 f g) (t2tb15 x))) :pattern ((mem
  (set1 (tuple21 enum_STATUT1 b)) g
  (infix_plmngt b enum_STATUT1 (t2tb14 s) t))
  (apply b enum_STATUT1 (infix_lspl b enum_STATUT1 f g) (t2tb15 x))) ))))

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

(declare-sort enum_ETAT_AUTOMATE 0)

(declare-fun enum_ETAT_AUTOMATE1 () ty)

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

(declare-fun t2tb8 ((set enum_ETAT_AUTOMATE)) uni)

;; t2tb_sort
  (assert
  (forall ((x (set enum_ETAT_AUTOMATE))) (sort (set1 enum_ETAT_AUTOMATE1)
  (t2tb8 x))))

(declare-fun tb2t8 (uni) (set enum_ETAT_AUTOMATE))

;; BridgeL
  (assert
  (forall ((i (set enum_ETAT_AUTOMATE)))
  (! (= (tb2t8 (t2tb8 i)) i) :pattern ((t2tb8 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 enum_ETAT_AUTOMATE1) j) (= (t2tb8 (tb2t8 j)) j)) :pattern (
  (t2tb8 (tb2t8 j))) )))

(declare-fun t2tb9 (enum_ETAT_AUTOMATE) uni)

;; t2tb_sort
  (assert
  (forall ((x enum_ETAT_AUTOMATE)) (sort enum_ETAT_AUTOMATE1 (t2tb9 x))))

(declare-fun tb2t9 (uni) enum_ETAT_AUTOMATE)

;; BridgeL
  (assert
  (forall ((i enum_ETAT_AUTOMATE))
  (! (= (tb2t9 (t2tb9 i)) i) :pattern ((t2tb9 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort enum_ETAT_AUTOMATE1 j) (= (t2tb9 (tb2t9 j)) j)) :pattern (
  (t2tb9 (tb2t9 j))) )))

;; set_enum_ETAT_AUTOMATE_axiom
  (assert
  (forall ((x enum_ETAT_AUTOMATE)) (mem enum_ETAT_AUTOMATE1 (t2tb9 x)
  (t2tb8 set_enum_ETAT_AUTOMATE))))

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

(declare-sort enum_MESSAGE 0)

(declare-fun enum_MESSAGE1 () ty)

(declare-fun E_Vide () enum_MESSAGE)

(declare-fun E_En_panne () enum_MESSAGE)

(declare-fun E_Veuillez_patienter () enum_MESSAGE)

(declare-fun E_Entrez_votre_carte () enum_MESSAGE)

(declare-fun E_Entrez_votre_code () enum_MESSAGE)

(declare-fun E_Nouvel_essai () enum_MESSAGE)

(declare-fun E_Dernier_essai () enum_MESSAGE)

(declare-fun E_Entrez_somme () enum_MESSAGE)

(declare-fun E_Prenez_vos_billets () enum_MESSAGE)

(declare-fun E_Carte_perimee () enum_MESSAGE)

(declare-fun E_Carte_epuisee () enum_MESSAGE)

(declare-fun E_Carte_invalide () enum_MESSAGE)

(declare-fun E_Carte_interdite () enum_MESSAGE)

(declare-fun E_Caisse_insuffisante () enum_MESSAGE)

(declare-fun E_Solde_insuffisant () enum_MESSAGE)

(declare-fun E_Credit_insuffisant () enum_MESSAGE)

(declare-fun E_Billets_confisques () enum_MESSAGE)

(declare-fun E_Retirez_votre_carte () enum_MESSAGE)

(declare-fun E_Code_invalide () enum_MESSAGE)

(declare-fun E_Carte_confisquee () enum_MESSAGE)

(declare-fun E_Merci_de_votre_visite () enum_MESSAGE)

(declare-fun match_enum_MESSAGE (ty enum_MESSAGE uni uni uni uni uni uni uni
  uni uni uni uni uni uni uni uni uni uni uni uni uni uni) uni)

;; match_enum_MESSAGE_sort
  (assert
  (forall ((a ty))
  (forall ((x enum_MESSAGE) (x1 uni) (x2 uni) (x3 uni) (x4 uni) (x5 uni)
  (x6 uni) (x7 uni) (x8 uni) (x9 uni) (x10 uni) (x11 uni) (x12 uni) (x13 uni)
  (x14 uni) (x15 uni) (x16 uni) (x17 uni) (x18 uni) (x19 uni) (x20 uni)
  (x21 uni)) (sort a
  (match_enum_MESSAGE a x x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
  x16 x17 x18 x19 x20 x21)))))

;; match_enum_MESSAGE_E_Vide
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni) (z9 uni) (z10 uni) (z11 uni) (z12 uni) (z13 uni)
  (z14 uni) (z15 uni) (z16 uni) (z17 uni) (z18 uni) (z19 uni) (z20 uni))
  (=> (sort a z)
  (= (match_enum_MESSAGE a E_Vide z z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12
     z13 z14 z15 z16 z17 z18 z19 z20) z)))))

;; match_enum_MESSAGE_E_En_panne
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni) (z9 uni) (z10 uni) (z11 uni) (z12 uni) (z13 uni)
  (z14 uni) (z15 uni) (z16 uni) (z17 uni) (z18 uni) (z19 uni) (z20 uni))
  (=> (sort a z1)
  (= (match_enum_MESSAGE a E_En_panne z z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11
     z12 z13 z14 z15 z16 z17 z18 z19 z20) z1)))))

;; match_enum_MESSAGE_E_Veuillez_patienter
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni) (z9 uni) (z10 uni) (z11 uni) (z12 uni) (z13 uni)
  (z14 uni) (z15 uni) (z16 uni) (z17 uni) (z18 uni) (z19 uni) (z20 uni))
  (=> (sort a z2)
  (= (match_enum_MESSAGE a E_Veuillez_patienter z z1 z2 z3 z4 z5 z6 z7 z8 z9
     z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20) z2)))))

;; match_enum_MESSAGE_E_Entrez_votre_carte
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni) (z9 uni) (z10 uni) (z11 uni) (z12 uni) (z13 uni)
  (z14 uni) (z15 uni) (z16 uni) (z17 uni) (z18 uni) (z19 uni) (z20 uni))
  (=> (sort a z3)
  (= (match_enum_MESSAGE a E_Entrez_votre_carte z z1 z2 z3 z4 z5 z6 z7 z8 z9
     z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20) z3)))))

;; match_enum_MESSAGE_E_Entrez_votre_code
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni) (z9 uni) (z10 uni) (z11 uni) (z12 uni) (z13 uni)
  (z14 uni) (z15 uni) (z16 uni) (z17 uni) (z18 uni) (z19 uni) (z20 uni))
  (=> (sort a z4)
  (= (match_enum_MESSAGE a E_Entrez_votre_code z z1 z2 z3 z4 z5 z6 z7 z8 z9
     z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20) z4)))))

;; match_enum_MESSAGE_E_Nouvel_essai
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni) (z9 uni) (z10 uni) (z11 uni) (z12 uni) (z13 uni)
  (z14 uni) (z15 uni) (z16 uni) (z17 uni) (z18 uni) (z19 uni) (z20 uni))
  (=> (sort a z5)
  (= (match_enum_MESSAGE a E_Nouvel_essai z z1 z2 z3 z4 z5 z6 z7 z8 z9 z10
     z11 z12 z13 z14 z15 z16 z17 z18 z19 z20) z5)))))

;; match_enum_MESSAGE_E_Dernier_essai
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni) (z9 uni) (z10 uni) (z11 uni) (z12 uni) (z13 uni)
  (z14 uni) (z15 uni) (z16 uni) (z17 uni) (z18 uni) (z19 uni) (z20 uni))
  (=> (sort a z6)
  (= (match_enum_MESSAGE a E_Dernier_essai z z1 z2 z3 z4 z5 z6 z7 z8 z9 z10
     z11 z12 z13 z14 z15 z16 z17 z18 z19 z20) z6)))))

;; match_enum_MESSAGE_E_Entrez_somme
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni) (z9 uni) (z10 uni) (z11 uni) (z12 uni) (z13 uni)
  (z14 uni) (z15 uni) (z16 uni) (z17 uni) (z18 uni) (z19 uni) (z20 uni))
  (=> (sort a z7)
  (= (match_enum_MESSAGE a E_Entrez_somme z z1 z2 z3 z4 z5 z6 z7 z8 z9 z10
     z11 z12 z13 z14 z15 z16 z17 z18 z19 z20) z7)))))

;; match_enum_MESSAGE_E_Prenez_vos_billets
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni) (z9 uni) (z10 uni) (z11 uni) (z12 uni) (z13 uni)
  (z14 uni) (z15 uni) (z16 uni) (z17 uni) (z18 uni) (z19 uni) (z20 uni))
  (=> (sort a z8)
  (= (match_enum_MESSAGE a E_Prenez_vos_billets z z1 z2 z3 z4 z5 z6 z7 z8 z9
     z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20) z8)))))

;; match_enum_MESSAGE_E_Carte_perimee
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni) (z9 uni) (z10 uni) (z11 uni) (z12 uni) (z13 uni)
  (z14 uni) (z15 uni) (z16 uni) (z17 uni) (z18 uni) (z19 uni) (z20 uni))
  (=> (sort a z9)
  (= (match_enum_MESSAGE a E_Carte_perimee z z1 z2 z3 z4 z5 z6 z7 z8 z9 z10
     z11 z12 z13 z14 z15 z16 z17 z18 z19 z20) z9)))))

;; match_enum_MESSAGE_E_Carte_epuisee
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni) (z9 uni) (z10 uni) (z11 uni) (z12 uni) (z13 uni)
  (z14 uni) (z15 uni) (z16 uni) (z17 uni) (z18 uni) (z19 uni) (z20 uni))
  (=> (sort a z10)
  (= (match_enum_MESSAGE a E_Carte_epuisee z z1 z2 z3 z4 z5 z6 z7 z8 z9 z10
     z11 z12 z13 z14 z15 z16 z17 z18 z19 z20) z10)))))

;; match_enum_MESSAGE_E_Carte_invalide
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni) (z9 uni) (z10 uni) (z11 uni) (z12 uni) (z13 uni)
  (z14 uni) (z15 uni) (z16 uni) (z17 uni) (z18 uni) (z19 uni) (z20 uni))
  (=> (sort a z11)
  (= (match_enum_MESSAGE a E_Carte_invalide z z1 z2 z3 z4 z5 z6 z7 z8 z9 z10
     z11 z12 z13 z14 z15 z16 z17 z18 z19 z20) z11)))))

;; match_enum_MESSAGE_E_Carte_interdite
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni) (z9 uni) (z10 uni) (z11 uni) (z12 uni) (z13 uni)
  (z14 uni) (z15 uni) (z16 uni) (z17 uni) (z18 uni) (z19 uni) (z20 uni))
  (=> (sort a z12)
  (= (match_enum_MESSAGE a E_Carte_interdite z z1 z2 z3 z4 z5 z6 z7 z8 z9 z10
     z11 z12 z13 z14 z15 z16 z17 z18 z19 z20) z12)))))

;; match_enum_MESSAGE_E_Caisse_insuffisante
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni) (z9 uni) (z10 uni) (z11 uni) (z12 uni) (z13 uni)
  (z14 uni) (z15 uni) (z16 uni) (z17 uni) (z18 uni) (z19 uni) (z20 uni))
  (=> (sort a z13)
  (= (match_enum_MESSAGE a E_Caisse_insuffisante z z1 z2 z3 z4 z5 z6 z7 z8 z9
     z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20) z13)))))

;; match_enum_MESSAGE_E_Solde_insuffisant
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni) (z9 uni) (z10 uni) (z11 uni) (z12 uni) (z13 uni)
  (z14 uni) (z15 uni) (z16 uni) (z17 uni) (z18 uni) (z19 uni) (z20 uni))
  (=> (sort a z14)
  (= (match_enum_MESSAGE a E_Solde_insuffisant z z1 z2 z3 z4 z5 z6 z7 z8 z9
     z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20) z14)))))

;; match_enum_MESSAGE_E_Credit_insuffisant
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni) (z9 uni) (z10 uni) (z11 uni) (z12 uni) (z13 uni)
  (z14 uni) (z15 uni) (z16 uni) (z17 uni) (z18 uni) (z19 uni) (z20 uni))
  (=> (sort a z15)
  (= (match_enum_MESSAGE a E_Credit_insuffisant z z1 z2 z3 z4 z5 z6 z7 z8 z9
     z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20) z15)))))

;; match_enum_MESSAGE_E_Billets_confisques
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni) (z9 uni) (z10 uni) (z11 uni) (z12 uni) (z13 uni)
  (z14 uni) (z15 uni) (z16 uni) (z17 uni) (z18 uni) (z19 uni) (z20 uni))
  (=> (sort a z16)
  (= (match_enum_MESSAGE a E_Billets_confisques z z1 z2 z3 z4 z5 z6 z7 z8 z9
     z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20) z16)))))

;; match_enum_MESSAGE_E_Retirez_votre_carte
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni) (z9 uni) (z10 uni) (z11 uni) (z12 uni) (z13 uni)
  (z14 uni) (z15 uni) (z16 uni) (z17 uni) (z18 uni) (z19 uni) (z20 uni))
  (=> (sort a z17)
  (= (match_enum_MESSAGE a E_Retirez_votre_carte z z1 z2 z3 z4 z5 z6 z7 z8 z9
     z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20) z17)))))

;; match_enum_MESSAGE_E_Code_invalide
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni) (z9 uni) (z10 uni) (z11 uni) (z12 uni) (z13 uni)
  (z14 uni) (z15 uni) (z16 uni) (z17 uni) (z18 uni) (z19 uni) (z20 uni))
  (=> (sort a z18)
  (= (match_enum_MESSAGE a E_Code_invalide z z1 z2 z3 z4 z5 z6 z7 z8 z9 z10
     z11 z12 z13 z14 z15 z16 z17 z18 z19 z20) z18)))))

;; match_enum_MESSAGE_E_Carte_confisquee
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni) (z9 uni) (z10 uni) (z11 uni) (z12 uni) (z13 uni)
  (z14 uni) (z15 uni) (z16 uni) (z17 uni) (z18 uni) (z19 uni) (z20 uni))
  (=> (sort a z19)
  (= (match_enum_MESSAGE a E_Carte_confisquee z z1 z2 z3 z4 z5 z6 z7 z8 z9
     z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20) z19)))))

;; match_enum_MESSAGE_E_Merci_de_votre_visite
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni) (z9 uni) (z10 uni) (z11 uni) (z12 uni) (z13 uni)
  (z14 uni) (z15 uni) (z16 uni) (z17 uni) (z18 uni) (z19 uni) (z20 uni))
  (=> (sort a z20)
  (= (match_enum_MESSAGE a E_Merci_de_votre_visite z z1 z2 z3 z4 z5 z6 z7 z8
     z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20) z20)))))

(declare-fun index_enum_MESSAGE (enum_MESSAGE) Int)

;; index_enum_MESSAGE_E_Vide
  (assert (= (index_enum_MESSAGE E_Vide) 0))

;; index_enum_MESSAGE_E_En_panne
  (assert (= (index_enum_MESSAGE E_En_panne) 1))

;; index_enum_MESSAGE_E_Veuillez_patienter
  (assert (= (index_enum_MESSAGE E_Veuillez_patienter) 2))

;; index_enum_MESSAGE_E_Entrez_votre_carte
  (assert (= (index_enum_MESSAGE E_Entrez_votre_carte) 3))

;; index_enum_MESSAGE_E_Entrez_votre_code
  (assert (= (index_enum_MESSAGE E_Entrez_votre_code) 4))

;; index_enum_MESSAGE_E_Nouvel_essai
  (assert (= (index_enum_MESSAGE E_Nouvel_essai) 5))

;; index_enum_MESSAGE_E_Dernier_essai
  (assert (= (index_enum_MESSAGE E_Dernier_essai) 6))

;; index_enum_MESSAGE_E_Entrez_somme
  (assert (= (index_enum_MESSAGE E_Entrez_somme) 7))

;; index_enum_MESSAGE_E_Prenez_vos_billets
  (assert (= (index_enum_MESSAGE E_Prenez_vos_billets) 8))

;; index_enum_MESSAGE_E_Carte_perimee
  (assert (= (index_enum_MESSAGE E_Carte_perimee) 9))

;; index_enum_MESSAGE_E_Carte_epuisee
  (assert (= (index_enum_MESSAGE E_Carte_epuisee) 10))

;; index_enum_MESSAGE_E_Carte_invalide
  (assert (= (index_enum_MESSAGE E_Carte_invalide) 11))

;; index_enum_MESSAGE_E_Carte_interdite
  (assert (= (index_enum_MESSAGE E_Carte_interdite) 12))

;; index_enum_MESSAGE_E_Caisse_insuffisante
  (assert (= (index_enum_MESSAGE E_Caisse_insuffisante) 13))

;; index_enum_MESSAGE_E_Solde_insuffisant
  (assert (= (index_enum_MESSAGE E_Solde_insuffisant) 14))

;; index_enum_MESSAGE_E_Credit_insuffisant
  (assert (= (index_enum_MESSAGE E_Credit_insuffisant) 15))

;; index_enum_MESSAGE_E_Billets_confisques
  (assert (= (index_enum_MESSAGE E_Billets_confisques) 16))

;; index_enum_MESSAGE_E_Retirez_votre_carte
  (assert (= (index_enum_MESSAGE E_Retirez_votre_carte) 17))

;; index_enum_MESSAGE_E_Code_invalide
  (assert (= (index_enum_MESSAGE E_Code_invalide) 18))

;; index_enum_MESSAGE_E_Carte_confisquee
  (assert (= (index_enum_MESSAGE E_Carte_confisquee) 19))

;; index_enum_MESSAGE_E_Merci_de_votre_visite
  (assert (= (index_enum_MESSAGE E_Merci_de_votre_visite) 20))

;; enum_MESSAGE_inversion
  (assert
  (forall ((u enum_MESSAGE))
  (or
  (or
  (or
  (or
  (or
  (or
  (or
  (or
  (or
  (or
  (or
  (or
  (or
  (or
  (or
  (or
  (or
  (or (or (or (= u E_Vide) (= u E_En_panne)) (= u E_Veuillez_patienter))
  (= u E_Entrez_votre_carte)) (= u E_Entrez_votre_code))
  (= u E_Nouvel_essai)) (= u E_Dernier_essai)) (= u E_Entrez_somme))
  (= u E_Prenez_vos_billets)) (= u E_Carte_perimee)) (= u E_Carte_epuisee))
  (= u E_Carte_invalide)) (= u E_Carte_interdite))
  (= u E_Caisse_insuffisante)) (= u E_Solde_insuffisant))
  (= u E_Credit_insuffisant)) (= u E_Billets_confisques))
  (= u E_Retirez_votre_carte)) (= u E_Code_invalide))
  (= u E_Carte_confisquee)) (= u E_Merci_de_votre_visite))))

(declare-fun set_enum_MESSAGE () (set enum_MESSAGE))

(declare-fun t2tb12 ((set enum_MESSAGE)) uni)

;; t2tb_sort
  (assert
  (forall ((x (set enum_MESSAGE))) (sort (set1 enum_MESSAGE1) (t2tb12 x))))

(declare-fun tb2t12 (uni) (set enum_MESSAGE))

;; BridgeL
  (assert
  (forall ((i (set enum_MESSAGE)))
  (! (= (tb2t12 (t2tb12 i)) i) :pattern ((t2tb12 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 enum_MESSAGE1) j) (= (t2tb12 (tb2t12 j)) j)) :pattern (
  (t2tb12 (tb2t12 j))) )))

(declare-fun t2tb13 (enum_MESSAGE) uni)

;; t2tb_sort
  (assert (forall ((x enum_MESSAGE)) (sort enum_MESSAGE1 (t2tb13 x))))

(declare-fun tb2t13 (uni) enum_MESSAGE)

;; BridgeL
  (assert
  (forall ((i enum_MESSAGE))
  (! (= (tb2t13 (t2tb13 i)) i) :pattern ((t2tb13 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort enum_MESSAGE1 j) (= (t2tb13 (tb2t13 j)) j)) :pattern (
  (t2tb13 (tb2t13 j))) )))

;; set_enum_MESSAGE_axiom
  (assert
  (forall ((x enum_MESSAGE)) (mem enum_MESSAGE1 (t2tb13 x)
  (t2tb12 set_enum_MESSAGE))))

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

;; set_enum_STATUT_axiom
  (assert (forall ((x enum_STATUT)) (mem3 x set_enum_STATUT)))

(declare-fun f2 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f2_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f2 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and (and (mem1 v_K0 v_CARTE) (mem1 v_HS v_CARTE)) (not (= v_K0 v_HS)))
  (mem (set1 int) (t2tb v_CARTE) (finite_subsets int (t2tb integer))))
  (not (infix_eqeq int (t2tb v_CARTE) (t2tb empty1)))))))

(declare-fun f3 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f3_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f3 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (mem1 v_K0 v_CARTE) (mem1 v_HS v_CARTE)) (not (= v_K0 v_HS)))
  (mem (set1 int) (t2tb v_CARTE) (finite_subsets int (t2tb integer))))
  (not (infix_eqeq int (t2tb v_CARTE) (t2tb empty1)))) (mem1 v_date v_DATE))
  (=> (or (= v_panne_dab_1 true) (= v_caisse_vde_1 true))
  (= v_etat_dab_1 E_Hors_service)))
  (=> (= v_etat_dab_1 E_Hors_service)
  (or (= v_panne_dab_1 true) (= v_caisse_vde_1 true))))
  (=> (and (= v_courant_1 E_Traitement_code) (= v_etat_dab_1 E_En_service))
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_precedent_1)
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_precedent_1 E_Traitement_code) (mem3 v_resultat_1
  (union4 (add3 E_Nouvel empty4) (add3 E_Dernier empty4)))))
  (=> (= v_precedent_1 E_Traitement_carte) (= v_resultat_1 E_Valide)))))
  (=> (and (= v_courant_1 E_Restitution_carte) (= v_etat_dab_1 E_En_service))
  (and
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_precedent_1)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_somme)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Distribution_billets)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_precedent_1 E_Traitement_carte) (mem3 v_resultat_1
  (union4
  (union4 (union4 (add3 E_Perimee empty4) (add3 E_Epuisee empty4))
  (add3 E_Illisible empty4)) (add3 E_Invalide empty4)))))
  (=> (= v_precedent_1 E_Traitement_code) (mem3 v_resultat_1
  (union4 (add3 E_Hors_delai empty4) (add3 E_Incident empty4)))))
  (=> (= v_precedent_1 E_Traitement_somme) (mem3 v_resultat_1
  (union4 (union4 (add3 E_Invalide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))
  (=> (= v_precedent_1 E_Distribution_billets) (mem3 v_resultat_1
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))))
  (=>
  (and (= v_courant_1 E_Confiscation_carte) (= v_etat_dab_1 E_En_service))
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_precedent_1)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Restitution_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_precedent_1 E_Traitement_carte) (= v_resultat_1 E_Interdite)))
  (=> (= v_precedent_1 E_Traitement_code) (= v_resultat_1 E_Invalide)))
  (=> (= v_precedent_1 E_Restitution_carte) (mem3 v_resultat_1
  (union4 (add3 E_Incident empty4) (add3 E_Hors_delai empty4))))))) (mem
  (set1 int) (t2tb v_clients_1)
  (power int
  (diff int (t2tb v_CARTE)
  (t2tb (union1 (add1 v_K0 empty1) (add1 v_HS empty1))))))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_comptes_1)
  (infix_plmngt int int (t2tb v_clients_1) (t2tb nat)))) (infix_eqeq 
  int (dom int int (t2tb5 v_comptes_1)) (t2tb v_clients_1))) (mem (set1 int)
  (t2tb v_interdits_1) (power int (t2tb v_clients_1)))) (mem1 v_caisse_1
  integer)) (<= 0 v_caisse_1)) (<= v_caisse_1 2147483647)) (mem1
  v_corbeille_1 integer)) (<= 0 v_corbeille_1))
  (<= v_corbeille_1 2147483647)) (mem1 v_retraits_1 integer))
  (<= 0 v_retraits_1)) (<= v_retraits_1 2147483647)) (mem1 v_carte_1
  v_CARTE)) (mem1 v_code_CB_1 (mk 0 9999))) (mem1 v_date_validite_1 v_DATE))
  (mem1 v_date_mesure_1 v_DATE)) (mem1 v_code_saisi_1 (mk 0 9999))) (mem1
  v_somme_1 (mk 100 900))) (mem1
  (+ (+ v_caisse_1 v_corbeille_1) v_retraits_1) integer))
  (<= 0 (+ (+ v_caisse_1 v_corbeille_1) v_retraits_1)))
  (<= (+ (+ v_caisse_1 v_corbeille_1) v_retraits_1) 2147483647)))))

(declare-fun f4 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f4_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f4 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (mem (set1 int) (t2tb v_cl)
  (power int
  (diff int (t2tb v_CARTE)
  (t2tb (union1 (add1 v_K0 empty1) (add1 v_HS empty1)))))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_co)
  (infix_plmngt int int (t2tb v_cl) (t2tb nat)))) (infix_eqeq int
  (dom int int (t2tb5 v_co)) (t2tb v_cl))) (mem (set1 int) (t2tb v_in)
  (power int (t2tb v_cl)))) (mem1 v_date_mesure_0 v_DATE)) (mem1 v_somme_0
  (mk 100 900)))
  (=> (and (= E_Veille E_Traitement_code) (= E_Hors_service E_En_service))
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 E_Veille)
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= E_Veille E_Traitement_code) (mem3 E_Incident
  (union4 (add3 E_Nouvel empty4) (add3 E_Dernier empty4)))))
  (=> (= E_Veille E_Traitement_carte) (= E_Incident E_Valide)))))
  (=> (and (= E_Veille E_Restitution_carte) (= E_Hors_service E_En_service))
  (and
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 E_Veille)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_somme)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Distribution_billets)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= E_Veille E_Traitement_carte) (mem3 E_Incident
  (union4
  (union4 (union4 (add3 E_Perimee empty4) (add3 E_Epuisee empty4))
  (add3 E_Illisible empty4)) (add3 E_Invalide empty4)))))
  (=> (= E_Veille E_Traitement_code) (mem3 E_Incident
  (union4 (add3 E_Hors_delai empty4) (add3 E_Incident empty4)))))
  (=> (= E_Veille E_Traitement_somme) (mem3 E_Incident
  (union4 (union4 (add3 E_Invalide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))
  (=> (= E_Veille E_Distribution_billets) (mem3 E_Incident
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))))
  (=> (and (= E_Veille E_Confiscation_carte) (= E_Hors_service E_En_service))
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 E_Veille)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Restitution_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= E_Veille E_Traitement_carte) (= E_Incident E_Interdite)))
  (=> (= E_Veille E_Traitement_code) (= E_Incident E_Invalide)))
  (=> (= E_Veille E_Restitution_carte) (mem3 E_Incident
  (union4 (add3 E_Incident empty4) (add3 E_Hors_delai empty4))))))) (mem1 0
  integer)) (mem1 0 (mk 0 9999))) (mem1 v_D_min v_DATE))
  (= E_Veille E_Traitement_code)) (= E_Hors_service E_En_service)))))

(declare-fun f7 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f7_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f7 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE) (not (mem1 v_K0 v_in)))))

(declare-fun f9 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f9_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f9 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (<= 100 (tb2t1 (apply int int (t2tb5 v_co) (t2tb1 v_K0)))))))

(declare-fun f10 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f10_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f10 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (mem (set1 int) (t2tb v_cl)
  (power int
  (diff int (t2tb v_CARTE)
  (t2tb (union1 (add1 v_K0 empty1) (add1 v_HS empty1)))))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_co)
  (infix_plmngt int int (t2tb v_cl) (t2tb nat)))) (infix_eqeq int
  (dom int int (t2tb5 v_co)) (t2tb v_cl))) (mem (set1 int) (t2tb v_in)
  (power int (t2tb v_cl)))) (mem1 v_date_mesure_0 v_DATE)) (mem1 v_somme_0
  (mk 100 900)))
  (=> (and (= E_Veille E_Traitement_code) (= E_Hors_service E_En_service))
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 E_Veille)
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= E_Veille E_Traitement_code) (mem3 E_Incident
  (union4 (add3 E_Nouvel empty4) (add3 E_Dernier empty4)))))
  (=> (= E_Veille E_Traitement_carte) (= E_Incident E_Valide)))))
  (=> (and (= E_Veille E_Restitution_carte) (= E_Hors_service E_En_service))
  (and
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 E_Veille)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_somme)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Distribution_billets)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= E_Veille E_Traitement_carte) (mem3 E_Incident
  (union4
  (union4 (union4 (add3 E_Perimee empty4) (add3 E_Epuisee empty4))
  (add3 E_Illisible empty4)) (add3 E_Invalide empty4)))))
  (=> (= E_Veille E_Traitement_code) (mem3 E_Incident
  (union4 (add3 E_Hors_delai empty4) (add3 E_Incident empty4)))))
  (=> (= E_Veille E_Traitement_somme) (mem3 E_Incident
  (union4 (union4 (add3 E_Invalide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))
  (=> (= E_Veille E_Distribution_billets) (mem3 E_Incident
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))))
  (=> (and (= E_Veille E_Confiscation_carte) (= E_Hors_service E_En_service))
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 E_Veille)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Restitution_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= E_Veille E_Traitement_carte) (= E_Incident E_Interdite)))
  (=> (= E_Veille E_Traitement_code) (= E_Incident E_Invalide)))
  (=> (= E_Veille E_Restitution_carte) (mem3 E_Incident
  (union4 (add3 E_Incident empty4) (add3 E_Hors_delai empty4))))))) (mem1 0
  integer)) (mem1 0 (mk 0 9999))) (mem1 v_D_min v_DATE))
  (= E_Veille E_Traitement_somme)) (= E_Hors_service E_En_service)))))

(declare-fun f12 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f12_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f12 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (mem (set1 int) (t2tb v_cl)
  (power int
  (diff int (t2tb v_CARTE)
  (t2tb (union1 (add1 v_K0 empty1) (add1 v_HS empty1)))))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_co)
  (infix_plmngt int int (t2tb v_cl) (t2tb nat)))) (infix_eqeq int
  (dom int int (t2tb5 v_co)) (t2tb v_cl))) (mem (set1 int) (t2tb v_in)
  (power int (t2tb v_cl)))) (mem1 v_date_mesure_0 v_DATE)) (mem1 v_somme_0
  (mk 100 900)))
  (=> (and (= E_Veille E_Traitement_code) (= E_Hors_service E_En_service))
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 E_Veille)
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= E_Veille E_Traitement_code) (mem3 E_Incident
  (union4 (add3 E_Nouvel empty4) (add3 E_Dernier empty4)))))
  (=> (= E_Veille E_Traitement_carte) (= E_Incident E_Valide)))))
  (=> (and (= E_Veille E_Restitution_carte) (= E_Hors_service E_En_service))
  (and
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 E_Veille)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_somme)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Distribution_billets)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= E_Veille E_Traitement_carte) (mem3 E_Incident
  (union4
  (union4 (union4 (add3 E_Perimee empty4) (add3 E_Epuisee empty4))
  (add3 E_Illisible empty4)) (add3 E_Invalide empty4)))))
  (=> (= E_Veille E_Traitement_code) (mem3 E_Incident
  (union4 (add3 E_Hors_delai empty4) (add3 E_Incident empty4)))))
  (=> (= E_Veille E_Traitement_somme) (mem3 E_Incident
  (union4 (union4 (add3 E_Invalide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))
  (=> (= E_Veille E_Distribution_billets) (mem3 E_Incident
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))))
  (=> (and (= E_Veille E_Confiscation_carte) (= E_Hors_service E_En_service))
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 E_Veille)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Restitution_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= E_Veille E_Traitement_carte) (= E_Incident E_Interdite)))
  (=> (= E_Veille E_Traitement_code) (= E_Incident E_Invalide)))
  (=> (= E_Veille E_Restitution_carte) (mem3 E_Incident
  (union4 (add3 E_Incident empty4) (add3 E_Hors_delai empty4))))))) (mem1 0
  integer)) (mem1 0 (mk 0 9999))) (mem1 v_D_min v_DATE))
  (= E_Veille E_Distribution_billets)) (= E_Hors_service E_En_service)))))

(declare-fun f14 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f14_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f14 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (<= v_somme_0 (tb2t1 (apply int int (t2tb5 v_co) (t2tb1 v_K0)))))))

(declare-fun f19 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f19_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f19 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (mem (set1 int) (t2tb v_cl)
  (power int
  (diff int (t2tb v_CARTE)
  (t2tb (union1 (add1 v_K0 empty1) (add1 v_HS empty1)))))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_co)
  (infix_plmngt int int (t2tb v_cl) (t2tb nat)))) (infix_eqeq int
  (dom int int (t2tb5 v_co)) (t2tb v_cl))) (mem (set1 int) (t2tb v_in)
  (power int (t2tb v_cl)))) (mem1 v_date_mesure_0 v_DATE)) (mem1 v_somme_0
  (mk 100 900)))
  (=> (and (= E_Veille E_Traitement_code) (= E_Hors_service E_En_service))
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 E_Veille)
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= E_Veille E_Traitement_code) (mem3 E_Incident
  (union4 (add3 E_Nouvel empty4) (add3 E_Dernier empty4)))))
  (=> (= E_Veille E_Traitement_carte) (= E_Incident E_Valide)))))
  (=> (and (= E_Veille E_Restitution_carte) (= E_Hors_service E_En_service))
  (and
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 E_Veille)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_somme)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Distribution_billets)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= E_Veille E_Traitement_carte) (mem3 E_Incident
  (union4
  (union4 (union4 (add3 E_Perimee empty4) (add3 E_Epuisee empty4))
  (add3 E_Illisible empty4)) (add3 E_Invalide empty4)))))
  (=> (= E_Veille E_Traitement_code) (mem3 E_Incident
  (union4 (add3 E_Hors_delai empty4) (add3 E_Incident empty4)))))
  (=> (= E_Veille E_Traitement_somme) (mem3 E_Incident
  (union4 (union4 (add3 E_Invalide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))
  (=> (= E_Veille E_Distribution_billets) (mem3 E_Incident
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))))
  (=> (and (= E_Veille E_Confiscation_carte) (= E_Hors_service E_En_service))
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 E_Veille)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Restitution_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= E_Veille E_Traitement_carte) (= E_Incident E_Interdite)))
  (=> (= E_Veille E_Traitement_code) (= E_Incident E_Invalide)))
  (=> (= E_Veille E_Restitution_carte) (mem3 E_Incident
  (union4 (add3 E_Incident empty4) (add3 E_Hors_delai empty4))))))) (mem1 0
  integer)) (mem1 0 (mk 0 9999))) (mem1 v_D_min v_DATE))
  (= E_Veille E_Restitution_carte)))))

(declare-fun f21 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f21_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f21 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (mem (set1 int) (t2tb v_cl)
  (power int
  (diff int (t2tb v_CARTE)
  (t2tb (union1 (add1 v_K0 empty1) (add1 v_HS empty1)))))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_co)
  (infix_plmngt int int (t2tb v_cl) (t2tb nat)))) (infix_eqeq int
  (dom int int (t2tb5 v_co)) (t2tb v_cl))) (mem (set1 int) (t2tb v_in)
  (power int (t2tb v_cl)))) (mem1 v_date_mesure_0 v_DATE)) (mem1 v_somme_0
  (mk 100 900)))
  (=> (and (= E_Veille E_Traitement_code) (= E_Hors_service E_En_service))
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 E_Veille)
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= E_Veille E_Traitement_code) (mem3 E_Incident
  (union4 (add3 E_Nouvel empty4) (add3 E_Dernier empty4)))))
  (=> (= E_Veille E_Traitement_carte) (= E_Incident E_Valide)))))
  (=> (and (= E_Veille E_Restitution_carte) (= E_Hors_service E_En_service))
  (and
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 E_Veille)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_somme)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Distribution_billets)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= E_Veille E_Traitement_carte) (mem3 E_Incident
  (union4
  (union4 (union4 (add3 E_Perimee empty4) (add3 E_Epuisee empty4))
  (add3 E_Illisible empty4)) (add3 E_Invalide empty4)))))
  (=> (= E_Veille E_Traitement_code) (mem3 E_Incident
  (union4 (add3 E_Hors_delai empty4) (add3 E_Incident empty4)))))
  (=> (= E_Veille E_Traitement_somme) (mem3 E_Incident
  (union4 (union4 (add3 E_Invalide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))
  (=> (= E_Veille E_Distribution_billets) (mem3 E_Incident
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))))
  (=> (and (= E_Veille E_Confiscation_carte) (= E_Hors_service E_En_service))
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 E_Veille)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Restitution_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= E_Veille E_Traitement_carte) (= E_Incident E_Interdite)))
  (=> (= E_Veille E_Traitement_code) (= E_Incident E_Invalide)))
  (=> (= E_Veille E_Restitution_carte) (mem3 E_Incident
  (union4 (add3 E_Incident empty4) (add3 E_Hors_delai empty4))))))) (mem1 0
  integer)) (mem1 0 (mk 0 9999))) (mem1 v_D_min v_DATE))
  (= E_Hors_service E_En_service)))))

(declare-fun f23 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f23_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f23 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (mem (set1 int) (t2tb v_cl)
  (power int
  (diff int (t2tb v_CARTE)
  (t2tb (union1 (add1 v_K0 empty1) (add1 v_HS empty1)))))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_co)
  (infix_plmngt int int (t2tb v_cl) (t2tb nat)))) (infix_eqeq int
  (dom int int (t2tb5 v_co)) (t2tb v_cl))) (mem (set1 int) (t2tb v_in)
  (power int (t2tb v_cl)))) (mem1 v_date_mesure_0 v_DATE)) (mem1 v_somme_0
  (mk 100 900)))
  (=> (and (= E_Veille E_Traitement_code) (= E_Hors_service E_En_service))
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 E_Veille)
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= E_Veille E_Traitement_code) (mem3 E_Incident
  (union4 (add3 E_Nouvel empty4) (add3 E_Dernier empty4)))))
  (=> (= E_Veille E_Traitement_carte) (= E_Incident E_Valide)))))
  (=> (and (= E_Veille E_Restitution_carte) (= E_Hors_service E_En_service))
  (and
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 E_Veille)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_somme)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Distribution_billets)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= E_Veille E_Traitement_carte) (mem3 E_Incident
  (union4
  (union4 (union4 (add3 E_Perimee empty4) (add3 E_Epuisee empty4))
  (add3 E_Illisible empty4)) (add3 E_Invalide empty4)))))
  (=> (= E_Veille E_Traitement_code) (mem3 E_Incident
  (union4 (add3 E_Hors_delai empty4) (add3 E_Incident empty4)))))
  (=> (= E_Veille E_Traitement_somme) (mem3 E_Incident
  (union4 (union4 (add3 E_Invalide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))
  (=> (= E_Veille E_Distribution_billets) (mem3 E_Incident
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))))
  (=> (and (= E_Veille E_Confiscation_carte) (= E_Hors_service E_En_service))
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 E_Veille)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Restitution_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= E_Veille E_Traitement_carte) (= E_Incident E_Interdite)))
  (=> (= E_Veille E_Traitement_code) (= E_Incident E_Invalide)))
  (=> (= E_Veille E_Restitution_carte) (mem3 E_Incident
  (union4 (add3 E_Incident empty4) (add3 E_Hors_delai empty4))))))) (mem1 0
  integer)) (mem1 0 (mk 0 9999))) (mem1 v_D_min v_DATE)) (mem
  enum_ETAT_AUTOMATE1 (t2tb9 E_Veille)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_somme)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Distribution_billets)
  (empty enum_ETAT_AUTOMATE1))))))))

(declare-fun f25 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f25_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f25 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (mem (set1 int) (t2tb v_clients_1)
  (power int
  (diff int (t2tb v_CARTE)
  (t2tb (union1 (add1 v_K0 empty1) (add1 v_HS empty1)))))) (mem
  (set1 (tuple21 int int)) (t2tb5 v_comptes_1)
  (infix_plmngt int int (t2tb v_clients_1) (t2tb nat)))) (infix_eqeq 
  int (dom int int (t2tb5 v_comptes_1)) (t2tb v_clients_1))) (mem (set1 int)
  (t2tb v_interdits_1) (power int (t2tb v_clients_1)))) (mem1 v_caisse_1
  integer)) (<= 0 v_caisse_1)) (<= v_caisse_1 2147483647)) (mem1
  v_corbeille_1 integer)) (<= 0 v_corbeille_1))
  (<= v_corbeille_1 2147483647)) (mem1 v_retraits_1 integer))
  (<= 0 v_retraits_1)) (<= v_retraits_1 2147483647)) (mem1 v_carte_1
  v_CARTE)) (mem1 (+ (+ v_caisse_1 v_corbeille_1) v_retraits_1) integer))
  (<= 0 (+ (+ v_caisse_1 v_corbeille_1) v_retraits_1)))
  (<= (+ (+ v_caisse_1 v_corbeille_1) v_retraits_1) 2147483647))
  (= v_etat_aut v_courant_1))
  (=> (= v_caisse_vde_1 true) (<= (+ v_caisse_1 1) 900)))
  (=> (and (= v_courant_1 E_Traitement_code) (= v_etat_dab_1 E_En_service))
  (and
  (and
  (and (mem1 v_carte_1 v_clients_1) (not (mem1 v_carte_1 v_interdits_1)))
  (<= v_date_mesure_1 v_date_validite_1))
  (<= 100 (tb2t1 (apply int int (t2tb5 v_comptes_1) (t2tb1 v_carte_1)))))))
  (=> (and (= v_courant_1 E_Traitement_somme) (= v_etat_dab_1 E_En_service))
  (and (= v_code_CB_1 v_code_saisi_1)
  (and
  (and
  (and (mem1 v_carte_1 v_clients_1) (not (mem1 v_carte_1 v_interdits_1)))
  (<= v_date_mesure_1 v_date_validite_1))
  (<= 100 (tb2t1 (apply int int (t2tb5 v_comptes_1) (t2tb1 v_carte_1))))))))
  (=>
  (and (= v_courant_1 E_Distribution_billets) (= v_etat_dab_1 E_En_service))
  (and
  (and
  (and
  (and
  (and
  (and (mem1 v_carte_1 v_clients_1) (not (mem1 v_carte_1 v_interdits_1)))
  (<= v_somme_1 (tb2t1 (apply int int (t2tb5 v_comptes_1) (t2tb1 v_carte_1)))))
  (<= v_somme_1 v_caisse_1)) (mem1 v_somme_1 (mk 100 900)))
  (= v_code_CB_1 v_code_saisi_1))
  (and
  (and
  (and (mem1 v_carte_1 v_clients_1) (not (mem1 v_carte_1 v_interdits_1)))
  (<= v_date_mesure_1 v_date_validite_1))
  (<= 100 (tb2t1 (apply int int (t2tb5 v_comptes_1) (t2tb1 v_carte_1))))))))
  (=> (= v_etat_dab_1 E_En_service)
  (and (= v_code_demande_1 false) (= v_somme_demandee_1 false))))
  (=> (and (= v_courant_1 E_Veille) (= v_etat_dab_1 E_En_service))
  (and (= v_carte_1 v_K0) (= v_infos_lues_1 false))))
  (=> (and (= v_courant_1 E_Traitement_carte) (= v_etat_dab_1 E_En_service))
  (and (= v_carte_1 v_K0) (= v_infos_lues_1 false))))
  (=> (and (= v_courant_1 E_Traitement_code) (= v_etat_dab_1 E_En_service))
  (and
  (=> (mem3 v_resultat_1
  (union4 (add3 E_Nouvel empty4) (add3 E_Dernier empty4)))
  (= v_essai_possible_1 true)) (= v_infos_lues_1 true))))
  (=> (and (= v_courant_1 E_Traitement_somme) (= v_etat_dab_1 E_En_service))
  (= v_infos_lues_1 true)))
  (=> (= v_courant_1 E_Restitution_carte) (not (= v_carte_1 v_K0))))
  (=> (= v_etat_dab_1 E_En_service)
  (and (= v_caisse_vde_1 false) (= v_panne_dab_1 false))))
  (=> (and (= v_caisse_vde_1 false) (= v_panne_dab_1 false))
  (= v_etat_dab_1 E_En_service)))
  (=> (mem enum_ETAT_AUTOMATE1 (t2tb9 v_courant_1)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_somme)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Distribution_billets)
  (empty enum_ETAT_AUTOMATE1)))) (not (= v_carte_1 v_K0))))
  (=> (= v_courant_1 E_Traitement_carte) (= v_carte_1 v_K0))) (infix_eqeq 
  int (t2tb v_clients) (t2tb v_clients_1))) (infix_eqeq (tuple21 int int)
  (t2tb5 v_comptes) (t2tb5 v_comptes_1))) (infix_eqeq int (t2tb v_interdits)
  (t2tb v_interdits_1))) (= v_caisse v_caisse_1))
  (= v_corbeille v_corbeille_1)) (= v_retraits v_retraits_1))
  (= v_etat_dab v_etat_dab_1)) (= v_panne_dab v_panne_dab_1))
  (= v_carte v_carte_1)))))

(declare-fun f26 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f26_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f26 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and (and (and (mem1 v_avnc integer) (<= 0 v_avnc)) (<= v_avnc 2147483647))
  (<= 900 v_avnc)))))

(declare-fun f27 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f27_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f27 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (and (mem1 v_avnc integer) (<= 0 v_avnc)) (<= v_avnc 2147483647))
  (<= 900 v_avnc)) (mem1 v_somme_0 (mk 100 900)))
  (not (= E_En_service E_Hors_service)))
  (=> (= E_Veille E_Traitement_code)
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 E_Veille)
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= E_Veille E_Traitement_code) (mem3 E_Hors_delai
  (union4 (add3 E_Nouvel empty4) (add3 E_Dernier empty4)))))
  (=> (= E_Veille E_Traitement_carte) (= E_Hors_delai E_Valide)))))
  (=> (= E_Veille E_Restitution_carte)
  (and
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 E_Veille)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_somme)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Distribution_billets)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= E_Veille E_Traitement_carte) (mem3 E_Hors_delai
  (union4
  (union4 (union4 (add3 E_Perimee empty4) (add3 E_Epuisee empty4))
  (add3 E_Illisible empty4)) (add3 E_Invalide empty4)))))
  (=> (= E_Veille E_Traitement_code) (mem3 E_Hors_delai
  (union4 (add3 E_Hors_delai empty4) (add3 E_Incident empty4)))))
  (=> (= E_Veille E_Traitement_somme) (mem3 E_Hors_delai
  (union4 (union4 (add3 E_Invalide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))
  (=> (= E_Veille E_Distribution_billets) (mem3 E_Hors_delai
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))))
  (=> (= E_Veille E_Confiscation_carte)
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 E_Veille)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Restitution_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= E_Veille E_Traitement_carte) (= E_Hors_delai E_Interdite)))
  (=> (= E_Veille E_Traitement_code) (= E_Hors_delai E_Invalide)))
  (=> (= E_Veille E_Restitution_carte) (mem3 E_Hors_delai
  (union4 (add3 E_Incident empty4) (add3 E_Hors_delai empty4))))))) (mem1 0
  integer)) (mem1 0 (mk 0 9999))) (mem1 v_D_min v_DATE)) (mem1
  (+ (+ v_avnc 0) 0) integer)) (<= 0 (+ (+ v_avnc 0) 0)))
  (<= (+ (+ v_avnc 0) 0) 2147483647)) (= E_Veille E_Traitement_code)))))

(declare-fun f30 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f30_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f30 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE) (not (mem1 v_K0 v_interdits_1)))))

(declare-fun f32 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f32_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f32 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (<= 100 (tb2t1 (apply int int (t2tb5 v_comptes_1) (t2tb1 v_K0)))))))

(declare-fun f33 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f33_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f33 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (and (mem1 v_avnc integer) (<= 0 v_avnc)) (<= v_avnc 2147483647))
  (<= 900 v_avnc)) (mem1 v_somme_0 (mk 100 900)))
  (not (= E_En_service E_Hors_service)))
  (=> (= E_Veille E_Traitement_code)
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 E_Veille)
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= E_Veille E_Traitement_code) (mem3 E_Hors_delai
  (union4 (add3 E_Nouvel empty4) (add3 E_Dernier empty4)))))
  (=> (= E_Veille E_Traitement_carte) (= E_Hors_delai E_Valide)))))
  (=> (= E_Veille E_Restitution_carte)
  (and
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 E_Veille)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_somme)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Distribution_billets)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= E_Veille E_Traitement_carte) (mem3 E_Hors_delai
  (union4
  (union4 (union4 (add3 E_Perimee empty4) (add3 E_Epuisee empty4))
  (add3 E_Illisible empty4)) (add3 E_Invalide empty4)))))
  (=> (= E_Veille E_Traitement_code) (mem3 E_Hors_delai
  (union4 (add3 E_Hors_delai empty4) (add3 E_Incident empty4)))))
  (=> (= E_Veille E_Traitement_somme) (mem3 E_Hors_delai
  (union4 (union4 (add3 E_Invalide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))
  (=> (= E_Veille E_Distribution_billets) (mem3 E_Hors_delai
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))))
  (=> (= E_Veille E_Confiscation_carte)
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 E_Veille)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Restitution_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= E_Veille E_Traitement_carte) (= E_Hors_delai E_Interdite)))
  (=> (= E_Veille E_Traitement_code) (= E_Hors_delai E_Invalide)))
  (=> (= E_Veille E_Restitution_carte) (mem3 E_Hors_delai
  (union4 (add3 E_Incident empty4) (add3 E_Hors_delai empty4))))))) (mem1 0
  integer)) (mem1 0 (mk 0 9999))) (mem1 v_D_min v_DATE)) (mem1
  (+ (+ v_avnc 0) 0) integer)) (<= 0 (+ (+ v_avnc 0) 0)))
  (<= (+ (+ v_avnc 0) 0) 2147483647)) (= E_Veille E_Traitement_somme)))))

(declare-fun f35 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f35_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f35 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (and (mem1 v_avnc integer) (<= 0 v_avnc)) (<= v_avnc 2147483647))
  (<= 900 v_avnc)) (mem1 v_somme_0 (mk 100 900)))
  (not (= E_En_service E_Hors_service)))
  (=> (= E_Veille E_Traitement_code)
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 E_Veille)
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= E_Veille E_Traitement_code) (mem3 E_Hors_delai
  (union4 (add3 E_Nouvel empty4) (add3 E_Dernier empty4)))))
  (=> (= E_Veille E_Traitement_carte) (= E_Hors_delai E_Valide)))))
  (=> (= E_Veille E_Restitution_carte)
  (and
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 E_Veille)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_somme)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Distribution_billets)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= E_Veille E_Traitement_carte) (mem3 E_Hors_delai
  (union4
  (union4 (union4 (add3 E_Perimee empty4) (add3 E_Epuisee empty4))
  (add3 E_Illisible empty4)) (add3 E_Invalide empty4)))))
  (=> (= E_Veille E_Traitement_code) (mem3 E_Hors_delai
  (union4 (add3 E_Hors_delai empty4) (add3 E_Incident empty4)))))
  (=> (= E_Veille E_Traitement_somme) (mem3 E_Hors_delai
  (union4 (union4 (add3 E_Invalide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))
  (=> (= E_Veille E_Distribution_billets) (mem3 E_Hors_delai
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))))
  (=> (= E_Veille E_Confiscation_carte)
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 E_Veille)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Restitution_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= E_Veille E_Traitement_carte) (= E_Hors_delai E_Interdite)))
  (=> (= E_Veille E_Traitement_code) (= E_Hors_delai E_Invalide)))
  (=> (= E_Veille E_Restitution_carte) (mem3 E_Hors_delai
  (union4 (add3 E_Incident empty4) (add3 E_Hors_delai empty4))))))) (mem1 0
  integer)) (mem1 0 (mk 0 9999))) (mem1 v_D_min v_DATE)) (mem1
  (+ (+ v_avnc 0) 0) integer)) (<= 0 (+ (+ v_avnc 0) 0)))
  (<= (+ (+ v_avnc 0) 0) 2147483647)) (= E_Veille E_Distribution_billets)))))

(declare-fun f37 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f37_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f37 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (<= v_somme_0 (tb2t1 (apply int int (t2tb5 v_comptes_1) (t2tb1 v_K0)))))))

(declare-fun f41 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f41_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f41 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (and (mem1 v_avnc integer) (<= 0 v_avnc)) (<= v_avnc 2147483647))
  (<= 900 v_avnc)) (mem1 v_somme_0 (mk 100 900)))
  (not (= E_En_service E_Hors_service)))
  (=> (= E_Veille E_Traitement_code)
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 E_Veille)
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= E_Veille E_Traitement_code) (mem3 E_Hors_delai
  (union4 (add3 E_Nouvel empty4) (add3 E_Dernier empty4)))))
  (=> (= E_Veille E_Traitement_carte) (= E_Hors_delai E_Valide)))))
  (=> (= E_Veille E_Restitution_carte)
  (and
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 E_Veille)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_somme)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Distribution_billets)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= E_Veille E_Traitement_carte) (mem3 E_Hors_delai
  (union4
  (union4 (union4 (add3 E_Perimee empty4) (add3 E_Epuisee empty4))
  (add3 E_Illisible empty4)) (add3 E_Invalide empty4)))))
  (=> (= E_Veille E_Traitement_code) (mem3 E_Hors_delai
  (union4 (add3 E_Hors_delai empty4) (add3 E_Incident empty4)))))
  (=> (= E_Veille E_Traitement_somme) (mem3 E_Hors_delai
  (union4 (union4 (add3 E_Invalide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))
  (=> (= E_Veille E_Distribution_billets) (mem3 E_Hors_delai
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))))
  (=> (= E_Veille E_Confiscation_carte)
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 E_Veille)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Restitution_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= E_Veille E_Traitement_carte) (= E_Hors_delai E_Interdite)))
  (=> (= E_Veille E_Traitement_code) (= E_Hors_delai E_Invalide)))
  (=> (= E_Veille E_Restitution_carte) (mem3 E_Hors_delai
  (union4 (add3 E_Incident empty4) (add3 E_Hors_delai empty4))))))) (mem1 0
  integer)) (mem1 0 (mk 0 9999))) (mem1 v_D_min v_DATE)) (mem1
  (+ (+ v_avnc 0) 0) integer)) (<= 0 (+ (+ v_avnc 0) 0)))
  (<= (+ (+ v_avnc 0) 0) 2147483647)) (= E_Veille E_Restitution_carte)))))

(declare-fun f43 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f43_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f43 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (and (mem1 v_avnc integer) (<= 0 v_avnc)) (<= v_avnc 2147483647))
  (<= 900 v_avnc)) (mem1 v_somme_0 (mk 100 900)))
  (not (= E_En_service E_Hors_service)))
  (=> (= E_Veille E_Traitement_code)
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 E_Veille)
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= E_Veille E_Traitement_code) (mem3 E_Hors_delai
  (union4 (add3 E_Nouvel empty4) (add3 E_Dernier empty4)))))
  (=> (= E_Veille E_Traitement_carte) (= E_Hors_delai E_Valide)))))
  (=> (= E_Veille E_Restitution_carte)
  (and
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 E_Veille)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_somme)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Distribution_billets)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= E_Veille E_Traitement_carte) (mem3 E_Hors_delai
  (union4
  (union4 (union4 (add3 E_Perimee empty4) (add3 E_Epuisee empty4))
  (add3 E_Illisible empty4)) (add3 E_Invalide empty4)))))
  (=> (= E_Veille E_Traitement_code) (mem3 E_Hors_delai
  (union4 (add3 E_Hors_delai empty4) (add3 E_Incident empty4)))))
  (=> (= E_Veille E_Traitement_somme) (mem3 E_Hors_delai
  (union4 (union4 (add3 E_Invalide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))
  (=> (= E_Veille E_Distribution_billets) (mem3 E_Hors_delai
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))))
  (=> (= E_Veille E_Confiscation_carte)
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 E_Veille)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Restitution_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= E_Veille E_Traitement_carte) (= E_Hors_delai E_Interdite)))
  (=> (= E_Veille E_Traitement_code) (= E_Hors_delai E_Invalide)))
  (=> (= E_Veille E_Restitution_carte) (mem3 E_Hors_delai
  (union4 (add3 E_Incident empty4) (add3 E_Hors_delai empty4))))))) (mem1 0
  integer)) (mem1 0 (mk 0 9999))) (mem1 v_D_min v_DATE)) (mem1
  (+ (+ v_avnc 0) 0) integer)) (<= 0 (+ (+ v_avnc 0) 0)))
  (<= (+ (+ v_avnc 0) 0) 2147483647)) (mem enum_ETAT_AUTOMATE1
  (t2tb9 E_Veille)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_somme)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Distribution_billets)
  (empty enum_ETAT_AUTOMATE1))))))))

(declare-fun f45 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f45_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f45 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE) (= v_etat_dab_1 E_En_service))))

(declare-fun f46 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f46_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f46 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and (= v_etat_dab_1 E_En_service)
  (or (= v_tst_dab_1 true) (<= (+ v_caisse_1 1) 900)))
  (=> (and (= v_courant_1 E_Traitement_code) (= E_Hors_service E_En_service))
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_precedent_1)
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_precedent_1 E_Traitement_code) (mem3 v_resultat_1
  (union4 (add3 E_Nouvel empty4) (add3 E_Dernier empty4)))))
  (=> (= v_precedent_1 E_Traitement_carte) (= v_resultat_1 E_Valide)))))
  (=>
  (and (= v_courant_1 E_Restitution_carte) (= E_Hors_service E_En_service))
  (and
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_precedent_1)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_somme)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Distribution_billets)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_precedent_1 E_Traitement_carte) (mem3 v_resultat_1
  (union4
  (union4 (union4 (add3 E_Perimee empty4) (add3 E_Epuisee empty4))
  (add3 E_Illisible empty4)) (add3 E_Invalide empty4)))))
  (=> (= v_precedent_1 E_Traitement_code) (mem3 v_resultat_1
  (union4 (add3 E_Hors_delai empty4) (add3 E_Incident empty4)))))
  (=> (= v_precedent_1 E_Traitement_somme) (mem3 v_resultat_1
  (union4 (union4 (add3 E_Invalide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))
  (=> (= v_precedent_1 E_Distribution_billets) (mem3 v_resultat_1
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))))
  (=>
  (and (= v_courant_1 E_Confiscation_carte) (= E_Hors_service E_En_service))
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_precedent_1)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Restitution_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_precedent_1 E_Traitement_carte) (= v_resultat_1 E_Interdite)))
  (=> (= v_precedent_1 E_Traitement_code) (= v_resultat_1 E_Invalide)))
  (=> (= v_precedent_1 E_Restitution_carte) (mem3 v_resultat_1
  (union4 (add3 E_Incident empty4) (add3 E_Hors_delai empty4)))))))
  (= E_Hors_service E_En_service)) (= v_courant_1 E_Traitement_code)))))

(declare-fun f48 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f48_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f48 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE) (not (mem1 v_carte_1 v_interdits_1)))))

(declare-fun f50 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f50_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f50 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (<= 100 (tb2t1 (apply int int (t2tb5 v_comptes_1) (t2tb1 v_carte_1)))))))

(declare-fun f51 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f51_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f51 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and (= v_etat_dab_1 E_En_service)
  (or (= v_tst_dab_1 true) (<= (+ v_caisse_1 1) 900)))
  (=> (and (= v_courant_1 E_Traitement_code) (= E_Hors_service E_En_service))
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_precedent_1)
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_precedent_1 E_Traitement_code) (mem3 v_resultat_1
  (union4 (add3 E_Nouvel empty4) (add3 E_Dernier empty4)))))
  (=> (= v_precedent_1 E_Traitement_carte) (= v_resultat_1 E_Valide)))))
  (=>
  (and (= v_courant_1 E_Restitution_carte) (= E_Hors_service E_En_service))
  (and
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_precedent_1)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_somme)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Distribution_billets)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_precedent_1 E_Traitement_carte) (mem3 v_resultat_1
  (union4
  (union4 (union4 (add3 E_Perimee empty4) (add3 E_Epuisee empty4))
  (add3 E_Illisible empty4)) (add3 E_Invalide empty4)))))
  (=> (= v_precedent_1 E_Traitement_code) (mem3 v_resultat_1
  (union4 (add3 E_Hors_delai empty4) (add3 E_Incident empty4)))))
  (=> (= v_precedent_1 E_Traitement_somme) (mem3 v_resultat_1
  (union4 (union4 (add3 E_Invalide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))
  (=> (= v_precedent_1 E_Distribution_billets) (mem3 v_resultat_1
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))))
  (=>
  (and (= v_courant_1 E_Confiscation_carte) (= E_Hors_service E_En_service))
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_precedent_1)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Restitution_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_precedent_1 E_Traitement_carte) (= v_resultat_1 E_Interdite)))
  (=> (= v_precedent_1 E_Traitement_code) (= v_resultat_1 E_Invalide)))
  (=> (= v_precedent_1 E_Restitution_carte) (mem3 v_resultat_1
  (union4 (add3 E_Incident empty4) (add3 E_Hors_delai empty4)))))))
  (= E_Hors_service E_En_service)) (= v_courant_1 E_Traitement_somme)))))

(declare-fun f53 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f53_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f53 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and (= v_etat_dab_1 E_En_service)
  (or (= v_tst_dab_1 true) (<= (+ v_caisse_1 1) 900)))
  (=> (and (= v_courant_1 E_Traitement_code) (= E_Hors_service E_En_service))
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_precedent_1)
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_precedent_1 E_Traitement_code) (mem3 v_resultat_1
  (union4 (add3 E_Nouvel empty4) (add3 E_Dernier empty4)))))
  (=> (= v_precedent_1 E_Traitement_carte) (= v_resultat_1 E_Valide)))))
  (=>
  (and (= v_courant_1 E_Restitution_carte) (= E_Hors_service E_En_service))
  (and
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_precedent_1)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_somme)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Distribution_billets)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_precedent_1 E_Traitement_carte) (mem3 v_resultat_1
  (union4
  (union4 (union4 (add3 E_Perimee empty4) (add3 E_Epuisee empty4))
  (add3 E_Illisible empty4)) (add3 E_Invalide empty4)))))
  (=> (= v_precedent_1 E_Traitement_code) (mem3 v_resultat_1
  (union4 (add3 E_Hors_delai empty4) (add3 E_Incident empty4)))))
  (=> (= v_precedent_1 E_Traitement_somme) (mem3 v_resultat_1
  (union4 (union4 (add3 E_Invalide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))
  (=> (= v_precedent_1 E_Distribution_billets) (mem3 v_resultat_1
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))))
  (=>
  (and (= v_courant_1 E_Confiscation_carte) (= E_Hors_service E_En_service))
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_precedent_1)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Restitution_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_precedent_1 E_Traitement_carte) (= v_resultat_1 E_Interdite)))
  (=> (= v_precedent_1 E_Traitement_code) (= v_resultat_1 E_Invalide)))
  (=> (= v_precedent_1 E_Restitution_carte) (mem3 v_resultat_1
  (union4 (add3 E_Incident empty4) (add3 E_Hors_delai empty4)))))))
  (= E_Hors_service E_En_service)) (= v_courant_1 E_Distribution_billets)))))

(declare-fun f54 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f54_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f54 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (<= v_somme_1 (tb2t1 (apply int int (t2tb5 v_comptes_1) (t2tb1 v_carte_1)))))))

(declare-fun f56 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f56_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f56 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and (= v_etat_dab_1 E_En_service)
  (or (= v_tst_dab_1 true) (<= (+ v_caisse_1 1) 900)))
  (=> (and (= v_courant_1 E_Traitement_code) (= E_Hors_service E_En_service))
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_precedent_1)
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_precedent_1 E_Traitement_code) (mem3 v_resultat_1
  (union4 (add3 E_Nouvel empty4) (add3 E_Dernier empty4)))))
  (=> (= v_precedent_1 E_Traitement_carte) (= v_resultat_1 E_Valide)))))
  (=>
  (and (= v_courant_1 E_Restitution_carte) (= E_Hors_service E_En_service))
  (and
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_precedent_1)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_somme)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Distribution_billets)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_precedent_1 E_Traitement_carte) (mem3 v_resultat_1
  (union4
  (union4 (union4 (add3 E_Perimee empty4) (add3 E_Epuisee empty4))
  (add3 E_Illisible empty4)) (add3 E_Invalide empty4)))))
  (=> (= v_precedent_1 E_Traitement_code) (mem3 v_resultat_1
  (union4 (add3 E_Hors_delai empty4) (add3 E_Incident empty4)))))
  (=> (= v_precedent_1 E_Traitement_somme) (mem3 v_resultat_1
  (union4 (union4 (add3 E_Invalide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))
  (=> (= v_precedent_1 E_Distribution_billets) (mem3 v_resultat_1
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))))
  (=>
  (and (= v_courant_1 E_Confiscation_carte) (= E_Hors_service E_En_service))
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_precedent_1)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Restitution_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_precedent_1 E_Traitement_carte) (= v_resultat_1 E_Interdite)))
  (=> (= v_precedent_1 E_Traitement_code) (= v_resultat_1 E_Invalide)))
  (=> (= v_precedent_1 E_Restitution_carte) (mem3 v_resultat_1
  (union4 (add3 E_Incident empty4) (add3 E_Hors_delai empty4)))))))
  (= E_Hors_service E_En_service)))))

(declare-fun f60 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f60_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f60 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and (= v_etat_dab_1 E_En_service)
  (or (= v_tst_dab_1 true) (<= (+ v_caisse_1 1) 900)))
  (=> (and (= v_courant_1 E_Traitement_code) (= E_Hors_service E_En_service))
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_precedent_1)
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_precedent_1 E_Traitement_code) (mem3 v_resultat_1
  (union4 (add3 E_Nouvel empty4) (add3 E_Dernier empty4)))))
  (=> (= v_precedent_1 E_Traitement_carte) (= v_resultat_1 E_Valide)))))
  (=>
  (and (= v_courant_1 E_Restitution_carte) (= E_Hors_service E_En_service))
  (and
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_precedent_1)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_somme)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Distribution_billets)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_precedent_1 E_Traitement_carte) (mem3 v_resultat_1
  (union4
  (union4 (union4 (add3 E_Perimee empty4) (add3 E_Epuisee empty4))
  (add3 E_Illisible empty4)) (add3 E_Invalide empty4)))))
  (=> (= v_precedent_1 E_Traitement_code) (mem3 v_resultat_1
  (union4 (add3 E_Hors_delai empty4) (add3 E_Incident empty4)))))
  (=> (= v_precedent_1 E_Traitement_somme) (mem3 v_resultat_1
  (union4 (union4 (add3 E_Invalide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))
  (=> (= v_precedent_1 E_Distribution_billets) (mem3 v_resultat_1
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))))
  (=>
  (and (= v_courant_1 E_Confiscation_carte) (= E_Hors_service E_En_service))
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_precedent_1)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Restitution_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_precedent_1 E_Traitement_carte) (= v_resultat_1 E_Interdite)))
  (=> (= v_precedent_1 E_Traitement_code) (= v_resultat_1 E_Invalide)))
  (=> (= v_precedent_1 E_Restitution_carte) (mem3 v_resultat_1
  (union4 (add3 E_Incident empty4) (add3 E_Hors_delai empty4)))))))
  (= E_Hors_service E_En_service)) (= v_courant_1 E_Veille)))))

(declare-fun f64 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f64_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f64 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and (= v_etat_dab_1 E_En_service)
  (or (= v_tst_dab_1 true) (<= (+ v_caisse_1 1) 900)))
  (=> (and (= v_courant_1 E_Traitement_code) (= E_Hors_service E_En_service))
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_precedent_1)
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_precedent_1 E_Traitement_code) (mem3 v_resultat_1
  (union4 (add3 E_Nouvel empty4) (add3 E_Dernier empty4)))))
  (=> (= v_precedent_1 E_Traitement_carte) (= v_resultat_1 E_Valide)))))
  (=>
  (and (= v_courant_1 E_Restitution_carte) (= E_Hors_service E_En_service))
  (and
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_precedent_1)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_somme)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Distribution_billets)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_precedent_1 E_Traitement_carte) (mem3 v_resultat_1
  (union4
  (union4 (union4 (add3 E_Perimee empty4) (add3 E_Epuisee empty4))
  (add3 E_Illisible empty4)) (add3 E_Invalide empty4)))))
  (=> (= v_precedent_1 E_Traitement_code) (mem3 v_resultat_1
  (union4 (add3 E_Hors_delai empty4) (add3 E_Incident empty4)))))
  (=> (= v_precedent_1 E_Traitement_somme) (mem3 v_resultat_1
  (union4 (union4 (add3 E_Invalide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))
  (=> (= v_precedent_1 E_Distribution_billets) (mem3 v_resultat_1
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))))
  (=>
  (and (= v_courant_1 E_Confiscation_carte) (= E_Hors_service E_En_service))
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_precedent_1)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Restitution_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_precedent_1 E_Traitement_carte) (= v_resultat_1 E_Interdite)))
  (=> (= v_precedent_1 E_Traitement_code) (= v_resultat_1 E_Invalide)))
  (=> (= v_precedent_1 E_Restitution_carte) (mem3 v_resultat_1
  (union4 (add3 E_Incident empty4) (add3 E_Hors_delai empty4)))))))
  (= E_Hors_service E_En_service)) (= v_courant_1 E_Traitement_carte)))))

(declare-fun f66 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f66_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f66 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and (= v_etat_dab_1 E_En_service)
  (or (= v_tst_dab_1 true) (<= (+ v_caisse_1 1) 900)))
  (=> (and (= v_courant_1 E_Traitement_code) (= E_Hors_service E_En_service))
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_precedent_1)
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_precedent_1 E_Traitement_code) (mem3 v_resultat_1
  (union4 (add3 E_Nouvel empty4) (add3 E_Dernier empty4)))))
  (=> (= v_precedent_1 E_Traitement_carte) (= v_resultat_1 E_Valide)))))
  (=>
  (and (= v_courant_1 E_Restitution_carte) (= E_Hors_service E_En_service))
  (and
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_precedent_1)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_somme)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Distribution_billets)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_precedent_1 E_Traitement_carte) (mem3 v_resultat_1
  (union4
  (union4 (union4 (add3 E_Perimee empty4) (add3 E_Epuisee empty4))
  (add3 E_Illisible empty4)) (add3 E_Invalide empty4)))))
  (=> (= v_precedent_1 E_Traitement_code) (mem3 v_resultat_1
  (union4 (add3 E_Hors_delai empty4) (add3 E_Incident empty4)))))
  (=> (= v_precedent_1 E_Traitement_somme) (mem3 v_resultat_1
  (union4 (union4 (add3 E_Invalide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))
  (=> (= v_precedent_1 E_Distribution_billets) (mem3 v_resultat_1
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))))
  (=>
  (and (= v_courant_1 E_Confiscation_carte) (= E_Hors_service E_En_service))
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_precedent_1)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Restitution_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_precedent_1 E_Traitement_carte) (= v_resultat_1 E_Interdite)))
  (=> (= v_precedent_1 E_Traitement_code) (= v_resultat_1 E_Invalide)))
  (=> (= v_precedent_1 E_Restitution_carte) (mem3 v_resultat_1
  (union4 (add3 E_Incident empty4) (add3 E_Hors_delai empty4)))))))
  (= E_Hors_service E_En_service)) (= v_courant_1 E_Traitement_code)) (mem3
  v_resultat_1 (union4 (add3 E_Nouvel empty4) (add3 E_Dernier empty4)))))))

(declare-fun f70 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f70_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f70 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE) (not (<= (+ v_caisse_1 1) 900)))))

(declare-fun f72 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f72_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f72 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and (= v_etat_dab_1 E_En_service)
  (or (= v_tst_dab_1 true) (<= (+ v_caisse_1 1) 900)))
  (=> (and (= v_courant_1 E_Traitement_code) (= E_Hors_service E_En_service))
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_precedent_1)
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_precedent_1 E_Traitement_code) (mem3 v_resultat_1
  (union4 (add3 E_Nouvel empty4) (add3 E_Dernier empty4)))))
  (=> (= v_precedent_1 E_Traitement_carte) (= v_resultat_1 E_Valide)))))
  (=>
  (and (= v_courant_1 E_Restitution_carte) (= E_Hors_service E_En_service))
  (and
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_precedent_1)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_somme)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Distribution_billets)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_precedent_1 E_Traitement_carte) (mem3 v_resultat_1
  (union4
  (union4 (union4 (add3 E_Perimee empty4) (add3 E_Epuisee empty4))
  (add3 E_Illisible empty4)) (add3 E_Invalide empty4)))))
  (=> (= v_precedent_1 E_Traitement_code) (mem3 v_resultat_1
  (union4 (add3 E_Hors_delai empty4) (add3 E_Incident empty4)))))
  (=> (= v_precedent_1 E_Traitement_somme) (mem3 v_resultat_1
  (union4 (union4 (add3 E_Invalide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))
  (=> (= v_precedent_1 E_Distribution_billets) (mem3 v_resultat_1
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))))
  (=>
  (and (= v_courant_1 E_Confiscation_carte) (= E_Hors_service E_En_service))
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_precedent_1)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Restitution_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_precedent_1 E_Traitement_carte) (= v_resultat_1 E_Interdite)))
  (=> (= v_precedent_1 E_Traitement_code) (= v_resultat_1 E_Invalide)))
  (=> (= v_precedent_1 E_Restitution_carte) (mem3 v_resultat_1
  (union4 (add3 E_Incident empty4) (add3 E_Hors_delai empty4)))))))
  (not (<= (+ v_caisse_1 1) 900))) (= v_tst_dab_1 false)))))

(declare-fun f74 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f74_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f74 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and (and (= v_etat_dab_1 E_En_service) (not (= v_tst_dab_1 true)))
  (not (<= (+ v_caisse_1 1) 900))) (= v_etat_dab_1 E_Hors_service)))))

(declare-fun f76 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f76_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f76 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (or (= v_panne_dab_1 true) (<= (+ v_caisse_1 1) 900)))))

(declare-fun f77 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f77_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f77 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and (and (= v_etat_dab_1 E_En_service) (not (= v_tst_dab_1 true)))
  (not (<= (+ v_caisse_1 1) 900))) (= v_panne_dab_1 true)))))

(declare-fun f79 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f79_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f79 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE) (= v_etat_dab_1 E_En_service))))

(declare-fun f80 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f80_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f80 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and (= v_etat_dab_1 E_En_service)
  (not (= v_courant_1 E_Restitution_carte)))
  (not (= v_courant_1 E_Distribution_billets)))
  (not (= v_courant_1 E_Traitement_somme)))
  (not (= v_courant_1 E_Traitement_code)))
  (not (= v_courant_1 E_Traitement_carte))) (= v_courant_1 E_Veille)))))

(declare-fun f82 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f82_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f82 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and (and (= v_etat_dab_1 E_En_service) (not (= v_courant_1 E_Veille)))
  (not (= v_courant_1 E_Restitution_carte)))
  (not (= v_courant_1 E_Distribution_billets)))
  (not (= v_courant_1 E_Traitement_somme)))
  (not (= v_courant_1 E_Traitement_code)))
  (= v_courant_1 E_Traitement_carte)))))

(declare-fun f83 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f83_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f83 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (= v_etat_dab_1 E_En_service) (not (= v_courant_1 E_Veille)))
  (not (= v_courant_1 E_Restitution_carte)))
  (not (= v_courant_1 E_Distribution_billets)))
  (not (= v_courant_1 E_Traitement_somme)))
  (not (= v_courant_1 E_Traitement_code)))
  (= v_courant_1 E_Traitement_carte)) (mem1 v_carte_2 v_CARTE)) (mem1
  v_code_CB_0 (mk 0 9999))) (mem1 v_date_validite_0 v_DATE)))))

(declare-fun f84 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f84_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f84 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and (and (= v_etat_dab_1 E_En_service) (not (= v_courant_1 E_Veille)))
  (not (= v_courant_1 E_Traitement_carte)))
  (not (= v_courant_1 E_Restitution_carte)))
  (not (= v_courant_1 E_Distribution_billets)))
  (not (= v_courant_1 E_Traitement_somme)))
  (= v_courant_1 E_Traitement_code)))))

(declare-fun f86 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f86_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f86 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and (and (= v_etat_dab_1 E_En_service) (not (= v_courant_1 E_Veille)))
  (not (= v_courant_1 E_Traitement_carte)))
  (not (= v_courant_1 E_Restitution_carte)))
  (not (= v_courant_1 E_Distribution_billets)))
  (not (= v_courant_1 E_Traitement_somme)))
  (= v_courant_1 E_Traitement_code)) (= v_precedent_1 E_Traitement_code)))))

(declare-fun f88 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f88_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f88 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and (and (= v_etat_dab_1 E_En_service) (not (= v_courant_1 E_Veille)))
  (not (= v_courant_1 E_Traitement_carte)))
  (not (= v_courant_1 E_Restitution_carte)))
  (not (= v_courant_1 E_Distribution_billets)))
  (not (= v_courant_1 E_Traitement_somme)))
  (= v_courant_1 E_Traitement_code)) (= v_precedent_1 E_Traitement_carte)))))

(declare-fun f90 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f90_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f90 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and (and (= v_etat_dab_1 E_En_service) (not (= v_courant_1 E_Veille)))
  (not (= v_courant_1 E_Traitement_carte)))
  (not (= v_courant_1 E_Traitement_code)))
  (not (= v_courant_1 E_Restitution_carte)))
  (not (= v_courant_1 E_Distribution_billets)))
  (= v_courant_1 E_Traitement_somme)))))

(declare-fun f91 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f91_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f91 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and (and (= v_etat_dab_1 E_En_service) (not (= v_courant_1 E_Veille)))
  (not (= v_courant_1 E_Traitement_carte)))
  (not (= v_courant_1 E_Traitement_code)))
  (not (= v_courant_1 E_Traitement_somme)))
  (not (= v_courant_1 E_Restitution_carte)))
  (= v_courant_1 E_Distribution_billets)))))

(declare-fun f92 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f92_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f92 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and (and (= v_etat_dab_1 E_En_service) (not (= v_courant_1 E_Veille)))
  (not (= v_courant_1 E_Traitement_carte)))
  (not (= v_courant_1 E_Traitement_code)))
  (not (= v_courant_1 E_Traitement_somme)))
  (not (= v_courant_1 E_Distribution_billets)))
  (= v_courant_1 E_Restitution_carte)))))

(declare-fun f94 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f94_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f94 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and (and (= v_etat_dab_1 E_En_service) (not (= v_courant_1 E_Veille)))
  (not (= v_courant_1 E_Traitement_carte)))
  (not (= v_courant_1 E_Traitement_code)))
  (not (= v_courant_1 E_Traitement_somme)))
  (not (= v_courant_1 E_Distribution_billets)))
  (= v_courant_1 E_Restitution_carte)) (= v_precedent_1 E_Traitement_carte)))))

(declare-fun f96 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f96_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f96 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and (and (= v_etat_dab_1 E_En_service) (not (= v_courant_1 E_Veille)))
  (not (= v_courant_1 E_Traitement_carte)))
  (not (= v_courant_1 E_Traitement_code)))
  (not (= v_courant_1 E_Traitement_somme)))
  (not (= v_courant_1 E_Distribution_billets)))
  (= v_courant_1 E_Restitution_carte)) (= v_precedent_1 E_Traitement_code)))))

(declare-fun f98 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f98_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f98 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0
  v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits
  v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab
  v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and (and (= v_etat_dab_1 E_En_service) (not (= v_courant_1 E_Veille)))
  (not (= v_courant_1 E_Traitement_carte)))
  (not (= v_courant_1 E_Traitement_code)))
  (not (= v_courant_1 E_Traitement_somme)))
  (not (= v_courant_1 E_Distribution_billets)))
  (= v_courant_1 E_Restitution_carte)) (= v_precedent_1 E_Traitement_somme)))))

(declare-fun f100 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f100_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f100 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1
  v_somme_0 v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1
  v_retraits v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1
  v_panne_dab v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1
  v_interdits v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and (and (= v_etat_dab_1 E_En_service) (not (= v_courant_1 E_Veille)))
  (not (= v_courant_1 E_Traitement_carte)))
  (not (= v_courant_1 E_Traitement_code)))
  (not (= v_courant_1 E_Traitement_somme)))
  (not (= v_courant_1 E_Distribution_billets)))
  (= v_courant_1 E_Restitution_carte))
  (= v_precedent_1 E_Distribution_billets)))))

(declare-fun f102 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f102_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f102 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1
  v_somme_0 v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1
  v_retraits v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1
  v_panne_dab v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1
  v_interdits v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and (and (= v_etat_dab_1 E_En_service) (not (= v_courant_1 E_Veille)))
  (not (= v_courant_1 E_Traitement_carte)))
  (not (= v_courant_1 E_Traitement_code)))
  (not (= v_courant_1 E_Traitement_somme)))
  (not (= v_courant_1 E_Distribution_billets)))
  (not (= v_courant_1 E_Restitution_carte))))))

(declare-fun f105 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f105_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f105 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1
  v_somme_0 v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1
  v_retraits v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1
  v_panne_dab v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1
  v_interdits v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and (= v_etat_dab_1 E_En_service)
  (not (= v_courant_1 E_Restitution_carte)))
  (not (= v_courant_1 E_Distribution_billets)))
  (not (= v_courant_1 E_Traitement_somme)))
  (not (= v_courant_1 E_Traitement_code)))
  (not (= v_courant_1 E_Traitement_carte))) (mem3 v_rslt_1
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))) (= v_courant_1 E_Veille)))))

(declare-fun f108 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f108_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int))) (f108 v_tst_dab_1
  v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0 v_somme v_som_0
  v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits v_resultat_1
  v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab v_n_msg
  v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)))

(declare-fun f109 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f109_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f109 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1
  v_somme_0 v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1
  v_retraits v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1
  v_panne_dab v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1
  v_interdits v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (= v_etat_dab_1 E_En_service)
  (not (= v_courant_1 E_Restitution_carte)))
  (not (= v_courant_1 E_Distribution_billets)))
  (not (= v_courant_1 E_Traitement_somme)))
  (not (= v_courant_1 E_Traitement_code)))
  (not (= v_courant_1 E_Traitement_carte))) (mem3 v_rslt_1
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))) (= v_courant_1 E_Veille))
  (= v_courant_1 E_Confiscation_carte)))))

(declare-fun f111 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f111_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f111 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1
  v_somme_0 v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1
  v_retraits v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1
  v_panne_dab v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1
  v_interdits v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (= v_etat_dab_1 E_En_service) (not (= v_courant_1 E_Veille)))
  (not (= v_courant_1 E_Restitution_carte)))
  (not (= v_courant_1 E_Distribution_billets)))
  (not (= v_courant_1 E_Traitement_somme)))
  (not (= v_courant_1 E_Traitement_code))) (mem1 v_carte_2 v_CARTE)) (mem1
  v_code_CB_0 (mk 0 9999))) (mem1 v_date_validite_0 v_DATE)) (mem3 v_ctr
  (union4
  (union4
  (union4
  (union4
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Invalide empty4))
  (add3 E_Illisible empty4)) (add3 E_Interdite empty4))
  (add3 E_Perimee empty4)) (add3 E_Incident empty4)) (add3 E_Epuisee empty4))))
  (=>
  (and
  (and
  (and
  (and (and (not (= v_ctr E_Invalide)) (not (= v_ctr E_Illisible)))
  (not (= v_ctr E_Incident)))
  (and (mem1 v_carte_2 v_clients_1) (not (mem1 v_carte_2 v_interdits_1))))
  (<= 100 (tb2t1 (apply int int (t2tb5 v_comptes_1) (t2tb1 v_carte_2)))))
  (<= v_date v_date_validite_0)) (= v_ctr E_Valide)))
  (=> (= v_ctr E_Valide)
  (and
  (and
  (and
  (and (and (not (= v_ctr E_Invalide)) (not (= v_ctr E_Illisible)))
  (not (= v_ctr E_Incident)))
  (and (mem1 v_carte_2 v_clients_1) (not (mem1 v_carte_2 v_interdits_1))))
  (<= 100 (tb2t1 (apply int int (t2tb5 v_comptes_1) (t2tb1 v_carte_2)))))
  (<= v_date v_date_validite_0))))
  (=> (and (not (= v_ctr E_Illisible)) (not (= v_ctr E_Incident)))
  (= v_infl true)))
  (=> (= v_infl true)
  (and (not (= v_ctr E_Illisible)) (not (= v_ctr E_Incident)))))
  (=> (= v_ctr E_Incident) (= v_carte_2 v_K0)))
  (=> (= v_carte_2 v_K0) (= v_ctr E_Incident)))
  (= v_courant_1 E_Traitement_carte)))))

(declare-fun f112 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f112_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int))) (f112 v_tst_dab_1
  v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0 v_somme v_som_0
  v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits v_resultat_1
  v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab v_n_msg
  v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)))

(declare-fun f114 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f114_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f114 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1
  v_somme_0 v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1
  v_retraits v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1
  v_panne_dab v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1
  v_interdits v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (= v_etat_dab_1 E_En_service) (not (= v_courant_1 E_Veille)))
  (not (= v_courant_1 E_Restitution_carte)))
  (not (= v_courant_1 E_Distribution_billets)))
  (not (= v_courant_1 E_Traitement_somme)))
  (not (= v_courant_1 E_Traitement_code))) (mem1 v_carte_2 v_CARTE)) (mem1
  v_code_CB_0 (mk 0 9999))) (mem1 v_date_validite_0 v_DATE)) (mem3 v_ctr
  (union4
  (union4
  (union4
  (union4
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Invalide empty4))
  (add3 E_Illisible empty4)) (add3 E_Interdite empty4))
  (add3 E_Perimee empty4)) (add3 E_Incident empty4)) (add3 E_Epuisee empty4))))
  (=>
  (and
  (and
  (and
  (and (and (not (= v_ctr E_Invalide)) (not (= v_ctr E_Illisible)))
  (not (= v_ctr E_Incident)))
  (and (mem1 v_carte_2 v_clients_1) (not (mem1 v_carte_2 v_interdits_1))))
  (<= 100 (tb2t1 (apply int int (t2tb5 v_comptes_1) (t2tb1 v_carte_2)))))
  (<= v_date v_date_validite_0)) (= v_ctr E_Valide)))
  (=> (= v_ctr E_Valide)
  (and
  (and
  (and
  (and (and (not (= v_ctr E_Invalide)) (not (= v_ctr E_Illisible)))
  (not (= v_ctr E_Incident)))
  (and (mem1 v_carte_2 v_clients_1) (not (mem1 v_carte_2 v_interdits_1))))
  (<= 100 (tb2t1 (apply int int (t2tb5 v_comptes_1) (t2tb1 v_carte_2)))))
  (<= v_date v_date_validite_0))))
  (=> (and (not (= v_ctr E_Illisible)) (not (= v_ctr E_Incident)))
  (= v_infl true)))
  (=> (= v_infl true)
  (and (not (= v_ctr E_Illisible)) (not (= v_ctr E_Incident)))))
  (=> (= v_ctr E_Incident) (= v_carte_2 v_K0)))
  (=> (= v_carte_2 v_K0) (= v_ctr E_Incident)))
  (= v_courant_1 E_Traitement_carte)) (mem enum_ETAT_AUTOMATE1
  (t2tb9 v_courant_1)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Distribution_billets)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Restitution_carte)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Veille) (empty enum_ETAT_AUTOMATE1))))))))

(declare-fun f116 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f116_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f116 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1
  v_somme_0 v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1
  v_retraits v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1
  v_panne_dab v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1
  v_interdits v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (= v_etat_dab_1 E_En_service) (not (= v_courant_1 E_Veille)))
  (not (= v_courant_1 E_Restitution_carte)))
  (not (= v_courant_1 E_Distribution_billets)))
  (not (= v_courant_1 E_Traitement_somme)))
  (not (= v_courant_1 E_Traitement_code))) (mem1 v_carte_2 v_CARTE)) (mem1
  v_code_CB_0 (mk 0 9999))) (mem1 v_date_validite_0 v_DATE)) (mem3 v_ctr
  (union4
  (union4
  (union4
  (union4
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Invalide empty4))
  (add3 E_Illisible empty4)) (add3 E_Interdite empty4))
  (add3 E_Perimee empty4)) (add3 E_Incident empty4)) (add3 E_Epuisee empty4))))
  (=>
  (and
  (and
  (and
  (and (and (not (= v_ctr E_Invalide)) (not (= v_ctr E_Illisible)))
  (not (= v_ctr E_Incident)))
  (and (mem1 v_carte_2 v_clients_1) (not (mem1 v_carte_2 v_interdits_1))))
  (<= 100 (tb2t1 (apply int int (t2tb5 v_comptes_1) (t2tb1 v_carte_2)))))
  (<= v_date v_date_validite_0)) (= v_ctr E_Valide)))
  (=> (= v_ctr E_Valide)
  (and
  (and
  (and
  (and (and (not (= v_ctr E_Invalide)) (not (= v_ctr E_Illisible)))
  (not (= v_ctr E_Incident)))
  (and (mem1 v_carte_2 v_clients_1) (not (mem1 v_carte_2 v_interdits_1))))
  (<= 100 (tb2t1 (apply int int (t2tb5 v_comptes_1) (t2tb1 v_carte_2)))))
  (<= v_date v_date_validite_0))))
  (=> (and (not (= v_ctr E_Illisible)) (not (= v_ctr E_Incident)))
  (= v_infl true)))
  (=> (= v_infl true)
  (and (not (= v_ctr E_Illisible)) (not (= v_ctr E_Incident)))))
  (=> (= v_ctr E_Incident) (= v_carte_2 v_K0)))
  (=> (= v_carte_2 v_K0) (= v_ctr E_Incident)))
  (= v_courant_1 E_Traitement_carte)) (= v_courant_1 E_Confiscation_carte)))))

(declare-fun f118 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f118_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f118 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1
  v_somme_0 v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1
  v_retraits v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1
  v_panne_dab v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1
  v_interdits v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (= v_etat_dab_1 E_En_service) (not (= v_courant_1 E_Veille)))
  (not (= v_courant_1 E_Traitement_carte)))
  (not (= v_courant_1 E_Restitution_carte)))
  (not (= v_courant_1 E_Distribution_billets)))
  (not (= v_courant_1 E_Traitement_somme)))
  (=> (= v_precedent_1 E_Traitement_carte) (= v_msg E_Entrez_votre_code)))
  (=> (= v_precedent_1 E_Traitement_code)
  (and (=> (= v_resultat_1 E_Nouvel) (= v_msg E_Nouvel_essai))
  (=> (= v_resultat_1 E_Dernier) (= v_msg E_Dernier_essai))))) (mem1 v_cds
  (mk 0 9999))) (mem3 v_ctrl
  (union4
  (union4
  (union4
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Nouvel empty4))
  (add3 E_Dernier empty4)) (add3 E_Invalide empty4))
  (add3 E_Hors_delai empty4)) (add3 E_Incident empty4)))) (mem1 v_cds_0
  (mk 0 9999)))
  (=>
  (and (= v_code_CB_1 v_cds_0)
  (and (not (= v_ctrl E_Hors_delai)) (not (= v_ctrl E_Incident))))
  (= v_ctrl E_Valide)))
  (=> (= v_ctrl E_Valide)
  (and (= v_code_CB_1 v_cds_0)
  (and (not (= v_ctrl E_Hors_delai)) (not (= v_ctrl E_Incident))))))
  (=> (= v_ctrl E_Invalide) (= v_essaip false)))
  (=> (mem3 v_ctrl (union4 (add3 E_Nouvel empty4) (add3 E_Dernier empty4)))
  (= v_essaip true))) (= v_courant_1 E_Traitement_code)))))

(declare-fun f119 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f119_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int))) (f119 v_tst_dab_1
  v_somme_demandee_1 v_somme_demandee v_somme_1 v_somme_0 v_somme v_som_0
  v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1 v_retraits v_resultat_1
  v_resultat v_precedent_1 v_precedent v_panne_dab_1 v_panne_dab v_n_msg
  v_msg_0 v_msg v_message_1 v_message v_interdits_1 v_interdits
  v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)))

(declare-fun f121 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f121_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f121 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1
  v_somme_0 v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1
  v_retraits v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1
  v_panne_dab v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1
  v_interdits v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (= v_etat_dab_1 E_En_service) (not (= v_courant_1 E_Veille)))
  (not (= v_courant_1 E_Traitement_carte)))
  (not (= v_courant_1 E_Restitution_carte)))
  (not (= v_courant_1 E_Distribution_billets)))
  (not (= v_courant_1 E_Traitement_somme)))
  (=> (= v_precedent_1 E_Traitement_carte) (= v_msg E_Entrez_votre_code)))
  (=> (= v_precedent_1 E_Traitement_code)
  (and (=> (= v_resultat_1 E_Nouvel) (= v_msg E_Nouvel_essai))
  (=> (= v_resultat_1 E_Dernier) (= v_msg E_Dernier_essai))))) (mem1 v_cds
  (mk 0 9999))) (mem3 v_ctrl
  (union4
  (union4
  (union4
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Nouvel empty4))
  (add3 E_Dernier empty4)) (add3 E_Invalide empty4))
  (add3 E_Hors_delai empty4)) (add3 E_Incident empty4)))) (mem1 v_cds_0
  (mk 0 9999)))
  (=>
  (and (= v_code_CB_1 v_cds_0)
  (and (not (= v_ctrl E_Hors_delai)) (not (= v_ctrl E_Incident))))
  (= v_ctrl E_Valide)))
  (=> (= v_ctrl E_Valide)
  (and (= v_code_CB_1 v_cds_0)
  (and (not (= v_ctrl E_Hors_delai)) (not (= v_ctrl E_Incident))))))
  (=> (= v_ctrl E_Invalide) (= v_essaip false)))
  (=> (mem3 v_ctrl (union4 (add3 E_Nouvel empty4) (add3 E_Dernier empty4)))
  (= v_essaip true))) (= v_courant_1 E_Traitement_code)) (mem
  enum_ETAT_AUTOMATE1 (t2tb9 v_courant_1)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Distribution_billets)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Restitution_carte)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Veille) (empty enum_ETAT_AUTOMATE1))))))))

(declare-fun f123 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f123_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f123 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1
  v_somme_0 v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1
  v_retraits v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1
  v_panne_dab v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1
  v_interdits v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (= v_etat_dab_1 E_En_service) (not (= v_courant_1 E_Veille)))
  (not (= v_courant_1 E_Traitement_carte)))
  (not (= v_courant_1 E_Restitution_carte)))
  (not (= v_courant_1 E_Distribution_billets)))
  (not (= v_courant_1 E_Traitement_somme)))
  (=> (= v_precedent_1 E_Traitement_carte) (= v_msg E_Entrez_votre_code)))
  (=> (= v_precedent_1 E_Traitement_code)
  (and (=> (= v_resultat_1 E_Nouvel) (= v_msg E_Nouvel_essai))
  (=> (= v_resultat_1 E_Dernier) (= v_msg E_Dernier_essai))))) (mem1 v_cds
  (mk 0 9999))) (mem3 v_ctrl
  (union4
  (union4
  (union4
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Nouvel empty4))
  (add3 E_Dernier empty4)) (add3 E_Invalide empty4))
  (add3 E_Hors_delai empty4)) (add3 E_Incident empty4)))) (mem1 v_cds_0
  (mk 0 9999)))
  (=>
  (and (= v_code_CB_1 v_cds_0)
  (and (not (= v_ctrl E_Hors_delai)) (not (= v_ctrl E_Incident))))
  (= v_ctrl E_Valide)))
  (=> (= v_ctrl E_Valide)
  (and (= v_code_CB_1 v_cds_0)
  (and (not (= v_ctrl E_Hors_delai)) (not (= v_ctrl E_Incident))))))
  (=> (= v_ctrl E_Invalide) (= v_essaip false)))
  (=> (mem3 v_ctrl (union4 (add3 E_Nouvel empty4) (add3 E_Dernier empty4)))
  (= v_essaip true))) (= v_courant_1 E_Traitement_code))
  (= v_courant_1 E_Confiscation_carte)))))

(declare-fun f125 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f125_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f125 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1
  v_somme_0 v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1
  v_retraits v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1
  v_panne_dab v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1
  v_interdits v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (= v_etat_dab_1 E_En_service) (not (= v_courant_1 E_Veille)))
  (not (= v_courant_1 E_Traitement_carte)))
  (not (= v_courant_1 E_Traitement_code)))
  (not (= v_courant_1 E_Restitution_carte)))
  (not (= v_courant_1 E_Distribution_billets))) (mem1 v_som (mk 100 900)))
  (mem3 v_ctr
  (union4
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Invalide empty4))
  (add3 E_Hors_delai empty4)) (add3 E_Incident empty4))))
  (=>
  (and
  (and
  (and (and (not (= v_ctr E_Hors_delai)) (not (= v_ctr E_Incident))) (mem1
  v_som (mk 100 900)))
  (<= v_som (tb2t1 (apply int int (t2tb5 v_comptes_1) (t2tb1 v_carte_1)))))
  (<= v_som v_caisse_1)) (= v_ctr E_Valide)))
  (=> (= v_ctr E_Valide)
  (and
  (and
  (and (and (not (= v_ctr E_Hors_delai)) (not (= v_ctr E_Incident))) (mem1
  v_som (mk 100 900)))
  (<= v_som (tb2t1 (apply int int (t2tb5 v_comptes_1) (t2tb1 v_carte_1)))))
  (<= v_som v_caisse_1)))) (= v_courant_1 E_Traitement_somme)))))

(declare-fun f126 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f126_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f126 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1
  v_somme_0 v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1
  v_retraits v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1
  v_panne_dab v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1
  v_interdits v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (= v_etat_dab_1 E_En_service) (not (= v_courant_1 E_Veille)))
  (not (= v_courant_1 E_Traitement_carte)))
  (not (= v_courant_1 E_Traitement_code)))
  (not (= v_courant_1 E_Restitution_carte)))
  (not (= v_courant_1 E_Distribution_billets))) (mem1 v_som (mk 100 900)))
  (mem3 v_ctr
  (union4
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Invalide empty4))
  (add3 E_Hors_delai empty4)) (add3 E_Incident empty4))))
  (=>
  (and
  (and
  (and (and (not (= v_ctr E_Hors_delai)) (not (= v_ctr E_Incident))) (mem1
  v_som (mk 100 900)))
  (<= v_som (tb2t1 (apply int int (t2tb5 v_comptes_1) (t2tb1 v_carte_1)))))
  (<= v_som v_caisse_1)) (= v_ctr E_Valide)))
  (=> (= v_ctr E_Valide)
  (and
  (and
  (and (and (not (= v_ctr E_Hors_delai)) (not (= v_ctr E_Incident))) (mem1
  v_som (mk 100 900)))
  (<= v_som (tb2t1 (apply int int (t2tb5 v_comptes_1) (t2tb1 v_carte_1)))))
  (<= v_som v_caisse_1)))) (= v_courant_1 E_Traitement_somme)) (mem
  enum_ETAT_AUTOMATE1 (t2tb9 v_courant_1)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Distribution_billets)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Restitution_carte)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Veille) (empty enum_ETAT_AUTOMATE1))))))))

(declare-fun f127 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f127_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f127 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1
  v_somme_0 v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1
  v_retraits v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1
  v_panne_dab v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1
  v_interdits v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (= v_etat_dab_1 E_En_service) (not (= v_courant_1 E_Veille)))
  (not (= v_courant_1 E_Traitement_carte)))
  (not (= v_courant_1 E_Traitement_code)))
  (not (= v_courant_1 E_Restitution_carte)))
  (not (= v_courant_1 E_Distribution_billets))) (mem1 v_som (mk 100 900)))
  (mem3 v_ctr
  (union4
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Invalide empty4))
  (add3 E_Hors_delai empty4)) (add3 E_Incident empty4))))
  (=>
  (and
  (and
  (and (and (not (= v_ctr E_Hors_delai)) (not (= v_ctr E_Incident))) (mem1
  v_som (mk 100 900)))
  (<= v_som (tb2t1 (apply int int (t2tb5 v_comptes_1) (t2tb1 v_carte_1)))))
  (<= v_som v_caisse_1)) (= v_ctr E_Valide)))
  (=> (= v_ctr E_Valide)
  (and
  (and
  (and (and (not (= v_ctr E_Hors_delai)) (not (= v_ctr E_Incident))) (mem1
  v_som (mk 100 900)))
  (<= v_som (tb2t1 (apply int int (t2tb5 v_comptes_1) (t2tb1 v_carte_1)))))
  (<= v_som v_caisse_1)))) (= v_courant_1 E_Traitement_somme))
  (= v_courant_1 E_Confiscation_carte)))))

(declare-fun f128 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f128_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f128 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1
  v_somme_0 v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1
  v_retraits v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1
  v_panne_dab v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1
  v_interdits v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (= v_etat_dab_1 E_En_service) (not (= v_courant_1 E_Veille)))
  (not (= v_courant_1 E_Traitement_carte)))
  (not (= v_courant_1 E_Traitement_code)))
  (not (= v_courant_1 E_Traitement_somme)))
  (not (= v_courant_1 E_Restitution_carte))) (mem3 v_ctr
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))) (mem1 v_rjt
  (union1 (add1 0 empty1) (add1 v_somme_1 empty1))))
  (=> (= v_ctr E_Valide) (= v_rjt 0)))
  (=> (= v_ctr E_Hors_delai) (= v_rjt v_somme_1)))
  (= v_courant_1 E_Distribution_billets)))))

(declare-fun f129 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f129_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f129 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1
  v_somme_0 v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1
  v_retraits v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1
  v_panne_dab v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1
  v_interdits v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (= v_etat_dab_1 E_En_service) (not (= v_courant_1 E_Veille)))
  (not (= v_courant_1 E_Traitement_carte)))
  (not (= v_courant_1 E_Traitement_code)))
  (not (= v_courant_1 E_Traitement_somme)))
  (not (= v_courant_1 E_Restitution_carte))) (mem3 v_ctr
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))) (mem1 v_rjt
  (union1 (add1 0 empty1) (add1 v_somme_1 empty1))))
  (=> (= v_ctr E_Valide) (= v_rjt 0)))
  (=> (= v_ctr E_Hors_delai) (= v_rjt v_somme_1)))
  (= v_courant_1 E_Distribution_billets))
  (= v_courant_1 E_Confiscation_carte)))))

(declare-fun f130 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f130_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f130 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1
  v_somme_0 v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1
  v_retraits v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1
  v_panne_dab v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1
  v_interdits v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (= v_etat_dab_1 E_En_service) (not (= v_courant_1 E_Veille)))
  (not (= v_courant_1 E_Traitement_carte)))
  (not (= v_courant_1 E_Traitement_code)))
  (not (= v_courant_1 E_Traitement_somme)))
  (not (= v_courant_1 E_Distribution_billets)))
  (=> (= v_precedent_1 E_Traitement_carte)
  (and
  (and
  (and (=> (= v_resultat_1 E_Perimee) (= v_msg E_Carte_perimee))
  (=> (= v_resultat_1 E_Epuisee) (= v_msg E_Carte_epuisee)))
  (=> (= v_resultat_1 E_Illisible) (= v_msg E_Carte_invalide)))
  (=> (= v_resultat_1 E_Invalide) (= v_msg E_Carte_invalide)))))
  (=> (= v_precedent_1 E_Traitement_code)
  (and (=> (= v_resultat_1 E_Hors_delai) (= v_msg E_Retirez_votre_carte))
  (=> (= v_resultat_1 E_Incident) (= v_msg E_Retirez_votre_carte)))))
  (=> (= v_precedent_1 E_Traitement_somme)
  (and
  (and (=> (= v_resultat_1 E_Invalide) (= v_msg E_Caisse_insuffisante))
  (=> (= v_resultat_1 E_Hors_delai) (= v_msg E_Retirez_votre_carte)))
  (=> (= v_resultat_1 E_Incident) (= v_msg E_Retirez_votre_carte)))))
  (=> (= v_precedent_1 E_Distribution_billets)
  (and
  (and (=> (= v_resultat_1 E_Valide) (= v_msg E_Retirez_votre_carte))
  (=> (= v_resultat_1 E_Hors_delai) (= v_msg E_Billets_confisques)))
  (=> (= v_resultat_1 E_Incident) (= v_msg E_Retirez_votre_carte))))) (mem3
  v_ctrl
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4))))
  (=> (= v_ctrl E_Valide) (= v_msg_0 E_Merci_de_votre_visite)))
  (=> (mem3 v_ctrl
  (union4 (add3 E_Hors_delai empty4) (add3 E_Incident empty4)))
  (= v_msg_0 v_msg))) (= v_courant_1 E_Restitution_carte)))))

(declare-fun f131 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f131_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f131 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1
  v_somme_0 v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1
  v_retraits v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1
  v_panne_dab v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1
  v_interdits v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (= v_etat_dab_1 E_En_service) (not (= v_courant_1 E_Veille)))
  (not (= v_courant_1 E_Traitement_carte)))
  (not (= v_courant_1 E_Traitement_code)))
  (not (= v_courant_1 E_Traitement_somme)))
  (not (= v_courant_1 E_Distribution_billets)))
  (=> (= v_precedent_1 E_Traitement_carte)
  (and
  (and
  (and (=> (= v_resultat_1 E_Perimee) (= v_msg E_Carte_perimee))
  (=> (= v_resultat_1 E_Epuisee) (= v_msg E_Carte_epuisee)))
  (=> (= v_resultat_1 E_Illisible) (= v_msg E_Carte_invalide)))
  (=> (= v_resultat_1 E_Invalide) (= v_msg E_Carte_invalide)))))
  (=> (= v_precedent_1 E_Traitement_code)
  (and (=> (= v_resultat_1 E_Hors_delai) (= v_msg E_Retirez_votre_carte))
  (=> (= v_resultat_1 E_Incident) (= v_msg E_Retirez_votre_carte)))))
  (=> (= v_precedent_1 E_Traitement_somme)
  (and
  (and (=> (= v_resultat_1 E_Invalide) (= v_msg E_Caisse_insuffisante))
  (=> (= v_resultat_1 E_Hors_delai) (= v_msg E_Retirez_votre_carte)))
  (=> (= v_resultat_1 E_Incident) (= v_msg E_Retirez_votre_carte)))))
  (=> (= v_precedent_1 E_Distribution_billets)
  (and
  (and (=> (= v_resultat_1 E_Valide) (= v_msg E_Retirez_votre_carte))
  (=> (= v_resultat_1 E_Hors_delai) (= v_msg E_Billets_confisques)))
  (=> (= v_resultat_1 E_Incident) (= v_msg E_Retirez_votre_carte))))) (mem3
  v_ctrl
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4))))
  (=> (= v_ctrl E_Valide) (= v_msg_0 E_Merci_de_votre_visite)))
  (=> (mem3 v_ctrl
  (union4 (add3 E_Hors_delai empty4) (add3 E_Incident empty4)))
  (= v_msg_0 v_msg))) (= v_courant_1 E_Restitution_carte))
  (= v_courant_1 E_Confiscation_carte)))))

(declare-fun f132 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f132_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f132 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1
  v_somme_0 v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1
  v_retraits v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1
  v_panne_dab v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1
  v_interdits v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (= v_etat_dab_1 E_En_service) (not (= v_courant_1 E_Veille)))
  (not (= v_courant_1 E_Traitement_carte)))
  (not (= v_courant_1 E_Traitement_code)))
  (not (= v_courant_1 E_Traitement_somme)))
  (not (= v_courant_1 E_Distribution_billets)))
  (not (= v_courant_1 E_Restitution_carte)))
  (=> (and (= v_precedent_1 E_Traitement_carte) (= v_resultat_1 E_Interdite))
  (= v_n_msg E_Carte_interdite)))
  (=> (= v_precedent_1 E_Restitution_carte)
  (and (=> (= v_resultat_1 E_Hors_delai) (= v_n_msg E_Carte_confisquee))
  (=> (= v_resultat_1 E_Incident) (= v_n_msg E_Carte_confisquee)))))
  (=> (and (= v_precedent_1 E_Traitement_code) (= v_resultat_1 E_Invalide))
  (= v_n_msg E_Code_invalide))) (mem3 v_ctrl
  (union4 (add3 E_Valide empty4) (add3 E_Invalide empty4)))) (mem3 v_rslt_1
  (union4 (add3 E_Valide empty4) (add3 E_Invalide empty4)))))))

(declare-fun f133 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f133_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f133 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1
  v_somme_0 v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1
  v_retraits v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1
  v_panne_dab v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1
  v_interdits v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (= v_etat_dab_1 E_En_service) (not (= v_courant_1 E_Veille)))
  (not (= v_courant_1 E_Traitement_carte)))
  (not (= v_courant_1 E_Traitement_code)))
  (not (= v_courant_1 E_Traitement_somme)))
  (not (= v_courant_1 E_Distribution_billets)))
  (not (= v_courant_1 E_Restitution_carte)))
  (=> (and (= v_precedent_1 E_Traitement_carte) (= v_resultat_1 E_Interdite))
  (= v_n_msg E_Carte_interdite)))
  (=> (= v_precedent_1 E_Restitution_carte)
  (and (=> (= v_resultat_1 E_Hors_delai) (= v_n_msg E_Carte_confisquee))
  (=> (= v_resultat_1 E_Incident) (= v_n_msg E_Carte_confisquee)))))
  (=> (and (= v_precedent_1 E_Traitement_code) (= v_resultat_1 E_Invalide))
  (= v_n_msg E_Code_invalide))) (mem3 v_ctrl
  (union4 (add3 E_Valide empty4) (add3 E_Invalide empty4)))) (mem3 v_rslt_1
  (union4 (add3 E_Valide empty4) (add3 E_Invalide empty4)))) (mem
  enum_ETAT_AUTOMATE1 (t2tb9 v_courant_1)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Distribution_billets)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Restitution_carte)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Veille) (empty enum_ETAT_AUTOMATE1))))))))

(declare-fun f135 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f135_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f135 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1
  v_somme_0 v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1
  v_retraits v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1
  v_panne_dab v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1
  v_interdits v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (= v_etat_dab_1 E_En_service)
  (=> (= v_courant_1 E_Veille)
  (and
  (and (=> (= v_rslt_1 E_Valide) (= v_etat E_Traitement_carte))
  (=> (= v_rslt_1 E_Hors_delai) (= v_etat E_Veille)))
  (=> (= v_rslt_1 E_Incident) (= v_etat E_Veille)))))
  (=> (= v_courant_1 E_Traitement_carte)
  (and
  (and
  (and
  (and
  (and
  (and (=> (= v_rslt_1 E_Valide) (= v_etat E_Traitement_code))
  (=> (= v_rslt_1 E_Invalide) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Illisible) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Interdite) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt_1 E_Perimee) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Incident) (= v_etat E_Veille)))
  (=> (= v_rslt_1 E_Epuisee) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant_1 E_Traitement_code)
  (and
  (and
  (and
  (and
  (and (=> (= v_rslt_1 E_Valide) (= v_etat E_Traitement_somme))
  (=> (= v_rslt_1 E_Invalide) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt_1 E_Nouvel) (= v_etat E_Traitement_code)))
  (=> (= v_rslt_1 E_Dernier) (= v_etat E_Traitement_code)))
  (=> (= v_rslt_1 E_Hors_delai) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Incident) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant_1 E_Traitement_somme)
  (and
  (and
  (and (=> (= v_rslt_1 E_Valide) (= v_etat E_Distribution_billets))
  (=> (= v_rslt_1 E_Invalide) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Hors_delai) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Incident) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant_1 E_Distribution_billets) (= v_etat E_Restitution_carte)))
  (=> (= v_courant_1 E_Restitution_carte)
  (and
  (and (=> (= v_rslt_1 E_Valide) (= v_etat E_Veille))
  (=> (= v_rslt_1 E_Hors_delai) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt_1 E_Incident) (= v_etat E_Confiscation_carte)))))
  (=> (= v_courant_1 E_Confiscation_carte) (= v_etat E_Veille)))
  (not (= v_courant_1 E_Restitution_carte)))
  (not (= v_courant_1 E_Distribution_billets)))
  (not (= v_courant_1 E_Traitement_somme)))
  (not (= v_courant_1 E_Traitement_code)))
  (not (= v_courant_1 E_Traitement_carte))) (mem3 v_rslt_1
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))) (= v_courant_1 E_Veille))
  (=> (and (= v_etat E_Traitement_code) (= v_etat_dab_1 E_En_service))
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_courant_1)
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_courant_1 E_Traitement_code) (mem3 v_rslt_1
  (union4 (add3 E_Nouvel empty4) (add3 E_Dernier empty4)))))
  (=> (= v_courant_1 E_Traitement_carte) (= v_rslt_1 E_Valide)))))
  (=> (and (= v_etat E_Restitution_carte) (= v_etat_dab_1 E_En_service))
  (and
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_courant_1)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_somme)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Distribution_billets)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_courant_1 E_Traitement_carte) (mem3 v_rslt_1
  (union4
  (union4 (union4 (add3 E_Perimee empty4) (add3 E_Epuisee empty4))
  (add3 E_Illisible empty4)) (add3 E_Invalide empty4)))))
  (=> (= v_courant_1 E_Traitement_code) (mem3 v_rslt_1
  (union4 (add3 E_Hors_delai empty4) (add3 E_Incident empty4)))))
  (=> (= v_courant_1 E_Traitement_somme) (mem3 v_rslt_1
  (union4 (union4 (add3 E_Invalide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))
  (=> (= v_courant_1 E_Distribution_billets) (mem3 v_rslt_1
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))))
  (=> (and (= v_etat E_Confiscation_carte) (= v_etat_dab_1 E_En_service))
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_courant_1)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Restitution_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_courant_1 E_Traitement_carte) (= v_rslt_1 E_Interdite)))
  (=> (= v_courant_1 E_Traitement_code) (= v_rslt_1 E_Invalide)))
  (=> (= v_courant_1 E_Restitution_carte) (mem3 v_rslt_1
  (union4 (add3 E_Incident empty4) (add3 E_Hors_delai empty4))))))))))

(declare-fun f137 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f137_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f137 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1
  v_somme_0 v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1
  v_retraits v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1
  v_panne_dab v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1
  v_interdits v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (or
  (or
  (exists ((v_crt1 Int) (v_som1 Int) (v_rjt1 Int))
  (and
  (and
  (and
  (and (and (mem1 v_crt1 v_clients_1) (mem1 v_som1 (mk 100 900))) (mem1
  v_rjt1 (union1 (add1 0 empty1) (add1 v_som1 empty1))))
  (<= v_som1 v_caisse_1))
  (<= v_som1 (tb2t1 (apply int int (t2tb5 v_comptes_1) (t2tb1 v_crt1)))))
  (and
  (and
  (and
  (and (= v_caisse_1 (- v_caisse_1 v_som1))
  (= v_corbeille_1 (+ v_corbeille_1 v_rjt1)))
  (= v_retraits_1 (- (+ v_retraits_1 v_som1) v_rjt1))) (infix_eqeq
  (tuple21 int int) (t2tb5 v_comptes_1)
  (infix_lspl int int (t2tb5 v_comptes_1)
  (add (tuple21 int int)
  (Tuple2 int int (t2tb1 v_crt1)
  (t2tb1
  (- (tb2t1 (apply int int (t2tb5 v_comptes_1) (t2tb1 v_crt1))) v_som1)))
  (t2tb5 empty2)))))
  (exists ((v_etat_aut_01 enum_ETAT_AUTOMATE)) (= v_etat v_etat_aut_01)))))
  (and
  (exists ((v_carte_01 Int))
  (and (mem1 v_carte_01 v_CARTE) (= v_carte_1 v_carte_01)))
  (exists ((v_etat_aut_01 enum_ETAT_AUTOMATE)) (= v_etat v_etat_aut_01))))
  (exists ((v_etat_aut_01 enum_ETAT_AUTOMATE)) (= v_etat v_etat_aut_01))))))

(declare-fun f138 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f138_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f138 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1
  v_somme_0 v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1
  v_retraits v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1
  v_panne_dab v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1
  v_interdits v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (= v_etat_dab_1 E_En_service)
  (=> (= v_courant_1 E_Veille)
  (and
  (and (=> (= v_rslt_1 E_Valide) (= v_etat E_Traitement_carte))
  (=> (= v_rslt_1 E_Hors_delai) (= v_etat E_Veille)))
  (=> (= v_rslt_1 E_Incident) (= v_etat E_Veille)))))
  (=> (= v_courant_1 E_Traitement_carte)
  (and
  (and
  (and
  (and
  (and
  (and (=> (= v_rslt_1 E_Valide) (= v_etat E_Traitement_code))
  (=> (= v_rslt_1 E_Invalide) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Illisible) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Interdite) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt_1 E_Perimee) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Incident) (= v_etat E_Veille)))
  (=> (= v_rslt_1 E_Epuisee) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant_1 E_Traitement_code)
  (and
  (and
  (and
  (and
  (and (=> (= v_rslt_1 E_Valide) (= v_etat E_Traitement_somme))
  (=> (= v_rslt_1 E_Invalide) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt_1 E_Nouvel) (= v_etat E_Traitement_code)))
  (=> (= v_rslt_1 E_Dernier) (= v_etat E_Traitement_code)))
  (=> (= v_rslt_1 E_Hors_delai) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Incident) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant_1 E_Traitement_somme)
  (and
  (and
  (and (=> (= v_rslt_1 E_Valide) (= v_etat E_Distribution_billets))
  (=> (= v_rslt_1 E_Invalide) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Hors_delai) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Incident) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant_1 E_Distribution_billets) (= v_etat E_Restitution_carte)))
  (=> (= v_courant_1 E_Restitution_carte)
  (and
  (and (=> (= v_rslt_1 E_Valide) (= v_etat E_Veille))
  (=> (= v_rslt_1 E_Hors_delai) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt_1 E_Incident) (= v_etat E_Confiscation_carte)))))
  (=> (= v_courant_1 E_Confiscation_carte) (= v_etat E_Veille)))
  (not (= v_courant_1 E_Restitution_carte)))
  (not (= v_courant_1 E_Distribution_billets)))
  (not (= v_courant_1 E_Traitement_somme)))
  (not (= v_courant_1 E_Traitement_code)))
  (not (= v_courant_1 E_Traitement_carte))) (mem3 v_rslt_1
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))) (= v_courant_1 E_Veille))
  (=> (and (= v_etat E_Traitement_code) (= v_etat_dab_1 E_En_service))
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_courant_1)
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_courant_1 E_Traitement_code) (mem3 v_rslt_1
  (union4 (add3 E_Nouvel empty4) (add3 E_Dernier empty4)))))
  (=> (= v_courant_1 E_Traitement_carte) (= v_rslt_1 E_Valide)))))
  (=> (and (= v_etat E_Restitution_carte) (= v_etat_dab_1 E_En_service))
  (and
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_courant_1)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_somme)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Distribution_billets)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_courant_1 E_Traitement_carte) (mem3 v_rslt_1
  (union4
  (union4 (union4 (add3 E_Perimee empty4) (add3 E_Epuisee empty4))
  (add3 E_Illisible empty4)) (add3 E_Invalide empty4)))))
  (=> (= v_courant_1 E_Traitement_code) (mem3 v_rslt_1
  (union4 (add3 E_Hors_delai empty4) (add3 E_Incident empty4)))))
  (=> (= v_courant_1 E_Traitement_somme) (mem3 v_rslt_1
  (union4 (union4 (add3 E_Invalide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))
  (=> (= v_courant_1 E_Distribution_billets) (mem3 v_rslt_1
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))))
  (=> (and (= v_etat E_Confiscation_carte) (= v_etat_dab_1 E_En_service))
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_courant_1)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Restitution_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_courant_1 E_Traitement_carte) (= v_rslt_1 E_Interdite)))
  (=> (= v_courant_1 E_Traitement_code) (= v_rslt_1 E_Invalide)))
  (=> (= v_courant_1 E_Restitution_carte) (mem3 v_rslt_1
  (union4 (add3 E_Incident empty4) (add3 E_Hors_delai empty4)))))))
  (= v_etat E_Traitement_code)))))

(declare-fun f139 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f139_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f139 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1
  v_somme_0 v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1
  v_retraits v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1
  v_panne_dab v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1
  v_interdits v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (= v_etat_dab_1 E_En_service)
  (=> (= v_courant_1 E_Veille)
  (and
  (and (=> (= v_rslt_1 E_Valide) (= v_etat E_Traitement_carte))
  (=> (= v_rslt_1 E_Hors_delai) (= v_etat E_Veille)))
  (=> (= v_rslt_1 E_Incident) (= v_etat E_Veille)))))
  (=> (= v_courant_1 E_Traitement_carte)
  (and
  (and
  (and
  (and
  (and
  (and (=> (= v_rslt_1 E_Valide) (= v_etat E_Traitement_code))
  (=> (= v_rslt_1 E_Invalide) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Illisible) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Interdite) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt_1 E_Perimee) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Incident) (= v_etat E_Veille)))
  (=> (= v_rslt_1 E_Epuisee) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant_1 E_Traitement_code)
  (and
  (and
  (and
  (and
  (and (=> (= v_rslt_1 E_Valide) (= v_etat E_Traitement_somme))
  (=> (= v_rslt_1 E_Invalide) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt_1 E_Nouvel) (= v_etat E_Traitement_code)))
  (=> (= v_rslt_1 E_Dernier) (= v_etat E_Traitement_code)))
  (=> (= v_rslt_1 E_Hors_delai) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Incident) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant_1 E_Traitement_somme)
  (and
  (and
  (and (=> (= v_rslt_1 E_Valide) (= v_etat E_Distribution_billets))
  (=> (= v_rslt_1 E_Invalide) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Hors_delai) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Incident) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant_1 E_Distribution_billets) (= v_etat E_Restitution_carte)))
  (=> (= v_courant_1 E_Restitution_carte)
  (and
  (and (=> (= v_rslt_1 E_Valide) (= v_etat E_Veille))
  (=> (= v_rslt_1 E_Hors_delai) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt_1 E_Incident) (= v_etat E_Confiscation_carte)))))
  (=> (= v_courant_1 E_Confiscation_carte) (= v_etat E_Veille)))
  (not (= v_courant_1 E_Restitution_carte)))
  (not (= v_courant_1 E_Distribution_billets)))
  (not (= v_courant_1 E_Traitement_somme)))
  (not (= v_courant_1 E_Traitement_code)))
  (not (= v_courant_1 E_Traitement_carte))) (mem3 v_rslt_1
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))) (= v_courant_1 E_Veille))
  (=> (and (= v_etat E_Traitement_code) (= v_etat_dab_1 E_En_service))
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_courant_1)
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_courant_1 E_Traitement_code) (mem3 v_rslt_1
  (union4 (add3 E_Nouvel empty4) (add3 E_Dernier empty4)))))
  (=> (= v_courant_1 E_Traitement_carte) (= v_rslt_1 E_Valide)))))
  (=> (and (= v_etat E_Restitution_carte) (= v_etat_dab_1 E_En_service))
  (and
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_courant_1)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_somme)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Distribution_billets)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_courant_1 E_Traitement_carte) (mem3 v_rslt_1
  (union4
  (union4 (union4 (add3 E_Perimee empty4) (add3 E_Epuisee empty4))
  (add3 E_Illisible empty4)) (add3 E_Invalide empty4)))))
  (=> (= v_courant_1 E_Traitement_code) (mem3 v_rslt_1
  (union4 (add3 E_Hors_delai empty4) (add3 E_Incident empty4)))))
  (=> (= v_courant_1 E_Traitement_somme) (mem3 v_rslt_1
  (union4 (union4 (add3 E_Invalide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))
  (=> (= v_courant_1 E_Distribution_billets) (mem3 v_rslt_1
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))))
  (=> (and (= v_etat E_Confiscation_carte) (= v_etat_dab_1 E_En_service))
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_courant_1)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Restitution_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_courant_1 E_Traitement_carte) (= v_rslt_1 E_Interdite)))
  (=> (= v_courant_1 E_Traitement_code) (= v_rslt_1 E_Invalide)))
  (=> (= v_courant_1 E_Restitution_carte) (mem3 v_rslt_1
  (union4 (add3 E_Incident empty4) (add3 E_Hors_delai empty4)))))))
  (= v_etat E_Traitement_somme)))))

(declare-fun f140 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f140_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f140 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1
  v_somme_0 v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1
  v_retraits v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1
  v_panne_dab v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1
  v_interdits v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (= v_etat_dab_1 E_En_service)
  (=> (= v_courant_1 E_Veille)
  (and
  (and (=> (= v_rslt_1 E_Valide) (= v_etat E_Traitement_carte))
  (=> (= v_rslt_1 E_Hors_delai) (= v_etat E_Veille)))
  (=> (= v_rslt_1 E_Incident) (= v_etat E_Veille)))))
  (=> (= v_courant_1 E_Traitement_carte)
  (and
  (and
  (and
  (and
  (and
  (and (=> (= v_rslt_1 E_Valide) (= v_etat E_Traitement_code))
  (=> (= v_rslt_1 E_Invalide) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Illisible) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Interdite) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt_1 E_Perimee) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Incident) (= v_etat E_Veille)))
  (=> (= v_rslt_1 E_Epuisee) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant_1 E_Traitement_code)
  (and
  (and
  (and
  (and
  (and (=> (= v_rslt_1 E_Valide) (= v_etat E_Traitement_somme))
  (=> (= v_rslt_1 E_Invalide) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt_1 E_Nouvel) (= v_etat E_Traitement_code)))
  (=> (= v_rslt_1 E_Dernier) (= v_etat E_Traitement_code)))
  (=> (= v_rslt_1 E_Hors_delai) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Incident) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant_1 E_Traitement_somme)
  (and
  (and
  (and (=> (= v_rslt_1 E_Valide) (= v_etat E_Distribution_billets))
  (=> (= v_rslt_1 E_Invalide) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Hors_delai) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Incident) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant_1 E_Distribution_billets) (= v_etat E_Restitution_carte)))
  (=> (= v_courant_1 E_Restitution_carte)
  (and
  (and (=> (= v_rslt_1 E_Valide) (= v_etat E_Veille))
  (=> (= v_rslt_1 E_Hors_delai) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt_1 E_Incident) (= v_etat E_Confiscation_carte)))))
  (=> (= v_courant_1 E_Confiscation_carte) (= v_etat E_Veille)))
  (not (= v_courant_1 E_Restitution_carte)))
  (not (= v_courant_1 E_Distribution_billets)))
  (not (= v_courant_1 E_Traitement_somme)))
  (not (= v_courant_1 E_Traitement_code)))
  (not (= v_courant_1 E_Traitement_carte))) (mem3 v_rslt_1
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))) (= v_courant_1 E_Veille))
  (=> (and (= v_etat E_Traitement_code) (= v_etat_dab_1 E_En_service))
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_courant_1)
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_courant_1 E_Traitement_code) (mem3 v_rslt_1
  (union4 (add3 E_Nouvel empty4) (add3 E_Dernier empty4)))))
  (=> (= v_courant_1 E_Traitement_carte) (= v_rslt_1 E_Valide)))))
  (=> (and (= v_etat E_Restitution_carte) (= v_etat_dab_1 E_En_service))
  (and
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_courant_1)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_somme)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Distribution_billets)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_courant_1 E_Traitement_carte) (mem3 v_rslt_1
  (union4
  (union4 (union4 (add3 E_Perimee empty4) (add3 E_Epuisee empty4))
  (add3 E_Illisible empty4)) (add3 E_Invalide empty4)))))
  (=> (= v_courant_1 E_Traitement_code) (mem3 v_rslt_1
  (union4 (add3 E_Hors_delai empty4) (add3 E_Incident empty4)))))
  (=> (= v_courant_1 E_Traitement_somme) (mem3 v_rslt_1
  (union4 (union4 (add3 E_Invalide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))
  (=> (= v_courant_1 E_Distribution_billets) (mem3 v_rslt_1
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))))
  (=> (and (= v_etat E_Confiscation_carte) (= v_etat_dab_1 E_En_service))
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_courant_1)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Restitution_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_courant_1 E_Traitement_carte) (= v_rslt_1 E_Interdite)))
  (=> (= v_courant_1 E_Traitement_code) (= v_rslt_1 E_Invalide)))
  (=> (= v_courant_1 E_Restitution_carte) (mem3 v_rslt_1
  (union4 (add3 E_Incident empty4) (add3 E_Hors_delai empty4)))))))
  (= v_etat E_Distribution_billets)))))

(declare-fun f141 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f141_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f141 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1
  v_somme_0 v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1
  v_retraits v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1
  v_panne_dab v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1
  v_interdits v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (= v_etat_dab_1 E_En_service)
  (=> (= v_courant_1 E_Veille)
  (and
  (and (=> (= v_rslt_1 E_Valide) (= v_etat E_Traitement_carte))
  (=> (= v_rslt_1 E_Hors_delai) (= v_etat E_Veille)))
  (=> (= v_rslt_1 E_Incident) (= v_etat E_Veille)))))
  (=> (= v_courant_1 E_Traitement_carte)
  (and
  (and
  (and
  (and
  (and
  (and (=> (= v_rslt_1 E_Valide) (= v_etat E_Traitement_code))
  (=> (= v_rslt_1 E_Invalide) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Illisible) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Interdite) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt_1 E_Perimee) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Incident) (= v_etat E_Veille)))
  (=> (= v_rslt_1 E_Epuisee) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant_1 E_Traitement_code)
  (and
  (and
  (and
  (and
  (and (=> (= v_rslt_1 E_Valide) (= v_etat E_Traitement_somme))
  (=> (= v_rslt_1 E_Invalide) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt_1 E_Nouvel) (= v_etat E_Traitement_code)))
  (=> (= v_rslt_1 E_Dernier) (= v_etat E_Traitement_code)))
  (=> (= v_rslt_1 E_Hors_delai) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Incident) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant_1 E_Traitement_somme)
  (and
  (and
  (and (=> (= v_rslt_1 E_Valide) (= v_etat E_Distribution_billets))
  (=> (= v_rslt_1 E_Invalide) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Hors_delai) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Incident) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant_1 E_Distribution_billets) (= v_etat E_Restitution_carte)))
  (=> (= v_courant_1 E_Restitution_carte)
  (and
  (and (=> (= v_rslt_1 E_Valide) (= v_etat E_Veille))
  (=> (= v_rslt_1 E_Hors_delai) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt_1 E_Incident) (= v_etat E_Confiscation_carte)))))
  (=> (= v_courant_1 E_Confiscation_carte) (= v_etat E_Veille)))
  (not (= v_courant_1 E_Restitution_carte)))
  (not (= v_courant_1 E_Distribution_billets)))
  (not (= v_courant_1 E_Traitement_somme)))
  (not (= v_courant_1 E_Traitement_code)))
  (not (= v_courant_1 E_Traitement_carte))) (mem3 v_rslt_1
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))) (= v_courant_1 E_Veille))
  (=> (and (= v_etat E_Traitement_code) (= v_etat_dab_1 E_En_service))
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_courant_1)
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_courant_1 E_Traitement_code) (mem3 v_rslt_1
  (union4 (add3 E_Nouvel empty4) (add3 E_Dernier empty4)))))
  (=> (= v_courant_1 E_Traitement_carte) (= v_rslt_1 E_Valide)))))
  (=> (and (= v_etat E_Restitution_carte) (= v_etat_dab_1 E_En_service))
  (and
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_courant_1)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_somme)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Distribution_billets)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_courant_1 E_Traitement_carte) (mem3 v_rslt_1
  (union4
  (union4 (union4 (add3 E_Perimee empty4) (add3 E_Epuisee empty4))
  (add3 E_Illisible empty4)) (add3 E_Invalide empty4)))))
  (=> (= v_courant_1 E_Traitement_code) (mem3 v_rslt_1
  (union4 (add3 E_Hors_delai empty4) (add3 E_Incident empty4)))))
  (=> (= v_courant_1 E_Traitement_somme) (mem3 v_rslt_1
  (union4 (union4 (add3 E_Invalide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))
  (=> (= v_courant_1 E_Distribution_billets) (mem3 v_rslt_1
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))))
  (=> (and (= v_etat E_Confiscation_carte) (= v_etat_dab_1 E_En_service))
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_courant_1)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Restitution_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_courant_1 E_Traitement_carte) (= v_rslt_1 E_Interdite)))
  (=> (= v_courant_1 E_Traitement_code) (= v_rslt_1 E_Invalide)))
  (=> (= v_courant_1 E_Restitution_carte) (mem3 v_rslt_1
  (union4 (add3 E_Incident empty4) (add3 E_Hors_delai empty4)))))))
  (= v_etat E_Veille)))))

(declare-fun f142 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f142_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f142 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1
  v_somme_0 v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1
  v_retraits v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1
  v_panne_dab v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1
  v_interdits v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (= v_etat_dab_1 E_En_service)
  (=> (= v_courant_1 E_Veille)
  (and
  (and (=> (= v_rslt_1 E_Valide) (= v_etat E_Traitement_carte))
  (=> (= v_rslt_1 E_Hors_delai) (= v_etat E_Veille)))
  (=> (= v_rslt_1 E_Incident) (= v_etat E_Veille)))))
  (=> (= v_courant_1 E_Traitement_carte)
  (and
  (and
  (and
  (and
  (and
  (and (=> (= v_rslt_1 E_Valide) (= v_etat E_Traitement_code))
  (=> (= v_rslt_1 E_Invalide) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Illisible) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Interdite) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt_1 E_Perimee) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Incident) (= v_etat E_Veille)))
  (=> (= v_rslt_1 E_Epuisee) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant_1 E_Traitement_code)
  (and
  (and
  (and
  (and
  (and (=> (= v_rslt_1 E_Valide) (= v_etat E_Traitement_somme))
  (=> (= v_rslt_1 E_Invalide) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt_1 E_Nouvel) (= v_etat E_Traitement_code)))
  (=> (= v_rslt_1 E_Dernier) (= v_etat E_Traitement_code)))
  (=> (= v_rslt_1 E_Hors_delai) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Incident) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant_1 E_Traitement_somme)
  (and
  (and
  (and (=> (= v_rslt_1 E_Valide) (= v_etat E_Distribution_billets))
  (=> (= v_rslt_1 E_Invalide) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Hors_delai) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Incident) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant_1 E_Distribution_billets) (= v_etat E_Restitution_carte)))
  (=> (= v_courant_1 E_Restitution_carte)
  (and
  (and (=> (= v_rslt_1 E_Valide) (= v_etat E_Veille))
  (=> (= v_rslt_1 E_Hors_delai) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt_1 E_Incident) (= v_etat E_Confiscation_carte)))))
  (=> (= v_courant_1 E_Confiscation_carte) (= v_etat E_Veille)))
  (not (= v_courant_1 E_Restitution_carte)))
  (not (= v_courant_1 E_Distribution_billets)))
  (not (= v_courant_1 E_Traitement_somme)))
  (not (= v_courant_1 E_Traitement_code)))
  (not (= v_courant_1 E_Traitement_carte))) (mem3 v_rslt_1
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))) (= v_courant_1 E_Veille))
  (=> (and (= v_etat E_Traitement_code) (= v_etat_dab_1 E_En_service))
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_courant_1)
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_courant_1 E_Traitement_code) (mem3 v_rslt_1
  (union4 (add3 E_Nouvel empty4) (add3 E_Dernier empty4)))))
  (=> (= v_courant_1 E_Traitement_carte) (= v_rslt_1 E_Valide)))))
  (=> (and (= v_etat E_Restitution_carte) (= v_etat_dab_1 E_En_service))
  (and
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_courant_1)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_somme)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Distribution_billets)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_courant_1 E_Traitement_carte) (mem3 v_rslt_1
  (union4
  (union4 (union4 (add3 E_Perimee empty4) (add3 E_Epuisee empty4))
  (add3 E_Illisible empty4)) (add3 E_Invalide empty4)))))
  (=> (= v_courant_1 E_Traitement_code) (mem3 v_rslt_1
  (union4 (add3 E_Hors_delai empty4) (add3 E_Incident empty4)))))
  (=> (= v_courant_1 E_Traitement_somme) (mem3 v_rslt_1
  (union4 (union4 (add3 E_Invalide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))
  (=> (= v_courant_1 E_Distribution_billets) (mem3 v_rslt_1
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))))
  (=> (and (= v_etat E_Confiscation_carte) (= v_etat_dab_1 E_En_service))
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_courant_1)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Restitution_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_courant_1 E_Traitement_carte) (= v_rslt_1 E_Interdite)))
  (=> (= v_courant_1 E_Traitement_code) (= v_rslt_1 E_Invalide)))
  (=> (= v_courant_1 E_Restitution_carte) (mem3 v_rslt_1
  (union4 (add3 E_Incident empty4) (add3 E_Hors_delai empty4)))))))
  (= v_etat E_Traitement_carte)))))

(declare-fun f143 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f143_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f143 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1
  v_somme_0 v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1
  v_retraits v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1
  v_panne_dab v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1
  v_interdits v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (= v_etat_dab_1 E_En_service)
  (=> (= v_courant_1 E_Veille)
  (and
  (and (=> (= v_rslt_1 E_Valide) (= v_etat E_Traitement_carte))
  (=> (= v_rslt_1 E_Hors_delai) (= v_etat E_Veille)))
  (=> (= v_rslt_1 E_Incident) (= v_etat E_Veille)))))
  (=> (= v_courant_1 E_Traitement_carte)
  (and
  (and
  (and
  (and
  (and
  (and (=> (= v_rslt_1 E_Valide) (= v_etat E_Traitement_code))
  (=> (= v_rslt_1 E_Invalide) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Illisible) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Interdite) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt_1 E_Perimee) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Incident) (= v_etat E_Veille)))
  (=> (= v_rslt_1 E_Epuisee) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant_1 E_Traitement_code)
  (and
  (and
  (and
  (and
  (and (=> (= v_rslt_1 E_Valide) (= v_etat E_Traitement_somme))
  (=> (= v_rslt_1 E_Invalide) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt_1 E_Nouvel) (= v_etat E_Traitement_code)))
  (=> (= v_rslt_1 E_Dernier) (= v_etat E_Traitement_code)))
  (=> (= v_rslt_1 E_Hors_delai) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Incident) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant_1 E_Traitement_somme)
  (and
  (and
  (and (=> (= v_rslt_1 E_Valide) (= v_etat E_Distribution_billets))
  (=> (= v_rslt_1 E_Invalide) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Hors_delai) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Incident) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant_1 E_Distribution_billets) (= v_etat E_Restitution_carte)))
  (=> (= v_courant_1 E_Restitution_carte)
  (and
  (and (=> (= v_rslt_1 E_Valide) (= v_etat E_Veille))
  (=> (= v_rslt_1 E_Hors_delai) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt_1 E_Incident) (= v_etat E_Confiscation_carte)))))
  (=> (= v_courant_1 E_Confiscation_carte) (= v_etat E_Veille)))
  (not (= v_courant_1 E_Restitution_carte)))
  (not (= v_courant_1 E_Distribution_billets)))
  (not (= v_courant_1 E_Traitement_somme)))
  (not (= v_courant_1 E_Traitement_code)))
  (not (= v_courant_1 E_Traitement_carte))) (mem3 v_rslt_1
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))) (= v_courant_1 E_Veille))
  (=> (and (= v_etat E_Traitement_code) (= v_etat_dab_1 E_En_service))
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_courant_1)
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_courant_1 E_Traitement_code) (mem3 v_rslt_1
  (union4 (add3 E_Nouvel empty4) (add3 E_Dernier empty4)))))
  (=> (= v_courant_1 E_Traitement_carte) (= v_rslt_1 E_Valide)))))
  (=> (and (= v_etat E_Restitution_carte) (= v_etat_dab_1 E_En_service))
  (and
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_courant_1)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_somme)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Distribution_billets)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_courant_1 E_Traitement_carte) (mem3 v_rslt_1
  (union4
  (union4 (union4 (add3 E_Perimee empty4) (add3 E_Epuisee empty4))
  (add3 E_Illisible empty4)) (add3 E_Invalide empty4)))))
  (=> (= v_courant_1 E_Traitement_code) (mem3 v_rslt_1
  (union4 (add3 E_Hors_delai empty4) (add3 E_Incident empty4)))))
  (=> (= v_courant_1 E_Traitement_somme) (mem3 v_rslt_1
  (union4 (union4 (add3 E_Invalide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))
  (=> (= v_courant_1 E_Distribution_billets) (mem3 v_rslt_1
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))))
  (=> (and (= v_etat E_Confiscation_carte) (= v_etat_dab_1 E_En_service))
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_courant_1)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Restitution_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_courant_1 E_Traitement_carte) (= v_rslt_1 E_Interdite)))
  (=> (= v_courant_1 E_Traitement_code) (= v_rslt_1 E_Invalide)))
  (=> (= v_courant_1 E_Restitution_carte) (mem3 v_rslt_1
  (union4 (add3 E_Incident empty4) (add3 E_Hors_delai empty4)))))))
  (= v_etat E_Traitement_code)) (mem3 v_rslt_1
  (union4 (add3 E_Nouvel empty4) (add3 E_Dernier empty4)))))))

(declare-fun f144 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f144_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f144 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1
  v_somme_0 v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1
  v_retraits v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1
  v_panne_dab v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1
  v_interdits v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (= v_etat_dab_1 E_En_service)
  (=> (= v_courant_1 E_Veille)
  (and
  (and (=> (= v_rslt_1 E_Valide) (= v_etat E_Traitement_carte))
  (=> (= v_rslt_1 E_Hors_delai) (= v_etat E_Veille)))
  (=> (= v_rslt_1 E_Incident) (= v_etat E_Veille)))))
  (=> (= v_courant_1 E_Traitement_carte)
  (and
  (and
  (and
  (and
  (and
  (and (=> (= v_rslt_1 E_Valide) (= v_etat E_Traitement_code))
  (=> (= v_rslt_1 E_Invalide) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Illisible) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Interdite) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt_1 E_Perimee) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Incident) (= v_etat E_Veille)))
  (=> (= v_rslt_1 E_Epuisee) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant_1 E_Traitement_code)
  (and
  (and
  (and
  (and
  (and (=> (= v_rslt_1 E_Valide) (= v_etat E_Traitement_somme))
  (=> (= v_rslt_1 E_Invalide) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt_1 E_Nouvel) (= v_etat E_Traitement_code)))
  (=> (= v_rslt_1 E_Dernier) (= v_etat E_Traitement_code)))
  (=> (= v_rslt_1 E_Hors_delai) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Incident) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant_1 E_Traitement_somme)
  (and
  (and
  (and (=> (= v_rslt_1 E_Valide) (= v_etat E_Distribution_billets))
  (=> (= v_rslt_1 E_Invalide) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Hors_delai) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Incident) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant_1 E_Distribution_billets) (= v_etat E_Restitution_carte)))
  (=> (= v_courant_1 E_Restitution_carte)
  (and
  (and (=> (= v_rslt_1 E_Valide) (= v_etat E_Veille))
  (=> (= v_rslt_1 E_Hors_delai) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt_1 E_Incident) (= v_etat E_Confiscation_carte)))))
  (=> (= v_courant_1 E_Confiscation_carte) (= v_etat E_Veille)))
  (not (= v_courant_1 E_Restitution_carte)))
  (not (= v_courant_1 E_Distribution_billets)))
  (not (= v_courant_1 E_Traitement_somme)))
  (not (= v_courant_1 E_Traitement_code)))
  (not (= v_courant_1 E_Traitement_carte))) (mem3 v_rslt_1
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))) (= v_courant_1 E_Veille))
  (=> (and (= v_etat E_Traitement_code) (= v_etat_dab_1 E_En_service))
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_courant_1)
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_courant_1 E_Traitement_code) (mem3 v_rslt_1
  (union4 (add3 E_Nouvel empty4) (add3 E_Dernier empty4)))))
  (=> (= v_courant_1 E_Traitement_carte) (= v_rslt_1 E_Valide)))))
  (=> (and (= v_etat E_Restitution_carte) (= v_etat_dab_1 E_En_service))
  (and
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_courant_1)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_somme)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Distribution_billets)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_courant_1 E_Traitement_carte) (mem3 v_rslt_1
  (union4
  (union4 (union4 (add3 E_Perimee empty4) (add3 E_Epuisee empty4))
  (add3 E_Illisible empty4)) (add3 E_Invalide empty4)))))
  (=> (= v_courant_1 E_Traitement_code) (mem3 v_rslt_1
  (union4 (add3 E_Hors_delai empty4) (add3 E_Incident empty4)))))
  (=> (= v_courant_1 E_Traitement_somme) (mem3 v_rslt_1
  (union4 (union4 (add3 E_Invalide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))
  (=> (= v_courant_1 E_Distribution_billets) (mem3 v_rslt_1
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))))
  (=> (and (= v_etat E_Confiscation_carte) (= v_etat_dab_1 E_En_service))
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_courant_1)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Restitution_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_courant_1 E_Traitement_carte) (= v_rslt_1 E_Interdite)))
  (=> (= v_courant_1 E_Traitement_code) (= v_rslt_1 E_Invalide)))
  (=> (= v_courant_1 E_Restitution_carte) (mem3 v_rslt_1
  (union4 (add3 E_Incident empty4) (add3 E_Hors_delai empty4)))))))
  (= v_etat E_Restitution_carte)))))

(declare-fun f145 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f145_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f145 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1
  v_somme_0 v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1
  v_retraits v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1
  v_panne_dab v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1
  v_interdits v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE) (not (= v_carte_1 v_K0)))))

(declare-fun f146 (Bool Bool Bool Int Int Int Int Int enum_STATUT Int Int Int
  Int enum_STATUT enum_STATUT enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool
  enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE enum_MESSAGE (set Int)
  (set Int) Bool Bool Bool (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE Bool Bool Bool Int
  Int Int Int Int Int Int enum_STATUT enum_STATUT Int Int enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE Int Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  Int Int Bool Bool Int Int Int (set (tuple2 Int Int)) (set Int) (set Int)
  (set Int) Int Int Int Int Int Int Bool Bool Int Int Int Int Int Int
  (set Int) (set Int)) Bool)

;; f146_def
  (assert
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f146 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1
  v_somme_0 v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1
  v_retraits v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1
  v_panne_dab v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1
  v_interdits v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (= v_etat_dab_1 E_En_service)
  (=> (= v_courant_1 E_Veille)
  (and
  (and (=> (= v_rslt_1 E_Valide) (= v_etat E_Traitement_carte))
  (=> (= v_rslt_1 E_Hors_delai) (= v_etat E_Veille)))
  (=> (= v_rslt_1 E_Incident) (= v_etat E_Veille)))))
  (=> (= v_courant_1 E_Traitement_carte)
  (and
  (and
  (and
  (and
  (and
  (and (=> (= v_rslt_1 E_Valide) (= v_etat E_Traitement_code))
  (=> (= v_rslt_1 E_Invalide) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Illisible) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Interdite) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt_1 E_Perimee) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Incident) (= v_etat E_Veille)))
  (=> (= v_rslt_1 E_Epuisee) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant_1 E_Traitement_code)
  (and
  (and
  (and
  (and
  (and (=> (= v_rslt_1 E_Valide) (= v_etat E_Traitement_somme))
  (=> (= v_rslt_1 E_Invalide) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt_1 E_Nouvel) (= v_etat E_Traitement_code)))
  (=> (= v_rslt_1 E_Dernier) (= v_etat E_Traitement_code)))
  (=> (= v_rslt_1 E_Hors_delai) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Incident) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant_1 E_Traitement_somme)
  (and
  (and
  (and (=> (= v_rslt_1 E_Valide) (= v_etat E_Distribution_billets))
  (=> (= v_rslt_1 E_Invalide) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Hors_delai) (= v_etat E_Restitution_carte)))
  (=> (= v_rslt_1 E_Incident) (= v_etat E_Restitution_carte)))))
  (=> (= v_courant_1 E_Distribution_billets) (= v_etat E_Restitution_carte)))
  (=> (= v_courant_1 E_Restitution_carte)
  (and
  (and (=> (= v_rslt_1 E_Valide) (= v_etat E_Veille))
  (=> (= v_rslt_1 E_Hors_delai) (= v_etat E_Confiscation_carte)))
  (=> (= v_rslt_1 E_Incident) (= v_etat E_Confiscation_carte)))))
  (=> (= v_courant_1 E_Confiscation_carte) (= v_etat E_Veille)))
  (not (= v_courant_1 E_Restitution_carte)))
  (not (= v_courant_1 E_Distribution_billets)))
  (not (= v_courant_1 E_Traitement_somme)))
  (not (= v_courant_1 E_Traitement_code)))
  (not (= v_courant_1 E_Traitement_carte))) (mem3 v_rslt_1
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))) (= v_courant_1 E_Veille))
  (=> (and (= v_etat E_Traitement_code) (= v_etat_dab_1 E_En_service))
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_courant_1)
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_courant_1 E_Traitement_code) (mem3 v_rslt_1
  (union4 (add3 E_Nouvel empty4) (add3 E_Dernier empty4)))))
  (=> (= v_courant_1 E_Traitement_carte) (= v_rslt_1 E_Valide)))))
  (=> (and (= v_etat E_Restitution_carte) (= v_etat_dab_1 E_En_service))
  (and
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_courant_1)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_somme)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Distribution_billets)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_courant_1 E_Traitement_carte) (mem3 v_rslt_1
  (union4
  (union4 (union4 (add3 E_Perimee empty4) (add3 E_Epuisee empty4))
  (add3 E_Illisible empty4)) (add3 E_Invalide empty4)))))
  (=> (= v_courant_1 E_Traitement_code) (mem3 v_rslt_1
  (union4 (add3 E_Hors_delai empty4) (add3 E_Incident empty4)))))
  (=> (= v_courant_1 E_Traitement_somme) (mem3 v_rslt_1
  (union4 (union4 (add3 E_Invalide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))
  (=> (= v_courant_1 E_Distribution_billets) (mem3 v_rslt_1
  (union4 (union4 (add3 E_Valide empty4) (add3 E_Hors_delai empty4))
  (add3 E_Incident empty4)))))))
  (=> (and (= v_etat E_Confiscation_carte) (= v_etat_dab_1 E_En_service))
  (and
  (and
  (and (mem enum_ETAT_AUTOMATE1 (t2tb9 v_courant_1)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_carte)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Restitution_carte)
  (empty enum_ETAT_AUTOMATE1))))
  (=> (= v_courant_1 E_Traitement_carte) (= v_rslt_1 E_Interdite)))
  (=> (= v_courant_1 E_Traitement_code) (= v_rslt_1 E_Invalide)))
  (=> (= v_courant_1 E_Restitution_carte) (mem3 v_rslt_1
  (union4 (add3 E_Incident empty4) (add3 E_Hors_delai empty4))))))) (mem
  enum_ETAT_AUTOMATE1 (t2tb9 v_etat)
  (union enum_ETAT_AUTOMATE1
  (union enum_ETAT_AUTOMATE1
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_code)
  (empty enum_ETAT_AUTOMATE1))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Traitement_somme)
  (empty enum_ETAT_AUTOMATE1)))
  (add enum_ETAT_AUTOMATE1 (t2tb9 E_Distribution_billets)
  (empty enum_ETAT_AUTOMATE1))))))))

(assert
;; traiter_operation_52
 ;; File "POwhy_bpo2why/DAB/Dab_imp_part2.why", line 24025, characters 7-27
  (not
  (forall ((v_tst_dab_1 Bool) (v_somme_demandee_1 Bool)
  (v_somme_demandee Bool) (v_somme_1 Int) (v_somme_0 Int) (v_somme Int)
  (v_som_0 Int) (v_som Int) (v_rslt_1 enum_STATUT) (v_rjt_0 Int) (v_rjt Int)
  (v_retraits_1 Int) (v_retraits Int) (v_resultat_1 enum_STATUT)
  (v_resultat enum_STATUT) (v_precedent_1 enum_ETAT_AUTOMATE)
  (v_precedent enum_ETAT_AUTOMATE) (v_panne_dab_1 Bool) (v_panne_dab Bool)
  (v_n_msg enum_MESSAGE) (v_msg_0 enum_MESSAGE) (v_msg enum_MESSAGE)
  (v_message_1 enum_MESSAGE) (v_message enum_MESSAGE)
  (v_interdits_1 (set Int)) (v_interdits (set Int)) (v_infos_lues_1 Bool)
  (v_infos_lues Bool) (v_infl Bool) (v_in (set Int))
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat enum_ETAT_AUTOMATE) (v_essaip Bool) (v_essai_possible_1 Bool)
  (v_essai_possible Bool) (v_date_validite_1 Int) (v_date_validite_0 Int)
  (v_date_validite Int) (v_date_mesure_1 Int) (v_date_mesure_0 Int)
  (v_date_mesure Int) (v_date Int) (v_ctrl enum_STATUT) (v_ctr enum_STATUT)
  (v_crt_0 Int) (v_crt Int) (v_courant_1 enum_ETAT_AUTOMATE)
  (v_courant enum_ETAT_AUTOMATE) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int Int)))
  (v_code_saisi_1 Int) (v_code_saisi Int) (v_code_demande_1 Bool)
  (v_code_demande Bool) (v_code_CB_1 Int) (v_code_CB_0 Int) (v_code_CB Int)
  (v_co (set (tuple2 Int Int))) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cl (set Int)) (v_cds_0 Int) (v_cds Int) (v_carte_2 Int) (v_carte_1 Int)
  (v_carte_0 Int) (v_carte Int) (v_caisse_vde_1 Bool) (v_caisse_vde Bool)
  (v_caisse_1 Int) (v_caisse Int) (v_avnc Int) (v_K0 Int) (v_HS Int)
  (v_D_min Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (=>
  (and (f2 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1
  v_somme_0 v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1
  v_retraits v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1
  v_panne_dab v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1
  v_interdits v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and (f3 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1
  v_somme_0 v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1
  v_retraits v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1
  v_panne_dab v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1
  v_interdits v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and (f25 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1
  v_somme_0 v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1
  v_retraits v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1
  v_panne_dab v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1
  v_interdits v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE)
  (and (f79 v_tst_dab_1 v_somme_demandee_1 v_somme_demandee v_somme_1
  v_somme_0 v_somme v_som_0 v_som v_rslt_1 v_rjt_0 v_rjt v_retraits_1
  v_retraits v_resultat_1 v_resultat v_precedent_1 v_precedent v_panne_dab_1
  v_panne_dab v_n_msg v_msg_0 v_msg v_message_1 v_message v_interdits_1
  v_interdits v_infos_lues_1 v_infos_lues v_infl v_in v_etat_dab_1 v_etat_dab
  v_etat_aut_0 v_etat_aut v_etat v_essaip v_essai_possible_1 v_essai_possible
  v_date_validite_1 v_date_validite_0 v_date_validite v_date_mesure_1
  v_date_mesure_0 v_date_mesure v_date v_ctrl v_ctr v_crt_0 v_crt v_courant_1
  v_courant v_corbeille_1 v_corbeille v_comptes_1 v_comptes v_code_saisi_1
  v_code_saisi v_code_demande_1 v_code_demande v_code_CB_1 v_code_CB_0
  v_code_CB v_co v_clients_1 v_clients v_cl v_cds_0 v_cds v_carte_2 v_carte_1
  v_carte_0 v_carte v_caisse_vde_1 v_caisse_vde v_caisse_1 v_caisse v_avnc
  v_K0 v_HS v_D_min v_DATE v_CARTE) (f116 v_tst_dab_1 v_somme_demandee_1
  v_somme_demandee v_somme_1 v_somme_0 v_somme v_som_0 v_som v_rslt_1 v_rjt_0
  v_rjt v_retraits_1 v_retraits v_resultat_1 v_resultat v_precedent_1
  v_precedent v_panne_dab_1 v_panne_dab v_n_msg v_msg_0 v_msg v_message_1
  v_message v_interdits_1 v_interdits v_infos_lues_1 v_infos_lues v_infl v_in
  v_etat_dab_1 v_etat_dab v_etat_aut_0 v_etat_aut v_etat v_essaip
  v_essai_possible_1 v_essai_possible v_date_validite_1 v_date_validite_0
  v_date_validite v_date_mesure_1 v_date_mesure_0 v_date_mesure v_date v_ctrl
  v_ctr v_crt_0 v_crt v_courant_1 v_courant v_corbeille_1 v_corbeille
  v_comptes_1 v_comptes v_code_saisi_1 v_code_saisi v_code_demande_1
  v_code_demande v_code_CB_1 v_code_CB_0 v_code_CB v_co v_clients_1 v_clients
  v_cl v_cds_0 v_cds v_carte_2 v_carte_1 v_carte_0 v_carte v_caisse_vde_1
  v_caisse_vde v_caisse_1 v_caisse v_avnc v_K0 v_HS v_D_min v_DATE v_CARTE)))))
  (mem3 v_ctr (union4 (add3 E_Valide empty4) (add3 E_Invalide empty4)))))))
(check-sat)
