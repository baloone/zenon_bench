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

(declare-sort enum_OBF__ii 0)

(declare-fun enum_OBF__ii1 () ty)

(declare-sort enum_OBF__aa 0)

(declare-fun enum_OBF__aa1 () ty)

(declare-sort tuple2 2)

(declare-fun tuple21 (ty ty) ty)

(declare-fun infix_eqeq (ty uni uni) Bool)

(declare-fun infix_eqeq1 ((set Int) (set Int)) Bool)

(declare-fun infix_eqeq2 ((set (tuple2 Int Int)) (set (tuple2 Int
  Int))) Bool)

(declare-fun infix_eqeq3 ((set enum_OBF__ii) (set enum_OBF__ii)) Bool)

(declare-fun infix_eqeq4 ((set (tuple2 (tuple2 Int Int) Int))
  (set (tuple2 (tuple2 Int Int) Int))) Bool)

(declare-fun infix_eqeq5 ((set (tuple2 (tuple2 (tuple2 Int Int) Int) Int))
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int))) Bool)

(declare-fun infix_eqeq6 ((set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int))) Bool)

(declare-fun t2tb2 ((set (tuple2 (tuple2 Int enum_OBF__aa) Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))) (sort
  (set1 (tuple21 (tuple21 int enum_OBF__aa1) int)) (t2tb2 x))))

(declare-fun tb2t2 (uni) (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (! (= (tb2t2 (t2tb2 i)) i) :pattern ((t2tb2 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb2 (tb2t2 j)) j) :pattern ((t2tb2 (tb2t2 j))) )))

(declare-fun t2tb7 ((tuple2 (tuple2 Int enum_OBF__aa) Int)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int))) (sort
  (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb7 x))))

(declare-fun tb2t7 (uni) (tuple2 (tuple2 Int enum_OBF__aa) Int))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (! (= (tb2t7 (t2tb7 i)) i) :pattern ((t2tb7 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb7 (tb2t7 j)) j) :pattern ((t2tb7 (tb2t7 j))) )))

;; infix ==_def
  (assert
  (forall ((s1 (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (s2 (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (= (infix_eqeq6 s1 s2)
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (= (mem (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb7 x) (t2tb2 s1))
  (mem (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb7 x) (t2tb2 s2)))))))

(declare-fun t2tb3 ((set (tuple2 (tuple2 (tuple2 Int Int) Int) Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))) (sort
  (set1 (tuple21 (tuple21 (tuple21 int int) int) int)) (t2tb3 x))))

(declare-fun tb2t3 (uni) (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int))))
  (! (= (tb2t3 (t2tb3 i)) i) :pattern ((t2tb3 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb3 (tb2t3 j)) j) :pattern ((t2tb3 (tb2t3 j))) )))

(declare-fun t2tb8 ((tuple2 (tuple2 (tuple2 Int Int) Int) Int)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Int Int) Int) Int))) (sort
  (tuple21 (tuple21 (tuple21 int int) int) int) (t2tb8 x))))

(declare-fun tb2t8 (uni) (tuple2 (tuple2 (tuple2 Int Int) Int) Int))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (! (= (tb2t8 (t2tb8 i)) i) :pattern ((t2tb8 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb8 (tb2t8 j)) j) :pattern ((t2tb8 (tb2t8 j))) )))

;; infix ==_def
  (assert
  (forall ((s1 (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (s2 (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int))))
  (= (infix_eqeq5 s1 s2)
  (forall ((x (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (= (mem (tuple21 (tuple21 (tuple21 int int) int) int) (t2tb8 x) (t2tb3 s1))
  (mem (tuple21 (tuple21 (tuple21 int int) int) int) (t2tb8 x) (t2tb3 s2)))))))

(declare-fun t2tb4 ((set (tuple2 (tuple2 Int Int) Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Int Int) Int)))) (sort
  (set1 (tuple21 (tuple21 int int) int)) (t2tb4 x))))

(declare-fun tb2t4 (uni) (set (tuple2 (tuple2 Int Int) Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Int Int) Int))))
  (! (= (tb2t4 (t2tb4 i)) i) :pattern ((t2tb4 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb4 (tb2t4 j)) j) :pattern ((t2tb4 (tb2t4 j))) )))

(declare-fun t2tb9 ((tuple2 (tuple2 Int Int) Int)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 Int Int) Int))) (sort
  (tuple21 (tuple21 int int) int) (t2tb9 x))))

(declare-fun tb2t9 (uni) (tuple2 (tuple2 Int Int) Int))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 Int Int) Int)))
  (! (= (tb2t9 (t2tb9 i)) i) :pattern ((t2tb9 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb9 (tb2t9 j)) j) :pattern ((t2tb9 (tb2t9 j))) )))

;; infix ==_def
  (assert
  (forall ((s1 (set (tuple2 (tuple2 Int Int) Int)))
  (s2 (set (tuple2 (tuple2 Int Int) Int))))
  (= (infix_eqeq4 s1 s2)
  (forall ((x (tuple2 (tuple2 Int Int) Int)))
  (= (mem (tuple21 (tuple21 int int) int) (t2tb9 x) (t2tb4 s1)) (mem
  (tuple21 (tuple21 int int) int) (t2tb9 x) (t2tb4 s2)))))))

(declare-fun t2tb5 ((set enum_OBF__ii)) uni)

;; t2tb_sort
  (assert
  (forall ((x (set enum_OBF__ii))) (sort (set1 enum_OBF__ii1) (t2tb5 x))))

(declare-fun tb2t5 (uni) (set enum_OBF__ii))

;; BridgeL
  (assert
  (forall ((i (set enum_OBF__ii)))
  (! (= (tb2t5 (t2tb5 i)) i) :pattern ((t2tb5 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 enum_OBF__ii1) j) (= (t2tb5 (tb2t5 j)) j)) :pattern (
  (t2tb5 (tb2t5 j))) )))

(declare-fun t2tb10 (enum_OBF__ii) uni)

;; t2tb_sort
  (assert (forall ((x enum_OBF__ii)) (sort enum_OBF__ii1 (t2tb10 x))))

(declare-fun tb2t10 (uni) enum_OBF__ii)

;; BridgeL
  (assert
  (forall ((i enum_OBF__ii))
  (! (= (tb2t10 (t2tb10 i)) i) :pattern ((t2tb10 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort enum_OBF__ii1 j) (= (t2tb10 (tb2t10 j)) j)) :pattern (
  (t2tb10 (tb2t10 j))) )))

;; infix ==_def
  (assert
  (forall ((s1 (set enum_OBF__ii)) (s2 (set enum_OBF__ii)))
  (= (infix_eqeq3 s1 s2)
  (forall ((x enum_OBF__ii))
  (= (mem enum_OBF__ii1 (t2tb10 x) (t2tb5 s1)) (mem enum_OBF__ii1 (t2tb10 x)
  (t2tb5 s2)))))))

(declare-fun t2tb6 ((set (tuple2 Int Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int Int)))) (sort (set1 (tuple21 int int))
  (t2tb6 x))))

(declare-fun tb2t6 (uni) (set (tuple2 Int Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int Int))))
  (! (= (tb2t6 (t2tb6 i)) i) :pattern ((t2tb6 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb6 (tb2t6 j)) j) :pattern ((t2tb6 (tb2t6 j))) )))

(declare-fun t2tb11 ((tuple2 Int Int)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Int Int))) (sort (tuple21 int int) (t2tb11 x))))

(declare-fun tb2t11 (uni) (tuple2 Int Int))

;; BridgeL
  (assert
  (forall ((i (tuple2 Int Int)))
  (! (= (tb2t11 (t2tb11 i)) i) :pattern ((t2tb11 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb11 (tb2t11 j)) j) :pattern ((t2tb11 (tb2t11 j))) )))

;; infix ==_def
  (assert
  (forall ((s1 (set (tuple2 Int Int))) (s2 (set (tuple2 Int Int))))
  (= (infix_eqeq2 s1 s2)
  (forall ((x (tuple2 Int Int)))
  (= (mem (tuple21 int int) (t2tb11 x) (t2tb6 s1)) (mem (tuple21 int int)
  (t2tb11 x) (t2tb6 s2)))))))

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

(declare-fun t2tb12 (Int) uni)

;; t2tb_sort
  (assert (forall ((x Int)) (sort int (t2tb12 x))))

(declare-fun tb2t12 (uni) Int)

;; BridgeL
  (assert
  (forall ((i Int)) (! (= (tb2t12 (t2tb12 i)) i) :pattern ((t2tb12 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb12 (tb2t12 j)) j) :pattern ((t2tb12 (tb2t12 j))) )))

;; infix ==_def
  (assert
  (forall ((s1 (set Int)) (s2 (set Int)))
  (= (infix_eqeq1 s1 s2)
  (forall ((x Int))
  (= (mem int (t2tb12 x) (t2tb1 s1)) (mem int (t2tb12 x) (t2tb1 s2)))))))

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
  (forall ((s1 (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (s2 (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (=> (infix_eqeq6 s1 s2) (= s1 s2))))

;; extensionality
  (assert
  (forall ((s1 (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (s2 (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int))))
  (=> (infix_eqeq5 s1 s2) (= s1 s2))))

;; extensionality
  (assert
  (forall ((s1 (set (tuple2 (tuple2 Int Int) Int)))
  (s2 (set (tuple2 (tuple2 Int Int) Int))))
  (=> (infix_eqeq4 s1 s2) (= s1 s2))))

;; extensionality
  (assert
  (forall ((s1 (set enum_OBF__ii)) (s2 (set enum_OBF__ii)))
  (=> (infix_eqeq3 s1 s2) (= s1 s2))))

;; extensionality
  (assert
  (forall ((s1 (set (tuple2 Int Int))) (s2 (set (tuple2 Int Int))))
  (=> (infix_eqeq2 s1 s2) (= s1 s2))))

;; extensionality
  (assert
  (forall ((s1 (set Int)) (s2 (set Int))) (=> (infix_eqeq1 s1 s2) (= s1 s2))))

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

(declare-fun empty (ty) uni)

;; empty_sort
  (assert (forall ((a ty)) (sort (set1 a) (empty a))))

(declare-fun empty1 () (set Int))

(declare-fun empty2 () (set (tuple2 Int Int)))

(declare-fun empty3 () (set enum_OBF__ii))

(declare-fun empty4 () (set (tuple2 (tuple2 Int Int) Int)))

(declare-fun empty5 () (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))

(declare-fun empty6 () (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))

(declare-fun is_empty (ty uni) Bool)

;; is_empty_def
  (assert
  (forall ((a ty))
  (forall ((s uni))
  (and (=> (is_empty a s) (forall ((x uni)) (not (mem a x s))))
  (=> (forall ((x uni)) (=> (sort a x) (not (mem a x s)))) (is_empty a s))))))

;; empty_def1
  (assert (is_empty (tuple21 (tuple21 int enum_OBF__aa1) int)
  (t2tb2 empty6)))

;; empty_def1
  (assert (is_empty (tuple21 (tuple21 (tuple21 int int) int) int)
  (t2tb3 empty5)))

;; empty_def1
  (assert (is_empty (tuple21 (tuple21 int int) int) (t2tb4 empty4)))

;; empty_def1
  (assert (is_empty enum_OBF__ii1 (t2tb5 empty3)))

;; empty_def1
  (assert (is_empty (tuple21 int int) (t2tb6 empty2)))

;; empty_def1
  (assert (is_empty int (t2tb1 empty1)))

;; empty_def1
  (assert (forall ((a ty)) (is_empty a (empty a))))

;; mem_empty
  (assert
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (not (mem (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb7 x)
  (t2tb2 empty6)))))

;; mem_empty
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (not (mem (tuple21 (tuple21 (tuple21 int int) int) int) (t2tb8 x)
  (t2tb3 empty5)))))

;; mem_empty
  (assert
  (forall ((x (tuple2 (tuple2 Int Int) Int)))
  (not (mem (tuple21 (tuple21 int int) int) (t2tb9 x) (t2tb4 empty4)))))

;; mem_empty
  (assert
  (forall ((x enum_OBF__ii))
  (not (mem enum_OBF__ii1 (t2tb10 x) (t2tb5 empty3)))))

;; mem_empty
  (assert
  (forall ((x (tuple2 Int Int)))
  (not (mem (tuple21 int int) (t2tb11 x) (t2tb6 empty2)))))

;; mem_empty
  (assert (forall ((x Int)) (not (mem int (t2tb12 x) (t2tb1 empty1)))))

;; mem_empty
  (assert (forall ((a ty)) (forall ((x uni)) (not (mem a x (empty a))))))

(declare-fun add (ty uni uni) uni)

;; add_sort
  (assert
  (forall ((a ty)) (forall ((x uni) (x1 uni)) (sort (set1 a) (add a x x1)))))

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

(declare-fun t2tb13 (Bool) uni)

;; t2tb_sort
  (assert (forall ((x Bool)) (sort bool (t2tb13 x))))

(declare-fun tb2t13 (uni) Bool)

;; BridgeL
  (assert
  (forall ((i Bool)) (! (= (tb2t13 (t2tb13 i)) i) :pattern ((t2tb13 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort bool j) (= (t2tb13 (tb2t13 j)) j)) :pattern ((t2tb13
                                                            (tb2t13 j))) )))

(declare-fun t2tb14 ((set Bool)) uni)

;; t2tb_sort
  (assert (forall ((x (set Bool))) (sort (set1 bool) (t2tb14 x))))

(declare-fun tb2t14 (uni) (set Bool))

;; BridgeL
  (assert
  (forall ((i (set Bool)))
  (! (= (tb2t14 (t2tb14 i)) i) :pattern ((t2tb14 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 bool) j) (= (t2tb14 (tb2t14 j)) j)) :pattern ((t2tb14
                                                                   (tb2t14 j))) )))

;; mem_b_bool
  (assert (forall ((x Bool)) (mem bool (t2tb13 x) (t2tb14 b_bool))))

(declare-fun integer () (set Int))

;; mem_integer
  (assert (forall ((x Int)) (mem int (t2tb12 x) (t2tb1 integer))))

(declare-fun natural () (set Int))

;; mem_natural
  (assert
  (forall ((x Int)) (= (mem int (t2tb12 x) (t2tb1 natural)) (<= 0 x))))

(declare-fun natural1 () (set Int))

;; mem_natural1
  (assert
  (forall ((x Int)) (= (mem int (t2tb12 x) (t2tb1 natural1)) (< 0 x))))

(declare-fun nat () (set Int))

;; mem_nat
  (assert
  (forall ((x Int))
  (= (mem int (t2tb12 x) (t2tb1 nat)) (and (<= 0 x) (<= x 2147483647)))))

(declare-fun nat1 () (set Int))

;; mem_nat1
  (assert
  (forall ((x Int))
  (= (mem int (t2tb12 x) (t2tb1 nat1)) (and (< 0 x) (<= x 2147483647)))))

(declare-fun bounded_int () (set Int))

;; mem_bounded_int
  (assert
  (forall ((x Int))
  (= (mem int (t2tb12 x) (t2tb1 bounded_int))
  (and (<= (- 2147483647) x) (<= x 2147483647)))))

(declare-fun mk (Int Int) (set Int))

;; mem_interval
  (assert
  (forall ((x Int) (a Int) (b Int))
  (! (= (mem int (t2tb12 x) (t2tb1 (mk a b))) (and (<= a x) (<= x b))) :pattern ((mem
  int (t2tb12 x) (t2tb1 (mk a b)))) )))

;; interval_empty
  (assert (forall ((a Int) (b Int)) (=> (< b a) (= (mk a b) empty1))))

;; interval_add
  (assert
  (forall ((a Int) (b Int))
  (=> (<= a b)
  (= (mk a b) (tb2t1 (add int (t2tb12 b) (t2tb1 (mk a (- b 1)))))))))

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

(declare-fun t2tb15 ((set (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))) (sort
  (set1 (set1 (tuple21 (tuple21 int enum_OBF__aa1) int))) (t2tb15 x))))

(declare-fun tb2t15 (uni) (set (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))))
  (! (= (tb2t15 (t2tb15 i)) i) :pattern ((t2tb15 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb15 (tb2t15 j)) j) :pattern ((t2tb15 (tb2t15 j))) )))

;; mem_non_empty_power
  (assert
  (forall ((x (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (y (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (! (= (mem (set1 (tuple21 (tuple21 int enum_OBF__aa1) int)) (t2tb2 x)
     (non_empty_power (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 y)))
     (and (subset (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 x)
     (t2tb2 y)) (not (= x empty6)))) :pattern ((mem
  (set1 (tuple21 (tuple21 int enum_OBF__aa1) int)) (t2tb2 x)
  (non_empty_power (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 y)))) )))

(declare-fun t2tb16 ((set (set (tuple2 (tuple2 (tuple2 Int Int) Int)
  Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int))))) (sort
  (set1 (set1 (tuple21 (tuple21 (tuple21 int int) int) int))) (t2tb16 x))))

(declare-fun tb2t16 (uni) (set (set (tuple2 (tuple2 (tuple2 Int Int) Int)
  Int))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))))
  (! (= (tb2t16 (t2tb16 i)) i) :pattern ((t2tb16 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb16 (tb2t16 j)) j) :pattern ((t2tb16 (tb2t16 j))) )))

;; mem_non_empty_power
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (y (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int))))
  (! (= (mem (set1 (tuple21 (tuple21 (tuple21 int int) int) int)) (t2tb3 x)
     (non_empty_power (tuple21 (tuple21 (tuple21 int int) int) int)
     (t2tb3 y)))
     (and (subset (tuple21 (tuple21 (tuple21 int int) int) int) (t2tb3 x)
     (t2tb3 y)) (not (= x empty5)))) :pattern ((mem
  (set1 (tuple21 (tuple21 (tuple21 int int) int) int)) (t2tb3 x)
  (non_empty_power (tuple21 (tuple21 (tuple21 int int) int) int) (t2tb3 y)))) )))

(declare-fun t2tb17 ((set (set (tuple2 (tuple2 Int Int) Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 Int Int) Int))))) (sort
  (set1 (set1 (tuple21 (tuple21 int int) int))) (t2tb17 x))))

(declare-fun tb2t17 (uni) (set (set (tuple2 (tuple2 Int Int) Int))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 Int Int) Int)))))
  (! (= (tb2t17 (t2tb17 i)) i) :pattern ((t2tb17 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb17 (tb2t17 j)) j) :pattern ((t2tb17 (tb2t17 j))) )))

;; mem_non_empty_power
  (assert
  (forall ((x (set (tuple2 (tuple2 Int Int) Int)))
  (y (set (tuple2 (tuple2 Int Int) Int))))
  (! (= (mem (set1 (tuple21 (tuple21 int int) int)) (t2tb4 x)
     (non_empty_power (tuple21 (tuple21 int int) int) (t2tb4 y)))
     (and (subset (tuple21 (tuple21 int int) int) (t2tb4 x) (t2tb4 y))
     (not (= x empty4)))) :pattern ((mem
  (set1 (tuple21 (tuple21 int int) int)) (t2tb4 x)
  (non_empty_power (tuple21 (tuple21 int int) int) (t2tb4 y)))) )))

(declare-fun t2tb ((set (set enum_OBF__ii))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set enum_OBF__ii)))) (sort (set1 (set1 enum_OBF__ii1))
  (t2tb x))))

(declare-fun tb2t (uni) (set (set enum_OBF__ii)))

;; BridgeL
  (assert
  (forall ((i (set (set enum_OBF__ii))))
  (! (= (tb2t (t2tb i)) i) :pattern ((t2tb i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (set1 enum_OBF__ii1)) j) (= (t2tb (tb2t j)) j)) :pattern (
  (t2tb (tb2t j))) )))

;; mem_non_empty_power
  (assert
  (forall ((x (set enum_OBF__ii)) (y (set enum_OBF__ii)))
  (! (= (mem (set1 enum_OBF__ii1) (t2tb5 x)
     (non_empty_power enum_OBF__ii1 (t2tb5 y)))
     (and (subset enum_OBF__ii1 (t2tb5 x) (t2tb5 y)) (not (= x empty3)))) :pattern ((mem
  (set1 enum_OBF__ii1) (t2tb5 x)
  (non_empty_power enum_OBF__ii1 (t2tb5 y)))) )))

(declare-fun t2tb19 ((set (set (tuple2 Int Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Int Int))))) (sort
  (set1 (set1 (tuple21 int int))) (t2tb19 x))))

(declare-fun tb2t19 (uni) (set (set (tuple2 Int Int))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Int Int)))))
  (! (= (tb2t19 (t2tb19 i)) i) :pattern ((t2tb19 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb19 (tb2t19 j)) j) :pattern ((t2tb19 (tb2t19 j))) )))

;; mem_non_empty_power
  (assert
  (forall ((x (set (tuple2 Int Int))) (y (set (tuple2 Int Int))))
  (! (= (mem (set1 (tuple21 int int)) (t2tb6 x)
     (non_empty_power (tuple21 int int) (t2tb6 y)))
     (and (subset (tuple21 int int) (t2tb6 x) (t2tb6 y)) (not (= x empty2)))) :pattern ((mem
  (set1 (tuple21 int int)) (t2tb6 x)
  (non_empty_power (tuple21 int int) (t2tb6 y)))) )))

(declare-fun t2tb20 ((set (set Int))) uni)

;; t2tb_sort
  (assert (forall ((x (set (set Int)))) (sort (set1 (set1 int)) (t2tb20 x))))

(declare-fun tb2t20 (uni) (set (set Int)))

;; BridgeL
  (assert
  (forall ((i (set (set Int))))
  (! (= (tb2t20 (t2tb20 i)) i) :pattern ((t2tb20 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb20 (tb2t20 j)) j) :pattern ((t2tb20 (tb2t20 j))) )))

;; mem_non_empty_power
  (assert
  (forall ((x (set Int)) (y (set Int)))
  (! (= (mem (set1 int) (t2tb1 x) (non_empty_power int (t2tb1 y)))
     (and (subset int (t2tb1 x) (t2tb1 y)) (not (= x empty1)))) :pattern ((mem
  (set1 int) (t2tb1 x) (non_empty_power int (t2tb1 y)))) )))

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
  (forall ((r uni) (dom1 (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (x (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (= (image b (tuple21 (tuple21 int enum_OBF__aa1) int) r
     (add (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb7 x) (t2tb2 dom1))) 
  (union b
  (image b (tuple21 (tuple21 int enum_OBF__aa1) int) r
  (add (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb7 x) (t2tb2 empty6)))
  (image b (tuple21 (tuple21 int enum_OBF__aa1) int) r (t2tb2 dom1)))))))

;; image_add
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom1 (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (x (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (= (image b (tuple21 (tuple21 (tuple21 int int) int) int) r
     (add (tuple21 (tuple21 (tuple21 int int) int) int) (t2tb8 x)
     (t2tb3 dom1))) (union b
                    (image b (tuple21 (tuple21 (tuple21 int int) int) int) r
                    (add (tuple21 (tuple21 (tuple21 int int) int) int)
                    (t2tb8 x) (t2tb3 empty5)))
                    (image b (tuple21 (tuple21 (tuple21 int int) int) int) r
                    (t2tb3 dom1)))))))

;; image_add
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom1 (set (tuple2 (tuple2 Int Int) Int)))
  (x (tuple2 (tuple2 Int Int) Int)))
  (= (image b (tuple21 (tuple21 int int) int) r
     (add (tuple21 (tuple21 int int) int) (t2tb9 x) (t2tb4 dom1))) (union b
                                                                   (image b
                                                                   (tuple21
                                                                   (tuple21
                                                                   int 
                                                                   int) 
                                                                   int) r
                                                                   (add
                                                                   (tuple21
                                                                   (tuple21
                                                                   int 
                                                                   int) 
                                                                   int)
                                                                   (t2tb9 x)
                                                                   (t2tb4
                                                                   empty4)))
                                                                   (image b
                                                                   (tuple21
                                                                   (tuple21
                                                                   int 
                                                                   int) 
                                                                   int) r
                                                                   (t2tb4
                                                                   dom1)))))))

;; image_add
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom1 (set enum_OBF__ii)) (x enum_OBF__ii))
  (= (image b enum_OBF__ii1 r (add enum_OBF__ii1 (t2tb10 x) (t2tb5 dom1))) 
  (union b
  (image b enum_OBF__ii1 r (add enum_OBF__ii1 (t2tb10 x) (t2tb5 empty3)))
  (image b enum_OBF__ii1 r (t2tb5 dom1)))))))

;; image_add
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom1 (set (tuple2 Int Int))) (x (tuple2 Int Int)))
  (= (image b (tuple21 int int) r
     (add (tuple21 int int) (t2tb11 x) (t2tb6 dom1))) (union b
                                                      (image b
                                                      (tuple21 int int) r
                                                      (add (tuple21 int int)
                                                      (t2tb11 x)
                                                      (t2tb6 empty2)))
                                                      (image b
                                                      (tuple21 int int) r
                                                      (t2tb6 dom1)))))))

;; image_add
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom1 (set Int)) (x Int))
  (= (image b int r (add int (t2tb12 x) (t2tb1 dom1))) (union b
                                                       (image b int r
                                                       (add int (t2tb12 x)
                                                       (t2tb1 empty1)))
                                                       (image b int r
                                                       (t2tb1 dom1)))))))

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
  (= (tb2t2
     (dom b (tuple21 (tuple21 int enum_OBF__aa1) int)
     (empty (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b)))) 
  empty6)))

(declare-fun t2tb30 ((set (tuple2 Int enum_OBF__aa))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int enum_OBF__aa)))) (sort
  (set1 (tuple21 int enum_OBF__aa1)) (t2tb30 x))))

(declare-fun tb2t30 (uni) (set (tuple2 Int enum_OBF__aa)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int enum_OBF__aa))))
  (! (= (tb2t30 (t2tb30 i)) i) :pattern ((t2tb30 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb30 (tb2t30 j)) j) :pattern ((t2tb30 (tb2t30 j))) )))

;; dom_empty
  (assert
  (= (tb2t30 (dom int (tuple21 int enum_OBF__aa1) (t2tb2 empty6))) (tb2t30
                                                                   (empty
                                                                   (tuple21
                                                                   int
                                                                   enum_OBF__aa1)))))

;; dom_empty
  (assert
  (forall ((b ty))
  (= (tb2t3
     (dom b (tuple21 (tuple21 (tuple21 int int) int) int)
     (empty (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int) b)))) 
  empty5)))

;; dom_empty
  (assert
  (= (tb2t4 (dom int (tuple21 (tuple21 int int) int) (t2tb3 empty5))) 
  empty4))

;; dom_empty
  (assert
  (forall ((b ty))
  (= (tb2t4
     (dom b (tuple21 (tuple21 int int) int)
     (empty (tuple21 (tuple21 (tuple21 int int) int) b)))) empty4)))

;; dom_empty
  (assert
  (forall ((b ty))
  (= (tb2t5 (dom b enum_OBF__ii1 (empty (tuple21 enum_OBF__ii1 b)))) 
  empty3)))

;; dom_empty
  (assert (= (tb2t6 (dom int (tuple21 int int) (t2tb4 empty4))) empty2))

;; dom_empty
  (assert
  (forall ((b ty))
  (= (tb2t6 (dom b (tuple21 int int) (empty (tuple21 (tuple21 int int) b)))) 
  empty2)))

;; dom_empty
  (assert (= (tb2t1 (dom int int (t2tb6 empty2))) empty1))

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
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int)) (y uni))
  (= (tb2t2
     (dom b (tuple21 (tuple21 int enum_OBF__aa1) int)
     (add (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b)
     (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int) b (t2tb7 x) y)
     (empty (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b))))) 
  (tb2t2
  (add (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb7 x) (t2tb2 empty6)))))))

(declare-fun t2tb31 ((tuple2 Int enum_OBF__aa)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Int enum_OBF__aa))) (sort (tuple21 int enum_OBF__aa1)
  (t2tb31 x))))

(declare-fun tb2t31 (uni) (tuple2 Int enum_OBF__aa))

;; BridgeL
  (assert
  (forall ((i (tuple2 Int enum_OBF__aa)))
  (! (= (tb2t31 (t2tb31 i)) i) :pattern ((t2tb31 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb31 (tb2t31 j)) j) :pattern ((t2tb31 (tb2t31 j))) )))

;; dom_singleton
  (assert
  (forall ((x (tuple2 Int enum_OBF__aa)) (y Int))
  (= (tb2t30
     (dom int (tuple21 int enum_OBF__aa1)
     (add (tuple21 (tuple21 int enum_OBF__aa1) int)
     (Tuple2 (tuple21 int enum_OBF__aa1) int (t2tb31 x) (t2tb12 y))
     (t2tb2 empty6)))) (tb2t30
                       (add (tuple21 int enum_OBF__aa1) (t2tb31 x)
                       (empty (tuple21 int enum_OBF__aa1)))))))

;; dom_singleton
  (assert
  (forall ((b ty))
  (forall ((x (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (y uni))
  (= (tb2t3
     (dom b (tuple21 (tuple21 (tuple21 int int) int) int)
     (add (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int) b)
     (Tuple2 (tuple21 (tuple21 (tuple21 int int) int) int) b (t2tb8 x) y)
     (empty (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int) b))))) 
  (tb2t3
  (add (tuple21 (tuple21 (tuple21 int int) int) int) (t2tb8 x)
  (t2tb3 empty5)))))))

;; dom_singleton
  (assert
  (forall ((x (tuple2 (tuple2 Int Int) Int)) (y Int))
  (= (tb2t4
     (dom int (tuple21 (tuple21 int int) int)
     (add (tuple21 (tuple21 (tuple21 int int) int) int)
     (Tuple2 (tuple21 (tuple21 int int) int) int (t2tb9 x) (t2tb12 y))
     (t2tb3 empty5)))) (tb2t4
                       (add (tuple21 (tuple21 int int) int) (t2tb9 x)
                       (t2tb4 empty4))))))

;; dom_singleton
  (assert
  (forall ((b ty))
  (forall ((x (tuple2 (tuple2 Int Int) Int)) (y uni))
  (= (tb2t4
     (dom b (tuple21 (tuple21 int int) int)
     (add (tuple21 (tuple21 (tuple21 int int) int) b)
     (Tuple2 (tuple21 (tuple21 int int) int) b (t2tb9 x) y)
     (empty (tuple21 (tuple21 (tuple21 int int) int) b))))) (tb2t4
                                                            (add
                                                            (tuple21
                                                            (tuple21 int int)
                                                            int) (t2tb9 x)
                                                            (t2tb4 empty4)))))))

;; dom_singleton
  (assert
  (forall ((b ty))
  (forall ((x enum_OBF__ii) (y uni))
  (= (tb2t5
     (dom b enum_OBF__ii1
     (add (tuple21 enum_OBF__ii1 b) (Tuple2 enum_OBF__ii1 b (t2tb10 x) y)
     (empty (tuple21 enum_OBF__ii1 b))))) (tb2t5
                                          (add enum_OBF__ii1 (t2tb10 x)
                                          (t2tb5 empty3)))))))

;; dom_singleton
  (assert
  (forall ((x (tuple2 Int Int)) (y Int))
  (= (tb2t6
     (dom int (tuple21 int int)
     (add (tuple21 (tuple21 int int) int)
     (Tuple2 (tuple21 int int) int (t2tb11 x) (t2tb12 y)) (t2tb4 empty4)))) 
  (tb2t6 (add (tuple21 int int) (t2tb11 x) (t2tb6 empty2))))))

;; dom_singleton
  (assert
  (forall ((b ty))
  (forall ((x (tuple2 Int Int)) (y uni))
  (= (tb2t6
     (dom b (tuple21 int int)
     (add (tuple21 (tuple21 int int) b)
     (Tuple2 (tuple21 int int) b (t2tb11 x) y)
     (empty (tuple21 (tuple21 int int) b))))) (tb2t6
                                              (add (tuple21 int int)
                                              (t2tb11 x) (t2tb6 empty2)))))))

;; dom_singleton
  (assert
  (forall ((x Int) (y Int))
  (= (tb2t1
     (dom int int
     (add (tuple21 int int) (Tuple2 int int (t2tb12 x) (t2tb12 y))
     (t2tb6 empty2)))) (tb2t1 (add int (t2tb12 x) (t2tb1 empty1))))))

;; dom_singleton
  (assert
  (forall ((b ty))
  (forall ((x Int) (y uni))
  (= (tb2t1
     (dom b int
     (add (tuple21 int b) (Tuple2 int b (t2tb12 x) y)
     (empty (tuple21 int b))))) (tb2t1 (add int (t2tb12 x) (t2tb1 empty1)))))))

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
  (forall ((s (set (tuple2 Int enum_OBF__aa))) (t (set Int)) (x (tuple2 Int
  enum_OBF__aa)) (y Int))
  (=>
  (and (mem (tuple21 int enum_OBF__aa1) (t2tb31 x) (t2tb30 s)) (mem int
  (t2tb12 y) (t2tb1 t))) (mem
  (set1 (tuple21 (tuple21 int enum_OBF__aa1) int))
  (add (tuple21 (tuple21 int enum_OBF__aa1) int)
  (Tuple2 (tuple21 int enum_OBF__aa1) int (t2tb31 x) (t2tb12 y))
  (t2tb2 empty6))
  (infix_plmngt int (tuple21 int enum_OBF__aa1) (t2tb30 s) (t2tb1 t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set (tuple2 (tuple2 Int Int) Int))) (t (set Int))
  (x (tuple2 (tuple2 Int Int) Int)) (y Int))
  (=>
  (and (mem (tuple21 (tuple21 int int) int) (t2tb9 x) (t2tb4 s)) (mem 
  int (t2tb12 y) (t2tb1 t))) (mem
  (set1 (tuple21 (tuple21 (tuple21 int int) int) int))
  (add (tuple21 (tuple21 (tuple21 int int) int) int)
  (Tuple2 (tuple21 (tuple21 int int) int) int (t2tb9 x) (t2tb12 y))
  (t2tb3 empty5))
  (infix_plmngt int (tuple21 (tuple21 int int) int) (t2tb4 s) (t2tb1 t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set (tuple2 Int Int))) (t (set Int)) (x (tuple2 Int Int))
  (y Int))
  (=>
  (and (mem (tuple21 int int) (t2tb11 x) (t2tb6 s)) (mem int (t2tb12 y)
  (t2tb1 t))) (mem (set1 (tuple21 (tuple21 int int) int))
  (add (tuple21 (tuple21 int int) int)
  (Tuple2 (tuple21 int int) int (t2tb11 x) (t2tb12 y)) (t2tb4 empty4))
  (infix_plmngt int (tuple21 int int) (t2tb6 s) (t2tb1 t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set Int)) (t (set Int)) (x Int) (y Int))
  (=> (and (mem int (t2tb12 x) (t2tb1 s)) (mem int (t2tb12 y) (t2tb1 t)))
  (mem (set1 (tuple21 int int))
  (add (tuple21 int int) (Tuple2 int int (t2tb12 x) (t2tb12 y))
  (t2tb6 empty2)) (infix_plmngt int int (t2tb1 s) (t2tb1 t))))))

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
  (forall ((x uni) (y (tuple2 (tuple2 Int enum_OBF__aa) Int))) (! (mem
  (set1 (tuple21 a (tuple21 (tuple21 int enum_OBF__aa1) int)))
  (add (tuple21 a (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 a (tuple21 (tuple21 int enum_OBF__aa1) int) x (t2tb7 y))
  (empty (tuple21 a (tuple21 (tuple21 int enum_OBF__aa1) int))))
  (infix_mnmngt (tuple21 (tuple21 int enum_OBF__aa1) int) a
  (add a x (empty a))
  (add (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb7 y) (t2tb2 empty6)))) :pattern (
  (add (tuple21 a (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 a (tuple21 (tuple21 int enum_OBF__aa1) int) x (t2tb7 y))
  (empty (tuple21 a (tuple21 (tuple21 int enum_OBF__aa1) int))))) ))))

;; singleton_is_function
  (assert
  (forall ((a ty))
  (forall ((x uni) (y (tuple2 (tuple2 (tuple2 Int Int) Int) Int))) (! (mem
  (set1 (tuple21 a (tuple21 (tuple21 (tuple21 int int) int) int)))
  (add (tuple21 a (tuple21 (tuple21 (tuple21 int int) int) int))
  (Tuple2 a (tuple21 (tuple21 (tuple21 int int) int) int) x (t2tb8 y))
  (empty (tuple21 a (tuple21 (tuple21 (tuple21 int int) int) int))))
  (infix_mnmngt (tuple21 (tuple21 (tuple21 int int) int) int) a
  (add a x (empty a))
  (add (tuple21 (tuple21 (tuple21 int int) int) int) (t2tb8 y)
  (t2tb3 empty5)))) :pattern ((add
                              (tuple21 a
                              (tuple21 (tuple21 (tuple21 int int) int) int))
                              (Tuple2 a
                              (tuple21 (tuple21 (tuple21 int int) int) int) x
                              (t2tb8 y))
                              (empty
                              (tuple21 a
                              (tuple21 (tuple21 (tuple21 int int) int) int))))) ))))

;; singleton_is_function
  (assert
  (forall ((a ty))
  (forall ((x uni) (y (tuple2 (tuple2 Int Int) Int))) (! (mem
  (set1 (tuple21 a (tuple21 (tuple21 int int) int)))
  (add (tuple21 a (tuple21 (tuple21 int int) int))
  (Tuple2 a (tuple21 (tuple21 int int) int) x (t2tb9 y))
  (empty (tuple21 a (tuple21 (tuple21 int int) int))))
  (infix_mnmngt (tuple21 (tuple21 int int) int) a (add a x (empty a))
  (add (tuple21 (tuple21 int int) int) (t2tb9 y) (t2tb4 empty4)))) :pattern (
  (add (tuple21 a (tuple21 (tuple21 int int) int))
  (Tuple2 a (tuple21 (tuple21 int int) int) x (t2tb9 y))
  (empty (tuple21 a (tuple21 (tuple21 int int) int))))) ))))

;; singleton_is_function
  (assert
  (forall ((a ty))
  (forall ((x uni) (y enum_OBF__ii)) (! (mem (set1 (tuple21 a enum_OBF__ii1))
  (add (tuple21 a enum_OBF__ii1) (Tuple2 a enum_OBF__ii1 x (t2tb10 y))
  (empty (tuple21 a enum_OBF__ii1)))
  (infix_mnmngt enum_OBF__ii1 a (add a x (empty a))
  (add enum_OBF__ii1 (t2tb10 y) (t2tb5 empty3)))) :pattern ((add
                                                            (tuple21 a
                                                            enum_OBF__ii1)
                                                            (Tuple2 a
                                                            enum_OBF__ii1 x
                                                            (t2tb10 y))
                                                            (empty
                                                            (tuple21 a
                                                            enum_OBF__ii1)))) ))))

;; singleton_is_function
  (assert
  (forall ((a ty))
  (forall ((x uni) (y (tuple2 Int Int))) (! (mem
  (set1 (tuple21 a (tuple21 int int)))
  (add (tuple21 a (tuple21 int int))
  (Tuple2 a (tuple21 int int) x (t2tb11 y))
  (empty (tuple21 a (tuple21 int int))))
  (infix_mnmngt (tuple21 int int) a (add a x (empty a))
  (add (tuple21 int int) (t2tb11 y) (t2tb6 empty2)))) :pattern ((add
                                                                (tuple21 a
                                                                (tuple21 
                                                                int int))
                                                                (Tuple2 a
                                                                (tuple21 
                                                                int int) x
                                                                (t2tb11 y))
                                                                (empty
                                                                (tuple21 a
                                                                (tuple21 
                                                                int int))))) ))))

;; singleton_is_function
  (assert
  (forall ((a ty))
  (forall ((x uni) (y Int)) (! (mem (set1 (tuple21 a int))
  (add (tuple21 a int) (Tuple2 a int x (t2tb12 y)) (empty (tuple21 a int)))
  (infix_mnmngt int a (add a x (empty a))
  (add int (t2tb12 y) (t2tb1 empty1)))) :pattern ((add (tuple21 a int)
                                                  (Tuple2 a int x (t2tb12 y))
                                                  (empty (tuple21 a int)))) ))))

(declare-fun t2tb32 ((set (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 Int enum_OBF__aa) Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 Int enum_OBF__aa) Int)))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int)))) (t2tb32 x))))

(declare-fun tb2t32 (uni) (set (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa)
  Int) (tuple2 (tuple2 Int enum_OBF__aa) Int)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 Int enum_OBF__aa) Int))))))
  (! (= (tb2t32 (t2tb32 i)) i) :pattern ((t2tb32 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb32 (tb2t32 j)) j) :pattern ((t2tb32 (tb2t32 j))) )))

(declare-fun t2tb33 ((set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 Int enum_OBF__aa) Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 Int enum_OBF__aa) Int))))) (sort
  (set1
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int))) (t2tb33 x))))

(declare-fun tb2t33 (uni) (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 Int enum_OBF__aa) Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 Int enum_OBF__aa) Int)))))
  (! (= (tb2t33 (t2tb33 i)) i) :pattern ((t2tb33 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb33 (tb2t33 j)) j) :pattern ((t2tb33 (tb2t33 j))) )))

(declare-fun t2tb34 ((tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 Int enum_OBF__aa) Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 Int enum_OBF__aa) Int)))) (sort
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int)) (t2tb34 x))))

(declare-fun tb2t34 (uni) (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 Int enum_OBF__aa) Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (! (= (tb2t34 (t2tb34 i)) i) :pattern ((t2tb34 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb34 (tb2t34 j)) j) :pattern ((t2tb34 (tb2t34 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int)) (y (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (! (mem
  (set1
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int)))
  (add
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb7 x) (t2tb7 y))
  (empty
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int))))
  (infix_mnmngt (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int)
  (add (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb7 x) (t2tb2 empty6))
  (add (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb7 y) (t2tb2 empty6)))) :pattern (
  (tb2t33
  (add
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb7 x) (t2tb7 y))
  (empty
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int)))))) )))

(declare-fun t2tb35 ((tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 (tuple2 Int Int) Int) Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))) (sort
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 (tuple21 int int) int) int)) (t2tb35 x))))

(declare-fun tb2t35 (uni) (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 (tuple2 Int Int) Int) Int))))
  (! (= (tb2t35 (t2tb35 i)) i) :pattern ((t2tb35 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb35 (tb2t35 j)) j) :pattern ((t2tb35 (tb2t35 j))) )))

(declare-fun t2tb36 ((set (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 (tuple2 Int Int) Int) Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 (tuple21 int int) int) int)))) (t2tb36 x))))

(declare-fun tb2t36 (uni) (set (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa)
  Int) (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 (tuple2 Int Int) Int) Int))))))
  (! (= (tb2t36 (t2tb36 i)) i) :pattern ((t2tb36 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb36 (tb2t36 j)) j) :pattern ((t2tb36 (tb2t36 j))) )))

(declare-fun t2tb37 ((set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 (tuple2 Int Int) Int) Int))))) (sort
  (set1
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 (tuple21 int int) int) int))) (t2tb37 x))))

(declare-fun tb2t37 (uni) (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 (tuple2 Int Int) Int) Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))))
  (! (= (tb2t37 (t2tb37 i)) i) :pattern ((t2tb37 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb37 (tb2t37 j)) j) :pattern ((t2tb37 (tb2t37 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (y (tuple2 (tuple2 (tuple2 Int Int) Int) Int))) (! (mem
  (set1
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 (tuple21 int int) int) int)))
  (add
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 (tuple21 int int) int) int))
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 (tuple21 int int) int) int) (t2tb7 x) (t2tb8 y))
  (empty
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 (tuple21 int int) int) int))))
  (infix_mnmngt (tuple21 (tuple21 (tuple21 int int) int) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int)
  (add (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb7 x) (t2tb2 empty6))
  (add (tuple21 (tuple21 (tuple21 int int) int) int) (t2tb8 y)
  (t2tb3 empty5)))) :pattern ((tb2t37
                              (add
                              (tuple21
                              (tuple21 (tuple21 int enum_OBF__aa1) int)
                              (tuple21 (tuple21 (tuple21 int int) int) int))
                              (Tuple2
                              (tuple21 (tuple21 int enum_OBF__aa1) int)
                              (tuple21 (tuple21 (tuple21 int int) int) int)
                              (t2tb7 x) (t2tb8 y))
                              (empty
                              (tuple21
                              (tuple21 (tuple21 int enum_OBF__aa1) int)
                              (tuple21 (tuple21 (tuple21 int int) int) int)))))) )))

(declare-fun t2tb38 ((set (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 Int Int) Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 Int Int) Int)))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int int) int)))) (t2tb38 x))))

(declare-fun tb2t38 (uni) (set (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa)
  Int) (tuple2 (tuple2 Int Int) Int)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 Int Int) Int))))))
  (! (= (tb2t38 (t2tb38 i)) i) :pattern ((t2tb38 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb38 (tb2t38 j)) j) :pattern ((t2tb38 (tb2t38 j))) )))

(declare-fun t2tb39 ((set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 Int Int) Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 Int Int) Int))))) (sort
  (set1
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int int) int))) (t2tb39 x))))

(declare-fun tb2t39 (uni) (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 Int Int) Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 Int Int) Int)))))
  (! (= (tb2t39 (t2tb39 i)) i) :pattern ((t2tb39 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb39 (tb2t39 j)) j) :pattern ((t2tb39 (tb2t39 j))) )))

(declare-fun t2tb40 ((tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 Int Int) Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 Int Int) Int)))) (sort
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int int) int)) (t2tb40 x))))

(declare-fun tb2t40 (uni) (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 Int Int) Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 (tuple2 Int Int) Int))))
  (! (= (tb2t40 (t2tb40 i)) i) :pattern ((t2tb40 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb40 (tb2t40 j)) j) :pattern ((t2tb40 (tb2t40 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int)) (y (tuple2 (tuple2 Int
  Int) Int))) (! (mem
  (set1
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int int) int)))
  (add
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int int) int))
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int int) int) (t2tb7 x) (t2tb9 y))
  (empty
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int int) int))))
  (infix_mnmngt (tuple21 (tuple21 int int) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int)
  (add (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb7 x) (t2tb2 empty6))
  (add (tuple21 (tuple21 int int) int) (t2tb9 y) (t2tb4 empty4)))) :pattern (
  (tb2t39
  (add
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int int) int))
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int int) int) (t2tb7 x) (t2tb9 y))
  (empty
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int int) int)))))) )))

(declare-fun t2tb44 ((set (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  enum_OBF__ii)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  enum_OBF__ii))))) (sort
  (set1
  (set1 (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) enum_OBF__ii1)))
  (t2tb44 x))))

(declare-fun tb2t44 (uni) (set (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa)
  Int) enum_OBF__ii))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  enum_OBF__ii))))) (! (= (tb2t44 (t2tb44 i)) i) :pattern ((t2tb44 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb44 (tb2t44 j)) j) :pattern ((t2tb44 (tb2t44 j))) )))

(declare-fun t2tb45 ((set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  enum_OBF__ii))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  enum_OBF__ii)))) (sort
  (set1 (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) enum_OBF__ii1))
  (t2tb45 x))))

(declare-fun tb2t45 (uni) (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  enum_OBF__ii)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  enum_OBF__ii)))) (! (= (tb2t45 (t2tb45 i)) i) :pattern ((t2tb45 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb45 (tb2t45 j)) j) :pattern ((t2tb45 (tb2t45 j))) )))

(declare-fun t2tb46 ((tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  enum_OBF__ii)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int) enum_OBF__ii)))
  (sort (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) enum_OBF__ii1)
  (t2tb46 x))))

(declare-fun tb2t46 (uni) (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  enum_OBF__ii))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int) enum_OBF__ii)))
  (! (= (tb2t46 (t2tb46 i)) i) :pattern ((t2tb46 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb46 (tb2t46 j)) j) :pattern ((t2tb46 (tb2t46 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int)) (y enum_OBF__ii))
  (! (mem
  (set1 (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) enum_OBF__ii1))
  (add (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) enum_OBF__ii1)
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int) enum_OBF__ii1 (t2tb7 x)
  (t2tb10 y))
  (empty (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) enum_OBF__ii1)))
  (infix_mnmngt enum_OBF__ii1 (tuple21 (tuple21 int enum_OBF__aa1) int)
  (add (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb7 x) (t2tb2 empty6))
  (add enum_OBF__ii1 (t2tb10 y) (t2tb5 empty3)))) :pattern ((tb2t45
                                                            (add
                                                            (tuple21
                                                            (tuple21
                                                            (tuple21 
                                                            int
                                                            enum_OBF__aa1)
                                                            int)
                                                            enum_OBF__ii1)
                                                            (Tuple2
                                                            (tuple21
                                                            (tuple21 
                                                            int
                                                            enum_OBF__aa1)
                                                            int)
                                                            enum_OBF__ii1
                                                            (t2tb7 x)
                                                            (t2tb10 y))
                                                            (empty
                                                            (tuple21
                                                            (tuple21
                                                            (tuple21 
                                                            int
                                                            enum_OBF__aa1)
                                                            int)
                                                            enum_OBF__ii1))))) )))

(declare-fun t2tb47 ((set (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 Int Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 Int Int)))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) (tuple21 int int))))
  (t2tb47 x))))

(declare-fun tb2t47 (uni) (set (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa)
  Int) (tuple2 Int Int)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 Int Int)))))) (! (= (tb2t47 (t2tb47 i)) i) :pattern ((t2tb47 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb47 (tb2t47 j)) j) :pattern ((t2tb47 (tb2t47 j))) )))

(declare-fun t2tb48 ((set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 Int Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int) (tuple2 Int
  Int))))) (sort
  (set1
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) (tuple21 int int)))
  (t2tb48 x))))

(declare-fun tb2t48 (uni) (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 Int Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int) (tuple2 Int
  Int))))) (! (= (tb2t48 (t2tb48 i)) i) :pattern ((t2tb48 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb48 (tb2t48 j)) j) :pattern ((t2tb48 (tb2t48 j))) )))

(declare-fun t2tb49 ((tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 Int Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int) (tuple2 Int
  Int)))) (sort
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) (tuple21 int int))
  (t2tb49 x))))

(declare-fun tb2t49 (uni) (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  (tuple2 Int Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int) (tuple2 Int
  Int)))) (! (= (tb2t49 (t2tb49 i)) i) :pattern ((t2tb49 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb49 (tb2t49 j)) j) :pattern ((t2tb49 (tb2t49 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int)) (y (tuple2 Int Int)))
  (! (mem
  (set1
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) (tuple21 int int)))
  (add (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) (tuple21 int int))
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int) (tuple21 int int)
  (t2tb7 x) (t2tb11 y))
  (empty
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) (tuple21 int int))))
  (infix_mnmngt (tuple21 int int) (tuple21 (tuple21 int enum_OBF__aa1) int)
  (add (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb7 x) (t2tb2 empty6))
  (add (tuple21 int int) (t2tb11 y) (t2tb6 empty2)))) :pattern ((tb2t48
                                                                (add
                                                                (tuple21
                                                                (tuple21
                                                                (tuple21 
                                                                int
                                                                enum_OBF__aa1)
                                                                int)
                                                                (tuple21 
                                                                int int))
                                                                (Tuple2
                                                                (tuple21
                                                                (tuple21 
                                                                int
                                                                enum_OBF__aa1)
                                                                int)
                                                                (tuple21 
                                                                int int)
                                                                (t2tb7 x)
                                                                (t2tb11 y))
                                                                (empty
                                                                (tuple21
                                                                (tuple21
                                                                (tuple21 
                                                                int
                                                                enum_OBF__aa1)
                                                                int)
                                                                (tuple21 
                                                                int int)))))) )))

(declare-fun t2tb50 ((set (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  Int))))) (sort
  (set1 (set1 (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) int)))
  (t2tb50 x))))

(declare-fun tb2t50 (uni) (set (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa)
  Int) Int))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  Int))))) (! (= (tb2t50 (t2tb50 i)) i) :pattern ((t2tb50 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb50 (tb2t50 j)) j) :pattern ((t2tb50 (tb2t50 j))) )))

(declare-fun t2tb51 ((set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int) Int))))
  (sort (set1 (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) int))
  (t2tb51 x))))

(declare-fun tb2t51 (uni) (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int) Int))))
  (! (= (tb2t51 (t2tb51 i)) i) :pattern ((t2tb51 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb51 (tb2t51 j)) j) :pattern ((t2tb51 (tb2t51 j))) )))

(declare-fun t2tb52 ((tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  Int)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int) Int))) (sort
  (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) int) (t2tb52 x))))

(declare-fun tb2t52 (uni) (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int)
  Int))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 Int enum_OBF__aa) Int) Int)))
  (! (= (tb2t52 (t2tb52 i)) i) :pattern ((t2tb52 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb52 (tb2t52 j)) j) :pattern ((t2tb52 (tb2t52 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int)) (y Int)) (! (mem
  (set1 (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) int))
  (add (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) int)
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int) int (t2tb7 x) (t2tb12 y))
  (empty (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) int)))
  (infix_mnmngt int (tuple21 (tuple21 int enum_OBF__aa1) int)
  (add (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb7 x) (t2tb2 empty6))
  (add int (t2tb12 y) (t2tb1 empty1)))) :pattern ((tb2t51
                                                  (add
                                                  (tuple21
                                                  (tuple21
                                                  (tuple21 int enum_OBF__aa1)
                                                  int) int)
                                                  (Tuple2
                                                  (tuple21
                                                  (tuple21 int enum_OBF__aa1)
                                                  int) int (t2tb7 x)
                                                  (t2tb12 y))
                                                  (empty
                                                  (tuple21
                                                  (tuple21
                                                  (tuple21 int enum_OBF__aa1)
                                                  int) int))))) )))

;; singleton_is_function
  (assert
  (forall ((b ty))
  (forall ((x (tuple2 (tuple2 Int enum_OBF__aa) Int)) (y uni)) (! (mem
  (set1 (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b))
  (add (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b)
  (Tuple2 (tuple21 (tuple21 int enum_OBF__aa1) int) b (t2tb7 x) y)
  (empty (tuple21 (tuple21 (tuple21 int enum_OBF__aa1) int) b)))
  (infix_mnmngt b (tuple21 (tuple21 int enum_OBF__aa1) int)
  (add (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb7 x) (t2tb2 empty6))
  (add b y (empty b)))) :pattern ((add
                                  (tuple21
                                  (tuple21 (tuple21 int enum_OBF__aa1) int)
                                  b)
                                  (Tuple2
                                  (tuple21 (tuple21 int enum_OBF__aa1) int) b
                                  (t2tb7 x) y)
                                  (empty
                                  (tuple21
                                  (tuple21 (tuple21 int enum_OBF__aa1) int)
                                  b)))) ))))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 Int enum_OBF__aa)) (y Int)) (! (mem
  (set1 (tuple21 (tuple21 int enum_OBF__aa1) int))
  (add (tuple21 (tuple21 int enum_OBF__aa1) int)
  (Tuple2 (tuple21 int enum_OBF__aa1) int (t2tb31 x) (t2tb12 y))
  (t2tb2 empty6))
  (infix_mnmngt int (tuple21 int enum_OBF__aa1)
  (add (tuple21 int enum_OBF__aa1) (t2tb31 x)
  (empty (tuple21 int enum_OBF__aa1))) (add int (t2tb12 y) (t2tb1 empty1)))) :pattern (
  (tb2t2
  (add (tuple21 (tuple21 int enum_OBF__aa1) int)
  (Tuple2 (tuple21 int enum_OBF__aa1) int (t2tb31 x) (t2tb12 y))
  (t2tb2 empty6)))) )))

(declare-fun t2tb53 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int)
  Int) (tuple2 (tuple2 Int enum_OBF__aa) Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  (tuple2 (tuple2 Int enum_OBF__aa) Int)))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int)))) (t2tb53 x))))

(declare-fun tb2t53 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int) (tuple2 (tuple2 Int enum_OBF__aa) Int)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  (tuple2 (tuple2 Int enum_OBF__aa) Int))))))
  (! (= (tb2t53 (t2tb53 i)) i) :pattern ((t2tb53 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb53 (tb2t53 j)) j) :pattern ((t2tb53 (tb2t53 j))) )))

(declare-fun t2tb54 ((set (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  (tuple2 (tuple2 Int enum_OBF__aa) Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  (tuple2 (tuple2 Int enum_OBF__aa) Int))))) (sort
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int))) (t2tb54 x))))

(declare-fun tb2t54 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int)
  Int) (tuple2 (tuple2 Int enum_OBF__aa) Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  (tuple2 (tuple2 Int enum_OBF__aa) Int)))))
  (! (= (tb2t54 (t2tb54 i)) i) :pattern ((t2tb54 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb54 (tb2t54 j)) j) :pattern ((t2tb54 (tb2t54 j))) )))

(declare-fun t2tb55 ((tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  (tuple2 (tuple2 Int enum_OBF__aa) Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  (tuple2 (tuple2 Int enum_OBF__aa) Int)))) (sort
  (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int)) (t2tb55 x))))

(declare-fun tb2t55 (uni) (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  (tuple2 (tuple2 Int enum_OBF__aa) Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (! (= (tb2t55 (t2tb55 i)) i) :pattern ((t2tb55 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb55 (tb2t55 j)) j) :pattern ((t2tb55 (tb2t55 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Int Int) Int) Int))
  (y (tuple2 (tuple2 Int enum_OBF__aa) Int))) (! (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int)))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 (tuple21 (tuple21 (tuple21 int int) int) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb8 x) (t2tb7 y))
  (empty
  (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int))))
  (infix_mnmngt (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 (tuple21 int int) int) int)
  (add (tuple21 (tuple21 (tuple21 int int) int) int) (t2tb8 x)
  (t2tb3 empty5))
  (add (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb7 y) (t2tb2 empty6)))) :pattern (
  (tb2t54
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 (tuple21 (tuple21 (tuple21 int int) int) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb8 x) (t2tb7 y))
  (empty
  (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int)))))) )))

(declare-fun t2tb56 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int)
  Int) (tuple2 (tuple2 (tuple2 Int Int) Int) Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int)
  (tuple21 (tuple21 (tuple21 int int) int) int)))) (t2tb56 x))))

(declare-fun tb2t56 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int) (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  (tuple2 (tuple2 (tuple2 Int Int) Int) Int))))))
  (! (= (tb2t56 (t2tb56 i)) i) :pattern ((t2tb56 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb56 (tb2t56 j)) j) :pattern ((t2tb56 (tb2t56 j))) )))

(declare-fun t2tb57 ((set (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  (tuple2 (tuple2 (tuple2 Int Int) Int) Int))))) (sort
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int)
  (tuple21 (tuple21 (tuple21 int int) int) int))) (t2tb57 x))))

(declare-fun tb2t57 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int)
  Int) (tuple2 (tuple2 (tuple2 Int Int) Int) Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))))
  (! (= (tb2t57 (t2tb57 i)) i) :pattern ((t2tb57 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb57 (tb2t57 j)) j) :pattern ((t2tb57 (tb2t57 j))) )))

(declare-fun t2tb58 ((tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  (tuple2 (tuple2 (tuple2 Int Int) Int) Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))) (sort
  (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int)
  (tuple21 (tuple21 (tuple21 int int) int) int)) (t2tb58 x))))

(declare-fun tb2t58 (uni) (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  (tuple2 (tuple2 (tuple2 Int Int) Int) Int))))
  (! (= (tb2t58 (t2tb58 i)) i) :pattern ((t2tb58 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb58 (tb2t58 j)) j) :pattern ((t2tb58 (tb2t58 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Int Int) Int) Int))
  (y (tuple2 (tuple2 (tuple2 Int Int) Int) Int))) (! (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int)
  (tuple21 (tuple21 (tuple21 int int) int) int)))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int)
  (tuple21 (tuple21 (tuple21 int int) int) int))
  (Tuple2 (tuple21 (tuple21 (tuple21 int int) int) int)
  (tuple21 (tuple21 (tuple21 int int) int) int) (t2tb8 x) (t2tb8 y))
  (empty
  (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int)
  (tuple21 (tuple21 (tuple21 int int) int) int))))
  (infix_mnmngt (tuple21 (tuple21 (tuple21 int int) int) int)
  (tuple21 (tuple21 (tuple21 int int) int) int)
  (add (tuple21 (tuple21 (tuple21 int int) int) int) (t2tb8 x)
  (t2tb3 empty5))
  (add (tuple21 (tuple21 (tuple21 int int) int) int) (t2tb8 y)
  (t2tb3 empty5)))) :pattern ((tb2t57
                              (add
                              (tuple21
                              (tuple21 (tuple21 (tuple21 int int) int) int)
                              (tuple21 (tuple21 (tuple21 int int) int) int))
                              (Tuple2
                              (tuple21 (tuple21 (tuple21 int int) int) int)
                              (tuple21 (tuple21 (tuple21 int int) int) int)
                              (t2tb8 x) (t2tb8 y))
                              (empty
                              (tuple21
                              (tuple21 (tuple21 (tuple21 int int) int) int)
                              (tuple21 (tuple21 (tuple21 int int) int) int)))))) )))

(declare-fun t2tb59 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int)
  Int) (tuple2 (tuple2 Int Int) Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  (tuple2 (tuple2 Int Int) Int)))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int)
  (tuple21 (tuple21 int int) int)))) (t2tb59 x))))

(declare-fun tb2t59 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int) (tuple2 (tuple2 Int Int) Int)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  (tuple2 (tuple2 Int Int) Int))))))
  (! (= (tb2t59 (t2tb59 i)) i) :pattern ((t2tb59 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb59 (tb2t59 j)) j) :pattern ((t2tb59 (tb2t59 j))) )))

(declare-fun t2tb60 ((set (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  (tuple2 (tuple2 Int Int) Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  (tuple2 (tuple2 Int Int) Int))))) (sort
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int)
  (tuple21 (tuple21 int int) int))) (t2tb60 x))))

(declare-fun tb2t60 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int)
  Int) (tuple2 (tuple2 Int Int) Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  (tuple2 (tuple2 Int Int) Int)))))
  (! (= (tb2t60 (t2tb60 i)) i) :pattern ((t2tb60 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb60 (tb2t60 j)) j) :pattern ((t2tb60 (tb2t60 j))) )))

(declare-fun t2tb61 ((tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  (tuple2 (tuple2 Int Int) Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  (tuple2 (tuple2 Int Int) Int)))) (sort
  (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int)
  (tuple21 (tuple21 int int) int)) (t2tb61 x))))

(declare-fun tb2t61 (uni) (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  (tuple2 (tuple2 Int Int) Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  (tuple2 (tuple2 Int Int) Int))))
  (! (= (tb2t61 (t2tb61 i)) i) :pattern ((t2tb61 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb61 (tb2t61 j)) j) :pattern ((t2tb61 (tb2t61 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Int Int) Int) Int))
  (y (tuple2 (tuple2 Int Int) Int))) (! (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int)
  (tuple21 (tuple21 int int) int)))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int)
  (tuple21 (tuple21 int int) int))
  (Tuple2 (tuple21 (tuple21 (tuple21 int int) int) int)
  (tuple21 (tuple21 int int) int) (t2tb8 x) (t2tb9 y))
  (empty
  (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int)
  (tuple21 (tuple21 int int) int))))
  (infix_mnmngt (tuple21 (tuple21 int int) int)
  (tuple21 (tuple21 (tuple21 int int) int) int)
  (add (tuple21 (tuple21 (tuple21 int int) int) int) (t2tb8 x)
  (t2tb3 empty5))
  (add (tuple21 (tuple21 int int) int) (t2tb9 y) (t2tb4 empty4)))) :pattern (
  (tb2t60
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int)
  (tuple21 (tuple21 int int) int))
  (Tuple2 (tuple21 (tuple21 (tuple21 int int) int) int)
  (tuple21 (tuple21 int int) int) (t2tb8 x) (t2tb9 y))
  (empty
  (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int)
  (tuple21 (tuple21 int int) int)))))) )))

(declare-fun t2tb65 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int)
  Int) enum_OBF__ii)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  enum_OBF__ii))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int) enum_OBF__ii1)))
  (t2tb65 x))))

(declare-fun tb2t65 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int) enum_OBF__ii))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  enum_OBF__ii))))) (! (= (tb2t65 (t2tb65 i)) i) :pattern ((t2tb65 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb65 (tb2t65 j)) j) :pattern ((t2tb65 (tb2t65 j))) )))

(declare-fun t2tb66 ((set (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  enum_OBF__ii))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  enum_OBF__ii)))) (sort
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int) enum_OBF__ii1))
  (t2tb66 x))))

(declare-fun tb2t66 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int)
  Int) enum_OBF__ii)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  enum_OBF__ii)))) (! (= (tb2t66 (t2tb66 i)) i) :pattern ((t2tb66 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb66 (tb2t66 j)) j) :pattern ((t2tb66 (tb2t66 j))) )))

(declare-fun t2tb67 ((tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  enum_OBF__ii)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  enum_OBF__ii))) (sort
  (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int) enum_OBF__ii1)
  (t2tb67 x))))

(declare-fun tb2t67 (uni) (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  enum_OBF__ii))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  enum_OBF__ii))) (! (= (tb2t67 (t2tb67 i)) i) :pattern ((t2tb67 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb67 (tb2t67 j)) j) :pattern ((t2tb67 (tb2t67 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (y enum_OBF__ii))
  (! (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int) enum_OBF__ii1))
  (add (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int) enum_OBF__ii1)
  (Tuple2 (tuple21 (tuple21 (tuple21 int int) int) int) enum_OBF__ii1
  (t2tb8 x) (t2tb10 y))
  (empty
  (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int) enum_OBF__ii1)))
  (infix_mnmngt enum_OBF__ii1 (tuple21 (tuple21 (tuple21 int int) int) int)
  (add (tuple21 (tuple21 (tuple21 int int) int) int) (t2tb8 x)
  (t2tb3 empty5)) (add enum_OBF__ii1 (t2tb10 y) (t2tb5 empty3)))) :pattern (
  (tb2t66
  (add (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int) enum_OBF__ii1)
  (Tuple2 (tuple21 (tuple21 (tuple21 int int) int) int) enum_OBF__ii1
  (t2tb8 x) (t2tb10 y))
  (empty
  (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int) enum_OBF__ii1))))) )))

(declare-fun t2tb68 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int)
  Int) (tuple2 Int Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  (tuple2 Int Int)))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int) (tuple21 int int))))
  (t2tb68 x))))

(declare-fun tb2t68 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int) (tuple2 Int Int)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  (tuple2 Int Int)))))) (! (= (tb2t68 (t2tb68 i)) i) :pattern ((t2tb68 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb68 (tb2t68 j)) j) :pattern ((t2tb68 (tb2t68 j))) )))

(declare-fun t2tb69 ((set (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  (tuple2 Int Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  (tuple2 Int Int))))) (sort
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int) (tuple21 int int)))
  (t2tb69 x))))

(declare-fun tb2t69 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int)
  Int) (tuple2 Int Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  (tuple2 Int Int))))) (! (= (tb2t69 (t2tb69 i)) i) :pattern ((t2tb69 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb69 (tb2t69 j)) j) :pattern ((t2tb69 (tb2t69 j))) )))

(declare-fun t2tb70 ((tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  (tuple2 Int Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int) (tuple2 Int
  Int)))) (sort
  (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int) (tuple21 int int))
  (t2tb70 x))))

(declare-fun tb2t70 (uni) (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  (tuple2 Int Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int) (tuple2 Int
  Int)))) (! (= (tb2t70 (t2tb70 i)) i) :pattern ((t2tb70 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb70 (tb2t70 j)) j) :pattern ((t2tb70 (tb2t70 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (y (tuple2 Int
  Int))) (! (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int) (tuple21 int int)))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int) (tuple21 int int))
  (Tuple2 (tuple21 (tuple21 (tuple21 int int) int) int) (tuple21 int int)
  (t2tb8 x) (t2tb11 y))
  (empty
  (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int) (tuple21 int int))))
  (infix_mnmngt (tuple21 int int)
  (tuple21 (tuple21 (tuple21 int int) int) int)
  (add (tuple21 (tuple21 (tuple21 int int) int) int) (t2tb8 x)
  (t2tb3 empty5)) (add (tuple21 int int) (t2tb11 y) (t2tb6 empty2)))) :pattern (
  (tb2t69
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int) (tuple21 int int))
  (Tuple2 (tuple21 (tuple21 (tuple21 int int) int) int) (tuple21 int int)
  (t2tb8 x) (t2tb11 y))
  (empty
  (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int) (tuple21 int int)))))) )))

(declare-fun t2tb71 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int)
  Int) Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  Int))))) (sort
  (set1 (set1 (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int) int)))
  (t2tb71 x))))

(declare-fun tb2t71 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int) Int))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  Int))))) (! (= (tb2t71 (t2tb71 i)) i) :pattern ((t2tb71 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb71 (tb2t71 j)) j) :pattern ((t2tb71 (tb2t71 j))) )))

(declare-fun t2tb72 ((set (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int) Int))))
  (sort (set1 (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int) int))
  (t2tb72 x))))

(declare-fun tb2t72 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int)
  Int) Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int) Int))))
  (! (= (tb2t72 (t2tb72 i)) i) :pattern ((t2tb72 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb72 (tb2t72 j)) j) :pattern ((t2tb72 (tb2t72 j))) )))

(declare-fun t2tb73 ((tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  Int)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int) Int))) (sort
  (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int) int) (t2tb73 x))))

(declare-fun tb2t73 (uni) (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int)
  Int))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 Int Int) Int) Int) Int)))
  (! (= (tb2t73 (t2tb73 i)) i) :pattern ((t2tb73 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb73 (tb2t73 j)) j) :pattern ((t2tb73 (tb2t73 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (y Int)) (! (mem
  (set1 (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int) int))
  (add (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int) int)
  (Tuple2 (tuple21 (tuple21 (tuple21 int int) int) int) int (t2tb8 x)
  (t2tb12 y))
  (empty (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int) int)))
  (infix_mnmngt int (tuple21 (tuple21 (tuple21 int int) int) int)
  (add (tuple21 (tuple21 (tuple21 int int) int) int) (t2tb8 x)
  (t2tb3 empty5)) (add int (t2tb12 y) (t2tb1 empty1)))) :pattern ((tb2t72
                                                                  (add
                                                                  (tuple21
                                                                  (tuple21
                                                                  (tuple21
                                                                  (tuple21
                                                                  int 
                                                                  int) 
                                                                  int) 
                                                                  int) 
                                                                  int)
                                                                  (Tuple2
                                                                  (tuple21
                                                                  (tuple21
                                                                  (tuple21
                                                                  int 
                                                                  int) 
                                                                  int) 
                                                                  int) 
                                                                  int
                                                                  (t2tb8 x)
                                                                  (t2tb12 y))
                                                                  (empty
                                                                  (tuple21
                                                                  (tuple21
                                                                  (tuple21
                                                                  (tuple21
                                                                  int 
                                                                  int) 
                                                                  int) 
                                                                  int) 
                                                                  int))))) )))

;; singleton_is_function
  (assert
  (forall ((b ty))
  (forall ((x (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (y uni)) (! (mem
  (set1 (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int) b))
  (add (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int) b)
  (Tuple2 (tuple21 (tuple21 (tuple21 int int) int) int) b (t2tb8 x) y)
  (empty (tuple21 (tuple21 (tuple21 (tuple21 int int) int) int) b)))
  (infix_mnmngt b (tuple21 (tuple21 (tuple21 int int) int) int)
  (add (tuple21 (tuple21 (tuple21 int int) int) int) (t2tb8 x)
  (t2tb3 empty5)) (add b y (empty b)))) :pattern ((add
                                                  (tuple21
                                                  (tuple21
                                                  (tuple21 (tuple21 int int)
                                                  int) int) b)
                                                  (Tuple2
                                                  (tuple21
                                                  (tuple21 (tuple21 int int)
                                                  int) int) b (t2tb8 x) y)
                                                  (empty
                                                  (tuple21
                                                  (tuple21
                                                  (tuple21 (tuple21 int int)
                                                  int) int) b)))) ))))

(declare-fun t2tb74 ((set (set (tuple2 (tuple2 (tuple2 Int Int) Int)
  (tuple2 (tuple2 Int enum_OBF__aa) Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 Int Int) Int)
  (tuple2 (tuple2 Int enum_OBF__aa) Int)))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 int int) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int)))) (t2tb74 x))))

(declare-fun tb2t74 (uni) (set (set (tuple2 (tuple2 (tuple2 Int Int) Int)
  (tuple2 (tuple2 Int enum_OBF__aa) Int)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 Int Int) Int)
  (tuple2 (tuple2 Int enum_OBF__aa) Int))))))
  (! (= (tb2t74 (t2tb74 i)) i) :pattern ((t2tb74 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb74 (tb2t74 j)) j) :pattern ((t2tb74 (tb2t74 j))) )))

(declare-fun t2tb75 ((set (tuple2 (tuple2 (tuple2 Int Int) Int)
  (tuple2 (tuple2 Int enum_OBF__aa) Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 Int Int) Int) (tuple2 (tuple2 Int
  enum_OBF__aa) Int))))) (sort
  (set1
  (tuple21 (tuple21 (tuple21 int int) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int))) (t2tb75 x))))

(declare-fun tb2t75 (uni) (set (tuple2 (tuple2 (tuple2 Int Int) Int)
  (tuple2 (tuple2 Int enum_OBF__aa) Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 Int Int) Int) (tuple2 (tuple2 Int
  enum_OBF__aa) Int)))))
  (! (= (tb2t75 (t2tb75 i)) i) :pattern ((t2tb75 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb75 (tb2t75 j)) j) :pattern ((t2tb75 (tb2t75 j))) )))

(declare-fun t2tb76 ((tuple2 (tuple2 (tuple2 Int Int) Int)
  (tuple2 (tuple2 Int enum_OBF__aa) Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Int Int) Int) (tuple2 (tuple2 Int
  enum_OBF__aa) Int)))) (sort
  (tuple21 (tuple21 (tuple21 int int) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int)) (t2tb76 x))))

(declare-fun tb2t76 (uni) (tuple2 (tuple2 (tuple2 Int Int) Int)
  (tuple2 (tuple2 Int enum_OBF__aa) Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 Int Int) Int) (tuple2 (tuple2 Int
  enum_OBF__aa) Int)))) (! (= (tb2t76 (t2tb76 i)) i) :pattern ((t2tb76 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb76 (tb2t76 j)) j) :pattern ((t2tb76 (tb2t76 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 Int Int) Int)) (y (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (! (mem
  (set1
  (tuple21 (tuple21 (tuple21 int int) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int)))
  (add
  (tuple21 (tuple21 (tuple21 int int) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 (tuple21 (tuple21 int int) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb9 x) (t2tb7 y))
  (empty
  (tuple21 (tuple21 (tuple21 int int) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int))))
  (infix_mnmngt (tuple21 (tuple21 int enum_OBF__aa1) int)
  (tuple21 (tuple21 int int) int)
  (add (tuple21 (tuple21 int int) int) (t2tb9 x) (t2tb4 empty4))
  (add (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb7 y) (t2tb2 empty6)))) :pattern (
  (tb2t75
  (add
  (tuple21 (tuple21 (tuple21 int int) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 (tuple21 (tuple21 int int) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb9 x) (t2tb7 y))
  (empty
  (tuple21 (tuple21 (tuple21 int int) int)
  (tuple21 (tuple21 int enum_OBF__aa1) int)))))) )))

(declare-fun t2tb77 ((tuple2 (tuple2 (tuple2 Int Int) Int)
  (tuple2 (tuple2 (tuple2 Int Int) Int) Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Int Int) Int)
  (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))) (sort
  (tuple21 (tuple21 (tuple21 int int) int)
  (tuple21 (tuple21 (tuple21 int int) int) int)) (t2tb77 x))))

(declare-fun tb2t77 (uni) (tuple2 (tuple2 (tuple2 Int Int) Int)
  (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 Int Int) Int)
  (tuple2 (tuple2 (tuple2 Int Int) Int) Int))))
  (! (= (tb2t77 (t2tb77 i)) i) :pattern ((t2tb77 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb77 (tb2t77 j)) j) :pattern ((t2tb77 (tb2t77 j))) )))

(declare-fun t2tb78 ((set (set (tuple2 (tuple2 (tuple2 Int Int) Int)
  (tuple2 (tuple2 (tuple2 Int Int) Int) Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 Int Int) Int)
  (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 int int) int)
  (tuple21 (tuple21 (tuple21 int int) int) int)))) (t2tb78 x))))

(declare-fun tb2t78 (uni) (set (set (tuple2 (tuple2 (tuple2 Int Int) Int)
  (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 Int Int) Int)
  (tuple2 (tuple2 (tuple2 Int Int) Int) Int))))))
  (! (= (tb2t78 (t2tb78 i)) i) :pattern ((t2tb78 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb78 (tb2t78 j)) j) :pattern ((t2tb78 (tb2t78 j))) )))

(declare-fun t2tb79 ((set (tuple2 (tuple2 (tuple2 Int Int) Int)
  (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 Int Int) Int)
  (tuple2 (tuple2 (tuple2 Int Int) Int) Int))))) (sort
  (set1
  (tuple21 (tuple21 (tuple21 int int) int)
  (tuple21 (tuple21 (tuple21 int int) int) int))) (t2tb79 x))))

(declare-fun tb2t79 (uni) (set (tuple2 (tuple2 (tuple2 Int Int) Int)
  (tuple2 (tuple2 (tuple2 Int Int) Int) Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 Int Int) Int)
  (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))))
  (! (= (tb2t79 (t2tb79 i)) i) :pattern ((t2tb79 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb79 (tb2t79 j)) j) :pattern ((t2tb79 (tb2t79 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 Int Int) Int)) (y (tuple2 (tuple2 (tuple2 Int
  Int) Int) Int))) (! (mem
  (set1
  (tuple21 (tuple21 (tuple21 int int) int)
  (tuple21 (tuple21 (tuple21 int int) int) int)))
  (add
  (tuple21 (tuple21 (tuple21 int int) int)
  (tuple21 (tuple21 (tuple21 int int) int) int))
  (Tuple2 (tuple21 (tuple21 int int) int)
  (tuple21 (tuple21 (tuple21 int int) int) int) (t2tb9 x) (t2tb8 y))
  (empty
  (tuple21 (tuple21 (tuple21 int int) int)
  (tuple21 (tuple21 (tuple21 int int) int) int))))
  (infix_mnmngt (tuple21 (tuple21 (tuple21 int int) int) int)
  (tuple21 (tuple21 int int) int)
  (add (tuple21 (tuple21 int int) int) (t2tb9 x) (t2tb4 empty4))
  (add (tuple21 (tuple21 (tuple21 int int) int) int) (t2tb8 y)
  (t2tb3 empty5)))) :pattern ((tb2t79
                              (add
                              (tuple21 (tuple21 (tuple21 int int) int)
                              (tuple21 (tuple21 (tuple21 int int) int) int))
                              (Tuple2 (tuple21 (tuple21 int int) int)
                              (tuple21 (tuple21 (tuple21 int int) int) int)
                              (t2tb9 x) (t2tb8 y))
                              (empty
                              (tuple21 (tuple21 (tuple21 int int) int)
                              (tuple21 (tuple21 (tuple21 int int) int) int)))))) )))

(declare-fun t2tb80 ((set (tuple2 (tuple2 (tuple2 Int Int) Int)
  (tuple2 (tuple2 Int Int) Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 Int Int) Int) (tuple2 (tuple2 Int
  Int) Int))))) (sort
  (set1
  (tuple21 (tuple21 (tuple21 int int) int) (tuple21 (tuple21 int int) int)))
  (t2tb80 x))))

(declare-fun tb2t80 (uni) (set (tuple2 (tuple2 (tuple2 Int Int) Int)
  (tuple2 (tuple2 Int Int) Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 Int Int) Int) (tuple2 (tuple2 Int
  Int) Int))))) (! (= (tb2t80 (t2tb80 i)) i) :pattern ((t2tb80 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb80 (tb2t80 j)) j) :pattern ((t2tb80 (tb2t80 j))) )))

(declare-fun t2tb81 ((tuple2 (tuple2 (tuple2 Int Int) Int)
  (tuple2 (tuple2 Int Int) Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Int Int) Int) (tuple2 (tuple2 Int Int)
  Int)))) (sort
  (tuple21 (tuple21 (tuple21 int int) int) (tuple21 (tuple21 int int) int))
  (t2tb81 x))))

(declare-fun tb2t81 (uni) (tuple2 (tuple2 (tuple2 Int Int) Int)
  (tuple2 (tuple2 Int Int) Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 Int Int) Int) (tuple2 (tuple2 Int Int)
  Int)))) (! (= (tb2t81 (t2tb81 i)) i) :pattern ((t2tb81 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb81 (tb2t81 j)) j) :pattern ((t2tb81 (tb2t81 j))) )))

(declare-fun t2tb82 ((set (set (tuple2 (tuple2 (tuple2 Int Int) Int)
  (tuple2 (tuple2 Int Int) Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 Int Int) Int)
  (tuple2 (tuple2 Int Int) Int)))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 int int) int) (tuple21 (tuple21 int int) int))))
  (t2tb82 x))))

(declare-fun tb2t82 (uni) (set (set (tuple2 (tuple2 (tuple2 Int Int) Int)
  (tuple2 (tuple2 Int Int) Int)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 Int Int) Int)
  (tuple2 (tuple2 Int Int) Int))))))
  (! (= (tb2t82 (t2tb82 i)) i) :pattern ((t2tb82 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb82 (tb2t82 j)) j) :pattern ((t2tb82 (tb2t82 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 Int Int) Int)) (y (tuple2 (tuple2 Int Int)
  Int))) (! (mem
  (set1
  (tuple21 (tuple21 (tuple21 int int) int) (tuple21 (tuple21 int int) int)))
  (add
  (tuple21 (tuple21 (tuple21 int int) int) (tuple21 (tuple21 int int) int))
  (Tuple2 (tuple21 (tuple21 int int) int) (tuple21 (tuple21 int int) int)
  (t2tb9 x) (t2tb9 y))
  (empty
  (tuple21 (tuple21 (tuple21 int int) int) (tuple21 (tuple21 int int) int))))
  (infix_mnmngt (tuple21 (tuple21 int int) int)
  (tuple21 (tuple21 int int) int)
  (add (tuple21 (tuple21 int int) int) (t2tb9 x) (t2tb4 empty4))
  (add (tuple21 (tuple21 int int) int) (t2tb9 y) (t2tb4 empty4)))) :pattern (
  (tb2t80
  (add
  (tuple21 (tuple21 (tuple21 int int) int) (tuple21 (tuple21 int int) int))
  (Tuple2 (tuple21 (tuple21 int int) int) (tuple21 (tuple21 int int) int)
  (t2tb9 x) (t2tb9 y))
  (empty
  (tuple21 (tuple21 (tuple21 int int) int) (tuple21 (tuple21 int int) int)))))) )))

(declare-fun t2tb86 ((set (tuple2 (tuple2 (tuple2 Int Int) Int)
  enum_OBF__ii))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 Int Int) Int) enum_OBF__ii))))
  (sort (set1 (tuple21 (tuple21 (tuple21 int int) int) enum_OBF__ii1))
  (t2tb86 x))))

(declare-fun tb2t86 (uni) (set (tuple2 (tuple2 (tuple2 Int Int) Int)
  enum_OBF__ii)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 Int Int) Int) enum_OBF__ii))))
  (! (= (tb2t86 (t2tb86 i)) i) :pattern ((t2tb86 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb86 (tb2t86 j)) j) :pattern ((t2tb86 (tb2t86 j))) )))

(declare-fun t2tb87 ((tuple2 (tuple2 (tuple2 Int Int) Int)
  enum_OBF__ii)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Int Int) Int) enum_OBF__ii))) (sort
  (tuple21 (tuple21 (tuple21 int int) int) enum_OBF__ii1) (t2tb87 x))))

(declare-fun tb2t87 (uni) (tuple2 (tuple2 (tuple2 Int Int) Int)
  enum_OBF__ii))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 Int Int) Int) enum_OBF__ii)))
  (! (= (tb2t87 (t2tb87 i)) i) :pattern ((t2tb87 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb87 (tb2t87 j)) j) :pattern ((t2tb87 (tb2t87 j))) )))

(declare-fun t2tb88 ((set (set (tuple2 (tuple2 (tuple2 Int Int) Int)
  enum_OBF__ii)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 Int Int) Int)
  enum_OBF__ii))))) (sort
  (set1 (set1 (tuple21 (tuple21 (tuple21 int int) int) enum_OBF__ii1)))
  (t2tb88 x))))

(declare-fun tb2t88 (uni) (set (set (tuple2 (tuple2 (tuple2 Int Int) Int)
  enum_OBF__ii))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 Int Int) Int)
  enum_OBF__ii))))) (! (= (tb2t88 (t2tb88 i)) i) :pattern ((t2tb88 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb88 (tb2t88 j)) j) :pattern ((t2tb88 (tb2t88 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 Int Int) Int)) (y enum_OBF__ii)) (! (mem
  (set1 (tuple21 (tuple21 (tuple21 int int) int) enum_OBF__ii1))
  (add (tuple21 (tuple21 (tuple21 int int) int) enum_OBF__ii1)
  (Tuple2 (tuple21 (tuple21 int int) int) enum_OBF__ii1 (t2tb9 x) (t2tb10 y))
  (empty (tuple21 (tuple21 (tuple21 int int) int) enum_OBF__ii1)))
  (infix_mnmngt enum_OBF__ii1 (tuple21 (tuple21 int int) int)
  (add (tuple21 (tuple21 int int) int) (t2tb9 x) (t2tb4 empty4))
  (add enum_OBF__ii1 (t2tb10 y) (t2tb5 empty3)))) :pattern ((tb2t86
                                                            (add
                                                            (tuple21
                                                            (tuple21
                                                            (tuple21 int int)
                                                            int)
                                                            enum_OBF__ii1)
                                                            (Tuple2
                                                            (tuple21
                                                            (tuple21 int int)
                                                            int)
                                                            enum_OBF__ii1
                                                            (t2tb9 x)
                                                            (t2tb10 y))
                                                            (empty
                                                            (tuple21
                                                            (tuple21
                                                            (tuple21 int int)
                                                            int)
                                                            enum_OBF__ii1))))) )))

(declare-fun t2tb89 ((set (tuple2 (tuple2 (tuple2 Int Int) Int) (tuple2 Int
  Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 Int Int) Int) (tuple2 Int Int)))))
  (sort (set1 (tuple21 (tuple21 (tuple21 int int) int) (tuple21 int int)))
  (t2tb89 x))))

(declare-fun tb2t89 (uni) (set (tuple2 (tuple2 (tuple2 Int Int) Int)
  (tuple2 Int Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 Int Int) Int) (tuple2 Int Int)))))
  (! (= (tb2t89 (t2tb89 i)) i) :pattern ((t2tb89 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb89 (tb2t89 j)) j) :pattern ((t2tb89 (tb2t89 j))) )))

(declare-fun t2tb90 ((tuple2 (tuple2 (tuple2 Int Int) Int) (tuple2 Int
  Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Int Int) Int) (tuple2 Int Int)))) (sort
  (tuple21 (tuple21 (tuple21 int int) int) (tuple21 int int)) (t2tb90 x))))

(declare-fun tb2t90 (uni) (tuple2 (tuple2 (tuple2 Int Int) Int) (tuple2 Int
  Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 Int Int) Int) (tuple2 Int Int))))
  (! (= (tb2t90 (t2tb90 i)) i) :pattern ((t2tb90 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb90 (tb2t90 j)) j) :pattern ((t2tb90 (tb2t90 j))) )))

(declare-fun t2tb91 ((set (set (tuple2 (tuple2 (tuple2 Int Int) Int)
  (tuple2 Int Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 Int Int) Int) (tuple2 Int
  Int)))))) (sort
  (set1 (set1 (tuple21 (tuple21 (tuple21 int int) int) (tuple21 int int))))
  (t2tb91 x))))

(declare-fun tb2t91 (uni) (set (set (tuple2 (tuple2 (tuple2 Int Int) Int)
  (tuple2 Int Int)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 Int Int) Int) (tuple2 Int
  Int)))))) (! (= (tb2t91 (t2tb91 i)) i) :pattern ((t2tb91 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb91 (tb2t91 j)) j) :pattern ((t2tb91 (tb2t91 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 Int Int) Int)) (y (tuple2 Int Int))) (! (mem
  (set1 (tuple21 (tuple21 (tuple21 int int) int) (tuple21 int int)))
  (add (tuple21 (tuple21 (tuple21 int int) int) (tuple21 int int))
  (Tuple2 (tuple21 (tuple21 int int) int) (tuple21 int int) (t2tb9 x)
  (t2tb11 y))
  (empty (tuple21 (tuple21 (tuple21 int int) int) (tuple21 int int))))
  (infix_mnmngt (tuple21 int int) (tuple21 (tuple21 int int) int)
  (add (tuple21 (tuple21 int int) int) (t2tb9 x) (t2tb4 empty4))
  (add (tuple21 int int) (t2tb11 y) (t2tb6 empty2)))) :pattern ((tb2t89
                                                                (add
                                                                (tuple21
                                                                (tuple21
                                                                (tuple21 
                                                                int int) 
                                                                int)
                                                                (tuple21 
                                                                int int))
                                                                (Tuple2
                                                                (tuple21
                                                                (tuple21 
                                                                int int) 
                                                                int)
                                                                (tuple21 
                                                                int int)
                                                                (t2tb9 x)
                                                                (t2tb11 y))
                                                                (empty
                                                                (tuple21
                                                                (tuple21
                                                                (tuple21 
                                                                int int) 
                                                                int)
                                                                (tuple21 
                                                                int int)))))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 Int Int) Int)) (y Int)) (! (mem
  (set1 (tuple21 (tuple21 (tuple21 int int) int) int))
  (add (tuple21 (tuple21 (tuple21 int int) int) int)
  (Tuple2 (tuple21 (tuple21 int int) int) int (t2tb9 x) (t2tb12 y))
  (t2tb3 empty5))
  (infix_mnmngt int (tuple21 (tuple21 int int) int)
  (add (tuple21 (tuple21 int int) int) (t2tb9 x) (t2tb4 empty4))
  (add int (t2tb12 y) (t2tb1 empty1)))) :pattern ((tb2t3
                                                  (add
                                                  (tuple21
                                                  (tuple21 (tuple21 int int)
                                                  int) int)
                                                  (Tuple2
                                                  (tuple21 (tuple21 int int)
                                                  int) int (t2tb9 x)
                                                  (t2tb12 y)) (t2tb3 empty5)))) )))

;; singleton_is_function
  (assert
  (forall ((b ty))
  (forall ((x (tuple2 (tuple2 Int Int) Int)) (y uni)) (! (mem
  (set1 (tuple21 (tuple21 (tuple21 int int) int) b))
  (add (tuple21 (tuple21 (tuple21 int int) int) b)
  (Tuple2 (tuple21 (tuple21 int int) int) b (t2tb9 x) y)
  (empty (tuple21 (tuple21 (tuple21 int int) int) b)))
  (infix_mnmngt b (tuple21 (tuple21 int int) int)
  (add (tuple21 (tuple21 int int) int) (t2tb9 x) (t2tb4 empty4))
  (add b y (empty b)))) :pattern ((add
                                  (tuple21 (tuple21 (tuple21 int int) int) b)
                                  (Tuple2 (tuple21 (tuple21 int int) int) b
                                  (t2tb9 x) y)
                                  (empty
                                  (tuple21 (tuple21 (tuple21 int int) int) b)))) ))))

(declare-fun t2tb107 ((set (tuple2 enum_OBF__ii (tuple2 (tuple2 Int
  enum_OBF__aa) Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 enum_OBF__ii (tuple2 (tuple2 Int enum_OBF__aa)
  Int))))) (sort
  (set1 (tuple21 enum_OBF__ii1 (tuple21 (tuple21 int enum_OBF__aa1) int)))
  (t2tb107 x))))

(declare-fun tb2t107 (uni) (set (tuple2 enum_OBF__ii (tuple2 (tuple2 Int
  enum_OBF__aa) Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 enum_OBF__ii (tuple2 (tuple2 Int enum_OBF__aa)
  Int))))) (! (= (tb2t107 (t2tb107 i)) i) :pattern ((t2tb107 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb107 (tb2t107 j)) j) :pattern ((t2tb107 (tb2t107 j))) )))

(declare-fun t2tb108 ((set (set (tuple2 enum_OBF__ii (tuple2 (tuple2 Int
  enum_OBF__aa) Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 enum_OBF__ii (tuple2 (tuple2 Int
  enum_OBF__aa) Int)))))) (sort
  (set1
  (set1 (tuple21 enum_OBF__ii1 (tuple21 (tuple21 int enum_OBF__aa1) int))))
  (t2tb108 x))))

(declare-fun tb2t108 (uni) (set (set (tuple2 enum_OBF__ii (tuple2 (tuple2 Int
  enum_OBF__aa) Int)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 enum_OBF__ii (tuple2 (tuple2 Int
  enum_OBF__aa) Int))))))
  (! (= (tb2t108 (t2tb108 i)) i) :pattern ((t2tb108 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb108 (tb2t108 j)) j) :pattern ((t2tb108 (tb2t108 j))) )))

(declare-fun t2tb109 ((tuple2 enum_OBF__ii (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 enum_OBF__ii (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (sort (tuple21 enum_OBF__ii1 (tuple21 (tuple21 int enum_OBF__aa1) int))
  (t2tb109 x))))

(declare-fun tb2t109 (uni) (tuple2 enum_OBF__ii (tuple2 (tuple2 Int
  enum_OBF__aa) Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 enum_OBF__ii (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (! (= (tb2t109 (t2tb109 i)) i) :pattern ((t2tb109 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb109 (tb2t109 j)) j) :pattern ((t2tb109 (tb2t109 j))) )))

;; singleton_is_function
  (assert
  (forall ((x enum_OBF__ii) (y (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (! (mem
  (set1 (tuple21 enum_OBF__ii1 (tuple21 (tuple21 int enum_OBF__aa1) int)))
  (add (tuple21 enum_OBF__ii1 (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 enum_OBF__ii1 (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb10 x)
  (t2tb7 y))
  (empty (tuple21 enum_OBF__ii1 (tuple21 (tuple21 int enum_OBF__aa1) int))))
  (infix_mnmngt (tuple21 (tuple21 int enum_OBF__aa1) int) enum_OBF__ii1
  (add enum_OBF__ii1 (t2tb10 x) (t2tb5 empty3))
  (add (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb7 y) (t2tb2 empty6)))) :pattern (
  (tb2t107
  (add (tuple21 enum_OBF__ii1 (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 enum_OBF__ii1 (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb10 x)
  (t2tb7 y))
  (empty (tuple21 enum_OBF__ii1 (tuple21 (tuple21 int enum_OBF__aa1) int)))))) )))

(declare-fun t2tb110 ((set (set (tuple2 enum_OBF__ii
  (tuple2 (tuple2 (tuple2 Int Int) Int) Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 enum_OBF__ii (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int)))))) (sort
  (set1
  (set1
  (tuple21 enum_OBF__ii1 (tuple21 (tuple21 (tuple21 int int) int) int))))
  (t2tb110 x))))

(declare-fun tb2t110 (uni) (set (set (tuple2 enum_OBF__ii
  (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 enum_OBF__ii (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int)))))) (! (= (tb2t110 (t2tb110 i)) i) :pattern ((t2tb110 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb110 (tb2t110 j)) j) :pattern ((t2tb110 (tb2t110 j))) )))

(declare-fun t2tb111 ((set (tuple2 enum_OBF__ii (tuple2 (tuple2 (tuple2 Int
  Int) Int) Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 enum_OBF__ii (tuple2 (tuple2 (tuple2 Int Int) Int)
  Int))))) (sort
  (set1
  (tuple21 enum_OBF__ii1 (tuple21 (tuple21 (tuple21 int int) int) int)))
  (t2tb111 x))))

(declare-fun tb2t111 (uni) (set (tuple2 enum_OBF__ii
  (tuple2 (tuple2 (tuple2 Int Int) Int) Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 enum_OBF__ii (tuple2 (tuple2 (tuple2 Int Int) Int)
  Int))))) (! (= (tb2t111 (t2tb111 i)) i) :pattern ((t2tb111 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb111 (tb2t111 j)) j) :pattern ((t2tb111 (tb2t111 j))) )))

(declare-fun t2tb112 ((tuple2 enum_OBF__ii (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 enum_OBF__ii (tuple2 (tuple2 (tuple2 Int Int) Int)
  Int)))) (sort
  (tuple21 enum_OBF__ii1 (tuple21 (tuple21 (tuple21 int int) int) int))
  (t2tb112 x))))

(declare-fun tb2t112 (uni) (tuple2 enum_OBF__ii (tuple2 (tuple2 (tuple2 Int
  Int) Int) Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 enum_OBF__ii (tuple2 (tuple2 (tuple2 Int Int) Int)
  Int)))) (! (= (tb2t112 (t2tb112 i)) i) :pattern ((t2tb112 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb112 (tb2t112 j)) j) :pattern ((t2tb112 (tb2t112 j))) )))

;; singleton_is_function
  (assert
  (forall ((x enum_OBF__ii) (y (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (! (mem
  (set1
  (tuple21 enum_OBF__ii1 (tuple21 (tuple21 (tuple21 int int) int) int)))
  (add (tuple21 enum_OBF__ii1 (tuple21 (tuple21 (tuple21 int int) int) int))
  (Tuple2 enum_OBF__ii1 (tuple21 (tuple21 (tuple21 int int) int) int)
  (t2tb10 x) (t2tb8 y))
  (empty
  (tuple21 enum_OBF__ii1 (tuple21 (tuple21 (tuple21 int int) int) int))))
  (infix_mnmngt (tuple21 (tuple21 (tuple21 int int) int) int) enum_OBF__ii1
  (add enum_OBF__ii1 (t2tb10 x) (t2tb5 empty3))
  (add (tuple21 (tuple21 (tuple21 int int) int) int) (t2tb8 y)
  (t2tb3 empty5)))) :pattern ((tb2t111
                              (add
                              (tuple21 enum_OBF__ii1
                              (tuple21 (tuple21 (tuple21 int int) int) int))
                              (Tuple2 enum_OBF__ii1
                              (tuple21 (tuple21 (tuple21 int int) int) int)
                              (t2tb10 x) (t2tb8 y))
                              (empty
                              (tuple21 enum_OBF__ii1
                              (tuple21 (tuple21 (tuple21 int int) int) int)))))) )))

(declare-fun t2tb113 ((set (set (tuple2 enum_OBF__ii (tuple2 (tuple2 Int Int)
  Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 enum_OBF__ii (tuple2 (tuple2 Int Int)
  Int)))))) (sort
  (set1 (set1 (tuple21 enum_OBF__ii1 (tuple21 (tuple21 int int) int))))
  (t2tb113 x))))

(declare-fun tb2t113 (uni) (set (set (tuple2 enum_OBF__ii (tuple2 (tuple2 Int
  Int) Int)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 enum_OBF__ii (tuple2 (tuple2 Int Int)
  Int)))))) (! (= (tb2t113 (t2tb113 i)) i) :pattern ((t2tb113 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb113 (tb2t113 j)) j) :pattern ((t2tb113 (tb2t113 j))) )))

(declare-fun t2tb114 ((set (tuple2 enum_OBF__ii (tuple2 (tuple2 Int Int)
  Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 enum_OBF__ii (tuple2 (tuple2 Int Int) Int)))))
  (sort (set1 (tuple21 enum_OBF__ii1 (tuple21 (tuple21 int int) int)))
  (t2tb114 x))))

(declare-fun tb2t114 (uni) (set (tuple2 enum_OBF__ii (tuple2 (tuple2 Int Int)
  Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 enum_OBF__ii (tuple2 (tuple2 Int Int) Int)))))
  (! (= (tb2t114 (t2tb114 i)) i) :pattern ((t2tb114 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb114 (tb2t114 j)) j) :pattern ((t2tb114 (tb2t114 j))) )))

(declare-fun t2tb115 ((tuple2 enum_OBF__ii (tuple2 (tuple2 Int Int)
  Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 enum_OBF__ii (tuple2 (tuple2 Int Int) Int)))) (sort
  (tuple21 enum_OBF__ii1 (tuple21 (tuple21 int int) int)) (t2tb115 x))))

(declare-fun tb2t115 (uni) (tuple2 enum_OBF__ii (tuple2 (tuple2 Int Int)
  Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 enum_OBF__ii (tuple2 (tuple2 Int Int) Int))))
  (! (= (tb2t115 (t2tb115 i)) i) :pattern ((t2tb115 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb115 (tb2t115 j)) j) :pattern ((t2tb115 (tb2t115 j))) )))

;; singleton_is_function
  (assert
  (forall ((x enum_OBF__ii) (y (tuple2 (tuple2 Int Int) Int))) (! (mem
  (set1 (tuple21 enum_OBF__ii1 (tuple21 (tuple21 int int) int)))
  (add (tuple21 enum_OBF__ii1 (tuple21 (tuple21 int int) int))
  (Tuple2 enum_OBF__ii1 (tuple21 (tuple21 int int) int) (t2tb10 x) (t2tb9 y))
  (empty (tuple21 enum_OBF__ii1 (tuple21 (tuple21 int int) int))))
  (infix_mnmngt (tuple21 (tuple21 int int) int) enum_OBF__ii1
  (add enum_OBF__ii1 (t2tb10 x) (t2tb5 empty3))
  (add (tuple21 (tuple21 int int) int) (t2tb9 y) (t2tb4 empty4)))) :pattern (
  (tb2t114
  (add (tuple21 enum_OBF__ii1 (tuple21 (tuple21 int int) int))
  (Tuple2 enum_OBF__ii1 (tuple21 (tuple21 int int) int) (t2tb10 x) (t2tb9 y))
  (empty (tuple21 enum_OBF__ii1 (tuple21 (tuple21 int int) int)))))) )))

(declare-fun t2tb119 ((set (set (tuple2 enum_OBF__ii enum_OBF__ii)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 enum_OBF__ii enum_OBF__ii))))) (sort
  (set1 (set1 (tuple21 enum_OBF__ii1 enum_OBF__ii1))) (t2tb119 x))))

(declare-fun tb2t119 (uni) (set (set (tuple2 enum_OBF__ii enum_OBF__ii))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 enum_OBF__ii enum_OBF__ii)))))
  (! (= (tb2t119 (t2tb119 i)) i) :pattern ((t2tb119 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (set1 (tuple21 enum_OBF__ii1 enum_OBF__ii1))) j)
     (= (t2tb119 (tb2t119 j)) j)) :pattern ((t2tb119 (tb2t119 j))) )))

(declare-fun t2tb120 ((set (tuple2 enum_OBF__ii enum_OBF__ii))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 enum_OBF__ii enum_OBF__ii)))) (sort
  (set1 (tuple21 enum_OBF__ii1 enum_OBF__ii1)) (t2tb120 x))))

(declare-fun tb2t120 (uni) (set (tuple2 enum_OBF__ii enum_OBF__ii)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 enum_OBF__ii enum_OBF__ii))))
  (! (= (tb2t120 (t2tb120 i)) i) :pattern ((t2tb120 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (tuple21 enum_OBF__ii1 enum_OBF__ii1)) j)
     (= (t2tb120 (tb2t120 j)) j)) :pattern ((t2tb120 (tb2t120 j))) )))

(declare-fun t2tb121 ((tuple2 enum_OBF__ii enum_OBF__ii)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 enum_OBF__ii enum_OBF__ii))) (sort
  (tuple21 enum_OBF__ii1 enum_OBF__ii1) (t2tb121 x))))

(declare-fun tb2t121 (uni) (tuple2 enum_OBF__ii enum_OBF__ii))

;; BridgeL
  (assert
  (forall ((i (tuple2 enum_OBF__ii enum_OBF__ii)))
  (! (= (tb2t121 (t2tb121 i)) i) :pattern ((t2tb121 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (tuple21 enum_OBF__ii1 enum_OBF__ii1) j)
     (= (t2tb121 (tb2t121 j)) j)) :pattern ((t2tb121 (tb2t121 j))) )))

;; singleton_is_function
  (assert
  (forall ((x enum_OBF__ii) (y enum_OBF__ii)) (! (mem
  (set1 (tuple21 enum_OBF__ii1 enum_OBF__ii1))
  (add (tuple21 enum_OBF__ii1 enum_OBF__ii1)
  (Tuple2 enum_OBF__ii1 enum_OBF__ii1 (t2tb10 x) (t2tb10 y))
  (empty (tuple21 enum_OBF__ii1 enum_OBF__ii1)))
  (infix_mnmngt enum_OBF__ii1 enum_OBF__ii1
  (add enum_OBF__ii1 (t2tb10 x) (t2tb5 empty3))
  (add enum_OBF__ii1 (t2tb10 y) (t2tb5 empty3)))) :pattern ((tb2t120
                                                            (add
                                                            (tuple21
                                                            enum_OBF__ii1
                                                            enum_OBF__ii1)
                                                            (Tuple2
                                                            enum_OBF__ii1
                                                            enum_OBF__ii1
                                                            (t2tb10 x)
                                                            (t2tb10 y))
                                                            (empty
                                                            (tuple21
                                                            enum_OBF__ii1
                                                            enum_OBF__ii1))))) )))

(declare-fun t2tb122 ((set (set (tuple2 enum_OBF__ii (tuple2 Int
  Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 enum_OBF__ii (tuple2 Int Int)))))) (sort
  (set1 (set1 (tuple21 enum_OBF__ii1 (tuple21 int int)))) (t2tb122 x))))

(declare-fun tb2t122 (uni) (set (set (tuple2 enum_OBF__ii (tuple2 Int
  Int)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 enum_OBF__ii (tuple2 Int Int))))))
  (! (= (tb2t122 (t2tb122 i)) i) :pattern ((t2tb122 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb122 (tb2t122 j)) j) :pattern ((t2tb122 (tb2t122 j))) )))

(declare-fun t2tb123 ((set (tuple2 enum_OBF__ii (tuple2 Int Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 enum_OBF__ii (tuple2 Int Int))))) (sort
  (set1 (tuple21 enum_OBF__ii1 (tuple21 int int))) (t2tb123 x))))

(declare-fun tb2t123 (uni) (set (tuple2 enum_OBF__ii (tuple2 Int Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 enum_OBF__ii (tuple2 Int Int)))))
  (! (= (tb2t123 (t2tb123 i)) i) :pattern ((t2tb123 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb123 (tb2t123 j)) j) :pattern ((t2tb123 (tb2t123 j))) )))

(declare-fun t2tb124 ((tuple2 enum_OBF__ii (tuple2 Int Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 enum_OBF__ii (tuple2 Int Int)))) (sort
  (tuple21 enum_OBF__ii1 (tuple21 int int)) (t2tb124 x))))

(declare-fun tb2t124 (uni) (tuple2 enum_OBF__ii (tuple2 Int Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 enum_OBF__ii (tuple2 Int Int))))
  (! (= (tb2t124 (t2tb124 i)) i) :pattern ((t2tb124 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb124 (tb2t124 j)) j) :pattern ((t2tb124 (tb2t124 j))) )))

;; singleton_is_function
  (assert
  (forall ((x enum_OBF__ii) (y (tuple2 Int Int))) (! (mem
  (set1 (tuple21 enum_OBF__ii1 (tuple21 int int)))
  (add (tuple21 enum_OBF__ii1 (tuple21 int int))
  (Tuple2 enum_OBF__ii1 (tuple21 int int) (t2tb10 x) (t2tb11 y))
  (empty (tuple21 enum_OBF__ii1 (tuple21 int int))))
  (infix_mnmngt (tuple21 int int) enum_OBF__ii1
  (add enum_OBF__ii1 (t2tb10 x) (t2tb5 empty3))
  (add (tuple21 int int) (t2tb11 y) (t2tb6 empty2)))) :pattern ((tb2t123
                                                                (add
                                                                (tuple21
                                                                enum_OBF__ii1
                                                                (tuple21 
                                                                int int))
                                                                (Tuple2
                                                                enum_OBF__ii1
                                                                (tuple21 
                                                                int int)
                                                                (t2tb10 x)
                                                                (t2tb11 y))
                                                                (empty
                                                                (tuple21
                                                                enum_OBF__ii1
                                                                (tuple21 
                                                                int int)))))) )))

(declare-fun t2tb125 ((tuple2 enum_OBF__ii Int)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 enum_OBF__ii Int))) (sort (tuple21 enum_OBF__ii1 int)
  (t2tb125 x))))

(declare-fun tb2t125 (uni) (tuple2 enum_OBF__ii Int))

;; BridgeL
  (assert
  (forall ((i (tuple2 enum_OBF__ii Int)))
  (! (= (tb2t125 (t2tb125 i)) i) :pattern ((t2tb125 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb125 (tb2t125 j)) j) :pattern ((t2tb125 (tb2t125 j))) )))

(declare-fun t2tb126 ((set (set (tuple2 enum_OBF__ii Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 enum_OBF__ii Int))))) (sort
  (set1 (set1 (tuple21 enum_OBF__ii1 int))) (t2tb126 x))))

(declare-fun tb2t126 (uni) (set (set (tuple2 enum_OBF__ii Int))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 enum_OBF__ii Int)))))
  (! (= (tb2t126 (t2tb126 i)) i) :pattern ((t2tb126 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb126 (tb2t126 j)) j) :pattern ((t2tb126 (tb2t126 j))) )))

(declare-fun t2tb127 ((set (tuple2 enum_OBF__ii Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 enum_OBF__ii Int)))) (sort
  (set1 (tuple21 enum_OBF__ii1 int)) (t2tb127 x))))

(declare-fun tb2t127 (uni) (set (tuple2 enum_OBF__ii Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 enum_OBF__ii Int))))
  (! (= (tb2t127 (t2tb127 i)) i) :pattern ((t2tb127 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb127 (tb2t127 j)) j) :pattern ((t2tb127 (tb2t127 j))) )))

;; singleton_is_function
  (assert
  (forall ((x enum_OBF__ii) (y Int)) (! (mem
  (set1 (tuple21 enum_OBF__ii1 int))
  (add (tuple21 enum_OBF__ii1 int)
  (Tuple2 enum_OBF__ii1 int (t2tb10 x) (t2tb12 y))
  (empty (tuple21 enum_OBF__ii1 int)))
  (infix_mnmngt int enum_OBF__ii1
  (add enum_OBF__ii1 (t2tb10 x) (t2tb5 empty3))
  (add int (t2tb12 y) (t2tb1 empty1)))) :pattern ((tb2t127
                                                  (add
                                                  (tuple21 enum_OBF__ii1 int)
                                                  (Tuple2 enum_OBF__ii1 
                                                  int (t2tb10 x) (t2tb12 y))
                                                  (empty
                                                  (tuple21 enum_OBF__ii1 int))))) )))

;; singleton_is_function
  (assert
  (forall ((b ty))
  (forall ((x enum_OBF__ii) (y uni)) (! (mem (set1 (tuple21 enum_OBF__ii1 b))
  (add (tuple21 enum_OBF__ii1 b) (Tuple2 enum_OBF__ii1 b (t2tb10 x) y)
  (empty (tuple21 enum_OBF__ii1 b)))
  (infix_mnmngt b enum_OBF__ii1 (add enum_OBF__ii1 (t2tb10 x) (t2tb5 empty3))
  (add b y (empty b)))) :pattern ((add (tuple21 enum_OBF__ii1 b)
                                  (Tuple2 enum_OBF__ii1 b (t2tb10 x) y)
                                  (empty (tuple21 enum_OBF__ii1 b)))) ))))

(declare-fun t2tb128 ((set (tuple2 (tuple2 Int Int) (tuple2 (tuple2 Int
  enum_OBF__aa) Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Int Int) (tuple2 (tuple2 Int enum_OBF__aa)
  Int))))) (sort
  (set1
  (tuple21 (tuple21 int int) (tuple21 (tuple21 int enum_OBF__aa1) int)))
  (t2tb128 x))))

(declare-fun tb2t128 (uni) (set (tuple2 (tuple2 Int Int) (tuple2 (tuple2 Int
  enum_OBF__aa) Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Int Int) (tuple2 (tuple2 Int enum_OBF__aa)
  Int))))) (! (= (tb2t128 (t2tb128 i)) i) :pattern ((t2tb128 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb128 (tb2t128 j)) j) :pattern ((t2tb128 (tb2t128 j))) )))

(declare-fun t2tb129 ((tuple2 (tuple2 Int Int) (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 Int Int) (tuple2 (tuple2 Int enum_OBF__aa)
  Int)))) (sort
  (tuple21 (tuple21 int int) (tuple21 (tuple21 int enum_OBF__aa1) int))
  (t2tb129 x))))

(declare-fun tb2t129 (uni) (tuple2 (tuple2 Int Int) (tuple2 (tuple2 Int
  enum_OBF__aa) Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 Int Int) (tuple2 (tuple2 Int enum_OBF__aa)
  Int)))) (! (= (tb2t129 (t2tb129 i)) i) :pattern ((t2tb129 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb129 (tb2t129 j)) j) :pattern ((t2tb129 (tb2t129 j))) )))

(declare-fun t2tb130 ((set (set (tuple2 (tuple2 Int Int) (tuple2 (tuple2 Int
  enum_OBF__aa) Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 Int Int) (tuple2 (tuple2 Int
  enum_OBF__aa) Int)))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 int int) (tuple21 (tuple21 int enum_OBF__aa1) int))))
  (t2tb130 x))))

(declare-fun tb2t130 (uni) (set (set (tuple2 (tuple2 Int Int)
  (tuple2 (tuple2 Int enum_OBF__aa) Int)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 Int Int) (tuple2 (tuple2 Int
  enum_OBF__aa) Int))))))
  (! (= (tb2t130 (t2tb130 i)) i) :pattern ((t2tb130 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb130 (tb2t130 j)) j) :pattern ((t2tb130 (tb2t130 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 Int Int)) (y (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (! (mem
  (set1
  (tuple21 (tuple21 int int) (tuple21 (tuple21 int enum_OBF__aa1) int)))
  (add (tuple21 (tuple21 int int) (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 (tuple21 int int) (tuple21 (tuple21 int enum_OBF__aa1) int)
  (t2tb11 x) (t2tb7 y))
  (empty
  (tuple21 (tuple21 int int) (tuple21 (tuple21 int enum_OBF__aa1) int))))
  (infix_mnmngt (tuple21 (tuple21 int enum_OBF__aa1) int) (tuple21 int int)
  (add (tuple21 int int) (t2tb11 x) (t2tb6 empty2))
  (add (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb7 y) (t2tb2 empty6)))) :pattern (
  (tb2t128
  (add (tuple21 (tuple21 int int) (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 (tuple21 int int) (tuple21 (tuple21 int enum_OBF__aa1) int)
  (t2tb11 x) (t2tb7 y))
  (empty
  (tuple21 (tuple21 int int) (tuple21 (tuple21 int enum_OBF__aa1) int)))))) )))

(declare-fun t2tb131 ((set (tuple2 (tuple2 Int Int)
  (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Int Int) (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))))) (sort
  (set1
  (tuple21 (tuple21 int int) (tuple21 (tuple21 (tuple21 int int) int) int)))
  (t2tb131 x))))

(declare-fun tb2t131 (uni) (set (tuple2 (tuple2 Int Int)
  (tuple2 (tuple2 (tuple2 Int Int) Int) Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Int Int) (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))))) (! (= (tb2t131 (t2tb131 i)) i) :pattern ((t2tb131 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb131 (tb2t131 j)) j) :pattern ((t2tb131 (tb2t131 j))) )))

(declare-fun t2tb132 ((tuple2 (tuple2 Int Int) (tuple2 (tuple2 (tuple2 Int
  Int) Int) Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 Int Int) (tuple2 (tuple2 (tuple2 Int Int) Int)
  Int)))) (sort
  (tuple21 (tuple21 int int) (tuple21 (tuple21 (tuple21 int int) int) int))
  (t2tb132 x))))

(declare-fun tb2t132 (uni) (tuple2 (tuple2 Int Int)
  (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 Int Int) (tuple2 (tuple2 (tuple2 Int Int) Int)
  Int)))) (! (= (tb2t132 (t2tb132 i)) i) :pattern ((t2tb132 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb132 (tb2t132 j)) j) :pattern ((t2tb132 (tb2t132 j))) )))

(declare-fun t2tb133 ((set (set (tuple2 (tuple2 Int Int)
  (tuple2 (tuple2 (tuple2 Int Int) Int) Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 Int Int) (tuple2 (tuple2 (tuple2 Int
  Int) Int) Int)))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 int int) (tuple21 (tuple21 (tuple21 int int) int) int))))
  (t2tb133 x))))

(declare-fun tb2t133 (uni) (set (set (tuple2 (tuple2 Int Int)
  (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 Int Int) (tuple2 (tuple2 (tuple2 Int
  Int) Int) Int))))))
  (! (= (tb2t133 (t2tb133 i)) i) :pattern ((t2tb133 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb133 (tb2t133 j)) j) :pattern ((t2tb133 (tb2t133 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 Int Int)) (y (tuple2 (tuple2 (tuple2 Int Int) Int)
  Int))) (! (mem
  (set1
  (tuple21 (tuple21 int int) (tuple21 (tuple21 (tuple21 int int) int) int)))
  (add
  (tuple21 (tuple21 int int) (tuple21 (tuple21 (tuple21 int int) int) int))
  (Tuple2 (tuple21 int int) (tuple21 (tuple21 (tuple21 int int) int) int)
  (t2tb11 x) (t2tb8 y))
  (empty
  (tuple21 (tuple21 int int) (tuple21 (tuple21 (tuple21 int int) int) int))))
  (infix_mnmngt (tuple21 (tuple21 (tuple21 int int) int) int)
  (tuple21 int int) (add (tuple21 int int) (t2tb11 x) (t2tb6 empty2))
  (add (tuple21 (tuple21 (tuple21 int int) int) int) (t2tb8 y)
  (t2tb3 empty5)))) :pattern ((tb2t131
                              (add
                              (tuple21 (tuple21 int int)
                              (tuple21 (tuple21 (tuple21 int int) int) int))
                              (Tuple2 (tuple21 int int)
                              (tuple21 (tuple21 (tuple21 int int) int) int)
                              (t2tb11 x) (t2tb8 y))
                              (empty
                              (tuple21 (tuple21 int int)
                              (tuple21 (tuple21 (tuple21 int int) int) int)))))) )))

(declare-fun t2tb134 ((set (tuple2 (tuple2 Int Int) (tuple2 (tuple2 Int Int)
  Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Int Int) (tuple2 (tuple2 Int Int) Int)))))
  (sort (set1 (tuple21 (tuple21 int int) (tuple21 (tuple21 int int) int)))
  (t2tb134 x))))

(declare-fun tb2t134 (uni) (set (tuple2 (tuple2 Int Int) (tuple2 (tuple2 Int
  Int) Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Int Int) (tuple2 (tuple2 Int Int) Int)))))
  (! (= (tb2t134 (t2tb134 i)) i) :pattern ((t2tb134 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb134 (tb2t134 j)) j) :pattern ((t2tb134 (tb2t134 j))) )))

(declare-fun t2tb135 ((tuple2 (tuple2 Int Int) (tuple2 (tuple2 Int Int)
  Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 Int Int) (tuple2 (tuple2 Int Int) Int)))) (sort
  (tuple21 (tuple21 int int) (tuple21 (tuple21 int int) int)) (t2tb135 x))))

(declare-fun tb2t135 (uni) (tuple2 (tuple2 Int Int) (tuple2 (tuple2 Int Int)
  Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 Int Int) (tuple2 (tuple2 Int Int) Int))))
  (! (= (tb2t135 (t2tb135 i)) i) :pattern ((t2tb135 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb135 (tb2t135 j)) j) :pattern ((t2tb135 (tb2t135 j))) )))

(declare-fun t2tb136 ((set (set (tuple2 (tuple2 Int Int) (tuple2 (tuple2 Int
  Int) Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 Int Int) (tuple2 (tuple2 Int Int)
  Int)))))) (sort
  (set1 (set1 (tuple21 (tuple21 int int) (tuple21 (tuple21 int int) int))))
  (t2tb136 x))))

(declare-fun tb2t136 (uni) (set (set (tuple2 (tuple2 Int Int)
  (tuple2 (tuple2 Int Int) Int)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 Int Int) (tuple2 (tuple2 Int Int)
  Int)))))) (! (= (tb2t136 (t2tb136 i)) i) :pattern ((t2tb136 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb136 (tb2t136 j)) j) :pattern ((t2tb136 (tb2t136 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 Int Int)) (y (tuple2 (tuple2 Int Int) Int))) (! (mem
  (set1 (tuple21 (tuple21 int int) (tuple21 (tuple21 int int) int)))
  (add (tuple21 (tuple21 int int) (tuple21 (tuple21 int int) int))
  (Tuple2 (tuple21 int int) (tuple21 (tuple21 int int) int) (t2tb11 x)
  (t2tb9 y))
  (empty (tuple21 (tuple21 int int) (tuple21 (tuple21 int int) int))))
  (infix_mnmngt (tuple21 (tuple21 int int) int) (tuple21 int int)
  (add (tuple21 int int) (t2tb11 x) (t2tb6 empty2))
  (add (tuple21 (tuple21 int int) int) (t2tb9 y) (t2tb4 empty4)))) :pattern (
  (tb2t134
  (add (tuple21 (tuple21 int int) (tuple21 (tuple21 int int) int))
  (Tuple2 (tuple21 int int) (tuple21 (tuple21 int int) int) (t2tb11 x)
  (t2tb9 y))
  (empty (tuple21 (tuple21 int int) (tuple21 (tuple21 int int) int)))))) )))

(declare-fun t2tb140 ((set (tuple2 (tuple2 Int Int) enum_OBF__ii))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Int Int) enum_OBF__ii)))) (sort
  (set1 (tuple21 (tuple21 int int) enum_OBF__ii1)) (t2tb140 x))))

(declare-fun tb2t140 (uni) (set (tuple2 (tuple2 Int Int) enum_OBF__ii)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Int Int) enum_OBF__ii))))
  (! (= (tb2t140 (t2tb140 i)) i) :pattern ((t2tb140 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb140 (tb2t140 j)) j) :pattern ((t2tb140 (tb2t140 j))) )))

(declare-fun t2tb141 ((tuple2 (tuple2 Int Int) enum_OBF__ii)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 Int Int) enum_OBF__ii))) (sort
  (tuple21 (tuple21 int int) enum_OBF__ii1) (t2tb141 x))))

(declare-fun tb2t141 (uni) (tuple2 (tuple2 Int Int) enum_OBF__ii))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 Int Int) enum_OBF__ii)))
  (! (= (tb2t141 (t2tb141 i)) i) :pattern ((t2tb141 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb141 (tb2t141 j)) j) :pattern ((t2tb141 (tb2t141 j))) )))

(declare-fun t2tb142 ((set (set (tuple2 (tuple2 Int Int)
  enum_OBF__ii)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 Int Int) enum_OBF__ii))))) (sort
  (set1 (set1 (tuple21 (tuple21 int int) enum_OBF__ii1))) (t2tb142 x))))

(declare-fun tb2t142 (uni) (set (set (tuple2 (tuple2 Int Int)
  enum_OBF__ii))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 Int Int) enum_OBF__ii)))))
  (! (= (tb2t142 (t2tb142 i)) i) :pattern ((t2tb142 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb142 (tb2t142 j)) j) :pattern ((t2tb142 (tb2t142 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 Int Int)) (y enum_OBF__ii)) (! (mem
  (set1 (tuple21 (tuple21 int int) enum_OBF__ii1))
  (add (tuple21 (tuple21 int int) enum_OBF__ii1)
  (Tuple2 (tuple21 int int) enum_OBF__ii1 (t2tb11 x) (t2tb10 y))
  (empty (tuple21 (tuple21 int int) enum_OBF__ii1)))
  (infix_mnmngt enum_OBF__ii1 (tuple21 int int)
  (add (tuple21 int int) (t2tb11 x) (t2tb6 empty2))
  (add enum_OBF__ii1 (t2tb10 y) (t2tb5 empty3)))) :pattern ((tb2t140
                                                            (add
                                                            (tuple21
                                                            (tuple21 int int)
                                                            enum_OBF__ii1)
                                                            (Tuple2
                                                            (tuple21 int int)
                                                            enum_OBF__ii1
                                                            (t2tb11 x)
                                                            (t2tb10 y))
                                                            (empty
                                                            (tuple21
                                                            (tuple21 int int)
                                                            enum_OBF__ii1))))) )))

(declare-fun t2tb143 ((set (set (tuple2 (tuple2 Int Int) (tuple2 Int
  Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 Int Int) (tuple2 Int Int)))))) (sort
  (set1 (set1 (tuple21 (tuple21 int int) (tuple21 int int)))) (t2tb143 x))))

(declare-fun tb2t143 (uni) (set (set (tuple2 (tuple2 Int Int) (tuple2 Int
  Int)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 Int Int) (tuple2 Int Int))))))
  (! (= (tb2t143 (t2tb143 i)) i) :pattern ((t2tb143 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb143 (tb2t143 j)) j) :pattern ((t2tb143 (tb2t143 j))) )))

(declare-fun t2tb144 ((set (tuple2 (tuple2 Int Int) (tuple2 Int Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Int Int) (tuple2 Int Int))))) (sort
  (set1 (tuple21 (tuple21 int int) (tuple21 int int))) (t2tb144 x))))

(declare-fun tb2t144 (uni) (set (tuple2 (tuple2 Int Int) (tuple2 Int Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Int Int) (tuple2 Int Int)))))
  (! (= (tb2t144 (t2tb144 i)) i) :pattern ((t2tb144 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb144 (tb2t144 j)) j) :pattern ((t2tb144 (tb2t144 j))) )))

(declare-fun t2tb145 ((tuple2 (tuple2 Int Int) (tuple2 Int Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 Int Int) (tuple2 Int Int)))) (sort
  (tuple21 (tuple21 int int) (tuple21 int int)) (t2tb145 x))))

(declare-fun tb2t145 (uni) (tuple2 (tuple2 Int Int) (tuple2 Int Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 Int Int) (tuple2 Int Int))))
  (! (= (tb2t145 (t2tb145 i)) i) :pattern ((t2tb145 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb145 (tb2t145 j)) j) :pattern ((t2tb145 (tb2t145 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 Int Int)) (y (tuple2 Int Int))) (! (mem
  (set1 (tuple21 (tuple21 int int) (tuple21 int int)))
  (add (tuple21 (tuple21 int int) (tuple21 int int))
  (Tuple2 (tuple21 int int) (tuple21 int int) (t2tb11 x) (t2tb11 y))
  (empty (tuple21 (tuple21 int int) (tuple21 int int))))
  (infix_mnmngt (tuple21 int int) (tuple21 int int)
  (add (tuple21 int int) (t2tb11 x) (t2tb6 empty2))
  (add (tuple21 int int) (t2tb11 y) (t2tb6 empty2)))) :pattern ((tb2t144
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
                                                                (t2tb11 x)
                                                                (t2tb11 y))
                                                                (empty
                                                                (tuple21
                                                                (tuple21 
                                                                int int)
                                                                (tuple21 
                                                                int int)))))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 Int Int)) (y Int)) (! (mem
  (set1 (tuple21 (tuple21 int int) int))
  (add (tuple21 (tuple21 int int) int)
  (Tuple2 (tuple21 int int) int (t2tb11 x) (t2tb12 y)) (t2tb4 empty4))
  (infix_mnmngt int (tuple21 int int)
  (add (tuple21 int int) (t2tb11 x) (t2tb6 empty2))
  (add int (t2tb12 y) (t2tb1 empty1)))) :pattern ((tb2t4
                                                  (add
                                                  (tuple21 (tuple21 int int)
                                                  int)
                                                  (Tuple2 (tuple21 int int)
                                                  int (t2tb11 x) (t2tb12 y))
                                                  (t2tb4 empty4)))) )))

;; singleton_is_function
  (assert
  (forall ((b ty))
  (forall ((x (tuple2 Int Int)) (y uni)) (! (mem
  (set1 (tuple21 (tuple21 int int) b))
  (add (tuple21 (tuple21 int int) b)
  (Tuple2 (tuple21 int int) b (t2tb11 x) y)
  (empty (tuple21 (tuple21 int int) b)))
  (infix_mnmngt b (tuple21 int int)
  (add (tuple21 int int) (t2tb11 x) (t2tb6 empty2)) (add b y (empty b)))) :pattern (
  (add (tuple21 (tuple21 int int) b)
  (Tuple2 (tuple21 int int) b (t2tb11 x) y)
  (empty (tuple21 (tuple21 int int) b)))) ))))

(declare-fun t2tb146 ((set (set (tuple2 Int (tuple2 (tuple2 Int enum_OBF__aa)
  Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Int (tuple2 (tuple2 Int enum_OBF__aa)
  Int)))))) (sort
  (set1 (set1 (tuple21 int (tuple21 (tuple21 int enum_OBF__aa1) int))))
  (t2tb146 x))))

(declare-fun tb2t146 (uni) (set (set (tuple2 Int (tuple2 (tuple2 Int
  enum_OBF__aa) Int)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Int (tuple2 (tuple2 Int enum_OBF__aa)
  Int)))))) (! (= (tb2t146 (t2tb146 i)) i) :pattern ((t2tb146 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb146 (tb2t146 j)) j) :pattern ((t2tb146 (tb2t146 j))) )))

(declare-fun t2tb147 ((set (tuple2 Int (tuple2 (tuple2 Int enum_OBF__aa)
  Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int (tuple2 (tuple2 Int enum_OBF__aa) Int)))))
  (sort (set1 (tuple21 int (tuple21 (tuple21 int enum_OBF__aa1) int)))
  (t2tb147 x))))

(declare-fun tb2t147 (uni) (set (tuple2 Int (tuple2 (tuple2 Int enum_OBF__aa)
  Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int (tuple2 (tuple2 Int enum_OBF__aa) Int)))))
  (! (= (tb2t147 (t2tb147 i)) i) :pattern ((t2tb147 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb147 (tb2t147 j)) j) :pattern ((t2tb147 (tb2t147 j))) )))

(declare-fun t2tb148 ((tuple2 Int (tuple2 (tuple2 Int enum_OBF__aa)
  Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Int (tuple2 (tuple2 Int enum_OBF__aa) Int)))) (sort
  (tuple21 int (tuple21 (tuple21 int enum_OBF__aa1) int)) (t2tb148 x))))

(declare-fun tb2t148 (uni) (tuple2 Int (tuple2 (tuple2 Int enum_OBF__aa)
  Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 Int (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (! (= (tb2t148 (t2tb148 i)) i) :pattern ((t2tb148 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb148 (tb2t148 j)) j) :pattern ((t2tb148 (tb2t148 j))) )))

;; singleton_is_function
  (assert
  (forall ((x Int) (y (tuple2 (tuple2 Int enum_OBF__aa) Int))) (! (mem
  (set1 (tuple21 int (tuple21 (tuple21 int enum_OBF__aa1) int)))
  (add (tuple21 int (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 int (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb12 x) (t2tb7 y))
  (empty (tuple21 int (tuple21 (tuple21 int enum_OBF__aa1) int))))
  (infix_mnmngt (tuple21 (tuple21 int enum_OBF__aa1) int) int
  (add int (t2tb12 x) (t2tb1 empty1))
  (add (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb7 y) (t2tb2 empty6)))) :pattern (
  (tb2t147
  (add (tuple21 int (tuple21 (tuple21 int enum_OBF__aa1) int))
  (Tuple2 int (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb12 x) (t2tb7 y))
  (empty (tuple21 int (tuple21 (tuple21 int enum_OBF__aa1) int)))))) )))

(declare-fun t2tb149 ((set (set (tuple2 Int (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Int (tuple2 (tuple2 (tuple2 Int Int) Int)
  Int)))))) (sort
  (set1 (set1 (tuple21 int (tuple21 (tuple21 (tuple21 int int) int) int))))
  (t2tb149 x))))

(declare-fun tb2t149 (uni) (set (set (tuple2 Int (tuple2 (tuple2 (tuple2 Int
  Int) Int) Int)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Int (tuple2 (tuple2 (tuple2 Int Int) Int)
  Int)))))) (! (= (tb2t149 (t2tb149 i)) i) :pattern ((t2tb149 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb149 (tb2t149 j)) j) :pattern ((t2tb149 (tb2t149 j))) )))

(declare-fun t2tb150 ((set (tuple2 Int (tuple2 (tuple2 (tuple2 Int Int) Int)
  Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))))
  (sort (set1 (tuple21 int (tuple21 (tuple21 (tuple21 int int) int) int)))
  (t2tb150 x))))

(declare-fun tb2t150 (uni) (set (tuple2 Int (tuple2 (tuple2 (tuple2 Int Int)
  Int) Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))))
  (! (= (tb2t150 (t2tb150 i)) i) :pattern ((t2tb150 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb150 (tb2t150 j)) j) :pattern ((t2tb150 (tb2t150 j))) )))

(declare-fun t2tb151 ((tuple2 Int (tuple2 (tuple2 (tuple2 Int Int) Int)
  Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Int (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))) (sort
  (tuple21 int (tuple21 (tuple21 (tuple21 int int) int) int)) (t2tb151 x))))

(declare-fun tb2t151 (uni) (tuple2 Int (tuple2 (tuple2 (tuple2 Int Int) Int)
  Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 Int (tuple2 (tuple2 (tuple2 Int Int) Int) Int))))
  (! (= (tb2t151 (t2tb151 i)) i) :pattern ((t2tb151 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb151 (tb2t151 j)) j) :pattern ((t2tb151 (tb2t151 j))) )))

;; singleton_is_function
  (assert
  (forall ((x Int) (y (tuple2 (tuple2 (tuple2 Int Int) Int) Int))) (! (mem
  (set1 (tuple21 int (tuple21 (tuple21 (tuple21 int int) int) int)))
  (add (tuple21 int (tuple21 (tuple21 (tuple21 int int) int) int))
  (Tuple2 int (tuple21 (tuple21 (tuple21 int int) int) int) (t2tb12 x)
  (t2tb8 y))
  (empty (tuple21 int (tuple21 (tuple21 (tuple21 int int) int) int))))
  (infix_mnmngt (tuple21 (tuple21 (tuple21 int int) int) int) int
  (add int (t2tb12 x) (t2tb1 empty1))
  (add (tuple21 (tuple21 (tuple21 int int) int) int) (t2tb8 y)
  (t2tb3 empty5)))) :pattern ((tb2t150
                              (add
                              (tuple21 int
                              (tuple21 (tuple21 (tuple21 int int) int) int))
                              (Tuple2 int
                              (tuple21 (tuple21 (tuple21 int int) int) int)
                              (t2tb12 x) (t2tb8 y))
                              (empty
                              (tuple21 int
                              (tuple21 (tuple21 (tuple21 int int) int) int)))))) )))

(declare-fun t2tb152 ((tuple2 Int (tuple2 (tuple2 Int Int) Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Int (tuple2 (tuple2 Int Int) Int)))) (sort
  (tuple21 int (tuple21 (tuple21 int int) int)) (t2tb152 x))))

(declare-fun tb2t152 (uni) (tuple2 Int (tuple2 (tuple2 Int Int) Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 Int (tuple2 (tuple2 Int Int) Int))))
  (! (= (tb2t152 (t2tb152 i)) i) :pattern ((t2tb152 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb152 (tb2t152 j)) j) :pattern ((t2tb152 (tb2t152 j))) )))

(declare-fun t2tb153 ((set (set (tuple2 Int (tuple2 (tuple2 Int Int)
  Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Int (tuple2 (tuple2 Int Int) Int)))))) (sort
  (set1 (set1 (tuple21 int (tuple21 (tuple21 int int) int)))) (t2tb153 x))))

(declare-fun tb2t153 (uni) (set (set (tuple2 Int (tuple2 (tuple2 Int Int)
  Int)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Int (tuple2 (tuple2 Int Int) Int))))))
  (! (= (tb2t153 (t2tb153 i)) i) :pattern ((t2tb153 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb153 (tb2t153 j)) j) :pattern ((t2tb153 (tb2t153 j))) )))

(declare-fun t2tb154 ((set (tuple2 Int (tuple2 (tuple2 Int Int) Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int (tuple2 (tuple2 Int Int) Int))))) (sort
  (set1 (tuple21 int (tuple21 (tuple21 int int) int))) (t2tb154 x))))

(declare-fun tb2t154 (uni) (set (tuple2 Int (tuple2 (tuple2 Int Int) Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int (tuple2 (tuple2 Int Int) Int)))))
  (! (= (tb2t154 (t2tb154 i)) i) :pattern ((t2tb154 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb154 (tb2t154 j)) j) :pattern ((t2tb154 (tb2t154 j))) )))

;; singleton_is_function
  (assert
  (forall ((x Int) (y (tuple2 (tuple2 Int Int) Int))) (! (mem
  (set1 (tuple21 int (tuple21 (tuple21 int int) int)))
  (add (tuple21 int (tuple21 (tuple21 int int) int))
  (Tuple2 int (tuple21 (tuple21 int int) int) (t2tb12 x) (t2tb9 y))
  (empty (tuple21 int (tuple21 (tuple21 int int) int))))
  (infix_mnmngt (tuple21 (tuple21 int int) int) int
  (add int (t2tb12 x) (t2tb1 empty1))
  (add (tuple21 (tuple21 int int) int) (t2tb9 y) (t2tb4 empty4)))) :pattern (
  (tb2t154
  (add (tuple21 int (tuple21 (tuple21 int int) int))
  (Tuple2 int (tuple21 (tuple21 int int) int) (t2tb12 x) (t2tb9 y))
  (empty (tuple21 int (tuple21 (tuple21 int int) int)))))) )))

(declare-fun t2tb155 ((set (tuple2 Int enum_OBF__ii))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int enum_OBF__ii)))) (sort
  (set1 (tuple21 int enum_OBF__ii1)) (t2tb155 x))))

(declare-fun tb2t155 (uni) (set (tuple2 Int enum_OBF__ii)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int enum_OBF__ii))))
  (! (= (tb2t155 (t2tb155 i)) i) :pattern ((t2tb155 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb155 (tb2t155 j)) j) :pattern ((t2tb155 (tb2t155 j))) )))

(declare-fun t2tb156 ((tuple2 Int enum_OBF__ii)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Int enum_OBF__ii))) (sort (tuple21 int enum_OBF__ii1)
  (t2tb156 x))))

(declare-fun tb2t156 (uni) (tuple2 Int enum_OBF__ii))

;; BridgeL
  (assert
  (forall ((i (tuple2 Int enum_OBF__ii)))
  (! (= (tb2t156 (t2tb156 i)) i) :pattern ((t2tb156 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb156 (tb2t156 j)) j) :pattern ((t2tb156 (tb2t156 j))) )))

(declare-fun t2tb157 ((set (set (tuple2 Int enum_OBF__ii)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Int enum_OBF__ii))))) (sort
  (set1 (set1 (tuple21 int enum_OBF__ii1))) (t2tb157 x))))

(declare-fun tb2t157 (uni) (set (set (tuple2 Int enum_OBF__ii))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Int enum_OBF__ii)))))
  (! (= (tb2t157 (t2tb157 i)) i) :pattern ((t2tb157 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb157 (tb2t157 j)) j) :pattern ((t2tb157 (tb2t157 j))) )))

;; singleton_is_function
  (assert
  (forall ((x Int) (y enum_OBF__ii)) (! (mem
  (set1 (tuple21 int enum_OBF__ii1))
  (add (tuple21 int enum_OBF__ii1)
  (Tuple2 int enum_OBF__ii1 (t2tb12 x) (t2tb10 y))
  (empty (tuple21 int enum_OBF__ii1)))
  (infix_mnmngt enum_OBF__ii1 int (add int (t2tb12 x) (t2tb1 empty1))
  (add enum_OBF__ii1 (t2tb10 y) (t2tb5 empty3)))) :pattern ((tb2t155
                                                            (add
                                                            (tuple21 
                                                            int
                                                            enum_OBF__ii1)
                                                            (Tuple2 int
                                                            enum_OBF__ii1
                                                            (t2tb12 x)
                                                            (t2tb10 y))
                                                            (empty
                                                            (tuple21 
                                                            int
                                                            enum_OBF__ii1))))) )))

(declare-fun t2tb158 ((set (set (tuple2 Int (tuple2 Int Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Int (tuple2 Int Int)))))) (sort
  (set1 (set1 (tuple21 int (tuple21 int int)))) (t2tb158 x))))

(declare-fun tb2t158 (uni) (set (set (tuple2 Int (tuple2 Int Int)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Int (tuple2 Int Int))))))
  (! (= (tb2t158 (t2tb158 i)) i) :pattern ((t2tb158 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb158 (tb2t158 j)) j) :pattern ((t2tb158 (tb2t158 j))) )))

(declare-fun t2tb159 ((set (tuple2 Int (tuple2 Int Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int (tuple2 Int Int))))) (sort
  (set1 (tuple21 int (tuple21 int int))) (t2tb159 x))))

(declare-fun tb2t159 (uni) (set (tuple2 Int (tuple2 Int Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int (tuple2 Int Int)))))
  (! (= (tb2t159 (t2tb159 i)) i) :pattern ((t2tb159 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb159 (tb2t159 j)) j) :pattern ((t2tb159 (tb2t159 j))) )))

(declare-fun t2tb160 ((tuple2 Int (tuple2 Int Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Int (tuple2 Int Int)))) (sort
  (tuple21 int (tuple21 int int)) (t2tb160 x))))

(declare-fun tb2t160 (uni) (tuple2 Int (tuple2 Int Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 Int (tuple2 Int Int))))
  (! (= (tb2t160 (t2tb160 i)) i) :pattern ((t2tb160 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb160 (tb2t160 j)) j) :pattern ((t2tb160 (tb2t160 j))) )))

;; singleton_is_function
  (assert
  (forall ((x Int) (y (tuple2 Int Int))) (! (mem
  (set1 (tuple21 int (tuple21 int int)))
  (add (tuple21 int (tuple21 int int))
  (Tuple2 int (tuple21 int int) (t2tb12 x) (t2tb11 y))
  (empty (tuple21 int (tuple21 int int))))
  (infix_mnmngt (tuple21 int int) int (add int (t2tb12 x) (t2tb1 empty1))
  (add (tuple21 int int) (t2tb11 y) (t2tb6 empty2)))) :pattern ((tb2t159
                                                                (add
                                                                (tuple21 
                                                                int
                                                                (tuple21 
                                                                int int))
                                                                (Tuple2 
                                                                int
                                                                (tuple21 
                                                                int int)
                                                                (t2tb12 x)
                                                                (t2tb11 y))
                                                                (empty
                                                                (tuple21 
                                                                int
                                                                (tuple21 
                                                                int int)))))) )))

;; singleton_is_function
  (assert
  (forall ((x Int) (y Int)) (! (mem (set1 (tuple21 int int))
  (add (tuple21 int int) (Tuple2 int int (t2tb12 x) (t2tb12 y))
  (t2tb6 empty2))
  (infix_mnmngt int int (add int (t2tb12 x) (t2tb1 empty1))
  (add int (t2tb12 y) (t2tb1 empty1)))) :pattern ((tb2t6
                                                  (add (tuple21 int int)
                                                  (Tuple2 int int (t2tb12 x)
                                                  (t2tb12 y)) (t2tb6 empty2)))) )))

;; singleton_is_function
  (assert
  (forall ((b ty))
  (forall ((x Int) (y uni)) (! (mem (set1 (tuple21 int b))
  (add (tuple21 int b) (Tuple2 int b (t2tb12 x) y) (empty (tuple21 int b)))
  (infix_mnmngt b int (add int (t2tb12 x) (t2tb1 empty1))
  (add b y (empty b)))) :pattern ((add (tuple21 int b)
                                  (Tuple2 int b (t2tb12 x) y)
                                  (empty (tuple21 int b)))) ))))

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
  (forall ((x (tuple2 Int enum_OBF__aa)) (y Int))
  (= (tb2t12
     (apply int (tuple21 int enum_OBF__aa1)
     (add (tuple21 (tuple21 int enum_OBF__aa1) int)
     (Tuple2 (tuple21 int enum_OBF__aa1) int (t2tb31 x) (t2tb12 y))
     (t2tb2 empty6)) (t2tb31 x))) y)))

;; apply_singleton
  (assert
  (forall ((x (tuple2 (tuple2 Int Int) Int)) (y Int))
  (= (tb2t12
     (apply int (tuple21 (tuple21 int int) int)
     (add (tuple21 (tuple21 (tuple21 int int) int) int)
     (Tuple2 (tuple21 (tuple21 int int) int) int (t2tb9 x) (t2tb12 y))
     (t2tb3 empty5)) (t2tb9 x))) y)))

;; apply_singleton
  (assert
  (forall ((x (tuple2 Int Int)) (y Int))
  (= (tb2t12
     (apply int (tuple21 int int)
     (add (tuple21 (tuple21 int int) int)
     (Tuple2 (tuple21 int int) int (t2tb11 x) (t2tb12 y)) (t2tb4 empty4))
     (t2tb11 x))) y)))

;; apply_singleton
  (assert
  (forall ((x Int) (y Int))
  (= (tb2t12
     (apply int int
     (add (tuple21 int int) (Tuple2 int int (t2tb12 x) (t2tb12 y))
     (t2tb6 empty2)) (t2tb12 x))) y)))

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
  (forall ((s (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (is_finite_subset (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 empty6)
  (t2tb2 s) 0)))

;; Empty
  (assert
  (forall ((s (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int))))
  (is_finite_subset (tuple21 (tuple21 (tuple21 int int) int) int)
  (t2tb3 empty5) (t2tb3 s) 0)))

;; Empty
  (assert
  (forall ((s (set (tuple2 (tuple2 Int Int) Int)))) (is_finite_subset
  (tuple21 (tuple21 int int) int) (t2tb4 empty4) (t2tb4 s) 0)))

;; Empty
  (assert
  (forall ((s (set enum_OBF__ii))) (is_finite_subset enum_OBF__ii1
  (t2tb5 empty3) (t2tb5 s) 0)))

;; Empty
  (assert
  (forall ((s (set (tuple2 Int Int)))) (is_finite_subset (tuple21 int int)
  (t2tb6 empty2) (t2tb6 s) 0)))

;; Empty
  (assert
  (forall ((s (set Int))) (is_finite_subset int (t2tb1 empty1) (t2tb1 s) 0)))

;; Empty
  (assert
  (forall ((a ty)) (forall ((s uni)) (is_finite_subset a (empty a) s 0))))

;; Add_mem
  (assert
  (forall ((a ty))
  (forall ((x uni) (s1 uni) (s2 uni) (c Int))
  (=> (is_finite_subset a s1 s2 c)
  (=> (mem a x s2) (=> (mem a x s1) (is_finite_subset a (add a x s1) s2 c)))))))

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
  (=> (is_finite_subset (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 z)
  (t2tb2 z1) z2)
  (or
  (or
  (exists ((s (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (and (and (= z empty6) (= z1 s)) (= z2 0)))
  (exists ((x (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (s1 (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (s2 (set (tuple2 (tuple2 Int enum_OBF__aa) Int))) (c Int))
  (and (is_finite_subset (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 s1)
  (t2tb2 s2) c)
  (and (mem (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb7 x) (t2tb2 s2))
  (and (mem (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb7 x) (t2tb2 s1))
  (and
  (and
  (= z (tb2t2
       (add (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb7 x) (t2tb2 s1))))
  (= z1 s2)) (= z2 c)))))))
  (exists ((x (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (s1 (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (s2 (set (tuple2 (tuple2 Int enum_OBF__aa) Int))) (c Int))
  (and (is_finite_subset (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 s1)
  (t2tb2 s2) c)
  (and (mem (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb7 x) (t2tb2 s2))
  (and
  (not (mem (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb7 x) (t2tb2 s1)))
  (and
  (and
  (= z (tb2t2
       (add (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb7 x) (t2tb2 s1))))
  (= z1 s2)) (= z2 (+ c 1)))))))))))

;; is_finite_subset_inversion
  (assert
  (forall ((z (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (z1 (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int))) (z2 Int))
  (=> (is_finite_subset (tuple21 (tuple21 (tuple21 int int) int) int)
  (t2tb3 z) (t2tb3 z1) z2)
  (or
  (or
  (exists ((s (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int))))
  (and (and (= z empty5) (= z1 s)) (= z2 0)))
  (exists ((x (tuple2 (tuple2 (tuple2 Int Int) Int) Int))
  (s1 (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (s2 (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int))) (c Int))
  (and (is_finite_subset (tuple21 (tuple21 (tuple21 int int) int) int)
  (t2tb3 s1) (t2tb3 s2) c)
  (and (mem (tuple21 (tuple21 (tuple21 int int) int) int) (t2tb8 x)
  (t2tb3 s2))
  (and (mem (tuple21 (tuple21 (tuple21 int int) int) int) (t2tb8 x)
  (t2tb3 s1))
  (and
  (and
  (= z (tb2t3
       (add (tuple21 (tuple21 (tuple21 int int) int) int) (t2tb8 x)
       (t2tb3 s1))))
  (= z1 s2)) (= z2 c)))))))
  (exists ((x (tuple2 (tuple2 (tuple2 Int Int) Int) Int))
  (s1 (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (s2 (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int))) (c Int))
  (and (is_finite_subset (tuple21 (tuple21 (tuple21 int int) int) int)
  (t2tb3 s1) (t2tb3 s2) c)
  (and (mem (tuple21 (tuple21 (tuple21 int int) int) int) (t2tb8 x)
  (t2tb3 s2))
  (and
  (not (mem (tuple21 (tuple21 (tuple21 int int) int) int) (t2tb8 x)
  (t2tb3 s1)))
  (and
  (and
  (= z (tb2t3
       (add (tuple21 (tuple21 (tuple21 int int) int) int) (t2tb8 x)
       (t2tb3 s1))))
  (= z1 s2)) (= z2 (+ c 1)))))))))))

;; is_finite_subset_inversion
  (assert
  (forall ((z (set (tuple2 (tuple2 Int Int) Int)))
  (z1 (set (tuple2 (tuple2 Int Int) Int))) (z2 Int))
  (=> (is_finite_subset (tuple21 (tuple21 int int) int) (t2tb4 z) (t2tb4 z1)
  z2)
  (or
  (or
  (exists ((s (set (tuple2 (tuple2 Int Int) Int))))
  (and (and (= z empty4) (= z1 s)) (= z2 0)))
  (exists ((x (tuple2 (tuple2 Int Int) Int)) (s1 (set (tuple2 (tuple2 Int
  Int) Int))) (s2 (set (tuple2 (tuple2 Int Int) Int))) (c Int))
  (and (is_finite_subset (tuple21 (tuple21 int int) int) (t2tb4 s1)
  (t2tb4 s2) c)
  (and (mem (tuple21 (tuple21 int int) int) (t2tb9 x) (t2tb4 s2))
  (and (mem (tuple21 (tuple21 int int) int) (t2tb9 x) (t2tb4 s1))
  (and
  (and
  (= z (tb2t4 (add (tuple21 (tuple21 int int) int) (t2tb9 x) (t2tb4 s1))))
  (= z1 s2)) (= z2 c)))))))
  (exists ((x (tuple2 (tuple2 Int Int) Int)) (s1 (set (tuple2 (tuple2 Int
  Int) Int))) (s2 (set (tuple2 (tuple2 Int Int) Int))) (c Int))
  (and (is_finite_subset (tuple21 (tuple21 int int) int) (t2tb4 s1)
  (t2tb4 s2) c)
  (and (mem (tuple21 (tuple21 int int) int) (t2tb9 x) (t2tb4 s2))
  (and (not (mem (tuple21 (tuple21 int int) int) (t2tb9 x) (t2tb4 s1)))
  (and
  (and
  (= z (tb2t4 (add (tuple21 (tuple21 int int) int) (t2tb9 x) (t2tb4 s1))))
  (= z1 s2)) (= z2 (+ c 1)))))))))))

;; is_finite_subset_inversion
  (assert
  (forall ((z (set enum_OBF__ii)) (z1 (set enum_OBF__ii)) (z2 Int))
  (=> (is_finite_subset enum_OBF__ii1 (t2tb5 z) (t2tb5 z1) z2)
  (or
  (or
  (exists ((s (set enum_OBF__ii)))
  (and (and (= z empty3) (= z1 s)) (= z2 0)))
  (exists ((x enum_OBF__ii) (s1 (set enum_OBF__ii)) (s2 (set enum_OBF__ii))
  (c Int))
  (and (is_finite_subset enum_OBF__ii1 (t2tb5 s1) (t2tb5 s2) c)
  (and (mem enum_OBF__ii1 (t2tb10 x) (t2tb5 s2))
  (and (mem enum_OBF__ii1 (t2tb10 x) (t2tb5 s1))
  (and
  (and (= z (tb2t5 (add enum_OBF__ii1 (t2tb10 x) (t2tb5 s1)))) (= z1 s2))
  (= z2 c)))))))
  (exists ((x enum_OBF__ii) (s1 (set enum_OBF__ii)) (s2 (set enum_OBF__ii))
  (c Int))
  (and (is_finite_subset enum_OBF__ii1 (t2tb5 s1) (t2tb5 s2) c)
  (and (mem enum_OBF__ii1 (t2tb10 x) (t2tb5 s2))
  (and (not (mem enum_OBF__ii1 (t2tb10 x) (t2tb5 s1)))
  (and
  (and (= z (tb2t5 (add enum_OBF__ii1 (t2tb10 x) (t2tb5 s1)))) (= z1 s2))
  (= z2 (+ c 1)))))))))))

;; is_finite_subset_inversion
  (assert
  (forall ((z (set (tuple2 Int Int))) (z1 (set (tuple2 Int Int))) (z2 Int))
  (=> (is_finite_subset (tuple21 int int) (t2tb6 z) (t2tb6 z1) z2)
  (or
  (or
  (exists ((s (set (tuple2 Int Int))))
  (and (and (= z empty2) (= z1 s)) (= z2 0)))
  (exists ((x (tuple2 Int Int)) (s1 (set (tuple2 Int Int)))
  (s2 (set (tuple2 Int Int))) (c Int))
  (and (is_finite_subset (tuple21 int int) (t2tb6 s1) (t2tb6 s2) c)
  (and (mem (tuple21 int int) (t2tb11 x) (t2tb6 s2))
  (and (mem (tuple21 int int) (t2tb11 x) (t2tb6 s1))
  (and
  (and (= z (tb2t6 (add (tuple21 int int) (t2tb11 x) (t2tb6 s1)))) (= z1 s2))
  (= z2 c)))))))
  (exists ((x (tuple2 Int Int)) (s1 (set (tuple2 Int Int)))
  (s2 (set (tuple2 Int Int))) (c Int))
  (and (is_finite_subset (tuple21 int int) (t2tb6 s1) (t2tb6 s2) c)
  (and (mem (tuple21 int int) (t2tb11 x) (t2tb6 s2))
  (and (not (mem (tuple21 int int) (t2tb11 x) (t2tb6 s1)))
  (and
  (and (= z (tb2t6 (add (tuple21 int int) (t2tb11 x) (t2tb6 s1)))) (= z1 s2))
  (= z2 (+ c 1)))))))))))

;; is_finite_subset_inversion
  (assert
  (forall ((z (set Int)) (z1 (set Int)) (z2 Int))
  (=> (is_finite_subset int (t2tb1 z) (t2tb1 z1) z2)
  (or
  (or (exists ((s (set Int))) (and (and (= z empty1) (= z1 s)) (= z2 0)))
  (exists ((x Int) (s1 (set Int)) (s2 (set Int)) (c Int))
  (and (is_finite_subset int (t2tb1 s1) (t2tb1 s2) c)
  (and (mem int (t2tb12 x) (t2tb1 s2))
  (and (mem int (t2tb12 x) (t2tb1 s1))
  (and (and (= z (tb2t1 (add int (t2tb12 x) (t2tb1 s1)))) (= z1 s2))
  (= z2 c)))))))
  (exists ((x Int) (s1 (set Int)) (s2 (set Int)) (c Int))
  (and (is_finite_subset int (t2tb1 s1) (t2tb1 s2) c)
  (and (mem int (t2tb12 x) (t2tb1 s2))
  (and (not (mem int (t2tb12 x) (t2tb1 s1)))
  (and (and (= z (tb2t1 (add int (t2tb12 x) (t2tb1 s1)))) (= z1 s2))
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
  (forall ((s (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))) (mem
  (set1 (tuple21 (tuple21 int enum_OBF__aa1) int)) (t2tb2 empty6)
  (finite_subsets (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 s)))))

;; finite_Empty
  (assert
  (forall ((s (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))) (mem
  (set1 (tuple21 (tuple21 (tuple21 int int) int) int)) (t2tb3 empty5)
  (finite_subsets (tuple21 (tuple21 (tuple21 int int) int) int) (t2tb3 s)))))

;; finite_Empty
  (assert
  (forall ((s (set (tuple2 (tuple2 Int Int) Int)))) (mem
  (set1 (tuple21 (tuple21 int int) int)) (t2tb4 empty4)
  (finite_subsets (tuple21 (tuple21 int int) int) (t2tb4 s)))))

;; finite_Empty
  (assert
  (forall ((s (set enum_OBF__ii))) (mem (set1 enum_OBF__ii1) (t2tb5 empty3)
  (finite_subsets enum_OBF__ii1 (t2tb5 s)))))

;; finite_Empty
  (assert
  (forall ((s (set (tuple2 Int Int)))) (mem (set1 (tuple21 int int))
  (t2tb6 empty2) (finite_subsets (tuple21 int int) (t2tb6 s)))))

;; finite_Empty
  (assert
  (forall ((s (set Int))) (mem (set1 int) (t2tb1 empty1)
  (finite_subsets int (t2tb1 s)))))

;; finite_Empty
  (assert
  (forall ((a ty))
  (forall ((s uni)) (mem (set1 a) (empty a) (finite_subsets a s)))))

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
  (forall ((s1 (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (s2 (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (=> (mem (set1 (tuple21 (tuple21 int enum_OBF__aa1) int)) (t2tb2 s1)
  (finite_subsets (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 s2)))
  (or (= s1 empty6)
  (exists ((x (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (s3 (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (and
  (= s1 (tb2t2
        (add (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb7 x) (t2tb2 s3))))
  (mem (set1 (tuple21 (tuple21 int enum_OBF__aa1) int)) (t2tb2 s3)
  (finite_subsets (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 s2)))))))))

;; finite_inversion
  (assert
  (forall ((s1 (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (s2 (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int))))
  (=> (mem (set1 (tuple21 (tuple21 (tuple21 int int) int) int)) (t2tb3 s1)
  (finite_subsets (tuple21 (tuple21 (tuple21 int int) int) int) (t2tb3 s2)))
  (or (= s1 empty5)
  (exists ((x (tuple2 (tuple2 (tuple2 Int Int) Int) Int))
  (s3 (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int))))
  (and
  (= s1 (tb2t3
        (add (tuple21 (tuple21 (tuple21 int int) int) int) (t2tb8 x)
        (t2tb3 s3))))
  (mem (set1 (tuple21 (tuple21 (tuple21 int int) int) int)) (t2tb3 s3)
  (finite_subsets (tuple21 (tuple21 (tuple21 int int) int) int) (t2tb3 s2)))))))))

;; finite_inversion
  (assert
  (forall ((s1 (set (tuple2 (tuple2 Int Int) Int)))
  (s2 (set (tuple2 (tuple2 Int Int) Int))))
  (=> (mem (set1 (tuple21 (tuple21 int int) int)) (t2tb4 s1)
  (finite_subsets (tuple21 (tuple21 int int) int) (t2tb4 s2)))
  (or (= s1 empty4)
  (exists ((x (tuple2 (tuple2 Int Int) Int)) (s3 (set (tuple2 (tuple2 Int
  Int) Int))))
  (and
  (= s1 (tb2t4 (add (tuple21 (tuple21 int int) int) (t2tb9 x) (t2tb4 s3))))
  (mem (set1 (tuple21 (tuple21 int int) int)) (t2tb4 s3)
  (finite_subsets (tuple21 (tuple21 int int) int) (t2tb4 s2)))))))))

;; finite_inversion
  (assert
  (forall ((s1 (set enum_OBF__ii)) (s2 (set enum_OBF__ii)))
  (=> (mem (set1 enum_OBF__ii1) (t2tb5 s1)
  (finite_subsets enum_OBF__ii1 (t2tb5 s2)))
  (or (= s1 empty3)
  (exists ((x enum_OBF__ii) (s3 (set enum_OBF__ii)))
  (and (= s1 (tb2t5 (add enum_OBF__ii1 (t2tb10 x) (t2tb5 s3)))) (mem
  (set1 enum_OBF__ii1) (t2tb5 s3) (finite_subsets enum_OBF__ii1 (t2tb5 s2)))))))))

;; finite_inversion
  (assert
  (forall ((s1 (set (tuple2 Int Int))) (s2 (set (tuple2 Int Int))))
  (=> (mem (set1 (tuple21 int int)) (t2tb6 s1)
  (finite_subsets (tuple21 int int) (t2tb6 s2)))
  (or (= s1 empty2)
  (exists ((x (tuple2 Int Int)) (s3 (set (tuple2 Int Int))))
  (and (= s1 (tb2t6 (add (tuple21 int int) (t2tb11 x) (t2tb6 s3)))) (mem
  (set1 (tuple21 int int)) (t2tb6 s3)
  (finite_subsets (tuple21 int int) (t2tb6 s2)))))))))

;; finite_inversion
  (assert
  (forall ((s1 (set Int)) (s2 (set Int)))
  (=> (mem (set1 int) (t2tb1 s1) (finite_subsets int (t2tb1 s2)))
  (or (= s1 empty1)
  (exists ((x Int) (s3 (set Int)))
  (and (= s1 (tb2t1 (add int (t2tb12 x) (t2tb1 s3)))) (mem (set1 int)
  (t2tb1 s3) (finite_subsets int (t2tb1 s2)))))))))

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
  (forall ((s (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (x (set (tuple2 (tuple2 Int enum_OBF__aa) Int))))
  (= (mem (set1 (tuple21 (tuple21 int enum_OBF__aa1) int)) (t2tb2 x)
  (non_empty_finite_subsets (tuple21 (tuple21 int enum_OBF__aa1) int)
  (t2tb2 s)))
  (exists ((c Int))
  (and (is_finite_subset (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 x)
  (t2tb2 s) c) (not (= x empty6)))))))

;; non_empty_finite_subsets_def
  (assert
  (forall ((s (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (x (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int))))
  (= (mem (set1 (tuple21 (tuple21 (tuple21 int int) int) int)) (t2tb3 x)
  (non_empty_finite_subsets (tuple21 (tuple21 (tuple21 int int) int) int)
  (t2tb3 s)))
  (exists ((c Int))
  (and (is_finite_subset (tuple21 (tuple21 (tuple21 int int) int) int)
  (t2tb3 x) (t2tb3 s) c) (not (= x empty5)))))))

;; non_empty_finite_subsets_def
  (assert
  (forall ((s (set (tuple2 (tuple2 Int Int) Int)))
  (x (set (tuple2 (tuple2 Int Int) Int))))
  (= (mem (set1 (tuple21 (tuple21 int int) int)) (t2tb4 x)
  (non_empty_finite_subsets (tuple21 (tuple21 int int) int) (t2tb4 s)))
  (exists ((c Int))
  (and (is_finite_subset (tuple21 (tuple21 int int) int) (t2tb4 x) (t2tb4 s)
  c) (not (= x empty4)))))))

;; non_empty_finite_subsets_def
  (assert
  (forall ((s (set enum_OBF__ii)) (x (set enum_OBF__ii)))
  (= (mem (set1 enum_OBF__ii1) (t2tb5 x)
  (non_empty_finite_subsets enum_OBF__ii1 (t2tb5 s)))
  (exists ((c Int))
  (and (is_finite_subset enum_OBF__ii1 (t2tb5 x) (t2tb5 s) c)
  (not (= x empty3)))))))

;; non_empty_finite_subsets_def
  (assert
  (forall ((s (set (tuple2 Int Int))) (x (set (tuple2 Int Int))))
  (= (mem (set1 (tuple21 int int)) (t2tb6 x)
  (non_empty_finite_subsets (tuple21 int int) (t2tb6 s)))
  (exists ((c Int))
  (and (is_finite_subset (tuple21 int int) (t2tb6 x) (t2tb6 s) c)
  (not (= x empty2)))))))

;; non_empty_finite_subsets_def
  (assert
  (forall ((s (set Int)) (x (set Int)))
  (= (mem (set1 int) (t2tb1 x) (non_empty_finite_subsets int (t2tb1 s)))
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
  (assert
  (= (card (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 empty6)) 0))

;; card_Empty
  (assert
  (= (card (tuple21 (tuple21 (tuple21 int int) int) int) (t2tb3 empty5)) 0))

;; card_Empty
  (assert (= (card (tuple21 (tuple21 int int) int) (t2tb4 empty4)) 0))

;; card_Empty
  (assert (= (card enum_OBF__ii1 (t2tb5 empty3)) 0))

;; card_Empty
  (assert (= (card (tuple21 int int) (t2tb6 empty2)) 0))

;; card_Empty
  (assert (= (card int (t2tb1 empty1)) 0))

;; card_Empty
  (assert (forall ((a ty)) (= (card a (empty a)) 0)))

;; card_Add_not_mem
  (assert
  (forall ((a ty))
  (forall ((x uni) (s1 uni) (s2 uni))
  (! (=> (mem (set1 a) s1 (finite_subsets a s2))
     (=> (not (mem a x s1)) (= (card a (add a x s1)) (+ (card a s1) 1)))) :pattern ((mem
  (set1 a) s1 (finite_subsets a s2)) (card a (add a x s1))) ))))

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
  (forall ((s uni) (x uni) (y (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (! (=> (mem a x s)
     (= (tb2t7
        (apply (tuple21 (tuple21 int enum_OBF__aa1) int) a
        (times (tuple21 (tuple21 int enum_OBF__aa1) int) a s
        (add (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb7 y)
        (t2tb2 empty6))) x)) y)) :pattern ((tb2t7
                                           (apply
                                           (tuple21
                                           (tuple21 int enum_OBF__aa1) 
                                           int) a
                                           (times
                                           (tuple21
                                           (tuple21 int enum_OBF__aa1) 
                                           int) a s
                                           (add
                                           (tuple21
                                           (tuple21 int enum_OBF__aa1) 
                                           int) (t2tb7 y) (t2tb2 empty6))) x))) ))))

;; apply_times
  (assert
  (forall ((a ty))
  (forall ((s uni) (x uni) (y (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (! (=> (mem a x s)
     (= (tb2t8
        (apply (tuple21 (tuple21 (tuple21 int int) int) int) a
        (times (tuple21 (tuple21 (tuple21 int int) int) int) a s
        (add (tuple21 (tuple21 (tuple21 int int) int) int) (t2tb8 y)
        (t2tb3 empty5))) x)) y)) :pattern ((tb2t8
                                           (apply
                                           (tuple21
                                           (tuple21 (tuple21 int int) int)
                                           int) a
                                           (times
                                           (tuple21
                                           (tuple21 (tuple21 int int) int)
                                           int) a s
                                           (add
                                           (tuple21
                                           (tuple21 (tuple21 int int) int)
                                           int) (t2tb8 y) (t2tb3 empty5))) x))) ))))

;; apply_times
  (assert
  (forall ((a ty))
  (forall ((s uni) (x uni) (y (tuple2 (tuple2 Int Int) Int)))
  (! (=> (mem a x s)
     (= (tb2t9
        (apply (tuple21 (tuple21 int int) int) a
        (times (tuple21 (tuple21 int int) int) a s
        (add (tuple21 (tuple21 int int) int) (t2tb9 y) (t2tb4 empty4))) x)) y)) :pattern (
  (tb2t9
  (apply (tuple21 (tuple21 int int) int) a
  (times (tuple21 (tuple21 int int) int) a s
  (add (tuple21 (tuple21 int int) int) (t2tb9 y) (t2tb4 empty4))) x))) ))))

;; apply_times
  (assert
  (forall ((a ty))
  (forall ((s uni) (x uni) (y enum_OBF__ii))
  (! (=> (mem a x s)
     (= (tb2t10
        (apply enum_OBF__ii1 a
        (times enum_OBF__ii1 a s
        (add enum_OBF__ii1 (t2tb10 y) (t2tb5 empty3))) x)) y)) :pattern (
  (tb2t10
  (apply enum_OBF__ii1 a
  (times enum_OBF__ii1 a s (add enum_OBF__ii1 (t2tb10 y) (t2tb5 empty3))) x))) ))))

;; apply_times
  (assert
  (forall ((a ty))
  (forall ((s uni) (x uni) (y (tuple2 Int Int)))
  (! (=> (mem a x s)
     (= (tb2t11
        (apply (tuple21 int int) a
        (times (tuple21 int int) a s
        (add (tuple21 int int) (t2tb11 y) (t2tb6 empty2))) x)) y)) :pattern (
  (tb2t11
  (apply (tuple21 int int) a
  (times (tuple21 int int) a s
  (add (tuple21 int int) (t2tb11 y) (t2tb6 empty2))) x))) ))))

;; apply_times
  (assert
  (forall ((a ty))
  (forall ((s uni) (x uni) (y Int))
  (! (=> (mem a x s)
     (= (tb2t12
        (apply int a (times int a s (add int (t2tb12 y) (t2tb1 empty1))) x)) y)) :pattern (
  (tb2t12
  (apply int a (times int a s (add int (t2tb12 y) (t2tb1 empty1))) x))) ))))

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

(declare-fun t2tb161 ((set enum_OBF__aa)) uni)

;; t2tb_sort
  (assert
  (forall ((x (set enum_OBF__aa))) (sort (set1 enum_OBF__aa1) (t2tb161 x))))

(declare-fun tb2t161 (uni) (set enum_OBF__aa))

;; BridgeL
  (assert
  (forall ((i (set enum_OBF__aa)))
  (! (= (tb2t161 (t2tb161 i)) i) :pattern ((t2tb161 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 enum_OBF__aa1) j) (= (t2tb161 (tb2t161 j)) j)) :pattern (
  (t2tb161 (tb2t161 j))) )))

(declare-fun t2tb162 (enum_OBF__aa) uni)

;; t2tb_sort
  (assert (forall ((x enum_OBF__aa)) (sort enum_OBF__aa1 (t2tb162 x))))

(declare-fun tb2t162 (uni) enum_OBF__aa)

;; BridgeL
  (assert
  (forall ((i enum_OBF__aa))
  (! (= (tb2t162 (t2tb162 i)) i) :pattern ((t2tb162 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort enum_OBF__aa1 j) (= (t2tb162 (tb2t162 j)) j)) :pattern (
  (t2tb162 (tb2t162 j))) )))

;; set_enum_OBF__aa_axiom
  (assert
  (forall ((x enum_OBF__aa)) (mem enum_OBF__aa1 (t2tb162 x)
  (t2tb161 set_enum_OBF__aa))))

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

;; set_enum_OBF__ii_axiom
  (assert
  (forall ((x enum_OBF__ii)) (mem enum_OBF__ii1 (t2tb10 x)
  (t2tb5 set_enum_OBF__ii))))

(declare-fun f1 ((set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set Int)
  (set Int) (set (tuple2 Int Int)) Int Int (set Int) (set Int) (set Int) Int
  (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) Int (set Int)
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int)) Bool
  (set (tuple2 (tuple2 Int Int) Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) (set Int)
  (set (tuple2 Int Int)) Int Int (set Int) Int (set (tuple2 Int Int)) Int Int
  (set Int) (set (tuple2 Int Int)) Int (set Int) Int Int Int (set Int)
  (set Int) Int (set Int) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) Bool Int (set (tuple2 (tuple2 (tuple2 Int Int) Int)
  Int)) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Bool
  (set (tuple2 Int Int)) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set Int) Int (set (tuple2 Int Int)) (set enum_OBF__ii)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int (set (tuple2 Int
  Int)) (set Int) (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) (set (tuple2 Int Int)) (set enum_OBF__ii)
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) enum_OBF__aa (set Int)
  (set Int) (set (tuple2 (tuple2 Int Int) Int)) (set (tuple2 Int Int)) Int
  (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) Int (set Int) (set Int) Int (set Int) Int
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int
  Int)) Int (set (tuple2 Int Int)) Bool (set (tuple2 Int Int)) (set Int)
  (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int
  Int)) (set Int) Int) Bool)

(declare-fun t2tb163 ((set (tuple2 Int (tuple2 Int (tuple2 Int Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int (tuple2 Int (tuple2 Int Int)))))) (sort
  (set1 (tuple21 int (tuple21 int (tuple21 int int)))) (t2tb163 x))))

(declare-fun tb2t163 (uni) (set (tuple2 Int (tuple2 Int (tuple2 Int Int)))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int (tuple2 Int (tuple2 Int Int))))))
  (! (= (tb2t163 (t2tb163 i)) i) :pattern ((t2tb163 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb163 (tb2t163 j)) j) :pattern ((t2tb163 (tb2t163 j))) )))

;; f1_def
  (assert
  (forall ((v_OBF__zzee (set (tuple2 Int Int))) (v_OBF__zzdd (set (tuple2 Int
  Int))) (v_OBF__zzcc Int) (v_OBF__zzbb (set Int)) (v_OBF__zz (set Int))
  (v_OBF__yyee (set (tuple2 Int Int))) (v_OBF__yydd Int) (v_OBF__yycc Int)
  (v_OBF__yybb (set Int)) (v_OBF__yy (set Int)) (v_OBF__xxee (set Int))
  (v_OBF__xxdd Int) (v_OBF__xxcc (set (tuple2 Int Int))) (v_OBF__xxbb Int)
  (v_OBF__xx Int) (v_OBF__wwee (set (tuple2 Int Int))) (v_OBF__wwdd Int)
  (v_OBF__wwcc (set Int)) (v_OBF__wwbb (set (tuple2 Int Int)))
  (v_OBF__ww (set Int)) (v_OBF__vvee (set (tuple2 Int Int)))
  (v_OBF__vvdd Bool) (v_OBF__vvcc (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__vvbb (set (tuple2 Int Int))) (v_OBF__vv Int)
  (v_OBF__uuee (set (tuple2 Int Int))) (v_OBF__uudd Int) (v_OBF__uucc Int)
  (v_OBF__uubb (set (tuple2 Int Int))) (v_OBF__uu (set Int))
  (v_OBF__ttee (set (tuple2 Int Int))) (v_OBF__ttdd Int) (v_OBF__ttcc Int)
  (v_OBF__ttbb (set Int)) (v_OBF__tt Int) (v_OBF__ssee (set (tuple2 Int
  Int))) (v_OBF__ssdd Int) (v_OBF__sscc Int) (v_OBF__ssbb (set Int))
  (v_OBF__rree (set (tuple2 Int Int))) (v_OBF__rrdd Int)
  (v_OBF__rrcc (set Int)) (v_OBF__rrbb Int) (v_OBF__qqee Int)
  (v_OBF__qqdd Int) (v_OBF__qqcc (set Int)) (v_OBF__qqbb (set Int))
  (v_OBF__ppee Int) (v_OBF__ppdd (set Int)) (v_OBF__ppcc (set (tuple2 Int
  Int))) (v_OBF__ppbb (set Int)) (v_OBF__ooee Int)
  (v_OBF__oodd (set (tuple2 Int Int))) (v_OBF__oocc Bool) (v_OBF__oobb Int)
  (v_OBF__nnff (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__nnee (set Int)) (v_OBF__nndd (set (tuple2 Int Int)))
  (v_OBF__nncc (set (tuple2 Int Int))) (v_OBF__nnbb Int)
  (v_OBF__mmff (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__mmee (set Int)) (v_OBF__mmdd Bool) (v_OBF__mmcc (set (tuple2 Int
  Int))) (v_OBF__mmbb Int) (v_OBF__llff (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (v_OBF__llee (set Int)) (v_OBF__lldd Int)
  (v_OBF__llcc (set (tuple2 Int Int))) (v_OBF__llbb (set enum_OBF__ii))
  (v_OBF__kkff (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__kkee (set Int)) (v_OBF__kkdd Int) (v_OBF__kkcc (set (tuple2 Int
  Int))) (v_OBF__kkbb (set Int)) (v_OBF__jjff (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (v_OBF__jjee (set Int)) (v_OBF__jjdd Int)
  (v_OBF__jjcc (set (tuple2 Int Int))) (v_OBF__jjbb Int)
  (v_OBF__iiff (set (tuple2 Int Int))) (v_OBF__iiee (set Int))
  (v_OBF__iidd (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb Int)
  (v_OBF__hhff (set (tuple2 Int Int))) (v_OBF__hhee (set (tuple2 Int Int)))
  (v_OBF__hhdd (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__hhcc (set (tuple2 Int Int))) (v_OBF__hhbb (set enum_OBF__ii))
  (v_OBF__ggff (set (tuple2 Int Int))) (v_OBF__ggee (set (tuple2 Int Int)))
  (v_OBF__ggdd enum_OBF__aa) (v_OBF__ggcc (set Int)) (v_OBF__ggbb (set Int))
  (v_OBF__ffff (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__ffee (set (tuple2 Int Int))) (v_OBF__ffdd Int)
  (v_OBF__ffcc (set Int)) (v_OBF__ffbb Int) (v_OBF__eeff (set (tuple2 Int
  Int))) (v_OBF__eeee (set (tuple2 Int Int))) (v_OBF__eedd (set (tuple2 Int
  Int))) (v_OBF__eecc (set Int)) (v_OBF__eebb Int) (v_OBF__ddff (set Int))
  (v_OBF__ddee (set Int)) (v_OBF__dddd Int) (v_OBF__ddcc (set Int))
  (v_OBF__ddbb Int) (v_OBF__ccff (set (tuple2 Int Int)))
  (v_OBF__ccee (set Int)) (v_OBF__ccdd (set (tuple2 Int Int)))
  (v_OBF__cccc (set (tuple2 Int Int))) (v_OBF__ccbb Int)
  (v_OBF__bbff (set (tuple2 Int Int))) (v_OBF__bbee Bool)
  (v_OBF__bbdd (set (tuple2 Int Int))) (v_OBF__bbcc (set Int))
  (v_OBF__bbbb (set Int)) (v_OBF__aaff (set (tuple2 Int Int)))
  (v_OBF__aaee (set (tuple2 Int Int))) (v_OBF__aadd (set (tuple2 Int Int)))
  (v_OBF__aacc (set Int)) (v_OBF__aabb Int))
  (= (f1 v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb v_OBF__zz
  v_OBF__yyee v_OBF__yydd v_OBF__yycc v_OBF__yybb v_OBF__yy v_OBF__xxee
  v_OBF__xxdd v_OBF__xxcc v_OBF__xxbb v_OBF__xx v_OBF__wwee v_OBF__wwdd
  v_OBF__wwcc v_OBF__wwbb v_OBF__ww v_OBF__vvee v_OBF__vvdd v_OBF__vvcc
  v_OBF__vvbb v_OBF__vv v_OBF__uuee v_OBF__uudd v_OBF__uucc v_OBF__uubb
  v_OBF__uu v_OBF__ttee v_OBF__ttdd v_OBF__ttcc v_OBF__ttbb v_OBF__tt
  v_OBF__ssee v_OBF__ssdd v_OBF__sscc v_OBF__ssbb v_OBF__rree v_OBF__rrdd
  v_OBF__rrcc v_OBF__rrbb v_OBF__qqee v_OBF__qqdd v_OBF__qqcc v_OBF__qqbb
  v_OBF__ppee v_OBF__ppdd v_OBF__ppcc v_OBF__ppbb v_OBF__ooee v_OBF__oodd
  v_OBF__oocc v_OBF__oobb v_OBF__nnff v_OBF__nnee v_OBF__nndd v_OBF__nncc
  v_OBF__nnbb v_OBF__mmff v_OBF__mmee v_OBF__mmdd v_OBF__mmcc v_OBF__mmbb
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkff
  v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjff v_OBF__jjee
  v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iiff v_OBF__iiee v_OBF__iidd
  v_OBF__iicc v_OBF__iibb v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc
  v_OBF__hhbb v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb
  v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb v_OBF__eeff
  v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb v_OBF__ddff v_OBF__ddee
  v_OBF__dddd v_OBF__ddcc v_OBF__ddbb v_OBF__ccff v_OBF__ccee v_OBF__ccdd
  v_OBF__cccc v_OBF__ccbb v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc
  v_OBF__bbbb v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (mem (set1 (tuple21 int int)) (t2tb6 v_OBF__ttee)
  (relation int int (t2tb1 v_OBF__ddcc) (t2tb1 v_OBF__eecc))) (mem
  (set1 (tuple21 int int)) (t2tb6 v_OBF__uuee)
  (relation int int (t2tb1 v_OBF__ddcc) (t2tb1 v_OBF__eecc)))) (mem
  (set1 (tuple21 int int)) (t2tb6 v_OBF__vvee)
  (relation int int (t2tb1 v_OBF__ddcc) (t2tb1 v_OBF__bbbb)))) (mem
  (set1 (tuple21 int int)) (t2tb6 v_OBF__wwee)
  (relation int int (t2tb1 v_OBF__ddcc) (t2tb1 v_OBF__ffcc)))) (mem
  (set1 int) (t2tb1 v_OBF__xxee) (power int (t2tb1 v_OBF__ddcc))))
  (infix_eqeq2 v_OBF__yyee
  (tb2t6
  (image (tuple21 int int) int
  (ran (tuple21 int (tuple21 int int)) int
  (domain_restriction (tuple21 int (tuple21 int int)) int (t2tb1 v_OBF__xxee)
  (direct_product (tuple21 int int) int int (t2tb6 v_OBF__wwee)
  (direct_product int int int (t2tb6 v_OBF__ttee) (t2tb6 v_OBF__vvee)))))
  (add int (t2tb12 v_OBF__rrbb) (t2tb1 empty1)))))) (infix_eqeq2 v_OBF__zzee
  (tb2t6
  (image (tuple21 int int) int
  (ran (tuple21 int (tuple21 int int)) int
  (domain_restriction (tuple21 int (tuple21 int int)) int (t2tb1 v_OBF__xxee)
  (direct_product (tuple21 int int) int int (t2tb6 v_OBF__wwee)
  (direct_product int int int (t2tb6 v_OBF__ttee) (t2tb6 v_OBF__vvee)))))
  (add int (t2tb12 v_OBF__mmbb) (t2tb1 empty1)))))) (infix_eqeq2 v_OBF__oodd
  (tb2t6
  (image (tuple21 int int) int
  (ran (tuple21 int (tuple21 int int)) int
  (domain_restriction (tuple21 int (tuple21 int int)) int (t2tb1 v_OBF__xxee)
  (direct_product (tuple21 int int) int int (t2tb6 v_OBF__wwee)
  (direct_product int int int (t2tb6 v_OBF__ttee) (t2tb6 v_OBF__vvee)))))
  (add int (t2tb12 v_OBF__ffbb) (t2tb1 empty1)))))) (infix_eqeq2 v_OBF__nndd
  (tb2t6
  (image (tuple21 int int) int
  (ran (tuple21 int (tuple21 int int)) int
  (domain_restriction (tuple21 int (tuple21 int int)) int (t2tb1 v_OBF__xxee)
  (direct_product (tuple21 int int) int int (t2tb6 v_OBF__wwee)
  (direct_product int int int (t2tb6 v_OBF__uuee) (t2tb6 v_OBF__vvee)))))
  (add int (t2tb12 v_OBF__ffbb) (t2tb1 empty1)))))) (mem
  (set1 (tuple21 int int)) (t2tb6 v_OBF__uuee)
  (power (tuple21 int int) (t2tb6 v_OBF__ttee)))) (mem
  (set1 (tuple21 int int)) (t2tb6 v_OBF__vvee)
  (infix_plmngt int int (t2tb1 v_OBF__ddcc) (t2tb1 v_OBF__bbbb))))
  (infix_eqeq1 (tb2t1 (dom int int (t2tb6 v_OBF__vvee))) v_OBF__ddcc)) (mem
  (set1 int) (ran int int (t2tb6 v_OBF__wwee))
  (power int
  (union int
  (union int (add int (t2tb12 v_OBF__rrbb) (t2tb1 empty1))
  (add int (t2tb12 v_OBF__mmbb) (t2tb1 empty1)))
  (add int (t2tb12 v_OBF__ffbb) (t2tb1 empty1)))))) (mem (set1 int)
  (t2tb1 v_OBF__ddcc) (finite_subsets int (t2tb1 integer))))
  (not (infix_eqeq1 v_OBF__ddcc empty1))) (mem (set1 (tuple21 int int))
  (t2tb6 v_OBF__oodd)
  (relation int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb)))) (mem
  (set1 (tuple21 int int)) (t2tb6 v_OBF__nndd)
  (relation int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb)))) (mem
  (set1 int) (t2tb1 v_OBF__ppdd) (power int (t2tb1 v_OBF__bbbb))))
  (infix_eqeq2 v_OBF__aaff
  (tb2t6
  (times int int
  (diff int (dom int int (t2tb6 v_OBF__oodd))
  (dom (tuple21 int int) int
  (range_substraction (tuple21 int int) int
  (direct_product int int int (t2tb6 v_OBF__oodd) (t2tb6 v_OBF__oodd))
  (id int (t2tb1 v_OBF__bbbb))))) (t2tb1 v_OBF__bbbb))))) (mem
  (set1 (tuple21 int int)) (t2tb6 v_OBF__nndd)
  (power (tuple21 int int) (t2tb6 v_OBF__oodd)))) (mem int
  (t2tb12 v_OBF__xxbb) (t2tb1 v_OBF__bbbb))) (mem (set1 (tuple21 int int))
  (t2tb6 v_OBF__yyee)
  (power (tuple21 int int)
  (times int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb))))) (mem
  (set1 (tuple21 int int)) (t2tb6 v_OBF__zzee)
  (power (tuple21 int int)
  (times int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb)))))
  (not (= v_OBF__xxbb v_OBF__sscc))) (infix_eqeq2 v_OBF__bbff
  (tb2t6
  (union (tuple21 int int) (t2tb6 v_OBF__yyee)
  (semicolon int int int (t2tb6 v_OBF__yyee)
  (times int int (add int (t2tb12 v_OBF__xxbb) (t2tb1 empty1))
  (t2tb1 v_OBF__bbbb))))))) (infix_eqeq2 v_OBF__ccff
  (tb2t6
  (union (tuple21 int int) (t2tb6 v_OBF__zzee)
  (semicolon int int int (t2tb6 v_OBF__zzee)
  (times int int (add int (t2tb12 v_OBF__xxbb) (t2tb1 empty1))
  (t2tb1 v_OBF__bbbb))))))) (mem int (t2tb12 v_OBF__oobb)
  (t2tb1 v_OBF__wwcc))) (mem int (t2tb12 v_OBF__sscc) (t2tb1 v_OBF__bbbb)))
  (mem (set1 int) (t2tb1 v_OBF__uu) (power int (t2tb1 v_OBF__eecc)))) (mem
  (set1 int) (t2tb1 v_OBF__qqbb) (power int (t2tb1 v_OBF__eecc)))) (mem
  (set1 int) (t2tb1 v_OBF__rrcc) (power int (t2tb1 v_OBF__eecc)))) (mem
  (set1 int) (t2tb1 v_OBF__qqcc) (power int (t2tb1 v_OBF__eecc)))) (mem 
  int (t2tb12 v_OBF__iibb) (t2tb1 v_OBF__eecc))) (mem int
  (t2tb12 v_OBF__jjbb) (t2tb1 v_OBF__eecc))) (mem int (t2tb12 v_OBF__ttcc)
  (t2tb1 v_OBF__eecc))) (mem int (t2tb12 v_OBF__uucc) (t2tb1 v_OBF__eecc)))
  (mem (set1 (tuple21 int int)) (t2tb6 v_OBF__bbff)
  (power (tuple21 int int)
  (times int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb))))) (mem
  (set1 (tuple21 int int)) (t2tb6 v_OBF__ccff)
  (power (tuple21 int int)
  (times int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb))))) (mem
  (set1 (tuple21 int int)) (t2tb6 v_OBF__aaff)
  (power (tuple21 int int)
  (times int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb))))) (mem (set1 int)
  (t2tb1 v_OBF__ddff) (power int (t2tb1 v_OBF__bbbb)))) (mem (set1 int)
  (t2tb1 v_OBF__qqbb) (power int (t2tb1 v_OBF__uu)))) (mem (set1 int)
  (t2tb1 v_OBF__rrcc)
  (power int (diff int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__uu))))) (mem
  (set1 int) (t2tb1 v_OBF__qqcc)
  (power int
  (diff int (t2tb1 v_OBF__eecc)
  (union int (t2tb1 v_OBF__uu) (t2tb1 v_OBF__rrcc))))))
  (not (mem int (t2tb12 v_OBF__iibb) (t2tb1 v_OBF__uu))))
  (not (mem int (t2tb12 v_OBF__iibb) (t2tb1 v_OBF__rrcc))))
  (not (mem int (t2tb12 v_OBF__iibb) (t2tb1 v_OBF__qqcc))))
  (not (= v_OBF__iibb v_OBF__jjbb))) (not (= v_OBF__iibb v_OBF__ttcc)))
  (not (= v_OBF__iibb v_OBF__uucc)))
  (not (mem int (t2tb12 v_OBF__jjbb) (t2tb1 v_OBF__uu))))
  (not (mem int (t2tb12 v_OBF__jjbb) (t2tb1 v_OBF__rrcc))))
  (not (mem int (t2tb12 v_OBF__jjbb) (t2tb1 v_OBF__qqcc))))
  (not (= v_OBF__jjbb v_OBF__iibb))) (not (= v_OBF__jjbb v_OBF__ttcc)))
  (not (= v_OBF__jjbb v_OBF__uucc)))
  (not (mem int (t2tb12 v_OBF__ttcc) (t2tb1 v_OBF__uu))))
  (not (mem int (t2tb12 v_OBF__ttcc) (t2tb1 v_OBF__rrcc))))
  (not (mem int (t2tb12 v_OBF__ttcc) (t2tb1 v_OBF__qqcc))))
  (not (= v_OBF__ttcc v_OBF__iibb))) (not (= v_OBF__ttcc v_OBF__jjbb)))
  (not (= v_OBF__ttcc v_OBF__uucc)))
  (not (mem int (t2tb12 v_OBF__uucc) (t2tb1 v_OBF__uu))))
  (not (mem int (t2tb12 v_OBF__uucc) (t2tb1 v_OBF__rrcc))))
  (not (mem int (t2tb12 v_OBF__uucc) (t2tb1 v_OBF__qqcc))))
  (not (= v_OBF__uucc v_OBF__iibb))) (not (= v_OBF__uucc v_OBF__jjbb)))
  (not (= v_OBF__uucc v_OBF__ttcc))) (infix_eqeq1 v_OBF__eecc
  (tb2t1
  (union int
  (union int (union int (t2tb1 v_OBF__uu) (t2tb1 v_OBF__rrcc))
  (t2tb1 v_OBF__qqcc))
  (union int
  (union int
  (union int (add int (t2tb12 v_OBF__iibb) (t2tb1 empty1))
  (add int (t2tb12 v_OBF__jjbb) (t2tb1 empty1)))
  (add int (t2tb12 v_OBF__ttcc) (t2tb1 empty1)))
  (add int (t2tb12 v_OBF__uucc) (t2tb1 empty1))))))) (infix_eqeq2 v_OBF__eeff
  (tb2t6
  (union (tuple21 int int)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (domain_restriction int int (t2tb1 v_OBF__uu) (t2tb6 v_OBF__bbff))
  (times int int (t2tb1 v_OBF__qqcc) (t2tb1 v_OBF__ddff)))
  (times int int
  (union int (add int (t2tb12 v_OBF__iibb) (t2tb1 empty1))
  (add int (t2tb12 v_OBF__jjbb) (t2tb1 empty1))) (t2tb1 v_OBF__ddff)))
  (times int int (t2tb1 v_OBF__rrcc)
  (add int (t2tb12 v_OBF__sscc) (t2tb1 empty1))))
  (times int int (t2tb1 v_OBF__qqbb) (t2tb1 v_OBF__bbbb)))
  (times int int (add int (t2tb12 v_OBF__ttcc) (t2tb1 empty1))
  (t2tb1 v_OBF__bbbb)))
  (add (tuple21 int int)
  (Tuple2 int int (t2tb12 v_OBF__uucc) (t2tb12 v_OBF__sscc)) (t2tb6 empty2))))))
  (infix_eqeq4 v_OBF__ffff
  (tb2t4
  (union (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (domain_restriction int int (t2tb1 v_OBF__uu) (t2tb6 v_OBF__ccff))
  (times int int (t2tb1 v_OBF__qqcc) (t2tb1 v_OBF__ddff)))
  (add (tuple21 int int)
  (Tuple2 int int (t2tb12 v_OBF__uucc) (t2tb12 v_OBF__sscc)) (t2tb6 empty2)))
  (t2tb1 v_OBF__wwcc))
  (times int (tuple21 int int)
  (times int int
  (union int (add int (t2tb12 v_OBF__iibb) (t2tb1 empty1))
  (add int (t2tb12 v_OBF__jjbb) (t2tb1 empty1))) (t2tb1 v_OBF__ddff))
  (add int (t2tb12 v_OBF__oobb) (t2tb1 empty1))))))) (infix_eqeq2 v_OBF__ggff
  (tb2t6 (domain_restriction int int (t2tb1 v_OBF__uu) (t2tb6 v_OBF__aaff)))))
  (mem int (t2tb12 v_OBF__dddd) (t2tb1 integer))) (infix_eqeq2 v_OBF__hhff
  (tb2t6 (times int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb)))))
  (infix_eqeq2 v_OBF__iiff
  (tb2t6 (times int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb)))))
  (<= 1 v_OBF__dddd)) (mem (set1 (tuple21 (tuple21 int enum_OBF__aa1) int))
  (t2tb2 v_OBF__jjff)
  (power (tuple21 (tuple21 int enum_OBF__aa1) int)
  (times int (tuple21 int enum_OBF__aa1)
  (times enum_OBF__aa1 int (t2tb1 integer) (t2tb161 set_enum_OBF__aa))
  (t2tb1 integer))))) (mem (set1 (tuple21 (tuple21 int enum_OBF__aa1) int))
  (t2tb2 v_OBF__kkff)
  (power (tuple21 (tuple21 int enum_OBF__aa1) int)
  (times int (tuple21 int enum_OBF__aa1)
  (times enum_OBF__aa1 int (t2tb1 integer) (t2tb161 set_enum_OBF__aa))
  (t2tb1 integer))))) (mem (set1 (tuple21 (tuple21 int enum_OBF__aa1) int))
  (t2tb2 v_OBF__llff)
  (power (tuple21 (tuple21 int enum_OBF__aa1) int)
  (times int (tuple21 int enum_OBF__aa1)
  (times enum_OBF__aa1 int (t2tb1 integer) (t2tb161 set_enum_OBF__aa))
  (t2tb1 integer))))) (mem (set1 (tuple21 (tuple21 int enum_OBF__aa1) int))
  (t2tb2 v_OBF__mmff)
  (power (tuple21 (tuple21 int enum_OBF__aa1) int)
  (times int (tuple21 int enum_OBF__aa1)
  (times enum_OBF__aa1 int (t2tb1 integer) (t2tb161 set_enum_OBF__aa))
  (t2tb1 integer))))) (mem (set1 (tuple21 (tuple21 int enum_OBF__aa1) int))
  (t2tb2 v_OBF__hhdd)
  (power (tuple21 (tuple21 int enum_OBF__aa1) int)
  (times int (tuple21 int enum_OBF__aa1)
  (times enum_OBF__aa1 int (t2tb1 integer) (t2tb161 set_enum_OBF__aa))
  (t2tb1 integer))))) (infix_eqeq6 v_OBF__jjff
  (tb2t2
  (times int (tuple21 int enum_OBF__aa1)
  (times enum_OBF__aa1 int (add int (t2tb12 0) (t2tb1 empty1))
  (union enum_OBF__aa1
  (union enum_OBF__aa1
  (union enum_OBF__aa1
  (union enum_OBF__aa1
  (add enum_OBF__aa1 (t2tb162 E_OBF__bb) (empty enum_OBF__aa1))
  (add enum_OBF__aa1 (t2tb162 E_OBF__ff) (empty enum_OBF__aa1)))
  (add enum_OBF__aa1 (t2tb162 E_OBF__gg) (empty enum_OBF__aa1)))
  (add enum_OBF__aa1 (t2tb162 E_OBF__ee) (empty enum_OBF__aa1)))
  (add enum_OBF__aa1 (t2tb162 E_OBF__cc) (empty enum_OBF__aa1))))
  (add int (t2tb12 0) (t2tb1 empty1)))))) (infix_eqeq6 v_OBF__kkff
  (tb2t2
  (times int (tuple21 int enum_OBF__aa1)
  (times enum_OBF__aa1 int (add int (t2tb12 0) (t2tb1 empty1))
  (union enum_OBF__aa1
  (add enum_OBF__aa1 (t2tb162 E_OBF__hh) (empty enum_OBF__aa1))
  (add enum_OBF__aa1 (t2tb162 E_OBF__dd) (empty enum_OBF__aa1))))
  (add int (t2tb12 1) (t2tb1 empty1)))))) (infix_eqeq6 v_OBF__llff
  (tb2t2
  (times int (tuple21 int enum_OBF__aa1)
  (times enum_OBF__aa1 int (add int (t2tb12 1) (t2tb1 empty1))
  (add enum_OBF__aa1 (t2tb162 E_OBF__cc) (empty enum_OBF__aa1)))
  (add int (t2tb12 0) (t2tb1 empty1)))))) (infix_eqeq6 v_OBF__mmff
  (tb2t2
  (times int (tuple21 int enum_OBF__aa1)
  (times enum_OBF__aa1 int (add int (t2tb12 1) (t2tb1 empty1))
  (union enum_OBF__aa1
  (union enum_OBF__aa1
  (union enum_OBF__aa1
  (union enum_OBF__aa1
  (union enum_OBF__aa1
  (add enum_OBF__aa1 (t2tb162 E_OBF__bb) (empty enum_OBF__aa1))
  (add enum_OBF__aa1 (t2tb162 E_OBF__ff) (empty enum_OBF__aa1)))
  (add enum_OBF__aa1 (t2tb162 E_OBF__gg) (empty enum_OBF__aa1)))
  (add enum_OBF__aa1 (t2tb162 E_OBF__ee) (empty enum_OBF__aa1)))
  (add enum_OBF__aa1 (t2tb162 E_OBF__hh) (empty enum_OBF__aa1)))
  (add enum_OBF__aa1 (t2tb162 E_OBF__dd) (empty enum_OBF__aa1))))
  (add int (t2tb12 1) (t2tb1 empty1)))))) (infix_eqeq6 v_OBF__hhdd
  (tb2t2
  (union (tuple21 (tuple21 int enum_OBF__aa1) int)
  (union (tuple21 (tuple21 int enum_OBF__aa1) int)
  (union (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 v_OBF__jjff)
  (t2tb2 v_OBF__kkff)) (t2tb2 v_OBF__llff)) (t2tb2 v_OBF__mmff))))) (mem
  (set1 (tuple21 int int)) (t2tb6 v_OBF__eeff)
  (power (tuple21 int int)
  (times int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb))))) (mem
  (set1 (tuple21 (tuple21 int int) int)) (t2tb4 v_OBF__ffff)
  (power (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int)
  (times int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb))
  (t2tb1 v_OBF__wwcc))))) (mem (set1 (tuple21 int int)) (t2tb6 v_OBF__ggff)
  (power (tuple21 int int)
  (times int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb))))) (mem
  (set1 (tuple21 int int)) (t2tb6 v_OBF__hhff)
  (power (tuple21 int int)
  (times int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb))))) (mem
  (set1 (tuple21 int int)) (t2tb6 v_OBF__iiff)
  (power (tuple21 int int)
  (times int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb))))) (infix_eqeq5
  v_OBF__nnff
  (tb2t3
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int) (t2tb6 v_OBF__eeff) (t2tb1 v_OBF__wwcc))
  (add int (t2tb12 v_OBF__rrbb) (t2tb1 empty1)))
  (times int (tuple21 (tuple21 int int) int) (t2tb4 v_OBF__ffff)
  (add int (t2tb12 v_OBF__mmbb) (t2tb1 empty1))))
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int) (t2tb6 v_OBF__ggff) (t2tb1 v_OBF__wwcc))
  (add int (t2tb12 v_OBF__ffbb) (t2tb1 empty1))))
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int) (t2tb6 v_OBF__hhff) (t2tb1 v_OBF__wwcc))
  (add int (t2tb12 v_OBF__jjdd) (t2tb1 empty1))))
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int) (t2tb6 v_OBF__iiff) (t2tb1 v_OBF__wwcc))
  (add int (t2tb12 v_OBF__kkdd) (t2tb1 empty1))))
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int)
  (times int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb))
  (t2tb1 v_OBF__wwcc)) (add int (t2tb12 v_OBF__lldd) (t2tb1 empty1)))))))
  (mem (set1 (tuple21 (tuple21 (tuple21 int int) int) int))
  (t2tb3 v_OBF__nnff)
  (power (tuple21 (tuple21 (tuple21 int int) int) int)
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int)
  (times int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb))
  (t2tb1 v_OBF__wwcc)) (t2tb1 v_OBF__ffcc))))) (mem int (t2tb12 v_OBF__rrbb)
  (t2tb1 v_OBF__ffcc))) (mem int (t2tb12 v_OBF__mmbb) (t2tb1 v_OBF__ffcc)))
  (mem int (t2tb12 v_OBF__ffbb) (t2tb1 v_OBF__ffcc))) (mem int
  (t2tb12 v_OBF__jjdd) (t2tb1 v_OBF__ffcc))) (mem int (t2tb12 v_OBF__kkdd)
  (t2tb1 v_OBF__ffcc))) (mem int (t2tb12 v_OBF__lldd) (t2tb1 v_OBF__ffcc)))
  (not (= v_OBF__rrbb v_OBF__mmbb))) (not (= v_OBF__rrbb v_OBF__ffbb)))
  (not (= v_OBF__rrbb v_OBF__jjdd))) (not (= v_OBF__rrbb v_OBF__kkdd)))
  (not (= v_OBF__rrbb v_OBF__lldd))) (not (= v_OBF__mmbb v_OBF__rrbb)))
  (not (= v_OBF__mmbb v_OBF__ffbb))) (not (= v_OBF__mmbb v_OBF__jjdd)))
  (not (= v_OBF__mmbb v_OBF__kkdd))) (not (= v_OBF__mmbb v_OBF__lldd)))
  (not (= v_OBF__ffbb v_OBF__rrbb))) (not (= v_OBF__ffbb v_OBF__mmbb)))
  (not (= v_OBF__ffbb v_OBF__jjdd))) (not (= v_OBF__ffbb v_OBF__kkdd)))
  (not (= v_OBF__ffbb v_OBF__lldd))) (not (= v_OBF__jjdd v_OBF__rrbb)))
  (not (= v_OBF__jjdd v_OBF__mmbb))) (not (= v_OBF__jjdd v_OBF__ffbb)))
  (not (= v_OBF__jjdd v_OBF__kkdd))) (not (= v_OBF__jjdd v_OBF__lldd)))
  (not (= v_OBF__kkdd v_OBF__rrbb))) (not (= v_OBF__kkdd v_OBF__mmbb)))
  (not (= v_OBF__kkdd v_OBF__ffbb))) (not (= v_OBF__kkdd v_OBF__jjdd)))
  (not (= v_OBF__kkdd v_OBF__lldd))) (not (= v_OBF__lldd v_OBF__rrbb)))
  (not (= v_OBF__lldd v_OBF__mmbb))) (not (= v_OBF__lldd v_OBF__ffbb)))
  (not (= v_OBF__lldd v_OBF__jjdd))) (not (= v_OBF__lldd v_OBF__kkdd))) (mem
  (set1 int) (t2tb1 v_OBF__eecc) (finite_subsets int (t2tb1 integer))))
  (not (infix_eqeq1 v_OBF__eecc empty1))) (mem (set1 int) (t2tb1 v_OBF__bbbb)
  (finite_subsets int (t2tb1 integer))))
  (not (infix_eqeq1 v_OBF__bbbb empty1))) (mem (set1 int) (t2tb1 v_OBF__wwcc)
  (finite_subsets int (t2tb1 integer))))
  (not (infix_eqeq1 v_OBF__wwcc empty1))) (mem (set1 int) (t2tb1 v_OBF__ffcc)
  (finite_subsets int (t2tb1 integer))))
  (not (infix_eqeq1 v_OBF__ffcc empty1))))))

(declare-fun f2 ((set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set Int)
  (set Int) (set (tuple2 Int Int)) Int Int (set Int) (set Int) (set Int) Int
  (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) Int (set Int)
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int)) Bool
  (set (tuple2 (tuple2 Int Int) Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) (set Int)
  (set (tuple2 Int Int)) Int Int (set Int) Int (set (tuple2 Int Int)) Int Int
  (set Int) (set (tuple2 Int Int)) Int (set Int) Int Int Int (set Int)
  (set Int) Int (set Int) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) Bool Int (set (tuple2 (tuple2 (tuple2 Int Int) Int)
  Int)) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Bool
  (set (tuple2 Int Int)) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set Int) Int (set (tuple2 Int Int)) (set enum_OBF__ii)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int (set (tuple2 Int
  Int)) (set Int) (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) (set (tuple2 Int Int)) (set enum_OBF__ii)
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) enum_OBF__aa (set Int)
  (set Int) (set (tuple2 (tuple2 Int Int) Int)) (set (tuple2 Int Int)) Int
  (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) Int (set Int) (set Int) Int (set Int) Int
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int
  Int)) Int (set (tuple2 Int Int)) Bool (set (tuple2 Int Int)) (set Int)
  (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int
  Int)) (set Int) Int) Bool)

;; f2_def
  (assert
  (forall ((v_OBF__zzee (set (tuple2 Int Int))) (v_OBF__zzdd (set (tuple2 Int
  Int))) (v_OBF__zzcc Int) (v_OBF__zzbb (set Int)) (v_OBF__zz (set Int))
  (v_OBF__yyee (set (tuple2 Int Int))) (v_OBF__yydd Int) (v_OBF__yycc Int)
  (v_OBF__yybb (set Int)) (v_OBF__yy (set Int)) (v_OBF__xxee (set Int))
  (v_OBF__xxdd Int) (v_OBF__xxcc (set (tuple2 Int Int))) (v_OBF__xxbb Int)
  (v_OBF__xx Int) (v_OBF__wwee (set (tuple2 Int Int))) (v_OBF__wwdd Int)
  (v_OBF__wwcc (set Int)) (v_OBF__wwbb (set (tuple2 Int Int)))
  (v_OBF__ww (set Int)) (v_OBF__vvee (set (tuple2 Int Int)))
  (v_OBF__vvdd Bool) (v_OBF__vvcc (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__vvbb (set (tuple2 Int Int))) (v_OBF__vv Int)
  (v_OBF__uuee (set (tuple2 Int Int))) (v_OBF__uudd Int) (v_OBF__uucc Int)
  (v_OBF__uubb (set (tuple2 Int Int))) (v_OBF__uu (set Int))
  (v_OBF__ttee (set (tuple2 Int Int))) (v_OBF__ttdd Int) (v_OBF__ttcc Int)
  (v_OBF__ttbb (set Int)) (v_OBF__tt Int) (v_OBF__ssee (set (tuple2 Int
  Int))) (v_OBF__ssdd Int) (v_OBF__sscc Int) (v_OBF__ssbb (set Int))
  (v_OBF__rree (set (tuple2 Int Int))) (v_OBF__rrdd Int)
  (v_OBF__rrcc (set Int)) (v_OBF__rrbb Int) (v_OBF__qqee Int)
  (v_OBF__qqdd Int) (v_OBF__qqcc (set Int)) (v_OBF__qqbb (set Int))
  (v_OBF__ppee Int) (v_OBF__ppdd (set Int)) (v_OBF__ppcc (set (tuple2 Int
  Int))) (v_OBF__ppbb (set Int)) (v_OBF__ooee Int)
  (v_OBF__oodd (set (tuple2 Int Int))) (v_OBF__oocc Bool) (v_OBF__oobb Int)
  (v_OBF__nnff (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__nnee (set Int)) (v_OBF__nndd (set (tuple2 Int Int)))
  (v_OBF__nncc (set (tuple2 Int Int))) (v_OBF__nnbb Int)
  (v_OBF__mmff (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__mmee (set Int)) (v_OBF__mmdd Bool) (v_OBF__mmcc (set (tuple2 Int
  Int))) (v_OBF__mmbb Int) (v_OBF__llff (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (v_OBF__llee (set Int)) (v_OBF__lldd Int)
  (v_OBF__llcc (set (tuple2 Int Int))) (v_OBF__llbb (set enum_OBF__ii))
  (v_OBF__kkff (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__kkee (set Int)) (v_OBF__kkdd Int) (v_OBF__kkcc (set (tuple2 Int
  Int))) (v_OBF__kkbb (set Int)) (v_OBF__jjff (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (v_OBF__jjee (set Int)) (v_OBF__jjdd Int)
  (v_OBF__jjcc (set (tuple2 Int Int))) (v_OBF__jjbb Int)
  (v_OBF__iiff (set (tuple2 Int Int))) (v_OBF__iiee (set Int))
  (v_OBF__iidd (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb Int)
  (v_OBF__hhff (set (tuple2 Int Int))) (v_OBF__hhee (set (tuple2 Int Int)))
  (v_OBF__hhdd (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__hhcc (set (tuple2 Int Int))) (v_OBF__hhbb (set enum_OBF__ii))
  (v_OBF__ggff (set (tuple2 Int Int))) (v_OBF__ggee (set (tuple2 Int Int)))
  (v_OBF__ggdd enum_OBF__aa) (v_OBF__ggcc (set Int)) (v_OBF__ggbb (set Int))
  (v_OBF__ffff (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__ffee (set (tuple2 Int Int))) (v_OBF__ffdd Int)
  (v_OBF__ffcc (set Int)) (v_OBF__ffbb Int) (v_OBF__eeff (set (tuple2 Int
  Int))) (v_OBF__eeee (set (tuple2 Int Int))) (v_OBF__eedd (set (tuple2 Int
  Int))) (v_OBF__eecc (set Int)) (v_OBF__eebb Int) (v_OBF__ddff (set Int))
  (v_OBF__ddee (set Int)) (v_OBF__dddd Int) (v_OBF__ddcc (set Int))
  (v_OBF__ddbb Int) (v_OBF__ccff (set (tuple2 Int Int)))
  (v_OBF__ccee (set Int)) (v_OBF__ccdd (set (tuple2 Int Int)))
  (v_OBF__cccc (set (tuple2 Int Int))) (v_OBF__ccbb Int)
  (v_OBF__bbff (set (tuple2 Int Int))) (v_OBF__bbee Bool)
  (v_OBF__bbdd (set (tuple2 Int Int))) (v_OBF__bbcc (set Int))
  (v_OBF__bbbb (set Int)) (v_OBF__aaff (set (tuple2 Int Int)))
  (v_OBF__aaee (set (tuple2 Int Int))) (v_OBF__aadd (set (tuple2 Int Int)))
  (v_OBF__aacc (set Int)) (v_OBF__aabb Int))
  (= (f2 v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb v_OBF__zz
  v_OBF__yyee v_OBF__yydd v_OBF__yycc v_OBF__yybb v_OBF__yy v_OBF__xxee
  v_OBF__xxdd v_OBF__xxcc v_OBF__xxbb v_OBF__xx v_OBF__wwee v_OBF__wwdd
  v_OBF__wwcc v_OBF__wwbb v_OBF__ww v_OBF__vvee v_OBF__vvdd v_OBF__vvcc
  v_OBF__vvbb v_OBF__vv v_OBF__uuee v_OBF__uudd v_OBF__uucc v_OBF__uubb
  v_OBF__uu v_OBF__ttee v_OBF__ttdd v_OBF__ttcc v_OBF__ttbb v_OBF__tt
  v_OBF__ssee v_OBF__ssdd v_OBF__sscc v_OBF__ssbb v_OBF__rree v_OBF__rrdd
  v_OBF__rrcc v_OBF__rrbb v_OBF__qqee v_OBF__qqdd v_OBF__qqcc v_OBF__qqbb
  v_OBF__ppee v_OBF__ppdd v_OBF__ppcc v_OBF__ppbb v_OBF__ooee v_OBF__oodd
  v_OBF__oocc v_OBF__oobb v_OBF__nnff v_OBF__nnee v_OBF__nndd v_OBF__nncc
  v_OBF__nnbb v_OBF__mmff v_OBF__mmee v_OBF__mmdd v_OBF__mmcc v_OBF__mmbb
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkff
  v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjff v_OBF__jjee
  v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iiff v_OBF__iiee v_OBF__iidd
  v_OBF__iicc v_OBF__iibb v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc
  v_OBF__hhbb v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb
  v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb v_OBF__eeff
  v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb v_OBF__ddff v_OBF__ddee
  v_OBF__dddd v_OBF__ddcc v_OBF__ddbb v_OBF__ccff v_OBF__ccee v_OBF__ccdd
  v_OBF__cccc v_OBF__ccbb v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc
  v_OBF__bbbb v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (mem int (t2tb12 v_OBF__ooee) (t2tb1 v_OBF__eecc)) (mem int
  (t2tb12 v_OBF__ppee) (t2tb1 v_OBF__wwcc))) (mem int (t2tb12 v_OBF__qqee)
  (t2tb1 v_OBF__ffcc))) (mem (set1 (tuple21 int int)) (t2tb6 v_OBF__rree)
  (infix_plmngt int int (t2tb1 (mk 1 v_OBF__dddd)) (t2tb1 v_OBF__bbbb))))
  (infix_eqeq1 (tb2t1 (dom int int (t2tb6 v_OBF__rree))) (mk 1 v_OBF__dddd)))
  (mem (set1 (tuple21 int int)) (t2tb6 v_OBF__ssee)
  (infix_plmngt int int (t2tb1 (mk 1 v_OBF__dddd)) (t2tb1 v_OBF__bbbb))))
  (infix_eqeq1 (tb2t1 (dom int int (t2tb6 v_OBF__ssee))) (mk 1 v_OBF__dddd)))
  (mem (set1 int) (t2tb1 v_OBF__aacc) (power int (t2tb1 v_OBF__ddcc)))) (mem
  (set1 int) (t2tb1 v_OBF__zzbb) (power int (t2tb1 v_OBF__ddcc)))) (mem
  (set1 int) (t2tb1 v_OBF__yybb) (power int (t2tb1 v_OBF__bbbb)))) (mem
  (set1 int) (t2tb1 v_OBF__bbcc) (power int (t2tb1 v_OBF__ddcc)))) (mem
  (set1 int) (t2tb1 v_OBF__ssbb) (power int (t2tb1 v_OBF__ddcc)))))))

(declare-fun f5 ((set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set Int)
  (set Int) (set (tuple2 Int Int)) Int Int (set Int) (set Int) (set Int) Int
  (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) Int (set Int)
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int)) Bool
  (set (tuple2 (tuple2 Int Int) Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) (set Int)
  (set (tuple2 Int Int)) Int Int (set Int) Int (set (tuple2 Int Int)) Int Int
  (set Int) (set (tuple2 Int Int)) Int (set Int) Int Int Int (set Int)
  (set Int) Int (set Int) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) Bool Int (set (tuple2 (tuple2 (tuple2 Int Int) Int)
  Int)) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Bool
  (set (tuple2 Int Int)) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set Int) Int (set (tuple2 Int Int)) (set enum_OBF__ii)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int (set (tuple2 Int
  Int)) (set Int) (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) (set (tuple2 Int Int)) (set enum_OBF__ii)
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) enum_OBF__aa (set Int)
  (set Int) (set (tuple2 (tuple2 Int Int) Int)) (set (tuple2 Int Int)) Int
  (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) Int (set Int) (set Int) Int (set Int) Int
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int
  Int)) Int (set (tuple2 Int Int)) Bool (set (tuple2 Int Int)) (set Int)
  (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int
  Int)) (set Int) Int) Bool)

(declare-fun t2tb164 ((set (tuple2 (tuple2 Int Int) Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Int Int) Bool)))) (sort
  (set1 (tuple21 (tuple21 int int) bool)) (t2tb164 x))))

(declare-fun tb2t164 (uni) (set (tuple2 (tuple2 Int Int) Bool)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Int Int) Bool))))
  (! (= (tb2t164 (t2tb164 i)) i) :pattern ((t2tb164 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb164 (tb2t164 j)) j) :pattern ((t2tb164 (tb2t164 j))) )))

;; f5_def
  (assert
  (forall ((v_OBF__zzee (set (tuple2 Int Int))) (v_OBF__zzdd (set (tuple2 Int
  Int))) (v_OBF__zzcc Int) (v_OBF__zzbb (set Int)) (v_OBF__zz (set Int))
  (v_OBF__yyee (set (tuple2 Int Int))) (v_OBF__yydd Int) (v_OBF__yycc Int)
  (v_OBF__yybb (set Int)) (v_OBF__yy (set Int)) (v_OBF__xxee (set Int))
  (v_OBF__xxdd Int) (v_OBF__xxcc (set (tuple2 Int Int))) (v_OBF__xxbb Int)
  (v_OBF__xx Int) (v_OBF__wwee (set (tuple2 Int Int))) (v_OBF__wwdd Int)
  (v_OBF__wwcc (set Int)) (v_OBF__wwbb (set (tuple2 Int Int)))
  (v_OBF__ww (set Int)) (v_OBF__vvee (set (tuple2 Int Int)))
  (v_OBF__vvdd Bool) (v_OBF__vvcc (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__vvbb (set (tuple2 Int Int))) (v_OBF__vv Int)
  (v_OBF__uuee (set (tuple2 Int Int))) (v_OBF__uudd Int) (v_OBF__uucc Int)
  (v_OBF__uubb (set (tuple2 Int Int))) (v_OBF__uu (set Int))
  (v_OBF__ttee (set (tuple2 Int Int))) (v_OBF__ttdd Int) (v_OBF__ttcc Int)
  (v_OBF__ttbb (set Int)) (v_OBF__tt Int) (v_OBF__ssee (set (tuple2 Int
  Int))) (v_OBF__ssdd Int) (v_OBF__sscc Int) (v_OBF__ssbb (set Int))
  (v_OBF__rree (set (tuple2 Int Int))) (v_OBF__rrdd Int)
  (v_OBF__rrcc (set Int)) (v_OBF__rrbb Int) (v_OBF__qqee Int)
  (v_OBF__qqdd Int) (v_OBF__qqcc (set Int)) (v_OBF__qqbb (set Int))
  (v_OBF__ppee Int) (v_OBF__ppdd (set Int)) (v_OBF__ppcc (set (tuple2 Int
  Int))) (v_OBF__ppbb (set Int)) (v_OBF__ooee Int)
  (v_OBF__oodd (set (tuple2 Int Int))) (v_OBF__oocc Bool) (v_OBF__oobb Int)
  (v_OBF__nnff (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__nnee (set Int)) (v_OBF__nndd (set (tuple2 Int Int)))
  (v_OBF__nncc (set (tuple2 Int Int))) (v_OBF__nnbb Int)
  (v_OBF__mmff (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__mmee (set Int)) (v_OBF__mmdd Bool) (v_OBF__mmcc (set (tuple2 Int
  Int))) (v_OBF__mmbb Int) (v_OBF__llff (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (v_OBF__llee (set Int)) (v_OBF__lldd Int)
  (v_OBF__llcc (set (tuple2 Int Int))) (v_OBF__llbb (set enum_OBF__ii))
  (v_OBF__kkff (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__kkee (set Int)) (v_OBF__kkdd Int) (v_OBF__kkcc (set (tuple2 Int
  Int))) (v_OBF__kkbb (set Int)) (v_OBF__jjff (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (v_OBF__jjee (set Int)) (v_OBF__jjdd Int)
  (v_OBF__jjcc (set (tuple2 Int Int))) (v_OBF__jjbb Int)
  (v_OBF__iiff (set (tuple2 Int Int))) (v_OBF__iiee (set Int))
  (v_OBF__iidd (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb Int)
  (v_OBF__hhff (set (tuple2 Int Int))) (v_OBF__hhee (set (tuple2 Int Int)))
  (v_OBF__hhdd (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__hhcc (set (tuple2 Int Int))) (v_OBF__hhbb (set enum_OBF__ii))
  (v_OBF__ggff (set (tuple2 Int Int))) (v_OBF__ggee (set (tuple2 Int Int)))
  (v_OBF__ggdd enum_OBF__aa) (v_OBF__ggcc (set Int)) (v_OBF__ggbb (set Int))
  (v_OBF__ffff (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__ffee (set (tuple2 Int Int))) (v_OBF__ffdd Int)
  (v_OBF__ffcc (set Int)) (v_OBF__ffbb Int) (v_OBF__eeff (set (tuple2 Int
  Int))) (v_OBF__eeee (set (tuple2 Int Int))) (v_OBF__eedd (set (tuple2 Int
  Int))) (v_OBF__eecc (set Int)) (v_OBF__eebb Int) (v_OBF__ddff (set Int))
  (v_OBF__ddee (set Int)) (v_OBF__dddd Int) (v_OBF__ddcc (set Int))
  (v_OBF__ddbb Int) (v_OBF__ccff (set (tuple2 Int Int)))
  (v_OBF__ccee (set Int)) (v_OBF__ccdd (set (tuple2 Int Int)))
  (v_OBF__cccc (set (tuple2 Int Int))) (v_OBF__ccbb Int)
  (v_OBF__bbff (set (tuple2 Int Int))) (v_OBF__bbee Bool)
  (v_OBF__bbdd (set (tuple2 Int Int))) (v_OBF__bbcc (set Int))
  (v_OBF__bbbb (set Int)) (v_OBF__aaff (set (tuple2 Int Int)))
  (v_OBF__aaee (set (tuple2 Int Int))) (v_OBF__aadd (set (tuple2 Int Int)))
  (v_OBF__aacc (set Int)) (v_OBF__aabb Int))
  (= (f5 v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb v_OBF__zz
  v_OBF__yyee v_OBF__yydd v_OBF__yycc v_OBF__yybb v_OBF__yy v_OBF__xxee
  v_OBF__xxdd v_OBF__xxcc v_OBF__xxbb v_OBF__xx v_OBF__wwee v_OBF__wwdd
  v_OBF__wwcc v_OBF__wwbb v_OBF__ww v_OBF__vvee v_OBF__vvdd v_OBF__vvcc
  v_OBF__vvbb v_OBF__vv v_OBF__uuee v_OBF__uudd v_OBF__uucc v_OBF__uubb
  v_OBF__uu v_OBF__ttee v_OBF__ttdd v_OBF__ttcc v_OBF__ttbb v_OBF__tt
  v_OBF__ssee v_OBF__ssdd v_OBF__sscc v_OBF__ssbb v_OBF__rree v_OBF__rrdd
  v_OBF__rrcc v_OBF__rrbb v_OBF__qqee v_OBF__qqdd v_OBF__qqcc v_OBF__qqbb
  v_OBF__ppee v_OBF__ppdd v_OBF__ppcc v_OBF__ppbb v_OBF__ooee v_OBF__oodd
  v_OBF__oocc v_OBF__oobb v_OBF__nnff v_OBF__nnee v_OBF__nndd v_OBF__nncc
  v_OBF__nnbb v_OBF__mmff v_OBF__mmee v_OBF__mmdd v_OBF__mmcc v_OBF__mmbb
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkff
  v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjff v_OBF__jjee
  v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iiff v_OBF__iiee v_OBF__iidd
  v_OBF__iicc v_OBF__iibb v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc
  v_OBF__hhbb v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb
  v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb v_OBF__eeff
  v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb v_OBF__ddff v_OBF__ddee
  v_OBF__dddd v_OBF__ddcc v_OBF__ddbb v_OBF__ccff v_OBF__ccee v_OBF__ccdd
  v_OBF__cccc v_OBF__ccbb v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc
  v_OBF__bbbb v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (mem (set1 (tuple21 int int)) (t2tb6 v_OBF__uubb)
  (relation int int (t2tb1 v_OBF__ddcc) (t2tb1 v_OBF__eecc))) (mem
  (set1 (tuple21 int int)) (t2tb6 v_OBF__cccc)
  (relation int int (t2tb1 v_OBF__ddcc) (t2tb1 v_OBF__eecc)))) (mem
  (set1 (tuple21 int int)) (t2tb6 v_OBF__wwbb)
  (relation int int (t2tb1 v_OBF__ddcc) (t2tb1 v_OBF__bbbb)))) (mem
  (set1 (tuple21 int int)) (t2tb6 v_OBF__vvbb)
  (relation int int (t2tb1 v_OBF__ddcc) (t2tb1 v_OBF__ffcc)))) (mem
  (set1 int) (t2tb1 v_OBF__ttbb) (power int (t2tb1 v_OBF__ddcc)))) (mem
  (set1 int) (t2tb1 v_OBF__ggbb) (power int (t2tb1 v_OBF__ddcc)))) (mem
  (set1 int) (t2tb1 v_OBF__ggcc) (power int (t2tb1 v_OBF__ddcc)))) (mem
  (set1 int) (t2tb1 v_OBF__ww) (power int (t2tb1 v_OBF__bbbb)))) (mem
  (set1 int) (t2tb1 v_OBF__zz) (power int (t2tb1 v_OBF__ddcc)))) (mem
  (set1 int) (t2tb1 v_OBF__ppbb) (power int (t2tb1 v_OBF__ddcc))))
  (infix_eqeq2 v_OBF__hhcc
  (tb2t6
  (image (tuple21 int int) int
  (ran (tuple21 int (tuple21 int int)) int
  (domain_restriction (tuple21 int (tuple21 int int)) int (t2tb1 v_OBF__ttbb)
  (direct_product (tuple21 int int) int int (t2tb6 v_OBF__vvbb)
  (direct_product int int int (t2tb6 v_OBF__uubb) (t2tb6 v_OBF__wwbb)))))
  (add int (t2tb12 v_OBF__rrbb) (t2tb1 empty1)))))) (infix_eqeq2 v_OBF__iicc
  (tb2t6
  (image (tuple21 int int) int
  (ran (tuple21 int (tuple21 int int)) int
  (domain_restriction (tuple21 int (tuple21 int int)) int (t2tb1 v_OBF__ttbb)
  (direct_product (tuple21 int int) int int (t2tb6 v_OBF__vvbb)
  (direct_product int int int (t2tb6 v_OBF__uubb) (t2tb6 v_OBF__wwbb)))))
  (add int (t2tb12 v_OBF__mmbb) (t2tb1 empty1)))))) (infix_eqeq2 v_OBF__jjcc
  (tb2t6
  (image (tuple21 int int) int
  (ran (tuple21 int (tuple21 int int)) int
  (domain_restriction (tuple21 int (tuple21 int int)) int (t2tb1 v_OBF__ttbb)
  (direct_product (tuple21 int int) int int (t2tb6 v_OBF__vvbb)
  (direct_product int int int (t2tb6 v_OBF__uubb) (t2tb6 v_OBF__wwbb)))))
  (add int (t2tb12 v_OBF__ffbb) (t2tb1 empty1)))))) (infix_eqeq2 v_OBF__kkcc
  (tb2t6
  (image (tuple21 int int) int
  (ran (tuple21 int (tuple21 int int)) int
  (domain_restriction (tuple21 int (tuple21 int int)) int (t2tb1 v_OBF__ttbb)
  (direct_product (tuple21 int int) int int (t2tb6 v_OBF__vvbb)
  (direct_product int int int (t2tb6 v_OBF__cccc) (t2tb6 v_OBF__wwbb)))))
  (add int (t2tb12 v_OBF__ffbb) (t2tb1 empty1)))))) (mem
  (set1 (tuple21 int int)) (t2tb6 v_OBF__cccc)
  (power (tuple21 int int) (t2tb6 v_OBF__uubb)))) (mem
  (set1 (tuple21 int int)) (t2tb6 v_OBF__wwbb)
  (infix_plmngt int int (t2tb1 v_OBF__ddcc) (t2tb1 v_OBF__bbbb))))
  (infix_eqeq1 (tb2t1 (dom int int (t2tb6 v_OBF__wwbb))) v_OBF__ddcc)) (mem
  (set1 int) (ran int int (t2tb6 v_OBF__vvbb))
  (power int
  (union int
  (union int (add int (t2tb12 v_OBF__rrbb) (t2tb1 empty1))
  (add int (t2tb12 v_OBF__mmbb) (t2tb1 empty1)))
  (add int (t2tb12 v_OBF__ffbb) (t2tb1 empty1))))))
  (=> (= v_OBF__ddbb 2) (infix_eqeq1 v_OBF__ggbb
  (tb2t1
  (inter int (t2tb1 v_OBF__ttbb)
  (image int int (inverse int int (t2tb6 v_OBF__uubb))
  (add int (t2tb12 v_OBF__tt) (t2tb1 empty1))))))))
  (=> (= v_OBF__ddbb 2) (infix_eqeq1 v_OBF__ggcc
  (tb2t1
  (inter int
  (inter int (t2tb1 v_OBF__ttbb)
  (image int int (inverse int int (t2tb6 v_OBF__uubb))
  (add int (t2tb12 v_OBF__tt) (t2tb1 empty1))))
  (image int int (inverse int int (t2tb6 v_OBF__vvbb))
  (add int (t2tb12 v_OBF__eebb) (t2tb1 empty1))))))))
  (=> (= v_OBF__ddbb 2) (infix_eqeq1 v_OBF__ww
  (tb2t1 (image int int (t2tb6 v_OBF__wwbb) (t2tb1 v_OBF__ggcc))))))
  (=> (= v_OBF__ddbb 2) (infix_eqeq1 v_OBF__zz
  (tb2t1
  (inter int
  (inter int (t2tb1 v_OBF__ttbb)
  (image int int (inverse int int (t2tb6 v_OBF__cccc))
  (add int (t2tb12 v_OBF__tt) (t2tb1 empty1))))
  (image int int (inverse int int (t2tb6 v_OBF__vvbb))
  (add int (t2tb12 v_OBF__eebb) (t2tb1 empty1))))))))
  (=> (= v_OBF__ddbb 2) (infix_eqeq1 v_OBF__ppbb
  (tb2t1
  (inter int
  (inter int
  (inter int (t2tb1 v_OBF__ttbb)
  (image int int (inverse int int (t2tb6 v_OBF__uubb))
  (add int (t2tb12 v_OBF__tt) (t2tb1 empty1))))
  (image int int (inverse int int (t2tb6 v_OBF__vvbb))
  (add int (t2tb12 v_OBF__eebb) (t2tb1 empty1))))
  (image int int (inverse int int (t2tb6 v_OBF__wwbb))
  (union int (add int (t2tb12 v_OBF__vv) (t2tb1 empty1))
  (add int (t2tb12 v_OBF__xxbb) (t2tb1 empty1))))))))) (mem
  (set1 (tuple21 int int)) (t2tb6 v_OBF__jjcc)
  (relation int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb)))) (mem
  (set1 (tuple21 int int)) (t2tb6 v_OBF__kkcc)
  (relation int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb)))) (mem
  (set1 int) (t2tb1 v_OBF__yy) (power int (t2tb1 v_OBF__bbbb)))) (infix_eqeq2
  v_OBF__llcc
  (tb2t6
  (times int int
  (diff int
  (dom int int
  (union (tuple21 int int) (t2tb6 v_OBF__kkcc)
  (range_substraction int int (t2tb6 v_OBF__jjcc)
  (image int int
  (times int int (add int (t2tb12 0) (t2tb1 empty1))
  (diff int (t2tb1 v_OBF__yy) (add int (t2tb12 v_OBF__vv) (t2tb1 empty1))))
  (add int (t2tb12 v_OBF__xx) (t2tb1 empty1))))))
  (dom (tuple21 int int) int
  (range_substraction (tuple21 int int) int
  (direct_product int int int (t2tb6 v_OBF__jjcc) (t2tb6 v_OBF__jjcc))
  (id int (t2tb1 v_OBF__bbbb))))) (t2tb1 v_OBF__bbbb))))) (mem
  (set1 (tuple21 int int)) (t2tb6 v_OBF__kkcc)
  (power (tuple21 int int) (t2tb6 v_OBF__jjcc)))) (mem
  (set1 (tuple21 int int)) (t2tb6 v_OBF__hhcc)
  (power (tuple21 int int)
  (times int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb))))) (mem
  (set1 (tuple21 int int)) (t2tb6 v_OBF__iicc)
  (power (tuple21 int int)
  (times int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb))))) (infix_eqeq2
  v_OBF__mmcc
  (tb2t6
  (union (tuple21 int int) (t2tb6 v_OBF__hhcc)
  (semicolon int int int (t2tb6 v_OBF__hhcc)
  (times int int (add int (t2tb12 v_OBF__xxbb) (t2tb1 empty1))
  (t2tb1 v_OBF__bbbb))))))) (infix_eqeq2 v_OBF__nncc
  (tb2t6
  (union (tuple21 int int) (t2tb6 v_OBF__iicc)
  (semicolon int int int (t2tb6 v_OBF__iicc)
  (times int int (add int (t2tb12 v_OBF__xxbb) (t2tb1 empty1))
  (t2tb1 v_OBF__bbbb))))))) (mem (set1 (tuple21 int int)) (t2tb6 v_OBF__mmcc)
  (power (tuple21 int int)
  (times int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb))))) (mem
  (set1 (tuple21 int int)) (t2tb6 v_OBF__nncc)
  (power (tuple21 int int)
  (times int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb))))) (mem
  (set1 (tuple21 int int)) (t2tb6 v_OBF__llcc)
  (power (tuple21 int int)
  (times int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb))))) (mem (set1 int)
  (t2tb1 v_OBF__kkbb) (power int (t2tb1 v_OBF__bbbb)))) (infix_eqeq2
  v_OBF__ppcc
  (tb2t6
  (union (tuple21 int int)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (domain_restriction int int (t2tb1 v_OBF__uu) (t2tb6 v_OBF__mmcc))
  (times int int (t2tb1 v_OBF__qqcc) (t2tb1 v_OBF__kkbb)))
  (times int int
  (union int (add int (t2tb12 v_OBF__iibb) (t2tb1 empty1))
  (add int (t2tb12 v_OBF__jjbb) (t2tb1 empty1))) (t2tb1 v_OBF__kkbb)))
  (times int int (t2tb1 v_OBF__rrcc)
  (add int (t2tb12 v_OBF__sscc) (t2tb1 empty1))))
  (dom int (tuple21 int int)
  (range_restriction int (tuple21 int int)
  (times int (tuple21 int int)
  (times int int (t2tb1 v_OBF__qqbb) (t2tb1 v_OBF__bbbb))
  (add int (t2tb12 1) (t2tb1 empty1)))
  (add int (t2tb12 v_OBF__xx) (t2tb1 empty1)))))
  (times int int (add int (t2tb12 v_OBF__ttcc) (t2tb1 empty1))
  (t2tb1 v_OBF__bbbb)))
  (add (tuple21 int int)
  (Tuple2 int int (t2tb12 v_OBF__uucc) (t2tb12 v_OBF__sscc)) (t2tb6 empty2))))))
  (infix_eqeq4 v_OBF__vvcc
  (tb2t4
  (union (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (domain_restriction int int (t2tb1 v_OBF__uu) (t2tb6 v_OBF__nncc))
  (times int int (t2tb1 v_OBF__qqcc) (t2tb1 v_OBF__kkbb)))
  (dom bool (tuple21 int int)
  (range_restriction bool (tuple21 int int)
  (times bool (tuple21 int int)
  (times int int (t2tb1 v_OBF__rrcc)
  (add int (t2tb12 v_OBF__sscc) (t2tb1 empty1)))
  (add bool (t2tb13 false) (empty bool)))
  (add bool (t2tb13 v_OBF__oocc) (empty bool)))))
  (add (tuple21 int int)
  (Tuple2 int int (t2tb12 v_OBF__uucc) (t2tb12 v_OBF__sscc)) (t2tb6 empty2)))
  (t2tb1 v_OBF__wwcc))
  (times int (tuple21 int int)
  (times int int
  (union int (add int (t2tb12 v_OBF__iibb) (t2tb1 empty1))
  (add int (t2tb12 v_OBF__jjbb) (t2tb1 empty1))) (t2tb1 v_OBF__kkbb))
  (add int (t2tb12 v_OBF__oobb) (t2tb1 empty1))))))) (infix_eqeq2 v_OBF__xxcc
  (tb2t6 (domain_restriction int int (t2tb1 v_OBF__uu) (t2tb6 v_OBF__llcc)))))
  (mem int (t2tb12 v_OBF__yycc) (t2tb1 v_OBF__bbbb))) (mem int
  (t2tb12 v_OBF__zzcc) (t2tb1 integer))) (mem (set1 (tuple21 int int))
  (t2tb6 v_OBF__aadd)
  (relation int int (t2tb1 integer) (t2tb1 v_OBF__bbbb)))) (mem
  (set1 (tuple21 int int)) (t2tb6 v_OBF__bbdd)
  (relation int int (t2tb1 integer) (t2tb1 v_OBF__bbbb)))) (infix_eqeq2
  v_OBF__ccdd
  (tb2t6
  (dom (tuple21 int int) (tuple21 int int)
  (range_substraction (tuple21 int int) (tuple21 int int)
  (times (tuple21 int int) (tuple21 int int)
  (times int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb))
  (add (tuple21 int int) (Tuple2 int int (t2tb12 v_OBF__dddd) (t2tb12 0))
  (t2tb6 empty2)))
  (add (tuple21 int int)
  (Tuple2 int int (t2tb12 v_OBF__zzcc) (t2tb12 v_OBF__xx)) (t2tb6 empty2)))))))
  (infix_eqeq2 v_OBF__eedd
  (tb2t6
  (dom (tuple21 int int) (tuple21 int int)
  (range_substraction (tuple21 int int) (tuple21 int int)
  (times (tuple21 int int) (tuple21 int int)
  (times int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb))
  (add (tuple21 int int) (Tuple2 int int (t2tb12 0) (t2tb12 0))
  (t2tb6 empty2)))
  (add (tuple21 int int)
  (Tuple2 int int (t2tb12 v_OBF__zzcc) (t2tb12 v_OBF__xx)) (t2tb6 empty2)))))))
  (mem int (t2tb12 v_OBF__zzcc) (t2tb1 (mk 0 v_OBF__dddd)))) (mem
  (set1 (tuple21 int int)) (t2tb6 v_OBF__aadd)
  (infix_plmngt int int (t2tb1 (mk 1 v_OBF__dddd)) (t2tb1 v_OBF__bbbb))))
  (infix_eqeq1 (tb2t1 (dom int int (t2tb6 v_OBF__aadd))) (mk 1 v_OBF__dddd)))
  (mem (set1 (tuple21 int int)) (t2tb6 v_OBF__bbdd)
  (infix_plmngt int int (t2tb1 (mk 1 v_OBF__dddd)) (t2tb1 v_OBF__bbbb))))
  (infix_eqeq1 (tb2t1 (dom int int (t2tb6 v_OBF__bbdd))) (mk 1 v_OBF__dddd)))
  (mem int (t2tb12 v_OBF__ffdd) (t2tb1 integer))) (mem int (t2tb12 v_OBF__xx)
  (t2tb1 integer))) (mem (tuple21 (tuple21 int enum_OBF__aa1) int)
  (Tuple2 (tuple21 int enum_OBF__aa1) int
  (Tuple2 int enum_OBF__aa1 (t2tb12 v_OBF__ffdd) (t2tb162 v_OBF__ggdd))
  (t2tb12 v_OBF__xx)) (t2tb2 v_OBF__hhdd))) (mem (set1 (tuple21 int int))
  (t2tb6 v_OBF__ppcc)
  (power (tuple21 int int)
  (times int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb))))) (mem
  (set1 (tuple21 (tuple21 int int) int)) (t2tb4 v_OBF__vvcc)
  (power (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int)
  (times int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb))
  (t2tb1 v_OBF__wwcc))))) (mem (set1 (tuple21 int int)) (t2tb6 v_OBF__xxcc)
  (power (tuple21 int int)
  (times int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb))))) (mem
  (set1 (tuple21 int int)) (t2tb6 v_OBF__ccdd)
  (power (tuple21 int int)
  (times int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb))))) (mem
  (set1 (tuple21 int int)) (t2tb6 v_OBF__eedd)
  (power (tuple21 int int)
  (times int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb))))) (infix_eqeq5
  v_OBF__iidd
  (tb2t3
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int) (t2tb6 v_OBF__ppcc) (t2tb1 v_OBF__wwcc))
  (add int (t2tb12 v_OBF__rrbb) (t2tb1 empty1)))
  (times int (tuple21 (tuple21 int int) int) (t2tb4 v_OBF__vvcc)
  (add int (t2tb12 v_OBF__mmbb) (t2tb1 empty1))))
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int) (t2tb6 v_OBF__xxcc) (t2tb1 v_OBF__wwcc))
  (add int (t2tb12 v_OBF__ffbb) (t2tb1 empty1))))
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int) (t2tb6 v_OBF__ccdd) (t2tb1 v_OBF__wwcc))
  (add int (t2tb12 v_OBF__jjdd) (t2tb1 empty1))))
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int) (t2tb6 v_OBF__eedd) (t2tb1 v_OBF__wwcc))
  (add int (t2tb12 v_OBF__kkdd) (t2tb1 empty1))))
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int)
  (times int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb))
  (t2tb1 v_OBF__wwcc)) (add int (t2tb12 v_OBF__lldd) (t2tb1 empty1)))))))
  (mem int (t2tb12 v_OBF__ddbb) (t2tb1 integer))) (mem int (t2tb12 v_OBF__tt)
  (t2tb1 v_OBF__eecc))) (mem int (t2tb12 v_OBF__vv) (t2tb1 v_OBF__bbbb)))
  (mem int (t2tb12 v_OBF__nnbb) (t2tb1 v_OBF__wwcc))) (mem int
  (t2tb12 v_OBF__eebb) (t2tb1 v_OBF__ffcc))) (mem
  (set1 (tuple21 (tuple21 (tuple21 int int) int) int)) (t2tb3 v_OBF__iidd)
  (power (tuple21 (tuple21 (tuple21 int int) int) int)
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int)
  (times int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb))
  (t2tb1 v_OBF__wwcc)) (t2tb1 v_OBF__ffcc)))))
  (=> (= v_OBF__ddbb 2) (infix_eqeq1 v_OBF__ggcc
  (tb2t1
  (inter int (t2tb1 v_OBF__ggbb)
  (image int int (inverse int int (t2tb6 v_OBF__vvbb))
  (add int (t2tb12 v_OBF__eebb) (t2tb1 empty1))))))))
  (=> (and (= v_OBF__ddbb 2) (= v_OBF__eebb v_OBF__ffbb)) (infix_eqeq1
  (tb2t1 (image int int (t2tb6 v_OBF__wwbb) (t2tb1 v_OBF__zz)))
  (tb2t1
  (image int int (t2tb6 v_OBF__kkcc)
  (add int (t2tb12 v_OBF__tt) (t2tb1 empty1)))))))
  (=> (and (= v_OBF__ddbb 2) (= v_OBF__eebb v_OBF__ffbb)) (infix_eqeq1
  v_OBF__ww
  (tb2t1
  (image int int (t2tb6 v_OBF__jjcc)
  (add int (t2tb12 v_OBF__tt) (t2tb1 empty1))))))) (infix_eqeq2
  (tb2t6
  (union (tuple21 int int) (t2tb6 v_OBF__kkcc)
  (range_substraction int int (t2tb6 v_OBF__jjcc)
  (image int int
  (times int int (add int (t2tb12 0) (t2tb1 empty1))
  (diff int (t2tb1 v_OBF__yy) (add int (t2tb12 v_OBF__vv) (t2tb1 empty1))))
  (add int (t2tb12 1) (t2tb1 empty1)))))) v_OBF__jjcc)) (infix_eqeq2
  (tb2t6
  (union (tuple21 int int) (t2tb6 v_OBF__kkcc)
  (range_substraction int int (t2tb6 v_OBF__jjcc)
  (image int int
  (times int int (add int (t2tb12 0) (t2tb1 empty1))
  (diff int (t2tb1 v_OBF__yy) (add int (t2tb12 v_OBF__vv) (t2tb1 empty1))))
  (add int (t2tb12 0) (t2tb1 empty1))))))
  (tb2t6
  (union (tuple21 int int) (t2tb6 v_OBF__kkcc)
  (range_substraction int int (t2tb6 v_OBF__jjcc)
  (diff int (t2tb1 v_OBF__yy) (add int (t2tb12 v_OBF__vv) (t2tb1 empty1))))))))
  (infix_eqeq2
  (tb2t6
  (union (tuple21 int int) (t2tb6 v_OBF__nndd)
  (range_substraction int int (t2tb6 v_OBF__oodd)
  (image int int
  (times int int (add int (t2tb12 0) (t2tb1 empty1))
  (diff int (t2tb1 v_OBF__ppdd)
  (add int (t2tb12 v_OBF__sscc) (t2tb1 empty1))))
  (add int (t2tb12 1) (t2tb1 empty1)))))) v_OBF__oodd)) (mem int
  (t2tb12 v_OBF__xx)
  (union int (add int (t2tb12 0) (t2tb1 empty1))
  (add int (t2tb12 1) (t2tb1 empty1))))) (mem
  (set1 (tuple21 (tuple21 int enum_OBF__aa1) int)) (t2tb2 v_OBF__hhdd)
  (infix_plmngt int (tuple21 int enum_OBF__aa1)
  (times enum_OBF__aa1 int
  (union int (add int (t2tb12 0) (t2tb1 empty1))
  (add int (t2tb12 1) (t2tb1 empty1))) (t2tb161 set_enum_OBF__aa))
  (union int (add int (t2tb12 0) (t2tb1 empty1))
  (add int (t2tb12 1) (t2tb1 empty1)))))) (infix_eqeq
  (tuple21 int enum_OBF__aa1)
  (dom int (tuple21 int enum_OBF__aa1) (t2tb2 v_OBF__hhdd))
  (times enum_OBF__aa1 int
  (union int (add int (t2tb12 0) (t2tb1 empty1))
  (add int (t2tb12 1) (t2tb1 empty1))) (t2tb161 set_enum_OBF__aa)))) (mem
  (set1 enum_OBF__ii1) (t2tb5 v_OBF__llbb)
  (power enum_OBF__ii1 (t2tb5 set_enum_OBF__ii))))
  (= v_OBF__qqdd v_OBF__ddbb)) (= v_OBF__rrdd v_OBF__tt))
  (= v_OBF__ssdd v_OBF__vv)) (= v_OBF__ttdd v_OBF__nnbb))
  (= v_OBF__uudd v_OBF__eebb)) (= v_OBF__vvdd v_OBF__mmdd))
  (= v_OBF__wwdd v_OBF__xx)) (= v_OBF__xxdd v_OBF__yycc))
  (= v_OBF__yydd v_OBF__zzcc)) (infix_eqeq2 v_OBF__zzdd v_OBF__aadd))
  (infix_eqeq2 v_OBF__aaee v_OBF__bbdd)) (= v_OBF__bbee v_OBF__oocc))
  (infix_eqeq1 v_OBF__ccee v_OBF__kkbb)) (infix_eqeq1 v_OBF__ddee v_OBF__yy))
  (infix_eqeq2 v_OBF__eeee v_OBF__uubb)) (infix_eqeq2 v_OBF__ffee
  v_OBF__cccc)) (infix_eqeq2 v_OBF__ggee v_OBF__wwbb)) (infix_eqeq2
  v_OBF__hhee v_OBF__vvbb)) (infix_eqeq1 v_OBF__iiee v_OBF__ttbb))
  (infix_eqeq1 v_OBF__jjee v_OBF__ggbb)) (infix_eqeq1 v_OBF__kkee
  v_OBF__ggcc)) (infix_eqeq1 v_OBF__llee v_OBF__ww)) (infix_eqeq1 v_OBF__mmee
  v_OBF__zz)) (infix_eqeq1 v_OBF__nnee v_OBF__ppbb)))))

(declare-fun f7 ((set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set Int)
  (set Int) (set (tuple2 Int Int)) Int Int (set Int) (set Int) (set Int) Int
  (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) Int (set Int)
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int)) Bool
  (set (tuple2 (tuple2 Int Int) Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) (set Int)
  (set (tuple2 Int Int)) Int Int (set Int) Int (set (tuple2 Int Int)) Int Int
  (set Int) (set (tuple2 Int Int)) Int (set Int) Int Int Int (set Int)
  (set Int) Int (set Int) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) Bool Int (set (tuple2 (tuple2 (tuple2 Int Int) Int)
  Int)) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Bool
  (set (tuple2 Int Int)) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set Int) Int (set (tuple2 Int Int)) (set enum_OBF__ii)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int (set (tuple2 Int
  Int)) (set Int) (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) (set (tuple2 Int Int)) (set enum_OBF__ii)
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) enum_OBF__aa (set Int)
  (set Int) (set (tuple2 (tuple2 Int Int) Int)) (set (tuple2 Int Int)) Int
  (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) Int (set Int) (set Int) Int (set Int) Int
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int
  Int)) Int (set (tuple2 Int Int)) Bool (set (tuple2 Int Int)) (set Int)
  (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int
  Int)) (set Int) Int) Bool)

;; f7_def
  (assert
  (forall ((v_OBF__zzee (set (tuple2 Int Int))) (v_OBF__zzdd (set (tuple2 Int
  Int))) (v_OBF__zzcc Int) (v_OBF__zzbb (set Int)) (v_OBF__zz (set Int))
  (v_OBF__yyee (set (tuple2 Int Int))) (v_OBF__yydd Int) (v_OBF__yycc Int)
  (v_OBF__yybb (set Int)) (v_OBF__yy (set Int)) (v_OBF__xxee (set Int))
  (v_OBF__xxdd Int) (v_OBF__xxcc (set (tuple2 Int Int))) (v_OBF__xxbb Int)
  (v_OBF__xx Int) (v_OBF__wwee (set (tuple2 Int Int))) (v_OBF__wwdd Int)
  (v_OBF__wwcc (set Int)) (v_OBF__wwbb (set (tuple2 Int Int)))
  (v_OBF__ww (set Int)) (v_OBF__vvee (set (tuple2 Int Int)))
  (v_OBF__vvdd Bool) (v_OBF__vvcc (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__vvbb (set (tuple2 Int Int))) (v_OBF__vv Int)
  (v_OBF__uuee (set (tuple2 Int Int))) (v_OBF__uudd Int) (v_OBF__uucc Int)
  (v_OBF__uubb (set (tuple2 Int Int))) (v_OBF__uu (set Int))
  (v_OBF__ttee (set (tuple2 Int Int))) (v_OBF__ttdd Int) (v_OBF__ttcc Int)
  (v_OBF__ttbb (set Int)) (v_OBF__tt Int) (v_OBF__ssee (set (tuple2 Int
  Int))) (v_OBF__ssdd Int) (v_OBF__sscc Int) (v_OBF__ssbb (set Int))
  (v_OBF__rree (set (tuple2 Int Int))) (v_OBF__rrdd Int)
  (v_OBF__rrcc (set Int)) (v_OBF__rrbb Int) (v_OBF__qqee Int)
  (v_OBF__qqdd Int) (v_OBF__qqcc (set Int)) (v_OBF__qqbb (set Int))
  (v_OBF__ppee Int) (v_OBF__ppdd (set Int)) (v_OBF__ppcc (set (tuple2 Int
  Int))) (v_OBF__ppbb (set Int)) (v_OBF__ooee Int)
  (v_OBF__oodd (set (tuple2 Int Int))) (v_OBF__oocc Bool) (v_OBF__oobb Int)
  (v_OBF__nnff (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__nnee (set Int)) (v_OBF__nndd (set (tuple2 Int Int)))
  (v_OBF__nncc (set (tuple2 Int Int))) (v_OBF__nnbb Int)
  (v_OBF__mmff (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__mmee (set Int)) (v_OBF__mmdd Bool) (v_OBF__mmcc (set (tuple2 Int
  Int))) (v_OBF__mmbb Int) (v_OBF__llff (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (v_OBF__llee (set Int)) (v_OBF__lldd Int)
  (v_OBF__llcc (set (tuple2 Int Int))) (v_OBF__llbb (set enum_OBF__ii))
  (v_OBF__kkff (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__kkee (set Int)) (v_OBF__kkdd Int) (v_OBF__kkcc (set (tuple2 Int
  Int))) (v_OBF__kkbb (set Int)) (v_OBF__jjff (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (v_OBF__jjee (set Int)) (v_OBF__jjdd Int)
  (v_OBF__jjcc (set (tuple2 Int Int))) (v_OBF__jjbb Int)
  (v_OBF__iiff (set (tuple2 Int Int))) (v_OBF__iiee (set Int))
  (v_OBF__iidd (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb Int)
  (v_OBF__hhff (set (tuple2 Int Int))) (v_OBF__hhee (set (tuple2 Int Int)))
  (v_OBF__hhdd (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__hhcc (set (tuple2 Int Int))) (v_OBF__hhbb (set enum_OBF__ii))
  (v_OBF__ggff (set (tuple2 Int Int))) (v_OBF__ggee (set (tuple2 Int Int)))
  (v_OBF__ggdd enum_OBF__aa) (v_OBF__ggcc (set Int)) (v_OBF__ggbb (set Int))
  (v_OBF__ffff (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__ffee (set (tuple2 Int Int))) (v_OBF__ffdd Int)
  (v_OBF__ffcc (set Int)) (v_OBF__ffbb Int) (v_OBF__eeff (set (tuple2 Int
  Int))) (v_OBF__eeee (set (tuple2 Int Int))) (v_OBF__eedd (set (tuple2 Int
  Int))) (v_OBF__eecc (set Int)) (v_OBF__eebb Int) (v_OBF__ddff (set Int))
  (v_OBF__ddee (set Int)) (v_OBF__dddd Int) (v_OBF__ddcc (set Int))
  (v_OBF__ddbb Int) (v_OBF__ccff (set (tuple2 Int Int)))
  (v_OBF__ccee (set Int)) (v_OBF__ccdd (set (tuple2 Int Int)))
  (v_OBF__cccc (set (tuple2 Int Int))) (v_OBF__ccbb Int)
  (v_OBF__bbff (set (tuple2 Int Int))) (v_OBF__bbee Bool)
  (v_OBF__bbdd (set (tuple2 Int Int))) (v_OBF__bbcc (set Int))
  (v_OBF__bbbb (set Int)) (v_OBF__aaff (set (tuple2 Int Int)))
  (v_OBF__aaee (set (tuple2 Int Int))) (v_OBF__aadd (set (tuple2 Int Int)))
  (v_OBF__aacc (set Int)) (v_OBF__aabb Int))
  (= (f7 v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb v_OBF__zz
  v_OBF__yyee v_OBF__yydd v_OBF__yycc v_OBF__yybb v_OBF__yy v_OBF__xxee
  v_OBF__xxdd v_OBF__xxcc v_OBF__xxbb v_OBF__xx v_OBF__wwee v_OBF__wwdd
  v_OBF__wwcc v_OBF__wwbb v_OBF__ww v_OBF__vvee v_OBF__vvdd v_OBF__vvcc
  v_OBF__vvbb v_OBF__vv v_OBF__uuee v_OBF__uudd v_OBF__uucc v_OBF__uubb
  v_OBF__uu v_OBF__ttee v_OBF__ttdd v_OBF__ttcc v_OBF__ttbb v_OBF__tt
  v_OBF__ssee v_OBF__ssdd v_OBF__sscc v_OBF__ssbb v_OBF__rree v_OBF__rrdd
  v_OBF__rrcc v_OBF__rrbb v_OBF__qqee v_OBF__qqdd v_OBF__qqcc v_OBF__qqbb
  v_OBF__ppee v_OBF__ppdd v_OBF__ppcc v_OBF__ppbb v_OBF__ooee v_OBF__oodd
  v_OBF__oocc v_OBF__oobb v_OBF__nnff v_OBF__nnee v_OBF__nndd v_OBF__nncc
  v_OBF__nnbb v_OBF__mmff v_OBF__mmee v_OBF__mmdd v_OBF__mmcc v_OBF__mmbb
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkff
  v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjff v_OBF__jjee
  v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iiff v_OBF__iiee v_OBF__iidd
  v_OBF__iicc v_OBF__iibb v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc
  v_OBF__hhbb v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb
  v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb v_OBF__eeff
  v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb v_OBF__ddff v_OBF__ddee
  v_OBF__dddd v_OBF__ddcc v_OBF__ddbb v_OBF__ccff v_OBF__ccee v_OBF__ccdd
  v_OBF__cccc v_OBF__ccbb v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc
  v_OBF__bbbb v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (and
  (and
  (and
  (and
  (and (infix_eqeq1 v_OBF__ssbb
  (tb2t1
  (inter int (t2tb1 v_OBF__zzbb)
  (image int int (inverse int int (t2tb6 v_OBF__wwbb))
  (union int (add int (t2tb12 v_OBF__vv) (t2tb1 empty1))
  (add int (t2tb12 v_OBF__xxbb) (t2tb1 empty1))))))) (= v_OBF__ddbb 1))
  (infix_eqeq1 v_OBF__aacc
  (tb2t1
  (inter int (t2tb1 v_OBF__ttbb)
  (image int int (inverse int int (t2tb6 v_OBF__uubb))
  (add int (t2tb12 v_OBF__tt) (t2tb1 empty1))))))) (infix_eqeq1 v_OBF__zzbb
  (tb2t1
  (inter int (t2tb1 v_OBF__aacc)
  (image int int (inverse int int (t2tb6 v_OBF__vvbb))
  (add int (t2tb12 v_OBF__eebb) (t2tb1 empty1))))))) (infix_eqeq1 v_OBF__yybb
  (tb2t1 (image int int (t2tb6 v_OBF__wwbb) (t2tb1 v_OBF__zzbb)))))
  (infix_eqeq1 v_OBF__bbcc
  (tb2t1
  (inter int
  (inter int (t2tb1 v_OBF__ttbb)
  (image int int (inverse int int (t2tb6 v_OBF__cccc))
  (add int (t2tb12 v_OBF__tt) (t2tb1 empty1))))
  (image int int (inverse int int (t2tb6 v_OBF__vvbb))
  (add int (t2tb12 v_OBF__eebb) (t2tb1 empty1))))))))))

(declare-fun f9 ((set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set Int)
  (set Int) (set (tuple2 Int Int)) Int Int (set Int) (set Int) (set Int) Int
  (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) Int (set Int)
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int)) Bool
  (set (tuple2 (tuple2 Int Int) Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) (set Int)
  (set (tuple2 Int Int)) Int Int (set Int) Int (set (tuple2 Int Int)) Int Int
  (set Int) (set (tuple2 Int Int)) Int (set Int) Int Int Int (set Int)
  (set Int) Int (set Int) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) Bool Int (set (tuple2 (tuple2 (tuple2 Int Int) Int)
  Int)) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Bool
  (set (tuple2 Int Int)) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set Int) Int (set (tuple2 Int Int)) (set enum_OBF__ii)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int (set (tuple2 Int
  Int)) (set Int) (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) (set (tuple2 Int Int)) (set enum_OBF__ii)
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) enum_OBF__aa (set Int)
  (set Int) (set (tuple2 (tuple2 Int Int) Int)) (set (tuple2 Int Int)) Int
  (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) Int (set Int) (set Int) Int (set Int) Int
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int
  Int)) Int (set (tuple2 Int Int)) Bool (set (tuple2 Int Int)) (set Int)
  (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int
  Int)) (set Int) Int) Bool)

;; f9_def
  (assert
  (forall ((v_OBF__zzee (set (tuple2 Int Int))) (v_OBF__zzdd (set (tuple2 Int
  Int))) (v_OBF__zzcc Int) (v_OBF__zzbb (set Int)) (v_OBF__zz (set Int))
  (v_OBF__yyee (set (tuple2 Int Int))) (v_OBF__yydd Int) (v_OBF__yycc Int)
  (v_OBF__yybb (set Int)) (v_OBF__yy (set Int)) (v_OBF__xxee (set Int))
  (v_OBF__xxdd Int) (v_OBF__xxcc (set (tuple2 Int Int))) (v_OBF__xxbb Int)
  (v_OBF__xx Int) (v_OBF__wwee (set (tuple2 Int Int))) (v_OBF__wwdd Int)
  (v_OBF__wwcc (set Int)) (v_OBF__wwbb (set (tuple2 Int Int)))
  (v_OBF__ww (set Int)) (v_OBF__vvee (set (tuple2 Int Int)))
  (v_OBF__vvdd Bool) (v_OBF__vvcc (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__vvbb (set (tuple2 Int Int))) (v_OBF__vv Int)
  (v_OBF__uuee (set (tuple2 Int Int))) (v_OBF__uudd Int) (v_OBF__uucc Int)
  (v_OBF__uubb (set (tuple2 Int Int))) (v_OBF__uu (set Int))
  (v_OBF__ttee (set (tuple2 Int Int))) (v_OBF__ttdd Int) (v_OBF__ttcc Int)
  (v_OBF__ttbb (set Int)) (v_OBF__tt Int) (v_OBF__ssee (set (tuple2 Int
  Int))) (v_OBF__ssdd Int) (v_OBF__sscc Int) (v_OBF__ssbb (set Int))
  (v_OBF__rree (set (tuple2 Int Int))) (v_OBF__rrdd Int)
  (v_OBF__rrcc (set Int)) (v_OBF__rrbb Int) (v_OBF__qqee Int)
  (v_OBF__qqdd Int) (v_OBF__qqcc (set Int)) (v_OBF__qqbb (set Int))
  (v_OBF__ppee Int) (v_OBF__ppdd (set Int)) (v_OBF__ppcc (set (tuple2 Int
  Int))) (v_OBF__ppbb (set Int)) (v_OBF__ooee Int)
  (v_OBF__oodd (set (tuple2 Int Int))) (v_OBF__oocc Bool) (v_OBF__oobb Int)
  (v_OBF__nnff (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__nnee (set Int)) (v_OBF__nndd (set (tuple2 Int Int)))
  (v_OBF__nncc (set (tuple2 Int Int))) (v_OBF__nnbb Int)
  (v_OBF__mmff (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__mmee (set Int)) (v_OBF__mmdd Bool) (v_OBF__mmcc (set (tuple2 Int
  Int))) (v_OBF__mmbb Int) (v_OBF__llff (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (v_OBF__llee (set Int)) (v_OBF__lldd Int)
  (v_OBF__llcc (set (tuple2 Int Int))) (v_OBF__llbb (set enum_OBF__ii))
  (v_OBF__kkff (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__kkee (set Int)) (v_OBF__kkdd Int) (v_OBF__kkcc (set (tuple2 Int
  Int))) (v_OBF__kkbb (set Int)) (v_OBF__jjff (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (v_OBF__jjee (set Int)) (v_OBF__jjdd Int)
  (v_OBF__jjcc (set (tuple2 Int Int))) (v_OBF__jjbb Int)
  (v_OBF__iiff (set (tuple2 Int Int))) (v_OBF__iiee (set Int))
  (v_OBF__iidd (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb Int)
  (v_OBF__hhff (set (tuple2 Int Int))) (v_OBF__hhee (set (tuple2 Int Int)))
  (v_OBF__hhdd (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__hhcc (set (tuple2 Int Int))) (v_OBF__hhbb (set enum_OBF__ii))
  (v_OBF__ggff (set (tuple2 Int Int))) (v_OBF__ggee (set (tuple2 Int Int)))
  (v_OBF__ggdd enum_OBF__aa) (v_OBF__ggcc (set Int)) (v_OBF__ggbb (set Int))
  (v_OBF__ffff (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__ffee (set (tuple2 Int Int))) (v_OBF__ffdd Int)
  (v_OBF__ffcc (set Int)) (v_OBF__ffbb Int) (v_OBF__eeff (set (tuple2 Int
  Int))) (v_OBF__eeee (set (tuple2 Int Int))) (v_OBF__eedd (set (tuple2 Int
  Int))) (v_OBF__eecc (set Int)) (v_OBF__eebb Int) (v_OBF__ddff (set Int))
  (v_OBF__ddee (set Int)) (v_OBF__dddd Int) (v_OBF__ddcc (set Int))
  (v_OBF__ddbb Int) (v_OBF__ccff (set (tuple2 Int Int)))
  (v_OBF__ccee (set Int)) (v_OBF__ccdd (set (tuple2 Int Int)))
  (v_OBF__cccc (set (tuple2 Int Int))) (v_OBF__ccbb Int)
  (v_OBF__bbff (set (tuple2 Int Int))) (v_OBF__bbee Bool)
  (v_OBF__bbdd (set (tuple2 Int Int))) (v_OBF__bbcc (set Int))
  (v_OBF__bbbb (set Int)) (v_OBF__aaff (set (tuple2 Int Int)))
  (v_OBF__aaee (set (tuple2 Int Int))) (v_OBF__aadd (set (tuple2 Int Int)))
  (v_OBF__aacc (set Int)) (v_OBF__aabb Int))
  (= (f9 v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb v_OBF__zz
  v_OBF__yyee v_OBF__yydd v_OBF__yycc v_OBF__yybb v_OBF__yy v_OBF__xxee
  v_OBF__xxdd v_OBF__xxcc v_OBF__xxbb v_OBF__xx v_OBF__wwee v_OBF__wwdd
  v_OBF__wwcc v_OBF__wwbb v_OBF__ww v_OBF__vvee v_OBF__vvdd v_OBF__vvcc
  v_OBF__vvbb v_OBF__vv v_OBF__uuee v_OBF__uudd v_OBF__uucc v_OBF__uubb
  v_OBF__uu v_OBF__ttee v_OBF__ttdd v_OBF__ttcc v_OBF__ttbb v_OBF__tt
  v_OBF__ssee v_OBF__ssdd v_OBF__sscc v_OBF__ssbb v_OBF__rree v_OBF__rrdd
  v_OBF__rrcc v_OBF__rrbb v_OBF__qqee v_OBF__qqdd v_OBF__qqcc v_OBF__qqbb
  v_OBF__ppee v_OBF__ppdd v_OBF__ppcc v_OBF__ppbb v_OBF__ooee v_OBF__oodd
  v_OBF__oocc v_OBF__oobb v_OBF__nnff v_OBF__nnee v_OBF__nndd v_OBF__nncc
  v_OBF__nnbb v_OBF__mmff v_OBF__mmee v_OBF__mmdd v_OBF__mmcc v_OBF__mmbb
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkff
  v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjff v_OBF__jjee
  v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iiff v_OBF__iiee v_OBF__iidd
  v_OBF__iicc v_OBF__iibb v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc
  v_OBF__hhbb v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb
  v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb v_OBF__eeff
  v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb v_OBF__ddff v_OBF__ddee
  v_OBF__dddd v_OBF__ddcc v_OBF__ddbb v_OBF__ccff v_OBF__ccee v_OBF__ccdd
  v_OBF__cccc v_OBF__ccbb v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc
  v_OBF__bbbb v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (infix_eqeq1 v_OBF__zzbb
  (tb2t1
  (inter int
  (inter int (t2tb1 v_OBF__ttbb)
  (image int int (inverse int int (t2tb6 v_OBF__uubb))
  (add int (t2tb12 v_OBF__tt) (t2tb1 empty1))))
  (image int int (inverse int int (t2tb6 v_OBF__vvbb))
  (add int (t2tb12 v_OBF__eebb) (t2tb1 empty1)))))))))

(declare-fun f11 ((set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set Int)
  (set Int) (set (tuple2 Int Int)) Int Int (set Int) (set Int) (set Int) Int
  (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) Int (set Int)
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int)) Bool
  (set (tuple2 (tuple2 Int Int) Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) (set Int)
  (set (tuple2 Int Int)) Int Int (set Int) Int (set (tuple2 Int Int)) Int Int
  (set Int) (set (tuple2 Int Int)) Int (set Int) Int Int Int (set Int)
  (set Int) Int (set Int) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) Bool Int (set (tuple2 (tuple2 (tuple2 Int Int) Int)
  Int)) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Bool
  (set (tuple2 Int Int)) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set Int) Int (set (tuple2 Int Int)) (set enum_OBF__ii)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int (set (tuple2 Int
  Int)) (set Int) (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) (set (tuple2 Int Int)) (set enum_OBF__ii)
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) enum_OBF__aa (set Int)
  (set Int) (set (tuple2 (tuple2 Int Int) Int)) (set (tuple2 Int Int)) Int
  (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) Int (set Int) (set Int) Int (set Int) Int
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int
  Int)) Int (set (tuple2 Int Int)) Bool (set (tuple2 Int Int)) (set Int)
  (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int
  Int)) (set Int) Int) Bool)

;; f11_def
  (assert
  (forall ((v_OBF__zzee (set (tuple2 Int Int))) (v_OBF__zzdd (set (tuple2 Int
  Int))) (v_OBF__zzcc Int) (v_OBF__zzbb (set Int)) (v_OBF__zz (set Int))
  (v_OBF__yyee (set (tuple2 Int Int))) (v_OBF__yydd Int) (v_OBF__yycc Int)
  (v_OBF__yybb (set Int)) (v_OBF__yy (set Int)) (v_OBF__xxee (set Int))
  (v_OBF__xxdd Int) (v_OBF__xxcc (set (tuple2 Int Int))) (v_OBF__xxbb Int)
  (v_OBF__xx Int) (v_OBF__wwee (set (tuple2 Int Int))) (v_OBF__wwdd Int)
  (v_OBF__wwcc (set Int)) (v_OBF__wwbb (set (tuple2 Int Int)))
  (v_OBF__ww (set Int)) (v_OBF__vvee (set (tuple2 Int Int)))
  (v_OBF__vvdd Bool) (v_OBF__vvcc (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__vvbb (set (tuple2 Int Int))) (v_OBF__vv Int)
  (v_OBF__uuee (set (tuple2 Int Int))) (v_OBF__uudd Int) (v_OBF__uucc Int)
  (v_OBF__uubb (set (tuple2 Int Int))) (v_OBF__uu (set Int))
  (v_OBF__ttee (set (tuple2 Int Int))) (v_OBF__ttdd Int) (v_OBF__ttcc Int)
  (v_OBF__ttbb (set Int)) (v_OBF__tt Int) (v_OBF__ssee (set (tuple2 Int
  Int))) (v_OBF__ssdd Int) (v_OBF__sscc Int) (v_OBF__ssbb (set Int))
  (v_OBF__rree (set (tuple2 Int Int))) (v_OBF__rrdd Int)
  (v_OBF__rrcc (set Int)) (v_OBF__rrbb Int) (v_OBF__qqee Int)
  (v_OBF__qqdd Int) (v_OBF__qqcc (set Int)) (v_OBF__qqbb (set Int))
  (v_OBF__ppee Int) (v_OBF__ppdd (set Int)) (v_OBF__ppcc (set (tuple2 Int
  Int))) (v_OBF__ppbb (set Int)) (v_OBF__ooee Int)
  (v_OBF__oodd (set (tuple2 Int Int))) (v_OBF__oocc Bool) (v_OBF__oobb Int)
  (v_OBF__nnff (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__nnee (set Int)) (v_OBF__nndd (set (tuple2 Int Int)))
  (v_OBF__nncc (set (tuple2 Int Int))) (v_OBF__nnbb Int)
  (v_OBF__mmff (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__mmee (set Int)) (v_OBF__mmdd Bool) (v_OBF__mmcc (set (tuple2 Int
  Int))) (v_OBF__mmbb Int) (v_OBF__llff (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (v_OBF__llee (set Int)) (v_OBF__lldd Int)
  (v_OBF__llcc (set (tuple2 Int Int))) (v_OBF__llbb (set enum_OBF__ii))
  (v_OBF__kkff (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__kkee (set Int)) (v_OBF__kkdd Int) (v_OBF__kkcc (set (tuple2 Int
  Int))) (v_OBF__kkbb (set Int)) (v_OBF__jjff (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (v_OBF__jjee (set Int)) (v_OBF__jjdd Int)
  (v_OBF__jjcc (set (tuple2 Int Int))) (v_OBF__jjbb Int)
  (v_OBF__iiff (set (tuple2 Int Int))) (v_OBF__iiee (set Int))
  (v_OBF__iidd (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb Int)
  (v_OBF__hhff (set (tuple2 Int Int))) (v_OBF__hhee (set (tuple2 Int Int)))
  (v_OBF__hhdd (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__hhcc (set (tuple2 Int Int))) (v_OBF__hhbb (set enum_OBF__ii))
  (v_OBF__ggff (set (tuple2 Int Int))) (v_OBF__ggee (set (tuple2 Int Int)))
  (v_OBF__ggdd enum_OBF__aa) (v_OBF__ggcc (set Int)) (v_OBF__ggbb (set Int))
  (v_OBF__ffff (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__ffee (set (tuple2 Int Int))) (v_OBF__ffdd Int)
  (v_OBF__ffcc (set Int)) (v_OBF__ffbb Int) (v_OBF__eeff (set (tuple2 Int
  Int))) (v_OBF__eeee (set (tuple2 Int Int))) (v_OBF__eedd (set (tuple2 Int
  Int))) (v_OBF__eecc (set Int)) (v_OBF__eebb Int) (v_OBF__ddff (set Int))
  (v_OBF__ddee (set Int)) (v_OBF__dddd Int) (v_OBF__ddcc (set Int))
  (v_OBF__ddbb Int) (v_OBF__ccff (set (tuple2 Int Int)))
  (v_OBF__ccee (set Int)) (v_OBF__ccdd (set (tuple2 Int Int)))
  (v_OBF__cccc (set (tuple2 Int Int))) (v_OBF__ccbb Int)
  (v_OBF__bbff (set (tuple2 Int Int))) (v_OBF__bbee Bool)
  (v_OBF__bbdd (set (tuple2 Int Int))) (v_OBF__bbcc (set Int))
  (v_OBF__bbbb (set Int)) (v_OBF__aaff (set (tuple2 Int Int)))
  (v_OBF__aaee (set (tuple2 Int Int))) (v_OBF__aadd (set (tuple2 Int Int)))
  (v_OBF__aacc (set Int)) (v_OBF__aabb Int))
  (= (f11 v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb v_OBF__zz
  v_OBF__yyee v_OBF__yydd v_OBF__yycc v_OBF__yybb v_OBF__yy v_OBF__xxee
  v_OBF__xxdd v_OBF__xxcc v_OBF__xxbb v_OBF__xx v_OBF__wwee v_OBF__wwdd
  v_OBF__wwcc v_OBF__wwbb v_OBF__ww v_OBF__vvee v_OBF__vvdd v_OBF__vvcc
  v_OBF__vvbb v_OBF__vv v_OBF__uuee v_OBF__uudd v_OBF__uucc v_OBF__uubb
  v_OBF__uu v_OBF__ttee v_OBF__ttdd v_OBF__ttcc v_OBF__ttbb v_OBF__tt
  v_OBF__ssee v_OBF__ssdd v_OBF__sscc v_OBF__ssbb v_OBF__rree v_OBF__rrdd
  v_OBF__rrcc v_OBF__rrbb v_OBF__qqee v_OBF__qqdd v_OBF__qqcc v_OBF__qqbb
  v_OBF__ppee v_OBF__ppdd v_OBF__ppcc v_OBF__ppbb v_OBF__ooee v_OBF__oodd
  v_OBF__oocc v_OBF__oobb v_OBF__nnff v_OBF__nnee v_OBF__nndd v_OBF__nncc
  v_OBF__nnbb v_OBF__mmff v_OBF__mmee v_OBF__mmdd v_OBF__mmcc v_OBF__mmbb
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkff
  v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjff v_OBF__jjee
  v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iiff v_OBF__iiee v_OBF__iidd
  v_OBF__iicc v_OBF__iibb v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc
  v_OBF__hhbb v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb
  v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb v_OBF__eeff
  v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb v_OBF__ddff v_OBF__ddee
  v_OBF__dddd v_OBF__ddcc v_OBF__ddbb v_OBF__ccff v_OBF__ccee v_OBF__ccdd
  v_OBF__cccc v_OBF__ccbb v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc
  v_OBF__bbbb v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (infix_eqeq1 v_OBF__yybb
  (tb2t1
  (image int int (t2tb6 v_OBF__wwbb)
  (inter int
  (inter int (t2tb1 v_OBF__ttbb)
  (image int int (inverse int int (t2tb6 v_OBF__uubb))
  (add int (t2tb12 v_OBF__tt) (t2tb1 empty1))))
  (image int int (inverse int int (t2tb6 v_OBF__vvbb))
  (add int (t2tb12 v_OBF__eebb) (t2tb1 empty1))))))))))

(declare-fun f13 ((set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set Int)
  (set Int) (set (tuple2 Int Int)) Int Int (set Int) (set Int) (set Int) Int
  (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) Int (set Int)
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int)) Bool
  (set (tuple2 (tuple2 Int Int) Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) (set Int)
  (set (tuple2 Int Int)) Int Int (set Int) Int (set (tuple2 Int Int)) Int Int
  (set Int) (set (tuple2 Int Int)) Int (set Int) Int Int Int (set Int)
  (set Int) Int (set Int) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) Bool Int (set (tuple2 (tuple2 (tuple2 Int Int) Int)
  Int)) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Bool
  (set (tuple2 Int Int)) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set Int) Int (set (tuple2 Int Int)) (set enum_OBF__ii)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int (set (tuple2 Int
  Int)) (set Int) (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) (set (tuple2 Int Int)) (set enum_OBF__ii)
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) enum_OBF__aa (set Int)
  (set Int) (set (tuple2 (tuple2 Int Int) Int)) (set (tuple2 Int Int)) Int
  (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) Int (set Int) (set Int) Int (set Int) Int
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int
  Int)) Int (set (tuple2 Int Int)) Bool (set (tuple2 Int Int)) (set Int)
  (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int
  Int)) (set Int) Int) Bool)

;; f13_def
  (assert
  (forall ((v_OBF__zzee (set (tuple2 Int Int))) (v_OBF__zzdd (set (tuple2 Int
  Int))) (v_OBF__zzcc Int) (v_OBF__zzbb (set Int)) (v_OBF__zz (set Int))
  (v_OBF__yyee (set (tuple2 Int Int))) (v_OBF__yydd Int) (v_OBF__yycc Int)
  (v_OBF__yybb (set Int)) (v_OBF__yy (set Int)) (v_OBF__xxee (set Int))
  (v_OBF__xxdd Int) (v_OBF__xxcc (set (tuple2 Int Int))) (v_OBF__xxbb Int)
  (v_OBF__xx Int) (v_OBF__wwee (set (tuple2 Int Int))) (v_OBF__wwdd Int)
  (v_OBF__wwcc (set Int)) (v_OBF__wwbb (set (tuple2 Int Int)))
  (v_OBF__ww (set Int)) (v_OBF__vvee (set (tuple2 Int Int)))
  (v_OBF__vvdd Bool) (v_OBF__vvcc (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__vvbb (set (tuple2 Int Int))) (v_OBF__vv Int)
  (v_OBF__uuee (set (tuple2 Int Int))) (v_OBF__uudd Int) (v_OBF__uucc Int)
  (v_OBF__uubb (set (tuple2 Int Int))) (v_OBF__uu (set Int))
  (v_OBF__ttee (set (tuple2 Int Int))) (v_OBF__ttdd Int) (v_OBF__ttcc Int)
  (v_OBF__ttbb (set Int)) (v_OBF__tt Int) (v_OBF__ssee (set (tuple2 Int
  Int))) (v_OBF__ssdd Int) (v_OBF__sscc Int) (v_OBF__ssbb (set Int))
  (v_OBF__rree (set (tuple2 Int Int))) (v_OBF__rrdd Int)
  (v_OBF__rrcc (set Int)) (v_OBF__rrbb Int) (v_OBF__qqee Int)
  (v_OBF__qqdd Int) (v_OBF__qqcc (set Int)) (v_OBF__qqbb (set Int))
  (v_OBF__ppee Int) (v_OBF__ppdd (set Int)) (v_OBF__ppcc (set (tuple2 Int
  Int))) (v_OBF__ppbb (set Int)) (v_OBF__ooee Int)
  (v_OBF__oodd (set (tuple2 Int Int))) (v_OBF__oocc Bool) (v_OBF__oobb Int)
  (v_OBF__nnff (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__nnee (set Int)) (v_OBF__nndd (set (tuple2 Int Int)))
  (v_OBF__nncc (set (tuple2 Int Int))) (v_OBF__nnbb Int)
  (v_OBF__mmff (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__mmee (set Int)) (v_OBF__mmdd Bool) (v_OBF__mmcc (set (tuple2 Int
  Int))) (v_OBF__mmbb Int) (v_OBF__llff (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (v_OBF__llee (set Int)) (v_OBF__lldd Int)
  (v_OBF__llcc (set (tuple2 Int Int))) (v_OBF__llbb (set enum_OBF__ii))
  (v_OBF__kkff (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__kkee (set Int)) (v_OBF__kkdd Int) (v_OBF__kkcc (set (tuple2 Int
  Int))) (v_OBF__kkbb (set Int)) (v_OBF__jjff (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (v_OBF__jjee (set Int)) (v_OBF__jjdd Int)
  (v_OBF__jjcc (set (tuple2 Int Int))) (v_OBF__jjbb Int)
  (v_OBF__iiff (set (tuple2 Int Int))) (v_OBF__iiee (set Int))
  (v_OBF__iidd (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb Int)
  (v_OBF__hhff (set (tuple2 Int Int))) (v_OBF__hhee (set (tuple2 Int Int)))
  (v_OBF__hhdd (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__hhcc (set (tuple2 Int Int))) (v_OBF__hhbb (set enum_OBF__ii))
  (v_OBF__ggff (set (tuple2 Int Int))) (v_OBF__ggee (set (tuple2 Int Int)))
  (v_OBF__ggdd enum_OBF__aa) (v_OBF__ggcc (set Int)) (v_OBF__ggbb (set Int))
  (v_OBF__ffff (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__ffee (set (tuple2 Int Int))) (v_OBF__ffdd Int)
  (v_OBF__ffcc (set Int)) (v_OBF__ffbb Int) (v_OBF__eeff (set (tuple2 Int
  Int))) (v_OBF__eeee (set (tuple2 Int Int))) (v_OBF__eedd (set (tuple2 Int
  Int))) (v_OBF__eecc (set Int)) (v_OBF__eebb Int) (v_OBF__ddff (set Int))
  (v_OBF__ddee (set Int)) (v_OBF__dddd Int) (v_OBF__ddcc (set Int))
  (v_OBF__ddbb Int) (v_OBF__ccff (set (tuple2 Int Int)))
  (v_OBF__ccee (set Int)) (v_OBF__ccdd (set (tuple2 Int Int)))
  (v_OBF__cccc (set (tuple2 Int Int))) (v_OBF__ccbb Int)
  (v_OBF__bbff (set (tuple2 Int Int))) (v_OBF__bbee Bool)
  (v_OBF__bbdd (set (tuple2 Int Int))) (v_OBF__bbcc (set Int))
  (v_OBF__bbbb (set Int)) (v_OBF__aaff (set (tuple2 Int Int)))
  (v_OBF__aaee (set (tuple2 Int Int))) (v_OBF__aadd (set (tuple2 Int Int)))
  (v_OBF__aacc (set Int)) (v_OBF__aabb Int))
  (= (f13 v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb v_OBF__zz
  v_OBF__yyee v_OBF__yydd v_OBF__yycc v_OBF__yybb v_OBF__yy v_OBF__xxee
  v_OBF__xxdd v_OBF__xxcc v_OBF__xxbb v_OBF__xx v_OBF__wwee v_OBF__wwdd
  v_OBF__wwcc v_OBF__wwbb v_OBF__ww v_OBF__vvee v_OBF__vvdd v_OBF__vvcc
  v_OBF__vvbb v_OBF__vv v_OBF__uuee v_OBF__uudd v_OBF__uucc v_OBF__uubb
  v_OBF__uu v_OBF__ttee v_OBF__ttdd v_OBF__ttcc v_OBF__ttbb v_OBF__tt
  v_OBF__ssee v_OBF__ssdd v_OBF__sscc v_OBF__ssbb v_OBF__rree v_OBF__rrdd
  v_OBF__rrcc v_OBF__rrbb v_OBF__qqee v_OBF__qqdd v_OBF__qqcc v_OBF__qqbb
  v_OBF__ppee v_OBF__ppdd v_OBF__ppcc v_OBF__ppbb v_OBF__ooee v_OBF__oodd
  v_OBF__oocc v_OBF__oobb v_OBF__nnff v_OBF__nnee v_OBF__nndd v_OBF__nncc
  v_OBF__nnbb v_OBF__mmff v_OBF__mmee v_OBF__mmdd v_OBF__mmcc v_OBF__mmbb
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkff
  v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjff v_OBF__jjee
  v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iiff v_OBF__iiee v_OBF__iidd
  v_OBF__iicc v_OBF__iibb v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc
  v_OBF__hhbb v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb
  v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb v_OBF__eeff
  v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb v_OBF__ddff v_OBF__ddee
  v_OBF__dddd v_OBF__ddcc v_OBF__ddbb v_OBF__ccff v_OBF__ccee v_OBF__ccdd
  v_OBF__cccc v_OBF__ccbb v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc
  v_OBF__bbbb v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (infix_eqeq1 v_OBF__ssbb
  (tb2t1
  (inter int
  (inter int
  (inter int (t2tb1 v_OBF__ttbb)
  (image int int (inverse int int (t2tb6 v_OBF__uubb))
  (add int (t2tb12 v_OBF__tt) (t2tb1 empty1))))
  (image int int (inverse int int (t2tb6 v_OBF__vvbb))
  (add int (t2tb12 v_OBF__eebb) (t2tb1 empty1))))
  (image int int (inverse int int (t2tb6 v_OBF__wwbb))
  (union int (add int (t2tb12 v_OBF__vv) (t2tb1 empty1))
  (add int (t2tb12 v_OBF__xxbb) (t2tb1 empty1))))))))))

(declare-fun f18 ((set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set Int)
  (set Int) (set (tuple2 Int Int)) Int Int (set Int) (set Int) (set Int) Int
  (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) Int (set Int)
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int)) Bool
  (set (tuple2 (tuple2 Int Int) Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) (set Int)
  (set (tuple2 Int Int)) Int Int (set Int) Int (set (tuple2 Int Int)) Int Int
  (set Int) (set (tuple2 Int Int)) Int (set Int) Int Int Int (set Int)
  (set Int) Int (set Int) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) Bool Int (set (tuple2 (tuple2 (tuple2 Int Int) Int)
  Int)) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Bool
  (set (tuple2 Int Int)) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set Int) Int (set (tuple2 Int Int)) (set enum_OBF__ii)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int (set (tuple2 Int
  Int)) (set Int) (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) (set (tuple2 Int Int)) (set enum_OBF__ii)
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) enum_OBF__aa (set Int)
  (set Int) (set (tuple2 (tuple2 Int Int) Int)) (set (tuple2 Int Int)) Int
  (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) Int (set Int) (set Int) Int (set Int) Int
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int
  Int)) Int (set (tuple2 Int Int)) Bool (set (tuple2 Int Int)) (set Int)
  (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int
  Int)) (set Int) Int) Bool)

;; f18_def
  (assert
  (forall ((v_OBF__zzee (set (tuple2 Int Int))) (v_OBF__zzdd (set (tuple2 Int
  Int))) (v_OBF__zzcc Int) (v_OBF__zzbb (set Int)) (v_OBF__zz (set Int))
  (v_OBF__yyee (set (tuple2 Int Int))) (v_OBF__yydd Int) (v_OBF__yycc Int)
  (v_OBF__yybb (set Int)) (v_OBF__yy (set Int)) (v_OBF__xxee (set Int))
  (v_OBF__xxdd Int) (v_OBF__xxcc (set (tuple2 Int Int))) (v_OBF__xxbb Int)
  (v_OBF__xx Int) (v_OBF__wwee (set (tuple2 Int Int))) (v_OBF__wwdd Int)
  (v_OBF__wwcc (set Int)) (v_OBF__wwbb (set (tuple2 Int Int)))
  (v_OBF__ww (set Int)) (v_OBF__vvee (set (tuple2 Int Int)))
  (v_OBF__vvdd Bool) (v_OBF__vvcc (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__vvbb (set (tuple2 Int Int))) (v_OBF__vv Int)
  (v_OBF__uuee (set (tuple2 Int Int))) (v_OBF__uudd Int) (v_OBF__uucc Int)
  (v_OBF__uubb (set (tuple2 Int Int))) (v_OBF__uu (set Int))
  (v_OBF__ttee (set (tuple2 Int Int))) (v_OBF__ttdd Int) (v_OBF__ttcc Int)
  (v_OBF__ttbb (set Int)) (v_OBF__tt Int) (v_OBF__ssee (set (tuple2 Int
  Int))) (v_OBF__ssdd Int) (v_OBF__sscc Int) (v_OBF__ssbb (set Int))
  (v_OBF__rree (set (tuple2 Int Int))) (v_OBF__rrdd Int)
  (v_OBF__rrcc (set Int)) (v_OBF__rrbb Int) (v_OBF__qqee Int)
  (v_OBF__qqdd Int) (v_OBF__qqcc (set Int)) (v_OBF__qqbb (set Int))
  (v_OBF__ppee Int) (v_OBF__ppdd (set Int)) (v_OBF__ppcc (set (tuple2 Int
  Int))) (v_OBF__ppbb (set Int)) (v_OBF__ooee Int)
  (v_OBF__oodd (set (tuple2 Int Int))) (v_OBF__oocc Bool) (v_OBF__oobb Int)
  (v_OBF__nnff (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__nnee (set Int)) (v_OBF__nndd (set (tuple2 Int Int)))
  (v_OBF__nncc (set (tuple2 Int Int))) (v_OBF__nnbb Int)
  (v_OBF__mmff (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__mmee (set Int)) (v_OBF__mmdd Bool) (v_OBF__mmcc (set (tuple2 Int
  Int))) (v_OBF__mmbb Int) (v_OBF__llff (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (v_OBF__llee (set Int)) (v_OBF__lldd Int)
  (v_OBF__llcc (set (tuple2 Int Int))) (v_OBF__llbb (set enum_OBF__ii))
  (v_OBF__kkff (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__kkee (set Int)) (v_OBF__kkdd Int) (v_OBF__kkcc (set (tuple2 Int
  Int))) (v_OBF__kkbb (set Int)) (v_OBF__jjff (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (v_OBF__jjee (set Int)) (v_OBF__jjdd Int)
  (v_OBF__jjcc (set (tuple2 Int Int))) (v_OBF__jjbb Int)
  (v_OBF__iiff (set (tuple2 Int Int))) (v_OBF__iiee (set Int))
  (v_OBF__iidd (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb Int)
  (v_OBF__hhff (set (tuple2 Int Int))) (v_OBF__hhee (set (tuple2 Int Int)))
  (v_OBF__hhdd (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__hhcc (set (tuple2 Int Int))) (v_OBF__hhbb (set enum_OBF__ii))
  (v_OBF__ggff (set (tuple2 Int Int))) (v_OBF__ggee (set (tuple2 Int Int)))
  (v_OBF__ggdd enum_OBF__aa) (v_OBF__ggcc (set Int)) (v_OBF__ggbb (set Int))
  (v_OBF__ffff (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__ffee (set (tuple2 Int Int))) (v_OBF__ffdd Int)
  (v_OBF__ffcc (set Int)) (v_OBF__ffbb Int) (v_OBF__eeff (set (tuple2 Int
  Int))) (v_OBF__eeee (set (tuple2 Int Int))) (v_OBF__eedd (set (tuple2 Int
  Int))) (v_OBF__eecc (set Int)) (v_OBF__eebb Int) (v_OBF__ddff (set Int))
  (v_OBF__ddee (set Int)) (v_OBF__dddd Int) (v_OBF__ddcc (set Int))
  (v_OBF__ddbb Int) (v_OBF__ccff (set (tuple2 Int Int)))
  (v_OBF__ccee (set Int)) (v_OBF__ccdd (set (tuple2 Int Int)))
  (v_OBF__cccc (set (tuple2 Int Int))) (v_OBF__ccbb Int)
  (v_OBF__bbff (set (tuple2 Int Int))) (v_OBF__bbee Bool)
  (v_OBF__bbdd (set (tuple2 Int Int))) (v_OBF__bbcc (set Int))
  (v_OBF__bbbb (set Int)) (v_OBF__aaff (set (tuple2 Int Int)))
  (v_OBF__aaee (set (tuple2 Int Int))) (v_OBF__aadd (set (tuple2 Int Int)))
  (v_OBF__aacc (set Int)) (v_OBF__aabb Int))
  (= (f18 v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb v_OBF__zz
  v_OBF__yyee v_OBF__yydd v_OBF__yycc v_OBF__yybb v_OBF__yy v_OBF__xxee
  v_OBF__xxdd v_OBF__xxcc v_OBF__xxbb v_OBF__xx v_OBF__wwee v_OBF__wwdd
  v_OBF__wwcc v_OBF__wwbb v_OBF__ww v_OBF__vvee v_OBF__vvdd v_OBF__vvcc
  v_OBF__vvbb v_OBF__vv v_OBF__uuee v_OBF__uudd v_OBF__uucc v_OBF__uubb
  v_OBF__uu v_OBF__ttee v_OBF__ttdd v_OBF__ttcc v_OBF__ttbb v_OBF__tt
  v_OBF__ssee v_OBF__ssdd v_OBF__sscc v_OBF__ssbb v_OBF__rree v_OBF__rrdd
  v_OBF__rrcc v_OBF__rrbb v_OBF__qqee v_OBF__qqdd v_OBF__qqcc v_OBF__qqbb
  v_OBF__ppee v_OBF__ppdd v_OBF__ppcc v_OBF__ppbb v_OBF__ooee v_OBF__oodd
  v_OBF__oocc v_OBF__oobb v_OBF__nnff v_OBF__nnee v_OBF__nndd v_OBF__nncc
  v_OBF__nnbb v_OBF__mmff v_OBF__mmee v_OBF__mmdd v_OBF__mmcc v_OBF__mmbb
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkff
  v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjff v_OBF__jjee
  v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iiff v_OBF__iiee v_OBF__iidd
  v_OBF__iicc v_OBF__iibb v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc
  v_OBF__hhbb v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb
  v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb v_OBF__eeff
  v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb v_OBF__ddff v_OBF__ddee
  v_OBF__dddd v_OBF__ddcc v_OBF__ddbb v_OBF__ccff v_OBF__ccee v_OBF__ccdd
  v_OBF__cccc v_OBF__ccbb v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc
  v_OBF__bbbb v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (and
  (and
  (and
  (and
  (and (mem int (t2tb12 v_OBF__tt)
  (union int (add int (t2tb12 v_OBF__iibb) (t2tb1 empty1))
  (add int (t2tb12 v_OBF__jjbb) (t2tb1 empty1)))) (mem int (t2tb12 v_OBF__vv)
  (t2tb1 v_OBF__kkbb))) (mem (set1 enum_OBF__ii1) (t2tb5 v_OBF__hhbb)
  (power enum_OBF__ii1 (t2tb5 v_OBF__llbb)))) (= v_OBF__ddbb 2))
  (= v_OBF__eebb v_OBF__mmbb)) (= v_OBF__nnbb v_OBF__oobb)))))

(declare-fun f21 ((set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set Int)
  (set Int) (set (tuple2 Int Int)) Int Int (set Int) (set Int) (set Int) Int
  (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) Int (set Int)
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int)) Bool
  (set (tuple2 (tuple2 Int Int) Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) (set Int)
  (set (tuple2 Int Int)) Int Int (set Int) Int (set (tuple2 Int Int)) Int Int
  (set Int) (set (tuple2 Int Int)) Int (set Int) Int Int Int (set Int)
  (set Int) Int (set Int) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) Bool Int (set (tuple2 (tuple2 (tuple2 Int Int) Int)
  Int)) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Bool
  (set (tuple2 Int Int)) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set Int) Int (set (tuple2 Int Int)) (set enum_OBF__ii)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int (set (tuple2 Int
  Int)) (set Int) (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) (set (tuple2 Int Int)) (set enum_OBF__ii)
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) enum_OBF__aa (set Int)
  (set Int) (set (tuple2 (tuple2 Int Int) Int)) (set (tuple2 Int Int)) Int
  (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) Int (set Int) (set Int) Int (set Int) Int
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int
  Int)) Int (set (tuple2 Int Int)) Bool (set (tuple2 Int Int)) (set Int)
  (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int
  Int)) (set Int) Int) Bool)

;; f21_def
  (assert
  (forall ((v_OBF__zzee (set (tuple2 Int Int))) (v_OBF__zzdd (set (tuple2 Int
  Int))) (v_OBF__zzcc Int) (v_OBF__zzbb (set Int)) (v_OBF__zz (set Int))
  (v_OBF__yyee (set (tuple2 Int Int))) (v_OBF__yydd Int) (v_OBF__yycc Int)
  (v_OBF__yybb (set Int)) (v_OBF__yy (set Int)) (v_OBF__xxee (set Int))
  (v_OBF__xxdd Int) (v_OBF__xxcc (set (tuple2 Int Int))) (v_OBF__xxbb Int)
  (v_OBF__xx Int) (v_OBF__wwee (set (tuple2 Int Int))) (v_OBF__wwdd Int)
  (v_OBF__wwcc (set Int)) (v_OBF__wwbb (set (tuple2 Int Int)))
  (v_OBF__ww (set Int)) (v_OBF__vvee (set (tuple2 Int Int)))
  (v_OBF__vvdd Bool) (v_OBF__vvcc (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__vvbb (set (tuple2 Int Int))) (v_OBF__vv Int)
  (v_OBF__uuee (set (tuple2 Int Int))) (v_OBF__uudd Int) (v_OBF__uucc Int)
  (v_OBF__uubb (set (tuple2 Int Int))) (v_OBF__uu (set Int))
  (v_OBF__ttee (set (tuple2 Int Int))) (v_OBF__ttdd Int) (v_OBF__ttcc Int)
  (v_OBF__ttbb (set Int)) (v_OBF__tt Int) (v_OBF__ssee (set (tuple2 Int
  Int))) (v_OBF__ssdd Int) (v_OBF__sscc Int) (v_OBF__ssbb (set Int))
  (v_OBF__rree (set (tuple2 Int Int))) (v_OBF__rrdd Int)
  (v_OBF__rrcc (set Int)) (v_OBF__rrbb Int) (v_OBF__qqee Int)
  (v_OBF__qqdd Int) (v_OBF__qqcc (set Int)) (v_OBF__qqbb (set Int))
  (v_OBF__ppee Int) (v_OBF__ppdd (set Int)) (v_OBF__ppcc (set (tuple2 Int
  Int))) (v_OBF__ppbb (set Int)) (v_OBF__ooee Int)
  (v_OBF__oodd (set (tuple2 Int Int))) (v_OBF__oocc Bool) (v_OBF__oobb Int)
  (v_OBF__nnff (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__nnee (set Int)) (v_OBF__nndd (set (tuple2 Int Int)))
  (v_OBF__nncc (set (tuple2 Int Int))) (v_OBF__nnbb Int)
  (v_OBF__mmff (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__mmee (set Int)) (v_OBF__mmdd Bool) (v_OBF__mmcc (set (tuple2 Int
  Int))) (v_OBF__mmbb Int) (v_OBF__llff (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (v_OBF__llee (set Int)) (v_OBF__lldd Int)
  (v_OBF__llcc (set (tuple2 Int Int))) (v_OBF__llbb (set enum_OBF__ii))
  (v_OBF__kkff (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__kkee (set Int)) (v_OBF__kkdd Int) (v_OBF__kkcc (set (tuple2 Int
  Int))) (v_OBF__kkbb (set Int)) (v_OBF__jjff (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (v_OBF__jjee (set Int)) (v_OBF__jjdd Int)
  (v_OBF__jjcc (set (tuple2 Int Int))) (v_OBF__jjbb Int)
  (v_OBF__iiff (set (tuple2 Int Int))) (v_OBF__iiee (set Int))
  (v_OBF__iidd (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb Int)
  (v_OBF__hhff (set (tuple2 Int Int))) (v_OBF__hhee (set (tuple2 Int Int)))
  (v_OBF__hhdd (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__hhcc (set (tuple2 Int Int))) (v_OBF__hhbb (set enum_OBF__ii))
  (v_OBF__ggff (set (tuple2 Int Int))) (v_OBF__ggee (set (tuple2 Int Int)))
  (v_OBF__ggdd enum_OBF__aa) (v_OBF__ggcc (set Int)) (v_OBF__ggbb (set Int))
  (v_OBF__ffff (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__ffee (set (tuple2 Int Int))) (v_OBF__ffdd Int)
  (v_OBF__ffcc (set Int)) (v_OBF__ffbb Int) (v_OBF__eeff (set (tuple2 Int
  Int))) (v_OBF__eeee (set (tuple2 Int Int))) (v_OBF__eedd (set (tuple2 Int
  Int))) (v_OBF__eecc (set Int)) (v_OBF__eebb Int) (v_OBF__ddff (set Int))
  (v_OBF__ddee (set Int)) (v_OBF__dddd Int) (v_OBF__ddcc (set Int))
  (v_OBF__ddbb Int) (v_OBF__ccff (set (tuple2 Int Int)))
  (v_OBF__ccee (set Int)) (v_OBF__ccdd (set (tuple2 Int Int)))
  (v_OBF__cccc (set (tuple2 Int Int))) (v_OBF__ccbb Int)
  (v_OBF__bbff (set (tuple2 Int Int))) (v_OBF__bbee Bool)
  (v_OBF__bbdd (set (tuple2 Int Int))) (v_OBF__bbcc (set Int))
  (v_OBF__bbbb (set Int)) (v_OBF__aaff (set (tuple2 Int Int)))
  (v_OBF__aaee (set (tuple2 Int Int))) (v_OBF__aadd (set (tuple2 Int Int)))
  (v_OBF__aacc (set Int)) (v_OBF__aabb Int))
  (= (f21 v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb v_OBF__zz
  v_OBF__yyee v_OBF__yydd v_OBF__yycc v_OBF__yybb v_OBF__yy v_OBF__xxee
  v_OBF__xxdd v_OBF__xxcc v_OBF__xxbb v_OBF__xx v_OBF__wwee v_OBF__wwdd
  v_OBF__wwcc v_OBF__wwbb v_OBF__ww v_OBF__vvee v_OBF__vvdd v_OBF__vvcc
  v_OBF__vvbb v_OBF__vv v_OBF__uuee v_OBF__uudd v_OBF__uucc v_OBF__uubb
  v_OBF__uu v_OBF__ttee v_OBF__ttdd v_OBF__ttcc v_OBF__ttbb v_OBF__tt
  v_OBF__ssee v_OBF__ssdd v_OBF__sscc v_OBF__ssbb v_OBF__rree v_OBF__rrdd
  v_OBF__rrcc v_OBF__rrbb v_OBF__qqee v_OBF__qqdd v_OBF__qqcc v_OBF__qqbb
  v_OBF__ppee v_OBF__ppdd v_OBF__ppcc v_OBF__ppbb v_OBF__ooee v_OBF__oodd
  v_OBF__oocc v_OBF__oobb v_OBF__nnff v_OBF__nnee v_OBF__nndd v_OBF__nncc
  v_OBF__nnbb v_OBF__mmff v_OBF__mmee v_OBF__mmdd v_OBF__mmcc v_OBF__mmbb
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkff
  v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjff v_OBF__jjee
  v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iiff v_OBF__iiee v_OBF__iidd
  v_OBF__iicc v_OBF__iibb v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc
  v_OBF__hhbb v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb
  v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb v_OBF__eeff
  v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb v_OBF__ddff v_OBF__ddee
  v_OBF__dddd v_OBF__ddcc v_OBF__ddbb v_OBF__ccff v_OBF__ccee v_OBF__ccdd
  v_OBF__cccc v_OBF__ccbb v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc
  v_OBF__bbbb v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (not (mem int (t2tb12 v_OBF__vv) (t2tb1 v_OBF__ww))))))

(declare-fun f23 ((set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set Int)
  (set Int) (set (tuple2 Int Int)) Int Int (set Int) (set Int) (set Int) Int
  (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) Int (set Int)
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int)) Bool
  (set (tuple2 (tuple2 Int Int) Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) (set Int)
  (set (tuple2 Int Int)) Int Int (set Int) Int (set (tuple2 Int Int)) Int Int
  (set Int) (set (tuple2 Int Int)) Int (set Int) Int Int Int (set Int)
  (set Int) Int (set Int) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) Bool Int (set (tuple2 (tuple2 (tuple2 Int Int) Int)
  Int)) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Bool
  (set (tuple2 Int Int)) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set Int) Int (set (tuple2 Int Int)) (set enum_OBF__ii)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int (set (tuple2 Int
  Int)) (set Int) (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) (set (tuple2 Int Int)) (set enum_OBF__ii)
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) enum_OBF__aa (set Int)
  (set Int) (set (tuple2 (tuple2 Int Int) Int)) (set (tuple2 Int Int)) Int
  (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) Int (set Int) (set Int) Int (set Int) Int
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int
  Int)) Int (set (tuple2 Int Int)) Bool (set (tuple2 Int Int)) (set Int)
  (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int
  Int)) (set Int) Int) Bool)

;; f23_def
  (assert
  (forall ((v_OBF__zzee (set (tuple2 Int Int))) (v_OBF__zzdd (set (tuple2 Int
  Int))) (v_OBF__zzcc Int) (v_OBF__zzbb (set Int)) (v_OBF__zz (set Int))
  (v_OBF__yyee (set (tuple2 Int Int))) (v_OBF__yydd Int) (v_OBF__yycc Int)
  (v_OBF__yybb (set Int)) (v_OBF__yy (set Int)) (v_OBF__xxee (set Int))
  (v_OBF__xxdd Int) (v_OBF__xxcc (set (tuple2 Int Int))) (v_OBF__xxbb Int)
  (v_OBF__xx Int) (v_OBF__wwee (set (tuple2 Int Int))) (v_OBF__wwdd Int)
  (v_OBF__wwcc (set Int)) (v_OBF__wwbb (set (tuple2 Int Int)))
  (v_OBF__ww (set Int)) (v_OBF__vvee (set (tuple2 Int Int)))
  (v_OBF__vvdd Bool) (v_OBF__vvcc (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__vvbb (set (tuple2 Int Int))) (v_OBF__vv Int)
  (v_OBF__uuee (set (tuple2 Int Int))) (v_OBF__uudd Int) (v_OBF__uucc Int)
  (v_OBF__uubb (set (tuple2 Int Int))) (v_OBF__uu (set Int))
  (v_OBF__ttee (set (tuple2 Int Int))) (v_OBF__ttdd Int) (v_OBF__ttcc Int)
  (v_OBF__ttbb (set Int)) (v_OBF__tt Int) (v_OBF__ssee (set (tuple2 Int
  Int))) (v_OBF__ssdd Int) (v_OBF__sscc Int) (v_OBF__ssbb (set Int))
  (v_OBF__rree (set (tuple2 Int Int))) (v_OBF__rrdd Int)
  (v_OBF__rrcc (set Int)) (v_OBF__rrbb Int) (v_OBF__qqee Int)
  (v_OBF__qqdd Int) (v_OBF__qqcc (set Int)) (v_OBF__qqbb (set Int))
  (v_OBF__ppee Int) (v_OBF__ppdd (set Int)) (v_OBF__ppcc (set (tuple2 Int
  Int))) (v_OBF__ppbb (set Int)) (v_OBF__ooee Int)
  (v_OBF__oodd (set (tuple2 Int Int))) (v_OBF__oocc Bool) (v_OBF__oobb Int)
  (v_OBF__nnff (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__nnee (set Int)) (v_OBF__nndd (set (tuple2 Int Int)))
  (v_OBF__nncc (set (tuple2 Int Int))) (v_OBF__nnbb Int)
  (v_OBF__mmff (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__mmee (set Int)) (v_OBF__mmdd Bool) (v_OBF__mmcc (set (tuple2 Int
  Int))) (v_OBF__mmbb Int) (v_OBF__llff (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (v_OBF__llee (set Int)) (v_OBF__lldd Int)
  (v_OBF__llcc (set (tuple2 Int Int))) (v_OBF__llbb (set enum_OBF__ii))
  (v_OBF__kkff (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__kkee (set Int)) (v_OBF__kkdd Int) (v_OBF__kkcc (set (tuple2 Int
  Int))) (v_OBF__kkbb (set Int)) (v_OBF__jjff (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (v_OBF__jjee (set Int)) (v_OBF__jjdd Int)
  (v_OBF__jjcc (set (tuple2 Int Int))) (v_OBF__jjbb Int)
  (v_OBF__iiff (set (tuple2 Int Int))) (v_OBF__iiee (set Int))
  (v_OBF__iidd (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb Int)
  (v_OBF__hhff (set (tuple2 Int Int))) (v_OBF__hhee (set (tuple2 Int Int)))
  (v_OBF__hhdd (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__hhcc (set (tuple2 Int Int))) (v_OBF__hhbb (set enum_OBF__ii))
  (v_OBF__ggff (set (tuple2 Int Int))) (v_OBF__ggee (set (tuple2 Int Int)))
  (v_OBF__ggdd enum_OBF__aa) (v_OBF__ggcc (set Int)) (v_OBF__ggbb (set Int))
  (v_OBF__ffff (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__ffee (set (tuple2 Int Int))) (v_OBF__ffdd Int)
  (v_OBF__ffcc (set Int)) (v_OBF__ffbb Int) (v_OBF__eeff (set (tuple2 Int
  Int))) (v_OBF__eeee (set (tuple2 Int Int))) (v_OBF__eedd (set (tuple2 Int
  Int))) (v_OBF__eecc (set Int)) (v_OBF__eebb Int) (v_OBF__ddff (set Int))
  (v_OBF__ddee (set Int)) (v_OBF__dddd Int) (v_OBF__ddcc (set Int))
  (v_OBF__ddbb Int) (v_OBF__ccff (set (tuple2 Int Int)))
  (v_OBF__ccee (set Int)) (v_OBF__ccdd (set (tuple2 Int Int)))
  (v_OBF__cccc (set (tuple2 Int Int))) (v_OBF__ccbb Int)
  (v_OBF__bbff (set (tuple2 Int Int))) (v_OBF__bbee Bool)
  (v_OBF__bbdd (set (tuple2 Int Int))) (v_OBF__bbcc (set Int))
  (v_OBF__bbbb (set Int)) (v_OBF__aaff (set (tuple2 Int Int)))
  (v_OBF__aaee (set (tuple2 Int Int))) (v_OBF__aadd (set (tuple2 Int Int)))
  (v_OBF__aacc (set Int)) (v_OBF__aabb Int))
  (= (f23 v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb v_OBF__zz
  v_OBF__yyee v_OBF__yydd v_OBF__yycc v_OBF__yybb v_OBF__yy v_OBF__xxee
  v_OBF__xxdd v_OBF__xxcc v_OBF__xxbb v_OBF__xx v_OBF__wwee v_OBF__wwdd
  v_OBF__wwcc v_OBF__wwbb v_OBF__ww v_OBF__vvee v_OBF__vvdd v_OBF__vvcc
  v_OBF__vvbb v_OBF__vv v_OBF__uuee v_OBF__uudd v_OBF__uucc v_OBF__uubb
  v_OBF__uu v_OBF__ttee v_OBF__ttdd v_OBF__ttcc v_OBF__ttbb v_OBF__tt
  v_OBF__ssee v_OBF__ssdd v_OBF__sscc v_OBF__ssbb v_OBF__rree v_OBF__rrdd
  v_OBF__rrcc v_OBF__rrbb v_OBF__qqee v_OBF__qqdd v_OBF__qqcc v_OBF__qqbb
  v_OBF__ppee v_OBF__ppdd v_OBF__ppcc v_OBF__ppbb v_OBF__ooee v_OBF__oodd
  v_OBF__oocc v_OBF__oobb v_OBF__nnff v_OBF__nnee v_OBF__nndd v_OBF__nncc
  v_OBF__nnbb v_OBF__mmff v_OBF__mmee v_OBF__mmdd v_OBF__mmcc v_OBF__mmbb
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkff
  v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjff v_OBF__jjee
  v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iiff v_OBF__iiee v_OBF__iidd
  v_OBF__iicc v_OBF__iibb v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc
  v_OBF__hhbb v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb
  v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb v_OBF__eeff
  v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb v_OBF__ddff v_OBF__ddee
  v_OBF__dddd v_OBF__ddcc v_OBF__ddbb v_OBF__ccff v_OBF__ccee v_OBF__ccdd
  v_OBF__cccc v_OBF__ccbb v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc
  v_OBF__bbbb v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (mem (set1 int) (t2tb1 v_OBF__ww) (power int (t2tb1 v_OBF__yy))))))

(declare-fun f25 ((set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set Int)
  (set Int) (set (tuple2 Int Int)) Int Int (set Int) (set Int) (set Int) Int
  (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) Int (set Int)
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int)) Bool
  (set (tuple2 (tuple2 Int Int) Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) (set Int)
  (set (tuple2 Int Int)) Int Int (set Int) Int (set (tuple2 Int Int)) Int Int
  (set Int) (set (tuple2 Int Int)) Int (set Int) Int Int Int (set Int)
  (set Int) Int (set Int) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) Bool Int (set (tuple2 (tuple2 (tuple2 Int Int) Int)
  Int)) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Bool
  (set (tuple2 Int Int)) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set Int) Int (set (tuple2 Int Int)) (set enum_OBF__ii)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int (set (tuple2 Int
  Int)) (set Int) (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) (set (tuple2 Int Int)) (set enum_OBF__ii)
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) enum_OBF__aa (set Int)
  (set Int) (set (tuple2 (tuple2 Int Int) Int)) (set (tuple2 Int Int)) Int
  (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) Int (set Int) (set Int) Int (set Int) Int
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int
  Int)) Int (set (tuple2 Int Int)) Bool (set (tuple2 Int Int)) (set Int)
  (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int
  Int)) (set Int) Int) Bool)

;; f25_def
  (assert
  (forall ((v_OBF__zzee (set (tuple2 Int Int))) (v_OBF__zzdd (set (tuple2 Int
  Int))) (v_OBF__zzcc Int) (v_OBF__zzbb (set Int)) (v_OBF__zz (set Int))
  (v_OBF__yyee (set (tuple2 Int Int))) (v_OBF__yydd Int) (v_OBF__yycc Int)
  (v_OBF__yybb (set Int)) (v_OBF__yy (set Int)) (v_OBF__xxee (set Int))
  (v_OBF__xxdd Int) (v_OBF__xxcc (set (tuple2 Int Int))) (v_OBF__xxbb Int)
  (v_OBF__xx Int) (v_OBF__wwee (set (tuple2 Int Int))) (v_OBF__wwdd Int)
  (v_OBF__wwcc (set Int)) (v_OBF__wwbb (set (tuple2 Int Int)))
  (v_OBF__ww (set Int)) (v_OBF__vvee (set (tuple2 Int Int)))
  (v_OBF__vvdd Bool) (v_OBF__vvcc (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__vvbb (set (tuple2 Int Int))) (v_OBF__vv Int)
  (v_OBF__uuee (set (tuple2 Int Int))) (v_OBF__uudd Int) (v_OBF__uucc Int)
  (v_OBF__uubb (set (tuple2 Int Int))) (v_OBF__uu (set Int))
  (v_OBF__ttee (set (tuple2 Int Int))) (v_OBF__ttdd Int) (v_OBF__ttcc Int)
  (v_OBF__ttbb (set Int)) (v_OBF__tt Int) (v_OBF__ssee (set (tuple2 Int
  Int))) (v_OBF__ssdd Int) (v_OBF__sscc Int) (v_OBF__ssbb (set Int))
  (v_OBF__rree (set (tuple2 Int Int))) (v_OBF__rrdd Int)
  (v_OBF__rrcc (set Int)) (v_OBF__rrbb Int) (v_OBF__qqee Int)
  (v_OBF__qqdd Int) (v_OBF__qqcc (set Int)) (v_OBF__qqbb (set Int))
  (v_OBF__ppee Int) (v_OBF__ppdd (set Int)) (v_OBF__ppcc (set (tuple2 Int
  Int))) (v_OBF__ppbb (set Int)) (v_OBF__ooee Int)
  (v_OBF__oodd (set (tuple2 Int Int))) (v_OBF__oocc Bool) (v_OBF__oobb Int)
  (v_OBF__nnff (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__nnee (set Int)) (v_OBF__nndd (set (tuple2 Int Int)))
  (v_OBF__nncc (set (tuple2 Int Int))) (v_OBF__nnbb Int)
  (v_OBF__mmff (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__mmee (set Int)) (v_OBF__mmdd Bool) (v_OBF__mmcc (set (tuple2 Int
  Int))) (v_OBF__mmbb Int) (v_OBF__llff (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (v_OBF__llee (set Int)) (v_OBF__lldd Int)
  (v_OBF__llcc (set (tuple2 Int Int))) (v_OBF__llbb (set enum_OBF__ii))
  (v_OBF__kkff (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__kkee (set Int)) (v_OBF__kkdd Int) (v_OBF__kkcc (set (tuple2 Int
  Int))) (v_OBF__kkbb (set Int)) (v_OBF__jjff (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (v_OBF__jjee (set Int)) (v_OBF__jjdd Int)
  (v_OBF__jjcc (set (tuple2 Int Int))) (v_OBF__jjbb Int)
  (v_OBF__iiff (set (tuple2 Int Int))) (v_OBF__iiee (set Int))
  (v_OBF__iidd (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb Int)
  (v_OBF__hhff (set (tuple2 Int Int))) (v_OBF__hhee (set (tuple2 Int Int)))
  (v_OBF__hhdd (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__hhcc (set (tuple2 Int Int))) (v_OBF__hhbb (set enum_OBF__ii))
  (v_OBF__ggff (set (tuple2 Int Int))) (v_OBF__ggee (set (tuple2 Int Int)))
  (v_OBF__ggdd enum_OBF__aa) (v_OBF__ggcc (set Int)) (v_OBF__ggbb (set Int))
  (v_OBF__ffff (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__ffee (set (tuple2 Int Int))) (v_OBF__ffdd Int)
  (v_OBF__ffcc (set Int)) (v_OBF__ffbb Int) (v_OBF__eeff (set (tuple2 Int
  Int))) (v_OBF__eeee (set (tuple2 Int Int))) (v_OBF__eedd (set (tuple2 Int
  Int))) (v_OBF__eecc (set Int)) (v_OBF__eebb Int) (v_OBF__ddff (set Int))
  (v_OBF__ddee (set Int)) (v_OBF__dddd Int) (v_OBF__ddcc (set Int))
  (v_OBF__ddbb Int) (v_OBF__ccff (set (tuple2 Int Int)))
  (v_OBF__ccee (set Int)) (v_OBF__ccdd (set (tuple2 Int Int)))
  (v_OBF__cccc (set (tuple2 Int Int))) (v_OBF__ccbb Int)
  (v_OBF__bbff (set (tuple2 Int Int))) (v_OBF__bbee Bool)
  (v_OBF__bbdd (set (tuple2 Int Int))) (v_OBF__bbcc (set Int))
  (v_OBF__bbbb (set Int)) (v_OBF__aaff (set (tuple2 Int Int)))
  (v_OBF__aaee (set (tuple2 Int Int))) (v_OBF__aadd (set (tuple2 Int Int)))
  (v_OBF__aacc (set Int)) (v_OBF__aabb Int))
  (= (f25 v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb v_OBF__zz
  v_OBF__yyee v_OBF__yydd v_OBF__yycc v_OBF__yybb v_OBF__yy v_OBF__xxee
  v_OBF__xxdd v_OBF__xxcc v_OBF__xxbb v_OBF__xx v_OBF__wwee v_OBF__wwdd
  v_OBF__wwcc v_OBF__wwbb v_OBF__ww v_OBF__vvee v_OBF__vvdd v_OBF__vvcc
  v_OBF__vvbb v_OBF__vv v_OBF__uuee v_OBF__uudd v_OBF__uucc v_OBF__uubb
  v_OBF__uu v_OBF__ttee v_OBF__ttdd v_OBF__ttcc v_OBF__ttbb v_OBF__tt
  v_OBF__ssee v_OBF__ssdd v_OBF__sscc v_OBF__ssbb v_OBF__rree v_OBF__rrdd
  v_OBF__rrcc v_OBF__rrbb v_OBF__qqee v_OBF__qqdd v_OBF__qqcc v_OBF__qqbb
  v_OBF__ppee v_OBF__ppdd v_OBF__ppcc v_OBF__ppbb v_OBF__ooee v_OBF__oodd
  v_OBF__oocc v_OBF__oobb v_OBF__nnff v_OBF__nnee v_OBF__nndd v_OBF__nncc
  v_OBF__nnbb v_OBF__mmff v_OBF__mmee v_OBF__mmdd v_OBF__mmcc v_OBF__mmbb
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkff
  v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjff v_OBF__jjee
  v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iiff v_OBF__iiee v_OBF__iidd
  v_OBF__iicc v_OBF__iibb v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc
  v_OBF__hhbb v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb
  v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb v_OBF__eeff
  v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb v_OBF__ddff v_OBF__ddee
  v_OBF__dddd v_OBF__ddcc v_OBF__ddbb v_OBF__ccff v_OBF__ccee v_OBF__ccdd
  v_OBF__cccc v_OBF__ccbb v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc
  v_OBF__bbbb v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (and
  (and
  (and
  (and
  (and
  (=> (mem int (t2tb12 v_OBF__tt) (t2tb1 v_OBF__uu))
  (and (not (infix_eqeq1 v_OBF__ggbb empty1)) (infix_eqeq1 v_OBF__ww empty1)))
  (= v_OBF__ddbb 2)) (= v_OBF__eebb v_OBF__ffbb)) (mem int (t2tb12 v_OBF__tt)
  (t2tb1 v_OBF__uu))) (mem int (t2tb12 v_OBF__aabb) (t2tb1 v_OBF__bbbb)))
  (infix_eqeq1 v_OBF__ww
  (tb2t1 (add int (t2tb12 v_OBF__aabb) (t2tb1 empty1))))))))

(declare-fun f26 ((set (tuple2 Int Int)) (set (tuple2 Int Int)) Int (set Int)
  (set Int) (set (tuple2 Int Int)) Int Int (set Int) (set Int) (set Int) Int
  (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) Int (set Int)
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int)) Bool
  (set (tuple2 (tuple2 Int Int) Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) Int Int (set (tuple2 Int Int)) (set Int)
  (set (tuple2 Int Int)) Int Int (set Int) Int (set (tuple2 Int Int)) Int Int
  (set Int) (set (tuple2 Int Int)) Int (set Int) Int Int Int (set Int)
  (set Int) Int (set Int) (set (tuple2 Int Int)) (set Int) Int
  (set (tuple2 Int Int)) Bool Int (set (tuple2 (tuple2 (tuple2 Int Int) Int)
  Int)) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Bool
  (set (tuple2 Int Int)) Int (set (tuple2 (tuple2 Int enum_OBF__aa) Int))
  (set Int) Int (set (tuple2 Int Int)) (set enum_OBF__ii)
  (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int (set (tuple2 Int
  Int)) (set Int) (set (tuple2 (tuple2 Int enum_OBF__aa) Int)) (set Int) Int
  (set (tuple2 Int Int)) Int (set (tuple2 Int Int)) (set Int)
  (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)) (set (tuple2 Int Int)) Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int)) (set (tuple2 Int Int)) (set enum_OBF__ii)
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) enum_OBF__aa (set Int)
  (set Int) (set (tuple2 (tuple2 Int Int) Int)) (set (tuple2 Int Int)) Int
  (set Int) Int (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) Int (set Int) (set Int) Int (set Int) Int
  (set (tuple2 Int Int)) (set Int) (set (tuple2 Int Int)) (set (tuple2 Int
  Int)) Int (set (tuple2 Int Int)) Bool (set (tuple2 Int Int)) (set Int)
  (set Int) (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int
  Int)) (set Int) Int) Bool)

;; f26_def
  (assert
  (forall ((v_OBF__zzee (set (tuple2 Int Int))) (v_OBF__zzdd (set (tuple2 Int
  Int))) (v_OBF__zzcc Int) (v_OBF__zzbb (set Int)) (v_OBF__zz (set Int))
  (v_OBF__yyee (set (tuple2 Int Int))) (v_OBF__yydd Int) (v_OBF__yycc Int)
  (v_OBF__yybb (set Int)) (v_OBF__yy (set Int)) (v_OBF__xxee (set Int))
  (v_OBF__xxdd Int) (v_OBF__xxcc (set (tuple2 Int Int))) (v_OBF__xxbb Int)
  (v_OBF__xx Int) (v_OBF__wwee (set (tuple2 Int Int))) (v_OBF__wwdd Int)
  (v_OBF__wwcc (set Int)) (v_OBF__wwbb (set (tuple2 Int Int)))
  (v_OBF__ww (set Int)) (v_OBF__vvee (set (tuple2 Int Int)))
  (v_OBF__vvdd Bool) (v_OBF__vvcc (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__vvbb (set (tuple2 Int Int))) (v_OBF__vv Int)
  (v_OBF__uuee (set (tuple2 Int Int))) (v_OBF__uudd Int) (v_OBF__uucc Int)
  (v_OBF__uubb (set (tuple2 Int Int))) (v_OBF__uu (set Int))
  (v_OBF__ttee (set (tuple2 Int Int))) (v_OBF__ttdd Int) (v_OBF__ttcc Int)
  (v_OBF__ttbb (set Int)) (v_OBF__tt Int) (v_OBF__ssee (set (tuple2 Int
  Int))) (v_OBF__ssdd Int) (v_OBF__sscc Int) (v_OBF__ssbb (set Int))
  (v_OBF__rree (set (tuple2 Int Int))) (v_OBF__rrdd Int)
  (v_OBF__rrcc (set Int)) (v_OBF__rrbb Int) (v_OBF__qqee Int)
  (v_OBF__qqdd Int) (v_OBF__qqcc (set Int)) (v_OBF__qqbb (set Int))
  (v_OBF__ppee Int) (v_OBF__ppdd (set Int)) (v_OBF__ppcc (set (tuple2 Int
  Int))) (v_OBF__ppbb (set Int)) (v_OBF__ooee Int)
  (v_OBF__oodd (set (tuple2 Int Int))) (v_OBF__oocc Bool) (v_OBF__oobb Int)
  (v_OBF__nnff (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__nnee (set Int)) (v_OBF__nndd (set (tuple2 Int Int)))
  (v_OBF__nncc (set (tuple2 Int Int))) (v_OBF__nnbb Int)
  (v_OBF__mmff (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__mmee (set Int)) (v_OBF__mmdd Bool) (v_OBF__mmcc (set (tuple2 Int
  Int))) (v_OBF__mmbb Int) (v_OBF__llff (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (v_OBF__llee (set Int)) (v_OBF__lldd Int)
  (v_OBF__llcc (set (tuple2 Int Int))) (v_OBF__llbb (set enum_OBF__ii))
  (v_OBF__kkff (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__kkee (set Int)) (v_OBF__kkdd Int) (v_OBF__kkcc (set (tuple2 Int
  Int))) (v_OBF__kkbb (set Int)) (v_OBF__jjff (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (v_OBF__jjee (set Int)) (v_OBF__jjdd Int)
  (v_OBF__jjcc (set (tuple2 Int Int))) (v_OBF__jjbb Int)
  (v_OBF__iiff (set (tuple2 Int Int))) (v_OBF__iiee (set Int))
  (v_OBF__iidd (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb Int)
  (v_OBF__hhff (set (tuple2 Int Int))) (v_OBF__hhee (set (tuple2 Int Int)))
  (v_OBF__hhdd (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__hhcc (set (tuple2 Int Int))) (v_OBF__hhbb (set enum_OBF__ii))
  (v_OBF__ggff (set (tuple2 Int Int))) (v_OBF__ggee (set (tuple2 Int Int)))
  (v_OBF__ggdd enum_OBF__aa) (v_OBF__ggcc (set Int)) (v_OBF__ggbb (set Int))
  (v_OBF__ffff (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__ffee (set (tuple2 Int Int))) (v_OBF__ffdd Int)
  (v_OBF__ffcc (set Int)) (v_OBF__ffbb Int) (v_OBF__eeff (set (tuple2 Int
  Int))) (v_OBF__eeee (set (tuple2 Int Int))) (v_OBF__eedd (set (tuple2 Int
  Int))) (v_OBF__eecc (set Int)) (v_OBF__eebb Int) (v_OBF__ddff (set Int))
  (v_OBF__ddee (set Int)) (v_OBF__dddd Int) (v_OBF__ddcc (set Int))
  (v_OBF__ddbb Int) (v_OBF__ccff (set (tuple2 Int Int)))
  (v_OBF__ccee (set Int)) (v_OBF__ccdd (set (tuple2 Int Int)))
  (v_OBF__cccc (set (tuple2 Int Int))) (v_OBF__ccbb Int)
  (v_OBF__bbff (set (tuple2 Int Int))) (v_OBF__bbee Bool)
  (v_OBF__bbdd (set (tuple2 Int Int))) (v_OBF__bbcc (set Int))
  (v_OBF__bbbb (set Int)) (v_OBF__aaff (set (tuple2 Int Int)))
  (v_OBF__aaee (set (tuple2 Int Int))) (v_OBF__aadd (set (tuple2 Int Int)))
  (v_OBF__aacc (set Int)) (v_OBF__aabb Int))
  (= (f26 v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb v_OBF__zz
  v_OBF__yyee v_OBF__yydd v_OBF__yycc v_OBF__yybb v_OBF__yy v_OBF__xxee
  v_OBF__xxdd v_OBF__xxcc v_OBF__xxbb v_OBF__xx v_OBF__wwee v_OBF__wwdd
  v_OBF__wwcc v_OBF__wwbb v_OBF__ww v_OBF__vvee v_OBF__vvdd v_OBF__vvcc
  v_OBF__vvbb v_OBF__vv v_OBF__uuee v_OBF__uudd v_OBF__uucc v_OBF__uubb
  v_OBF__uu v_OBF__ttee v_OBF__ttdd v_OBF__ttcc v_OBF__ttbb v_OBF__tt
  v_OBF__ssee v_OBF__ssdd v_OBF__sscc v_OBF__ssbb v_OBF__rree v_OBF__rrdd
  v_OBF__rrcc v_OBF__rrbb v_OBF__qqee v_OBF__qqdd v_OBF__qqcc v_OBF__qqbb
  v_OBF__ppee v_OBF__ppdd v_OBF__ppcc v_OBF__ppbb v_OBF__ooee v_OBF__oodd
  v_OBF__oocc v_OBF__oobb v_OBF__nnff v_OBF__nnee v_OBF__nndd v_OBF__nncc
  v_OBF__nnbb v_OBF__mmff v_OBF__mmee v_OBF__mmdd v_OBF__mmcc v_OBF__mmbb
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkff
  v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjff v_OBF__jjee
  v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iiff v_OBF__iiee v_OBF__iidd
  v_OBF__iicc v_OBF__iibb v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc
  v_OBF__hhbb v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb
  v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb v_OBF__eeff
  v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb v_OBF__ddff v_OBF__ddee
  v_OBF__dddd v_OBF__ddcc v_OBF__ddbb v_OBF__ccff v_OBF__ccee v_OBF__ccdd
  v_OBF__cccc v_OBF__ccbb v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc
  v_OBF__bbbb v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (and
  (and
  (and
  (and
  (and
  (and (mem int (t2tb12 v_OBF__tt) (t2tb1 v_OBF__uu))
  (not (infix_eqeq1 v_OBF__ww empty1)))
  (forall ((v_OBF__aabb1 Int))
  (=> (mem int (t2tb12 v_OBF__aabb1) (t2tb1 v_OBF__bbbb))
  (not (infix_eqeq1 v_OBF__ww
  (tb2t1 (add int (t2tb12 v_OBF__aabb1) (t2tb1 empty1))))))))
  (= v_OBF__ddbb 2)) (= v_OBF__eebb v_OBF__ffbb)) (mem int
  (t2tb12 v_OBF__aabb) (t2tb1 v_OBF__bbbb))) (infix_eqeq1 v_OBF__ww
  (tb2t1 (add int (t2tb12 v_OBF__aabb) (t2tb1 empty1))))))))

(assert
;; OBF__vvff_4
 ;; File "POwhy_bpo2why/p9/p9_8.why", line 3114, characters 7-18
  (not
  (forall ((v_OBF__zzee (set (tuple2 Int Int))) (v_OBF__zzdd (set (tuple2 Int
  Int))) (v_OBF__zzcc Int) (v_OBF__zzbb (set Int)) (v_OBF__zz (set Int))
  (v_OBF__yyee (set (tuple2 Int Int))) (v_OBF__yydd Int) (v_OBF__yycc Int)
  (v_OBF__yybb (set Int)) (v_OBF__yy (set Int)) (v_OBF__xxee (set Int))
  (v_OBF__xxdd Int) (v_OBF__xxcc (set (tuple2 Int Int))) (v_OBF__xxbb Int)
  (v_OBF__xx Int) (v_OBF__wwee (set (tuple2 Int Int))) (v_OBF__wwdd Int)
  (v_OBF__wwcc (set Int)) (v_OBF__wwbb (set (tuple2 Int Int)))
  (v_OBF__ww (set Int)) (v_OBF__vvee (set (tuple2 Int Int)))
  (v_OBF__vvdd Bool) (v_OBF__vvcc (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__vvbb (set (tuple2 Int Int))) (v_OBF__vv Int)
  (v_OBF__uuee (set (tuple2 Int Int))) (v_OBF__uudd Int) (v_OBF__uucc Int)
  (v_OBF__uubb (set (tuple2 Int Int))) (v_OBF__uu (set Int))
  (v_OBF__ttee (set (tuple2 Int Int))) (v_OBF__ttdd Int) (v_OBF__ttcc Int)
  (v_OBF__ttbb (set Int)) (v_OBF__tt Int) (v_OBF__ssee (set (tuple2 Int
  Int))) (v_OBF__ssdd Int) (v_OBF__sscc Int) (v_OBF__ssbb (set Int))
  (v_OBF__rree (set (tuple2 Int Int))) (v_OBF__rrdd Int)
  (v_OBF__rrcc (set Int)) (v_OBF__rrbb Int) (v_OBF__qqee Int)
  (v_OBF__qqdd Int) (v_OBF__qqcc (set Int)) (v_OBF__qqbb (set Int))
  (v_OBF__ppee Int) (v_OBF__ppdd (set Int)) (v_OBF__ppcc (set (tuple2 Int
  Int))) (v_OBF__ppbb (set Int)) (v_OBF__ooee Int)
  (v_OBF__oodd (set (tuple2 Int Int))) (v_OBF__oocc Bool) (v_OBF__oobb Int)
  (v_OBF__nnff (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__nnee (set Int)) (v_OBF__nndd (set (tuple2 Int Int)))
  (v_OBF__nncc (set (tuple2 Int Int))) (v_OBF__nnbb Int)
  (v_OBF__mmff (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__mmee (set Int)) (v_OBF__mmdd Bool) (v_OBF__mmcc (set (tuple2 Int
  Int))) (v_OBF__mmbb Int) (v_OBF__llff (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (v_OBF__llee (set Int)) (v_OBF__lldd Int)
  (v_OBF__llcc (set (tuple2 Int Int))) (v_OBF__llbb (set enum_OBF__ii))
  (v_OBF__kkff (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__kkee (set Int)) (v_OBF__kkdd Int) (v_OBF__kkcc (set (tuple2 Int
  Int))) (v_OBF__kkbb (set Int)) (v_OBF__jjff (set (tuple2 (tuple2 Int
  enum_OBF__aa) Int))) (v_OBF__jjee (set Int)) (v_OBF__jjdd Int)
  (v_OBF__jjcc (set (tuple2 Int Int))) (v_OBF__jjbb Int)
  (v_OBF__iiff (set (tuple2 Int Int))) (v_OBF__iiee (set Int))
  (v_OBF__iidd (set (tuple2 (tuple2 (tuple2 Int Int) Int) Int)))
  (v_OBF__iicc (set (tuple2 Int Int))) (v_OBF__iibb Int)
  (v_OBF__hhff (set (tuple2 Int Int))) (v_OBF__hhee (set (tuple2 Int Int)))
  (v_OBF__hhdd (set (tuple2 (tuple2 Int enum_OBF__aa) Int)))
  (v_OBF__hhcc (set (tuple2 Int Int))) (v_OBF__hhbb (set enum_OBF__ii))
  (v_OBF__ggff (set (tuple2 Int Int))) (v_OBF__ggee (set (tuple2 Int Int)))
  (v_OBF__ggdd enum_OBF__aa) (v_OBF__ggcc (set Int)) (v_OBF__ggbb (set Int))
  (v_OBF__ffff (set (tuple2 (tuple2 Int Int) Int)))
  (v_OBF__ffee (set (tuple2 Int Int))) (v_OBF__ffdd Int)
  (v_OBF__ffcc (set Int)) (v_OBF__ffbb Int) (v_OBF__eeff (set (tuple2 Int
  Int))) (v_OBF__eeee (set (tuple2 Int Int))) (v_OBF__eedd (set (tuple2 Int
  Int))) (v_OBF__eecc (set Int)) (v_OBF__eebb Int) (v_OBF__ddff (set Int))
  (v_OBF__ddee (set Int)) (v_OBF__dddd Int) (v_OBF__ddcc (set Int))
  (v_OBF__ddbb Int) (v_OBF__ccff (set (tuple2 Int Int)))
  (v_OBF__ccee (set Int)) (v_OBF__ccdd (set (tuple2 Int Int)))
  (v_OBF__cccc (set (tuple2 Int Int))) (v_OBF__ccbb Int)
  (v_OBF__bbff (set (tuple2 Int Int))) (v_OBF__bbee Bool)
  (v_OBF__bbdd (set (tuple2 Int Int))) (v_OBF__bbcc (set Int))
  (v_OBF__bbbb (set Int)) (v_OBF__aaff (set (tuple2 Int Int)))
  (v_OBF__aaee (set (tuple2 Int Int))) (v_OBF__aadd (set (tuple2 Int Int)))
  (v_OBF__aacc (set Int)) (v_OBF__aabb Int))
  (=>
  (and (f1 v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb v_OBF__zz
  v_OBF__yyee v_OBF__yydd v_OBF__yycc v_OBF__yybb v_OBF__yy v_OBF__xxee
  v_OBF__xxdd v_OBF__xxcc v_OBF__xxbb v_OBF__xx v_OBF__wwee v_OBF__wwdd
  v_OBF__wwcc v_OBF__wwbb v_OBF__ww v_OBF__vvee v_OBF__vvdd v_OBF__vvcc
  v_OBF__vvbb v_OBF__vv v_OBF__uuee v_OBF__uudd v_OBF__uucc v_OBF__uubb
  v_OBF__uu v_OBF__ttee v_OBF__ttdd v_OBF__ttcc v_OBF__ttbb v_OBF__tt
  v_OBF__ssee v_OBF__ssdd v_OBF__sscc v_OBF__ssbb v_OBF__rree v_OBF__rrdd
  v_OBF__rrcc v_OBF__rrbb v_OBF__qqee v_OBF__qqdd v_OBF__qqcc v_OBF__qqbb
  v_OBF__ppee v_OBF__ppdd v_OBF__ppcc v_OBF__ppbb v_OBF__ooee v_OBF__oodd
  v_OBF__oocc v_OBF__oobb v_OBF__nnff v_OBF__nnee v_OBF__nndd v_OBF__nncc
  v_OBF__nnbb v_OBF__mmff v_OBF__mmee v_OBF__mmdd v_OBF__mmcc v_OBF__mmbb
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkff
  v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjff v_OBF__jjee
  v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iiff v_OBF__iiee v_OBF__iidd
  v_OBF__iicc v_OBF__iibb v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc
  v_OBF__hhbb v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb
  v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb v_OBF__eeff
  v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb v_OBF__ddff v_OBF__ddee
  v_OBF__dddd v_OBF__ddcc v_OBF__ddbb v_OBF__ccff v_OBF__ccee v_OBF__ccdd
  v_OBF__cccc v_OBF__ccbb v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc
  v_OBF__bbbb v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (and (f5 v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb v_OBF__zz
  v_OBF__yyee v_OBF__yydd v_OBF__yycc v_OBF__yybb v_OBF__yy v_OBF__xxee
  v_OBF__xxdd v_OBF__xxcc v_OBF__xxbb v_OBF__xx v_OBF__wwee v_OBF__wwdd
  v_OBF__wwcc v_OBF__wwbb v_OBF__ww v_OBF__vvee v_OBF__vvdd v_OBF__vvcc
  v_OBF__vvbb v_OBF__vv v_OBF__uuee v_OBF__uudd v_OBF__uucc v_OBF__uubb
  v_OBF__uu v_OBF__ttee v_OBF__ttdd v_OBF__ttcc v_OBF__ttbb v_OBF__tt
  v_OBF__ssee v_OBF__ssdd v_OBF__sscc v_OBF__ssbb v_OBF__rree v_OBF__rrdd
  v_OBF__rrcc v_OBF__rrbb v_OBF__qqee v_OBF__qqdd v_OBF__qqcc v_OBF__qqbb
  v_OBF__ppee v_OBF__ppdd v_OBF__ppcc v_OBF__ppbb v_OBF__ooee v_OBF__oodd
  v_OBF__oocc v_OBF__oobb v_OBF__nnff v_OBF__nnee v_OBF__nndd v_OBF__nncc
  v_OBF__nnbb v_OBF__mmff v_OBF__mmee v_OBF__mmdd v_OBF__mmcc v_OBF__mmbb
  v_OBF__llff v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkff
  v_OBF__kkee v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjff v_OBF__jjee
  v_OBF__jjdd v_OBF__jjcc v_OBF__jjbb v_OBF__iiff v_OBF__iiee v_OBF__iidd
  v_OBF__iicc v_OBF__iibb v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc
  v_OBF__hhbb v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb
  v_OBF__ffff v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb v_OBF__eeff
  v_OBF__eeee v_OBF__eedd v_OBF__eecc v_OBF__eebb v_OBF__ddff v_OBF__ddee
  v_OBF__dddd v_OBF__ddcc v_OBF__ddbb v_OBF__ccff v_OBF__ccee v_OBF__ccdd
  v_OBF__cccc v_OBF__ccbb v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc
  v_OBF__bbbb v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)
  (f25 v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb v_OBF__zz v_OBF__yyee
  v_OBF__yydd v_OBF__yycc v_OBF__yybb v_OBF__yy v_OBF__xxee v_OBF__xxdd
  v_OBF__xxcc v_OBF__xxbb v_OBF__xx v_OBF__wwee v_OBF__wwdd v_OBF__wwcc
  v_OBF__wwbb v_OBF__ww v_OBF__vvee v_OBF__vvdd v_OBF__vvcc v_OBF__vvbb
  v_OBF__vv v_OBF__uuee v_OBF__uudd v_OBF__uucc v_OBF__uubb v_OBF__uu
  v_OBF__ttee v_OBF__ttdd v_OBF__ttcc v_OBF__ttbb v_OBF__tt v_OBF__ssee
  v_OBF__ssdd v_OBF__sscc v_OBF__ssbb v_OBF__rree v_OBF__rrdd v_OBF__rrcc
  v_OBF__rrbb v_OBF__qqee v_OBF__qqdd v_OBF__qqcc v_OBF__qqbb v_OBF__ppee
  v_OBF__ppdd v_OBF__ppcc v_OBF__ppbb v_OBF__ooee v_OBF__oodd v_OBF__oocc
  v_OBF__oobb v_OBF__nnff v_OBF__nnee v_OBF__nndd v_OBF__nncc v_OBF__nnbb
  v_OBF__mmff v_OBF__mmee v_OBF__mmdd v_OBF__mmcc v_OBF__mmbb v_OBF__llff
  v_OBF__llee v_OBF__lldd v_OBF__llcc v_OBF__llbb v_OBF__kkff v_OBF__kkee
  v_OBF__kkdd v_OBF__kkcc v_OBF__kkbb v_OBF__jjff v_OBF__jjee v_OBF__jjdd
  v_OBF__jjcc v_OBF__jjbb v_OBF__iiff v_OBF__iiee v_OBF__iidd v_OBF__iicc
  v_OBF__iibb v_OBF__hhff v_OBF__hhee v_OBF__hhdd v_OBF__hhcc v_OBF__hhbb
  v_OBF__ggff v_OBF__ggee v_OBF__ggdd v_OBF__ggcc v_OBF__ggbb v_OBF__ffff
  v_OBF__ffee v_OBF__ffdd v_OBF__ffcc v_OBF__ffbb v_OBF__eeff v_OBF__eeee
  v_OBF__eedd v_OBF__eecc v_OBF__eebb v_OBF__ddff v_OBF__ddee v_OBF__dddd
  v_OBF__ddcc v_OBF__ddbb v_OBF__ccff v_OBF__ccee v_OBF__ccdd v_OBF__cccc
  v_OBF__ccbb v_OBF__bbff v_OBF__bbee v_OBF__bbdd v_OBF__bbcc v_OBF__bbbb
  v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb))) (infix_eqeq1
  v_OBF__zz empty1)))))
(check-sat)
