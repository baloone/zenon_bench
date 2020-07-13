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

(declare-sort tuple2 2)

(declare-fun tuple21 (ty ty) ty)

(declare-fun mem (ty uni uni) Bool)

(declare-fun mem1 (Int (set Int)) Bool)

(declare-fun mem2 (Bool (set Bool)) Bool)

(declare-fun mem3 ((set Int) (set (set Int))) Bool)

(declare-fun mem4 ((set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))) (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))) Bool)

(declare-fun infix_eqeq (ty uni uni) Bool)

(declare-fun t2tb ((set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (t2tb x))))

(declare-fun tb2t (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))))) (! (= (tb2t (t2tb i)) i) :pattern ((t2tb i)) )))

;; BridgeR
  (assert
  (forall ((j uni)) (! (= (t2tb (tb2t j)) j) :pattern ((t2tb (tb2t j))) )))

;; infix ==_def
  (assert
  (forall ((s1 (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (s2 (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))))
  (= (infix_eqeq
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s1) (t2tb s2))
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (= (mem4 x s1) (mem4 x s2))))))

(declare-fun t2tb1 ((set (set Int))) uni)

;; t2tb_sort
  (assert (forall ((x (set (set Int)))) (sort (set1 (set1 int)) (t2tb1 x))))

(declare-fun tb2t1 (uni) (set (set Int)))

;; BridgeL
  (assert
  (forall ((i (set (set Int))))
  (! (= (tb2t1 (t2tb1 i)) i) :pattern ((t2tb1 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb1 (tb2t1 j)) j) :pattern ((t2tb1 (tb2t1 j))) )))

;; infix ==_def
  (assert
  (forall ((s1 (set (set Int))) (s2 (set (set Int))))
  (= (infix_eqeq (set1 int) (t2tb1 s1) (t2tb1 s2))
  (forall ((x (set Int))) (= (mem3 x s1) (mem3 x s2))))))

(declare-fun t2tb2 ((set Bool)) uni)

;; t2tb_sort
  (assert (forall ((x (set Bool))) (sort (set1 bool) (t2tb2 x))))

(declare-fun tb2t2 (uni) (set Bool))

;; BridgeL
  (assert
  (forall ((i (set Bool))) (! (= (tb2t2 (t2tb2 i)) i) :pattern ((t2tb2 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 bool) j) (= (t2tb2 (tb2t2 j)) j)) :pattern ((t2tb2
                                                                 (tb2t2 j))) )))

;; infix ==_def
  (assert
  (forall ((s1 (set Bool)) (s2 (set Bool)))
  (= (infix_eqeq bool (t2tb2 s1) (t2tb2 s2))
  (forall ((x Bool)) (= (mem2 x s1) (mem2 x s2))))))

(declare-fun t2tb3 ((set Int)) uni)

;; t2tb_sort
  (assert (forall ((x (set Int))) (sort (set1 int) (t2tb3 x))))

(declare-fun tb2t3 (uni) (set Int))

;; BridgeL
  (assert
  (forall ((i (set Int))) (! (= (tb2t3 (t2tb3 i)) i) :pattern ((t2tb3 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb3 (tb2t3 j)) j) :pattern ((t2tb3 (tb2t3 j))) )))

;; infix ==_def
  (assert
  (forall ((s1 (set Int)) (s2 (set Int)))
  (= (infix_eqeq int (t2tb3 s1) (t2tb3 s2))
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
  (forall ((s1 (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (s2 (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))))
  (= (subset
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s1) (t2tb s2))
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (=> (mem4 x s1) (mem4 x s2))))))

;; subset_def
  (assert
  (forall ((s1 (set (set Int))) (s2 (set (set Int))))
  (= (subset (set1 int) (t2tb1 s1) (t2tb1 s2))
  (forall ((x (set Int))) (=> (mem3 x s1) (mem3 x s2))))))

;; subset_def
  (assert
  (forall ((s1 (set Bool)) (s2 (set Bool)))
  (= (subset bool (t2tb2 s1) (t2tb2 s2))
  (forall ((x Bool)) (=> (mem2 x s1) (mem2 x s2))))))

;; subset_def
  (assert
  (forall ((s1 (set Int)) (s2 (set Int)))
  (= (subset int (t2tb3 s1) (t2tb3 s2))
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

(declare-fun empty1 () (set Bool))

(declare-fun empty2 () (set Int))

(declare-fun empty3 () (set (set Int)))

(declare-fun empty4 () (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))

(declare-fun empty5 () (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))

(declare-fun empty6 () (set (tuple2 (tuple2 Bool Bool) Bool)))

(declare-fun empty7 () (set (tuple2 Bool Bool)))

(declare-fun empty8 () (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))))

(declare-fun is_empty (ty uni) Bool)

;; is_empty_def
  (assert
  (forall ((s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))))
  (= (is_empty
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s))
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (not (mem4 x s))))))

;; is_empty_def
  (assert
  (forall ((s (set (set Int))))
  (= (is_empty (set1 int) (t2tb1 s))
  (forall ((x (set Int))) (not (mem3 x s))))))

;; is_empty_def
  (assert
  (forall ((s (set Bool)))
  (= (is_empty bool (t2tb2 s)) (forall ((x Bool)) (not (mem2 x s))))))

;; is_empty_def
  (assert
  (forall ((s (set Int)))
  (= (is_empty int (t2tb3 s)) (forall ((x Int)) (not (mem1 x s))))))

;; is_empty_def
  (assert
  (forall ((a ty))
  (forall ((s uni))
  (and (=> (is_empty a s) (forall ((x uni)) (not (mem a x s))))
  (=> (forall ((x uni)) (=> (sort a x) (not (mem a x s)))) (is_empty a s))))))

;; empty_def1
  (assert (is_empty
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb empty8)))

(declare-fun t2tb4 ((set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (sort
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb4 x))))

(declare-fun tb2t4 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (! (= (tb2t4 (t2tb4 i)) i) :pattern ((t2tb4 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb4 (tb2t4 j)) j) :pattern ((t2tb4 (tb2t4 j))) )))

;; empty_def1
  (assert (is_empty
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb4 empty4)))

(declare-fun t2tb5 ((set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))) (sort
  (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb5 x))))

(declare-fun tb2t5 (uni) (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (! (= (tb2t5 (t2tb5 i)) i) :pattern ((t2tb5 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) j)
     (= (t2tb5 (tb2t5 j)) j)) :pattern ((t2tb5 (tb2t5 j))) )))

;; empty_def1
  (assert (is_empty (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 empty5)))

(declare-fun t2tb6 ((set (tuple2 (tuple2 Bool Bool) Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Bool Bool) Bool)))) (sort
  (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb6 x))))

(declare-fun tb2t6 (uni) (set (tuple2 (tuple2 Bool Bool) Bool)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Bool Bool) Bool))))
  (! (= (tb2t6 (t2tb6 i)) i) :pattern ((t2tb6 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (tuple21 (tuple21 bool bool) bool)) j)
     (= (t2tb6 (tb2t6 j)) j)) :pattern ((t2tb6 (tb2t6 j))) )))

;; empty_def1
  (assert (is_empty (tuple21 (tuple21 bool bool) bool) (t2tb6 empty6)))

;; empty_def1
  (assert (is_empty (set1 int) (t2tb1 empty3)))

(declare-fun t2tb7 ((set (tuple2 Bool Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Bool Bool)))) (sort (set1 (tuple21 bool bool))
  (t2tb7 x))))

(declare-fun tb2t7 (uni) (set (tuple2 Bool Bool)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Bool Bool))))
  (! (= (tb2t7 (t2tb7 i)) i) :pattern ((t2tb7 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (tuple21 bool bool)) j) (= (t2tb7 (tb2t7 j)) j)) :pattern (
  (t2tb7 (tb2t7 j))) )))

;; empty_def1
  (assert (is_empty (tuple21 bool bool) (t2tb7 empty7)))

;; empty_def1
  (assert (is_empty bool (t2tb2 empty1)))

;; empty_def1
  (assert (is_empty int (t2tb3 empty2)))

;; empty_def1
  (assert (forall ((a ty)) (is_empty a (empty a))))

;; mem_empty
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (not (mem4 x empty8))))

(declare-fun t2tb8 ((tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (sort
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb8 x))))

(declare-fun tb2t8 (uni) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (! (= (tb2t8 (t2tb8 i)) i) :pattern ((t2tb8 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb8 (tb2t8 j)) j) :pattern ((t2tb8 (tb2t8 j))) )))

;; mem_empty
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))
  (not (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb8 x) (t2tb4 empty4)))))

(declare-fun t2tb9 ((tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))) (sort
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x))))

(declare-fun tb2t9 (uni) (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (! (= (tb2t9 (t2tb9 i)) i) :pattern ((t2tb9 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (tuple21 (tuple21 (tuple21 bool bool) bool) bool) j)
     (= (t2tb9 (tb2t9 j)) j)) :pattern ((t2tb9 (tb2t9 j))) )))

;; mem_empty
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (not (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
  (t2tb5 empty5)))))

(declare-fun t2tb10 ((tuple2 (tuple2 Bool Bool) Bool)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool))) (sort
  (tuple21 (tuple21 bool bool) bool) (t2tb10 x))))

(declare-fun tb2t10 (uni) (tuple2 (tuple2 Bool Bool) Bool))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 Bool Bool) Bool)))
  (! (= (tb2t10 (t2tb10 i)) i) :pattern ((t2tb10 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (tuple21 (tuple21 bool bool) bool) j)
     (= (t2tb10 (tb2t10 j)) j)) :pattern ((t2tb10 (tb2t10 j))) )))

;; mem_empty
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)))
  (not (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb6 empty6)))))

;; mem_empty
  (assert (forall ((x (set Int))) (not (mem3 x empty3))))

(declare-fun t2tb11 ((tuple2 Bool Bool)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Bool Bool))) (sort (tuple21 bool bool) (t2tb11 x))))

(declare-fun tb2t11 (uni) (tuple2 Bool Bool))

;; BridgeL
  (assert
  (forall ((i (tuple2 Bool Bool)))
  (! (= (tb2t11 (t2tb11 i)) i) :pattern ((t2tb11 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (tuple21 bool bool) j) (= (t2tb11 (tb2t11 j)) j)) :pattern (
  (t2tb11 (tb2t11 j))) )))

;; mem_empty
  (assert
  (forall ((x (tuple2 Bool Bool)))
  (not (mem (tuple21 bool bool) (t2tb11 x) (t2tb7 empty7)))))

;; mem_empty
  (assert (forall ((x Bool)) (not (mem2 x empty1))))

;; mem_empty
  (assert (forall ((x Int)) (not (mem1 x empty2))))

;; mem_empty
  (assert (forall ((a ty)) (forall ((x uni)) (not (mem a x (empty a))))))

(declare-fun add (ty uni uni) uni)

;; add_sort
  (assert
  (forall ((a ty)) (forall ((x uni) (x1 uni)) (sort (set1 a) (add a x x1)))))

(declare-fun add1 (Bool (set Bool)) (set Bool))

(declare-fun add2 (Int (set Int)) (set Int))

(declare-fun add3 ((set Int) (set (set Int))) (set (set Int)))

(declare-fun add4 ((set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))) (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))) (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))))

;; add_def1
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))
  (forall ((s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))))) (= (mem4 x (add4 y s)) (or (= x y) (mem4 x s))))))

;; add_def1
  (assert
  (forall ((x (set Int)) (y (set Int)))
  (forall ((s (set (set Int))))
  (= (mem3 x (add3 y s)) (or (= x y) (mem3 x s))))))

;; add_def1
  (assert
  (forall ((x Bool) (y Bool))
  (forall ((s (set Bool))) (= (mem2 x (add1 y s)) (or (= x y) (mem2 x s))))))

;; add_def1
  (assert
  (forall ((x Int) (y Int))
  (forall ((s (set Int))) (= (mem1 x (add2 y s)) (or (= x y) (mem1 x s))))))

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
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))))
  (= (mem4 x
  (tb2t
  (remove
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb4 y) (t2tb s)))) (and (not (= x y)) (mem4 x s)))))

;; remove_def1
  (assert
  (forall ((x (set Int)) (y (set Int)) (s (set (set Int))))
  (= (mem3 x (tb2t1 (remove (set1 int) (t2tb3 y) (t2tb1 s))))
  (and (not (= x y)) (mem3 x s)))))

(declare-fun t2tb12 (Bool) uni)

;; t2tb_sort
  (assert (forall ((x Bool)) (sort bool (t2tb12 x))))

(declare-fun tb2t12 (uni) Bool)

;; BridgeL
  (assert
  (forall ((i Bool)) (! (= (tb2t12 (t2tb12 i)) i) :pattern ((t2tb12 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort bool j) (= (t2tb12 (tb2t12 j)) j)) :pattern ((t2tb12
                                                            (tb2t12 j))) )))

;; remove_def1
  (assert
  (forall ((x Bool) (y Bool) (s (set Bool)))
  (= (mem2 x (tb2t2 (remove bool (t2tb12 y) (t2tb2 s))))
  (and (not (= x y)) (mem2 x s)))))

(declare-fun t2tb13 (Int) uni)

;; t2tb_sort
  (assert (forall ((x Int)) (sort int (t2tb13 x))))

(declare-fun tb2t13 (uni) Int)

;; BridgeL
  (assert
  (forall ((i Int)) (! (= (tb2t13 (t2tb13 i)) i) :pattern ((t2tb13 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb13 (tb2t13 j)) j) :pattern ((t2tb13 (tb2t13 j))) )))

;; remove_def1
  (assert
  (forall ((x Int) (y Int) (s (set Int)))
  (= (mem1 x (tb2t3 (remove int (t2tb13 y) (t2tb3 s))))
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
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))))
  (=> (mem4 x s)
  (= (add4 x
     (tb2t
     (remove
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb4 x) (t2tb s)))) s))))

;; add_remove
  (assert
  (forall ((x (set Int)) (s (set (set Int))))
  (=> (mem3 x s)
  (= (add3 x (tb2t1 (remove (set1 int) (t2tb3 x) (t2tb1 s)))) s))))

;; add_remove
  (assert
  (forall ((x Bool) (s (set Bool)))
  (=> (mem2 x s) (= (add1 x (tb2t2 (remove bool (t2tb12 x) (t2tb2 s)))) s))))

;; add_remove
  (assert
  (forall ((x Int) (s (set Int)))
  (=> (mem1 x s) (= (add2 x (tb2t3 (remove int (t2tb13 x) (t2tb3 s)))) s))))

;; add_remove
  (assert
  (forall ((a ty))
  (forall ((x uni) (s uni))
  (=> (sort (set1 a) s) (=> (mem a x s) (= (add a x (remove a x s)) s))))))

;; remove_add
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))))
  (= (tb2t
     (remove
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb4 x) (t2tb (add4 x s)))) (tb2t
                                   (remove
                                   (set1
                                   (tuple21
                                   (tuple21
                                   (tuple21 (tuple21 bool bool) bool) 
                                   bool) (set1 int))) (t2tb4 x) (t2tb s))))))

;; remove_add
  (assert
  (forall ((x (set Int)) (s (set (set Int))))
  (= (tb2t1 (remove (set1 int) (t2tb3 x) (t2tb1 (add3 x s)))) (tb2t1
                                                              (remove
                                                              (set1 int)
                                                              (t2tb3 x)
                                                              (t2tb1 s))))))

;; remove_add
  (assert
  (forall ((x Bool) (s (set Bool)))
  (= (tb2t2 (remove bool (t2tb12 x) (t2tb2 (add1 x s)))) (tb2t2
                                                         (remove bool
                                                         (t2tb12 x)
                                                         (t2tb2 s))))))

;; remove_add
  (assert
  (forall ((x Int) (s (set Int)))
  (= (tb2t3 (remove int (t2tb13 x) (t2tb3 (add2 x s)))) (tb2t3
                                                        (remove int
                                                        (t2tb13 x) (t2tb3 s))))))

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
  (forall ((s1 (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (s2 (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))))
  (x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))
  (= (mem4 x
  (tb2t
  (union
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s1) (t2tb s2)))) (or (mem4 x s1) (mem4 x s2)))))

;; union_def1
  (assert
  (forall ((s1 (set (set Int))) (s2 (set (set Int))) (x (set Int)))
  (= (mem3 x (tb2t1 (union (set1 int) (t2tb1 s1) (t2tb1 s2))))
  (or (mem3 x s1) (mem3 x s2)))))

;; union_def1
  (assert
  (forall ((s1 (set Bool)) (s2 (set Bool)) (x Bool))
  (= (mem2 x (tb2t2 (union bool (t2tb2 s1) (t2tb2 s2))))
  (or (mem2 x s1) (mem2 x s2)))))

;; union_def1
  (assert
  (forall ((s1 (set Int)) (s2 (set Int)) (x Int))
  (= (mem1 x (tb2t3 (union int (t2tb3 s1) (t2tb3 s2))))
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
  (forall ((s1 (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (s2 (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))))
  (x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))
  (= (mem4 x
  (tb2t
  (inter
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s1) (t2tb s2)))) (and (mem4 x s1) (mem4 x s2)))))

;; inter_def1
  (assert
  (forall ((s1 (set (set Int))) (s2 (set (set Int))) (x (set Int)))
  (= (mem3 x (tb2t1 (inter (set1 int) (t2tb1 s1) (t2tb1 s2))))
  (and (mem3 x s1) (mem3 x s2)))))

;; inter_def1
  (assert
  (forall ((s1 (set Bool)) (s2 (set Bool)) (x Bool))
  (= (mem2 x (tb2t2 (inter bool (t2tb2 s1) (t2tb2 s2))))
  (and (mem2 x s1) (mem2 x s2)))))

;; inter_def1
  (assert
  (forall ((s1 (set Int)) (s2 (set Int)) (x Int))
  (= (mem1 x (tb2t3 (inter int (t2tb3 s1) (t2tb3 s2))))
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
  (forall ((s1 (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (s2 (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))))
  (x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))
  (= (mem4 x
  (tb2t
  (diff
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s1) (t2tb s2)))) (and (mem4 x s1) (not (mem4 x s2))))))

;; diff_def1
  (assert
  (forall ((s1 (set (set Int))) (s2 (set (set Int))) (x (set Int)))
  (= (mem3 x (tb2t1 (diff (set1 int) (t2tb1 s1) (t2tb1 s2))))
  (and (mem3 x s1) (not (mem3 x s2))))))

;; diff_def1
  (assert
  (forall ((s1 (set Bool)) (s2 (set Bool)) (x Bool))
  (= (mem2 x (tb2t2 (diff bool (t2tb2 s1) (t2tb2 s2))))
  (and (mem2 x s1) (not (mem2 x s2))))))

;; diff_def1
  (assert
  (forall ((s1 (set Int)) (s2 (set Int)) (x Int))
  (= (mem1 x (tb2t3 (diff int (t2tb3 s1) (t2tb3 s2))))
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
  (forall ((s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))))
  (=>
  (not (is_empty
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s))) (mem4
  (tb2t4
  (choose
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s))) s))))

;; choose_def
  (assert
  (forall ((s (set (set Int))))
  (=> (not (is_empty (set1 int) (t2tb1 s))) (mem3
  (tb2t3 (choose (set1 int) (t2tb1 s))) s))))

;; choose_def
  (assert
  (forall ((s (set Bool)))
  (=> (not (is_empty bool (t2tb2 s))) (mem2 (tb2t12 (choose bool (t2tb2 s)))
  s))))

;; choose_def
  (assert
  (forall ((s (set Int)))
  (=> (not (is_empty int (t2tb3 s))) (mem1 (tb2t13 (choose int (t2tb3 s)))
  s))))

;; choose_def
  (assert
  (forall ((a ty))
  (forall ((s uni)) (=> (not (is_empty a s)) (mem a (choose a s) s)))))

(declare-fun all (ty) uni)

;; all_sort
  (assert (forall ((a ty)) (sort (set1 a) (all a))))

;; all_def
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (mem4 x
  (tb2t
  (all
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))))))

;; all_def
  (assert (forall ((x (set Int))) (mem3 x (tb2t1 (all (set1 int))))))

;; all_def
  (assert (forall ((x Bool)) (mem2 x (tb2t2 (all bool)))))

;; all_def
  (assert (forall ((x Int)) (mem1 x (tb2t3 (all int)))))

;; all_def
  (assert (forall ((a ty)) (forall ((x uni)) (mem a x (all a)))))

(declare-fun b_bool () (set Bool))

;; mem_b_bool
  (assert (forall ((x Bool)) (mem2 x b_bool)))

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
  (assert (forall ((a Int) (b Int)) (=> (< b a) (= (mk a b) empty2))))

;; interval_add
  (assert
  (forall ((a Int) (b Int))
  (=> (<= a b) (= (mk a b) (add2 b (mk a (- b 1)))))))

(declare-fun power (ty uni) uni)

;; power_sort
  (assert
  (forall ((a ty)) (forall ((x uni)) (sort (set1 (set1 a)) (power a x)))))

(declare-fun power1 ((set Int)) (set (set Int)))

(declare-fun power2 ((set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))) (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))))

;; mem_power
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))
  (! (= (mem4 x (power2 y)) (subset
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
     (t2tb4 x) (t2tb4 y))) :pattern ((mem4
  x (power2 y))) )))

;; mem_power
  (assert
  (forall ((x (set Int)) (y (set Int)))
  (! (= (mem3 x (power1 y)) (subset int (t2tb3 x) (t2tb3 y))) :pattern ((mem3
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

(declare-fun t2tb14 ((set (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))))) (sort
  (set1
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (t2tb14 x))))

(declare-fun tb2t14 (uni) (set (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))))

;; BridgeL
  (assert
  (forall ((i (set (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))))) (! (= (tb2t14 (t2tb14 i)) i) :pattern ((t2tb14 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb14 (tb2t14 j)) j) :pattern ((t2tb14 (tb2t14 j))) )))

;; mem_non_empty_power
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (y (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))))
  (! (= (mem
     (set1
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
     (t2tb x)
     (non_empty_power
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb y)))
     (and (subset
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb x) (t2tb y)) (not (= x empty8)))) :pattern ((mem
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (t2tb x)
  (non_empty_power
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb y)))) )))

;; mem_non_empty_power
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))
  (! (= (mem4 x
     (tb2t
     (non_empty_power
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
     (t2tb4 y))))
     (and (subset
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
     (t2tb4 x) (t2tb4 y)) (not (= x empty4)))) :pattern ((mem4
  x
  (tb2t
  (non_empty_power
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb4 y))))) )))

(declare-fun t2tb15 ((set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))))
  (sort (set1 (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))
  (t2tb15 x))))

(declare-fun tb2t15 (uni) (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))))
  (! (= (tb2t15 (t2tb15 i)) i) :pattern ((t2tb15 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1 (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool))) j)
     (= (t2tb15 (tb2t15 j)) j)) :pattern ((t2tb15 (tb2t15 j))) )))

;; mem_non_empty_power
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (y (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (! (= (mem (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
     (t2tb5 x)
     (non_empty_power (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (t2tb5 y)))
     (and (subset (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb5 x)
     (t2tb5 y)) (not (= x empty5)))) :pattern ((mem
  (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb5 x)
  (non_empty_power (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 y)))) )))

(declare-fun t2tb16 ((set (set (tuple2 (tuple2 Bool Bool) Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 Bool Bool) Bool))))) (sort
  (set1 (set1 (tuple21 (tuple21 bool bool) bool))) (t2tb16 x))))

(declare-fun tb2t16 (uni) (set (set (tuple2 (tuple2 Bool Bool) Bool))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 Bool Bool) Bool)))))
  (! (= (tb2t16 (t2tb16 i)) i) :pattern ((t2tb16 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (set1 (tuple21 (tuple21 bool bool) bool))) j)
     (= (t2tb16 (tb2t16 j)) j)) :pattern ((t2tb16 (tb2t16 j))) )))

;; mem_non_empty_power
  (assert
  (forall ((x (set (tuple2 (tuple2 Bool Bool) Bool)))
  (y (set (tuple2 (tuple2 Bool Bool) Bool))))
  (! (= (mem (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb6 x)
     (non_empty_power (tuple21 (tuple21 bool bool) bool) (t2tb6 y)))
     (and (subset (tuple21 (tuple21 bool bool) bool) (t2tb6 x) (t2tb6 y))
     (not (= x empty6)))) :pattern ((mem
  (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb6 x)
  (non_empty_power (tuple21 (tuple21 bool bool) bool) (t2tb6 y)))) )))

(declare-fun t2tb17 ((set (set (set Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (set Int))))) (sort (set1 (set1 (set1 int)))
  (t2tb17 x))))

(declare-fun tb2t17 (uni) (set (set (set Int))))

;; BridgeL
  (assert
  (forall ((i (set (set (set Int)))))
  (! (= (tb2t17 (t2tb17 i)) i) :pattern ((t2tb17 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb17 (tb2t17 j)) j) :pattern ((t2tb17 (tb2t17 j))) )))

;; mem_non_empty_power
  (assert
  (forall ((x (set (set Int))) (y (set (set Int))))
  (! (= (mem (set1 (set1 int)) (t2tb1 x)
     (non_empty_power (set1 int) (t2tb1 y)))
     (and (subset (set1 int) (t2tb1 x) (t2tb1 y)) (not (= x empty3)))) :pattern ((mem
  (set1 (set1 int)) (t2tb1 x) (non_empty_power (set1 int) (t2tb1 y)))) )))

(declare-fun t2tb18 ((set (set (tuple2 Bool Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Bool Bool))))) (sort
  (set1 (set1 (tuple21 bool bool))) (t2tb18 x))))

(declare-fun tb2t18 (uni) (set (set (tuple2 Bool Bool))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Bool Bool)))))
  (! (= (tb2t18 (t2tb18 i)) i) :pattern ((t2tb18 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (set1 (tuple21 bool bool))) j)
     (= (t2tb18 (tb2t18 j)) j)) :pattern ((t2tb18 (tb2t18 j))) )))

;; mem_non_empty_power
  (assert
  (forall ((x (set (tuple2 Bool Bool))) (y (set (tuple2 Bool Bool))))
  (! (= (mem (set1 (tuple21 bool bool)) (t2tb7 x)
     (non_empty_power (tuple21 bool bool) (t2tb7 y)))
     (and (subset (tuple21 bool bool) (t2tb7 x) (t2tb7 y))
     (not (= x empty7)))) :pattern ((mem
  (set1 (tuple21 bool bool)) (t2tb7 x)
  (non_empty_power (tuple21 bool bool) (t2tb7 y)))) )))

(declare-fun t2tb19 ((set (set Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set Bool)))) (sort (set1 (set1 bool)) (t2tb19 x))))

(declare-fun tb2t19 (uni) (set (set Bool)))

;; BridgeL
  (assert
  (forall ((i (set (set Bool))))
  (! (= (tb2t19 (t2tb19 i)) i) :pattern ((t2tb19 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (set1 bool)) j) (= (t2tb19 (tb2t19 j)) j)) :pattern (
  (t2tb19 (tb2t19 j))) )))

;; mem_non_empty_power
  (assert
  (forall ((x (set Bool)) (y (set Bool)))
  (! (= (mem (set1 bool) (t2tb2 x) (non_empty_power bool (t2tb2 y)))
     (and (subset bool (t2tb2 x) (t2tb2 y)) (not (= x empty1)))) :pattern ((mem
  (set1 bool) (t2tb2 x) (non_empty_power bool (t2tb2 y)))) )))

;; mem_non_empty_power
  (assert
  (forall ((x (set Int)) (y (set Int)))
  (! (= (mem3 x (tb2t1 (non_empty_power int (t2tb3 y))))
     (and (subset int (t2tb3 x) (t2tb3 y)) (not (= x empty2)))) :pattern ((mem3
  x (tb2t1 (non_empty_power int (t2tb3 y))))) )))

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
  (forall ((f uni) (s uni) (t (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))))
  (and
  (=> (mem
  (set1
  (tuple21 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))) f
  (relation
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) a s
  (t2tb t)))
  (forall ((x uni) (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))))
  (=> (mem
  (tuple21 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) x
  (t2tb4 y)) f) (and (mem a x s) (mem4 y t)))))
  (=>
  (forall ((x uni) (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))))
  (=> (sort a x)
  (=> (mem
  (tuple21 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) x
  (t2tb4 y)) f) (and (mem a x s) (mem4 y t))))) (mem
  (set1
  (tuple21 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))) f
  (relation
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) a s
  (t2tb t))))))))

;; mem_relation
  (assert
  (forall ((a ty))
  (forall ((f uni) (s uni) (t (set (set Int))))
  (and
  (=> (mem (set1 (tuple21 a (set1 int))) f
  (relation (set1 int) a s (t2tb1 t)))
  (forall ((x uni) (y (set Int)))
  (=> (mem (tuple21 a (set1 int)) (Tuple2 a (set1 int) x (t2tb3 y)) f)
  (and (mem a x s) (mem3 y t)))))
  (=>
  (forall ((x uni) (y (set Int)))
  (=> (sort a x)
  (=> (mem (tuple21 a (set1 int)) (Tuple2 a (set1 int) x (t2tb3 y)) f)
  (and (mem a x s) (mem3 y t))))) (mem (set1 (tuple21 a (set1 int))) f
  (relation (set1 int) a s (t2tb1 t))))))))

;; mem_relation
  (assert
  (forall ((a ty))
  (forall ((f uni) (s uni) (t (set Bool)))
  (and
  (=> (mem (set1 (tuple21 a bool)) f (relation bool a s (t2tb2 t)))
  (forall ((x uni) (y Bool))
  (=> (mem (tuple21 a bool) (Tuple2 a bool x (t2tb12 y)) f)
  (and (mem a x s) (mem2 y t)))))
  (=>
  (forall ((x uni) (y Bool))
  (=> (sort a x)
  (=> (mem (tuple21 a bool) (Tuple2 a bool x (t2tb12 y)) f)
  (and (mem a x s) (mem2 y t))))) (mem (set1 (tuple21 a bool)) f
  (relation bool a s (t2tb2 t))))))))

;; mem_relation
  (assert
  (forall ((a ty))
  (forall ((f uni) (s uni) (t (set Int)))
  (and
  (=> (mem (set1 (tuple21 a int)) f (relation int a s (t2tb3 t)))
  (forall ((x uni) (y Int))
  (=> (mem (tuple21 a int) (Tuple2 a int x (t2tb13 y)) f)
  (and (mem a x s) (mem1 y t)))))
  (=>
  (forall ((x uni) (y Int))
  (=> (sort a x)
  (=> (mem (tuple21 a int) (Tuple2 a int x (t2tb13 y)) f)
  (and (mem a x s) (mem1 y t))))) (mem (set1 (tuple21 a int)) f
  (relation int a s (t2tb3 t))))))))

(declare-fun t2tb20 ((set (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))))))) (sort
  (set1
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))))
  (t2tb20 x))))

(declare-fun tb2t20 (uni) (set (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))))))
  (! (= (tb2t20 (t2tb20 i)) i) :pattern ((t2tb20 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb20 (tb2t20 j)) j) :pattern ((t2tb20 (tb2t20 j))) )))

(declare-fun t2tb21 ((set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))))) (sort
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (t2tb21 x))))

(declare-fun tb2t21 (uni) (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))))))
  (! (= (tb2t21 (t2tb21 i)) i) :pattern ((t2tb21 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb21 (tb2t21 j)) j) :pattern ((t2tb21 (tb2t21 j))) )))

(declare-fun t2tb22 ((tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))))) (sort
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (t2tb22 x))))

(declare-fun tb2t22 (uni) (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))))

;; BridgeL
  (assert
  (forall ((i (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))))) (! (= (tb2t22 (t2tb22 i)) i) :pattern ((t2tb22 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb22 (tb2t22 j)) j) :pattern ((t2tb22 (tb2t22 j))) )))

;; mem_relation
  (assert
  (forall ((f (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))))
  (s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (t (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))))
  (= (mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (t2tb21 f)
  (relation
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s) (t2tb t)))
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))
  (=> (mem
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb4 x) (t2tb4 y)) (t2tb21 f)) (and (mem4 x s) (mem4 y t)))))))

(declare-fun t2tb23 ((set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (set Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))) (set Int))))) (sort
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1 int))) (t2tb23 x))))

(declare-fun tb2t23 (uni) (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (set Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))) (set Int)))))
  (! (= (tb2t23 (t2tb23 i)) i) :pattern ((t2tb23 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb23 (tb2t23 j)) j) :pattern ((t2tb23 (tb2t23 j))) )))

(declare-fun t2tb24 ((tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))) (set Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))) (set Int)))) (sort
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1 int)) (t2tb24 x))))

(declare-fun tb2t24 (uni) (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (set Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))) (set Int))))
  (! (= (tb2t24 (t2tb24 i)) i) :pattern ((t2tb24 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb24 (tb2t24 j)) j) :pattern ((t2tb24 (tb2t24 j))) )))

(declare-fun t2tb25 ((set (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (set Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (set Int)))))) (sort
  (set1
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1 int)))) (t2tb25 x))))

(declare-fun tb2t25 (uni) (set (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (set Int)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (set Int))))))
  (! (= (tb2t25 (t2tb25 i)) i) :pattern ((t2tb25 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb25 (tb2t25 j)) j) :pattern ((t2tb25 (tb2t25 j))) )))

;; mem_relation
  (assert
  (forall ((f (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))) (set Int))))
  (s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (t (set (set Int))))
  (= (mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1 int))) (t2tb23 f)
  (relation (set1 int)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s) (t2tb1 t)))
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (y (set Int)))
  (=> (mem
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1 int))
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1 int) (t2tb4 x) (t2tb3 y)) (t2tb23 f)) (and (mem4 x s) (mem3 y t)))))))

(declare-fun t2tb26 ((set (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) Bool))))) (sort
  (set1
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  bool))) (t2tb26 x))))

(declare-fun tb2t26 (uni) (set (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) Bool))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) Bool)))))
  (! (= (tb2t26 (t2tb26 i)) i) :pattern ((t2tb26 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb26 (tb2t26 j)) j) :pattern ((t2tb26 (tb2t26 j))) )))

(declare-fun t2tb27 ((set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))) Bool)))) (sort
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  bool)) (t2tb27 x))))

(declare-fun tb2t27 (uni) (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) Bool)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))) Bool))))
  (! (= (tb2t27 (t2tb27 i)) i) :pattern ((t2tb27 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb27 (tb2t27 j)) j) :pattern ((t2tb27 (tb2t27 j))) )))

(declare-fun t2tb28 ((tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))) Bool)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))) Bool))) (sort
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  bool) (t2tb28 x))))

(declare-fun tb2t28 (uni) (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) Bool))

;; BridgeL
  (assert
  (forall ((i (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))) Bool)))
  (! (= (tb2t28 (t2tb28 i)) i) :pattern ((t2tb28 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb28 (tb2t28 j)) j) :pattern ((t2tb28 (tb2t28 j))) )))

;; mem_relation
  (assert
  (forall ((f (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))) Bool)))
  (s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (t (set Bool)))
  (= (mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  bool)) (t2tb27 f)
  (relation bool
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s) (t2tb2 t)))
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (y Bool))
  (=> (mem
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  bool)
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  bool (t2tb4 x) (t2tb12 y)) (t2tb27 f)) (and (mem4 x s) (mem2 y t)))))))

(declare-fun t2tb29 ((set (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) Int))))) (sort
  (set1
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  int))) (t2tb29 x))))

(declare-fun tb2t29 (uni) (set (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) Int))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) Int)))))
  (! (= (tb2t29 (t2tb29 i)) i) :pattern ((t2tb29 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb29 (tb2t29 j)) j) :pattern ((t2tb29 (tb2t29 j))) )))

(declare-fun t2tb30 ((set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))) Int)))) (sort
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  int)) (t2tb30 x))))

(declare-fun tb2t30 (uni) (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))) Int))))
  (! (= (tb2t30 (t2tb30 i)) i) :pattern ((t2tb30 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb30 (tb2t30 j)) j) :pattern ((t2tb30 (tb2t30 j))) )))

(declare-fun t2tb31 ((tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))) Int)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))) Int))) (sort
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  int) (t2tb31 x))))

(declare-fun tb2t31 (uni) (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) Int))

;; BridgeL
  (assert
  (forall ((i (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))) Int)))
  (! (= (tb2t31 (t2tb31 i)) i) :pattern ((t2tb31 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb31 (tb2t31 j)) j) :pattern ((t2tb31 (tb2t31 j))) )))

;; mem_relation
  (assert
  (forall ((f (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))) Int)))
  (s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (t (set Int)))
  (= (mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  int)) (t2tb30 f)
  (relation int
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s) (t2tb3 t)))
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (y Int))
  (=> (mem
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  int)
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) 
  int (t2tb4 x) (t2tb13 y)) (t2tb30 f)) (and (mem4 x s) (mem1 y t)))))))

;; mem_relation
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))) (t uni))
  (and
  (=> (mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b))
  f
  (relation b
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s) t))
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (y uni))
  (=> (mem
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b)
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b
  (t2tb4 x) y) f) (and (mem4 x s) (mem b y t)))))
  (=>
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (y uni))
  (=> (sort b y)
  (=> (mem
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b)
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b
  (t2tb4 x) y) f) (and (mem4 x s) (mem b y t))))) (mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b))
  f
  (relation b
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s) t)))))))

;; mem_relation
  (assert
  (forall ((f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (t (set (set Int))))
  (= (mem4 f
  (tb2t
  (relation (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 s) (t2tb1 t))))
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)) (y (set Int)))
  (=> (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb9 x) (t2tb3 y)) (t2tb4 f))
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
  (t2tb5 s)) (mem3 y t)))))))

(declare-fun t2tb32 ((set (set (tuple2 (set Int)
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (set Int)
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))))) (sort
  (set1
  (set1
  (tuple21 (set1 int)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))))
  (t2tb32 x))))

(declare-fun tb2t32 (uni) (set (set (tuple2 (set Int)
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (set Int)
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))))) (! (= (tb2t32 (t2tb32 i)) i) :pattern ((t2tb32 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb32 (tb2t32 j)) j) :pattern ((t2tb32 (tb2t32 j))) )))

(declare-fun t2tb33 ((set (tuple2 (set Int)
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (set Int)
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))))
  (sort
  (set1
  (tuple21 (set1 int)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (t2tb33 x))))

(declare-fun tb2t33 (uni) (set (tuple2 (set Int)
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (set Int)
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))))
  (! (= (tb2t33 (t2tb33 i)) i) :pattern ((t2tb33 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb33 (tb2t33 j)) j) :pattern ((t2tb33 (tb2t33 j))) )))

(declare-fun t2tb34 ((tuple2 (set Int)
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (set Int) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))))) (sort
  (tuple21 (set1 int)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (t2tb34 x))))

(declare-fun tb2t34 (uni) (tuple2 (set Int)
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))

;; BridgeL
  (assert
  (forall ((i (tuple2 (set Int) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))))
  (! (= (tb2t34 (t2tb34 i)) i) :pattern ((t2tb34 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb34 (tb2t34 j)) j) :pattern ((t2tb34 (tb2t34 j))) )))

;; mem_relation
  (assert
  (forall ((f (set (tuple2 (set Int)
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))))
  (s (set (set Int))) (t (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))))
  (= (mem
  (set1
  (tuple21 (set1 int)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (t2tb33 f)
  (relation
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1 int) (t2tb1 s) (t2tb t)))
  (forall ((x (set Int)) (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))))
  (=> (mem
  (tuple21 (set1 int)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2 (set1 int)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb3 x) (t2tb4 y)) (t2tb33 f)) (and (mem3 x s) (mem4 y t)))))))

(declare-fun t2tb35 ((tuple2 (set Int) (set Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (set Int) (set Int)))) (sort
  (tuple21 (set1 int) (set1 int)) (t2tb35 x))))

(declare-fun tb2t35 (uni) (tuple2 (set Int) (set Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (set Int) (set Int))))
  (! (= (tb2t35 (t2tb35 i)) i) :pattern ((t2tb35 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb35 (tb2t35 j)) j) :pattern ((t2tb35 (tb2t35 j))) )))

(declare-fun t2tb36 ((set (set (tuple2 (set Int) (set Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (set Int) (set Int)))))) (sort
  (set1 (set1 (tuple21 (set1 int) (set1 int)))) (t2tb36 x))))

(declare-fun tb2t36 (uni) (set (set (tuple2 (set Int) (set Int)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (set Int) (set Int))))))
  (! (= (tb2t36 (t2tb36 i)) i) :pattern ((t2tb36 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb36 (tb2t36 j)) j) :pattern ((t2tb36 (tb2t36 j))) )))

(declare-fun t2tb37 ((set (tuple2 (set Int) (set Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (set Int) (set Int))))) (sort
  (set1 (tuple21 (set1 int) (set1 int))) (t2tb37 x))))

(declare-fun tb2t37 (uni) (set (tuple2 (set Int) (set Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (set Int) (set Int)))))
  (! (= (tb2t37 (t2tb37 i)) i) :pattern ((t2tb37 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb37 (tb2t37 j)) j) :pattern ((t2tb37 (tb2t37 j))) )))

;; mem_relation
  (assert
  (forall ((f (set (tuple2 (set Int) (set Int)))) (s (set (set Int)))
  (t (set (set Int))))
  (= (mem (set1 (tuple21 (set1 int) (set1 int))) (t2tb37 f)
  (relation (set1 int) (set1 int) (t2tb1 s) (t2tb1 t)))
  (forall ((x (set Int)) (y (set Int)))
  (=> (mem (tuple21 (set1 int) (set1 int))
  (Tuple2 (set1 int) (set1 int) (t2tb3 x) (t2tb3 y)) (t2tb37 f))
  (and (mem3 x s) (mem3 y t)))))))

(declare-fun t2tb38 ((set (set (tuple2 (set Int) Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (set Int) Bool))))) (sort
  (set1 (set1 (tuple21 (set1 int) bool))) (t2tb38 x))))

(declare-fun tb2t38 (uni) (set (set (tuple2 (set Int) Bool))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (set Int) Bool)))))
  (! (= (tb2t38 (t2tb38 i)) i) :pattern ((t2tb38 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb38 (tb2t38 j)) j) :pattern ((t2tb38 (tb2t38 j))) )))

(declare-fun t2tb39 ((set (tuple2 (set Int) Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (set Int) Bool)))) (sort
  (set1 (tuple21 (set1 int) bool)) (t2tb39 x))))

(declare-fun tb2t39 (uni) (set (tuple2 (set Int) Bool)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (set Int) Bool))))
  (! (= (tb2t39 (t2tb39 i)) i) :pattern ((t2tb39 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb39 (tb2t39 j)) j) :pattern ((t2tb39 (tb2t39 j))) )))

(declare-fun t2tb40 ((tuple2 (set Int) Bool)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (set Int) Bool))) (sort (tuple21 (set1 int) bool)
  (t2tb40 x))))

(declare-fun tb2t40 (uni) (tuple2 (set Int) Bool))

;; BridgeL
  (assert
  (forall ((i (tuple2 (set Int) Bool)))
  (! (= (tb2t40 (t2tb40 i)) i) :pattern ((t2tb40 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb40 (tb2t40 j)) j) :pattern ((t2tb40 (tb2t40 j))) )))

;; mem_relation
  (assert
  (forall ((f (set (tuple2 (set Int) Bool))) (s (set (set Int)))
  (t (set Bool)))
  (= (mem (set1 (tuple21 (set1 int) bool)) (t2tb39 f)
  (relation bool (set1 int) (t2tb1 s) (t2tb2 t)))
  (forall ((x (set Int)) (y Bool))
  (=> (mem (tuple21 (set1 int) bool)
  (Tuple2 (set1 int) bool (t2tb3 x) (t2tb12 y)) (t2tb39 f))
  (and (mem3 x s) (mem2 y t)))))))

(declare-fun t2tb41 ((set (set (tuple2 (set Int) Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (set Int) Int))))) (sort
  (set1 (set1 (tuple21 (set1 int) int))) (t2tb41 x))))

(declare-fun tb2t41 (uni) (set (set (tuple2 (set Int) Int))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (set Int) Int)))))
  (! (= (tb2t41 (t2tb41 i)) i) :pattern ((t2tb41 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb41 (tb2t41 j)) j) :pattern ((t2tb41 (tb2t41 j))) )))

(declare-fun t2tb42 ((set (tuple2 (set Int) Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (set Int) Int)))) (sort
  (set1 (tuple21 (set1 int) int)) (t2tb42 x))))

(declare-fun tb2t42 (uni) (set (tuple2 (set Int) Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (set Int) Int))))
  (! (= (tb2t42 (t2tb42 i)) i) :pattern ((t2tb42 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb42 (tb2t42 j)) j) :pattern ((t2tb42 (tb2t42 j))) )))

(declare-fun t2tb43 ((tuple2 (set Int) Int)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (set Int) Int))) (sort (tuple21 (set1 int) int)
  (t2tb43 x))))

(declare-fun tb2t43 (uni) (tuple2 (set Int) Int))

;; BridgeL
  (assert
  (forall ((i (tuple2 (set Int) Int)))
  (! (= (tb2t43 (t2tb43 i)) i) :pattern ((t2tb43 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb43 (tb2t43 j)) j) :pattern ((t2tb43 (tb2t43 j))) )))

;; mem_relation
  (assert
  (forall ((f (set (tuple2 (set Int) Int))) (s (set (set Int)))
  (t (set Int)))
  (= (mem (set1 (tuple21 (set1 int) int)) (t2tb42 f)
  (relation int (set1 int) (t2tb1 s) (t2tb3 t)))
  (forall ((x (set Int)) (y Int))
  (=> (mem (tuple21 (set1 int) int)
  (Tuple2 (set1 int) int (t2tb3 x) (t2tb13 y)) (t2tb42 f))
  (and (mem3 x s) (mem1 y t)))))))

;; mem_relation
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set (set Int))) (t uni))
  (and
  (=> (mem (set1 (tuple21 (set1 int) b)) f
  (relation b (set1 int) (t2tb1 s) t))
  (forall ((x (set Int)) (y uni))
  (=> (mem (tuple21 (set1 int) b) (Tuple2 (set1 int) b (t2tb3 x) y) f)
  (and (mem3 x s) (mem b y t)))))
  (=>
  (forall ((x (set Int)) (y uni))
  (=> (sort b y)
  (=> (mem (tuple21 (set1 int) b) (Tuple2 (set1 int) b (t2tb3 x) y) f)
  (and (mem3 x s) (mem b y t))))) (mem (set1 (tuple21 (set1 int) b)) f
  (relation b (set1 int) (t2tb1 s) t)))))))

(declare-fun t2tb44 ((set (set (tuple2 Bool
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Bool
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))))) (sort
  (set1
  (set1
  (tuple21 bool
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))))
  (t2tb44 x))))

(declare-fun tb2t44 (uni) (set (set (tuple2 Bool
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Bool
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))))) (! (= (tb2t44 (t2tb44 i)) i) :pattern ((t2tb44 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb44 (tb2t44 j)) j) :pattern ((t2tb44 (tb2t44 j))) )))

(declare-fun t2tb45 ((set (tuple2 Bool
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Bool (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))))) (sort
  (set1
  (tuple21 bool
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (t2tb45 x))))

(declare-fun tb2t45 (uni) (set (tuple2 Bool
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Bool (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))))))
  (! (= (tb2t45 (t2tb45 i)) i) :pattern ((t2tb45 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb45 (tb2t45 j)) j) :pattern ((t2tb45 (tb2t45 j))) )))

(declare-fun t2tb46 ((tuple2 Bool (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Bool (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))))) (sort
  (tuple21 bool
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (t2tb46 x))))

(declare-fun tb2t46 (uni) (tuple2 Bool
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))

;; BridgeL
  (assert
  (forall ((i (tuple2 Bool (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))))
  (! (= (tb2t46 (t2tb46 i)) i) :pattern ((t2tb46 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb46 (tb2t46 j)) j) :pattern ((t2tb46 (tb2t46 j))) )))

;; mem_relation
  (assert
  (forall ((f (set (tuple2 Bool (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))))) (s (set Bool))
  (t (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))))
  (= (mem
  (set1
  (tuple21 bool
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (t2tb45 f)
  (relation
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  bool (t2tb2 s) (t2tb t)))
  (forall ((x Bool) (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))))
  (=> (mem
  (tuple21 bool
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2 bool
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb12 x) (t2tb4 y)) (t2tb45 f)) (and (mem2 x s) (mem4 y t)))))))

(declare-fun t2tb47 ((set (set (tuple2 Bool (set Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Bool (set Int)))))) (sort
  (set1 (set1 (tuple21 bool (set1 int)))) (t2tb47 x))))

(declare-fun tb2t47 (uni) (set (set (tuple2 Bool (set Int)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Bool (set Int))))))
  (! (= (tb2t47 (t2tb47 i)) i) :pattern ((t2tb47 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb47 (tb2t47 j)) j) :pattern ((t2tb47 (tb2t47 j))) )))

(declare-fun t2tb48 ((set (tuple2 Bool (set Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Bool (set Int))))) (sort
  (set1 (tuple21 bool (set1 int))) (t2tb48 x))))

(declare-fun tb2t48 (uni) (set (tuple2 Bool (set Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Bool (set Int)))))
  (! (= (tb2t48 (t2tb48 i)) i) :pattern ((t2tb48 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb48 (tb2t48 j)) j) :pattern ((t2tb48 (tb2t48 j))) )))

(declare-fun t2tb49 ((tuple2 Bool (set Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Bool (set Int)))) (sort (tuple21 bool (set1 int))
  (t2tb49 x))))

(declare-fun tb2t49 (uni) (tuple2 Bool (set Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 Bool (set Int))))
  (! (= (tb2t49 (t2tb49 i)) i) :pattern ((t2tb49 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb49 (tb2t49 j)) j) :pattern ((t2tb49 (tb2t49 j))) )))

;; mem_relation
  (assert
  (forall ((f (set (tuple2 Bool (set Int)))) (s (set Bool))
  (t (set (set Int))))
  (= (mem (set1 (tuple21 bool (set1 int))) (t2tb48 f)
  (relation (set1 int) bool (t2tb2 s) (t2tb1 t)))
  (forall ((x Bool) (y (set Int)))
  (=> (mem (tuple21 bool (set1 int))
  (Tuple2 bool (set1 int) (t2tb12 x) (t2tb3 y)) (t2tb48 f))
  (and (mem2 x s) (mem3 y t)))))))

;; mem_relation
  (assert
  (forall ((f (set (tuple2 Bool Bool))) (s (set Bool)) (t (set Bool)))
  (= (mem (set1 (tuple21 bool bool)) (t2tb7 f)
  (relation bool bool (t2tb2 s) (t2tb2 t)))
  (forall ((x Bool) (y Bool))
  (=> (mem (tuple21 bool bool) (Tuple2 bool bool (t2tb12 x) (t2tb12 y))
  (t2tb7 f)) (and (mem2 x s) (mem2 y t)))))))

(declare-fun t2tb50 ((set (set (tuple2 Bool Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Bool Int))))) (sort
  (set1 (set1 (tuple21 bool int))) (t2tb50 x))))

(declare-fun tb2t50 (uni) (set (set (tuple2 Bool Int))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Bool Int)))))
  (! (= (tb2t50 (t2tb50 i)) i) :pattern ((t2tb50 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb50 (tb2t50 j)) j) :pattern ((t2tb50 (tb2t50 j))) )))

(declare-fun t2tb51 ((set (tuple2 Bool Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Bool Int)))) (sort (set1 (tuple21 bool int))
  (t2tb51 x))))

(declare-fun tb2t51 (uni) (set (tuple2 Bool Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Bool Int))))
  (! (= (tb2t51 (t2tb51 i)) i) :pattern ((t2tb51 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb51 (tb2t51 j)) j) :pattern ((t2tb51 (tb2t51 j))) )))

(declare-fun t2tb52 ((tuple2 Bool Int)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Bool Int))) (sort (tuple21 bool int) (t2tb52 x))))

(declare-fun tb2t52 (uni) (tuple2 Bool Int))

;; BridgeL
  (assert
  (forall ((i (tuple2 Bool Int)))
  (! (= (tb2t52 (t2tb52 i)) i) :pattern ((t2tb52 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb52 (tb2t52 j)) j) :pattern ((t2tb52 (tb2t52 j))) )))

;; mem_relation
  (assert
  (forall ((f (set (tuple2 Bool Int))) (s (set Bool)) (t (set Int)))
  (= (mem (set1 (tuple21 bool int)) (t2tb51 f)
  (relation int bool (t2tb2 s) (t2tb3 t)))
  (forall ((x Bool) (y Int))
  (=> (mem (tuple21 bool int) (Tuple2 bool int (t2tb12 x) (t2tb13 y))
  (t2tb51 f)) (and (mem2 x s) (mem1 y t)))))))

;; mem_relation
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set Bool)) (t uni))
  (and
  (=> (mem (set1 (tuple21 bool b)) f (relation b bool (t2tb2 s) t))
  (forall ((x Bool) (y uni))
  (=> (mem (tuple21 bool b) (Tuple2 bool b (t2tb12 x) y) f)
  (and (mem2 x s) (mem b y t)))))
  (=>
  (forall ((x Bool) (y uni))
  (=> (sort b y)
  (=> (mem (tuple21 bool b) (Tuple2 bool b (t2tb12 x) y) f)
  (and (mem2 x s) (mem b y t))))) (mem (set1 (tuple21 bool b)) f
  (relation b bool (t2tb2 s) t)))))))

(declare-fun t2tb53 ((set (set (tuple2 Int
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Int (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))))))) (sort
  (set1
  (set1
  (tuple21 int
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))))
  (t2tb53 x))))

(declare-fun tb2t53 (uni) (set (set (tuple2 Int
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Int (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))))))
  (! (= (tb2t53 (t2tb53 i)) i) :pattern ((t2tb53 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb53 (tb2t53 j)) j) :pattern ((t2tb53 (tb2t53 j))) )))

(declare-fun t2tb54 ((set (tuple2 Int
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))))) (sort
  (set1
  (tuple21 int
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (t2tb54 x))))

(declare-fun tb2t54 (uni) (set (tuple2 Int
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))))))
  (! (= (tb2t54 (t2tb54 i)) i) :pattern ((t2tb54 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb54 (tb2t54 j)) j) :pattern ((t2tb54 (tb2t54 j))) )))

(declare-fun t2tb55 ((tuple2 Int (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Int (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))))) (sort
  (tuple21 int
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (t2tb55 x))))

(declare-fun tb2t55 (uni) (tuple2 Int
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))

;; BridgeL
  (assert
  (forall ((i (tuple2 Int (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))))
  (! (= (tb2t55 (t2tb55 i)) i) :pattern ((t2tb55 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb55 (tb2t55 j)) j) :pattern ((t2tb55 (tb2t55 j))) )))

;; mem_relation
  (assert
  (forall ((f (set (tuple2 Int (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))))) (s (set Int))
  (t (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))))
  (= (mem
  (set1
  (tuple21 int
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (t2tb54 f)
  (relation
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) 
  int (t2tb3 s) (t2tb t)))
  (forall ((x Int) (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))))
  (=> (mem
  (tuple21 int
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2 int
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb13 x) (t2tb4 y)) (t2tb54 f)) (and (mem1 x s) (mem4 y t)))))))

(declare-fun t2tb56 ((set (set (tuple2 Int (set Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Int (set Int)))))) (sort
  (set1 (set1 (tuple21 int (set1 int)))) (t2tb56 x))))

(declare-fun tb2t56 (uni) (set (set (tuple2 Int (set Int)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Int (set Int))))))
  (! (= (tb2t56 (t2tb56 i)) i) :pattern ((t2tb56 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb56 (tb2t56 j)) j) :pattern ((t2tb56 (tb2t56 j))) )))

(declare-fun t2tb57 ((set (tuple2 Int (set Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int (set Int))))) (sort
  (set1 (tuple21 int (set1 int))) (t2tb57 x))))

(declare-fun tb2t57 (uni) (set (tuple2 Int (set Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int (set Int)))))
  (! (= (tb2t57 (t2tb57 i)) i) :pattern ((t2tb57 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb57 (tb2t57 j)) j) :pattern ((t2tb57 (tb2t57 j))) )))

(declare-fun t2tb58 ((tuple2 Int (set Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Int (set Int)))) (sort (tuple21 int (set1 int))
  (t2tb58 x))))

(declare-fun tb2t58 (uni) (tuple2 Int (set Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 Int (set Int))))
  (! (= (tb2t58 (t2tb58 i)) i) :pattern ((t2tb58 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb58 (tb2t58 j)) j) :pattern ((t2tb58 (tb2t58 j))) )))

;; mem_relation
  (assert
  (forall ((f (set (tuple2 Int (set Int)))) (s (set Int))
  (t (set (set Int))))
  (= (mem (set1 (tuple21 int (set1 int))) (t2tb57 f)
  (relation (set1 int) int (t2tb3 s) (t2tb1 t)))
  (forall ((x Int) (y (set Int)))
  (=> (mem (tuple21 int (set1 int))
  (Tuple2 int (set1 int) (t2tb13 x) (t2tb3 y)) (t2tb57 f))
  (and (mem1 x s) (mem3 y t)))))))

(declare-fun t2tb59 ((set (set (tuple2 Int Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Int Bool))))) (sort
  (set1 (set1 (tuple21 int bool))) (t2tb59 x))))

(declare-fun tb2t59 (uni) (set (set (tuple2 Int Bool))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Int Bool)))))
  (! (= (tb2t59 (t2tb59 i)) i) :pattern ((t2tb59 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb59 (tb2t59 j)) j) :pattern ((t2tb59 (tb2t59 j))) )))

(declare-fun t2tb60 ((set (tuple2 Int Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int Bool)))) (sort (set1 (tuple21 int bool))
  (t2tb60 x))))

(declare-fun tb2t60 (uni) (set (tuple2 Int Bool)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int Bool))))
  (! (= (tb2t60 (t2tb60 i)) i) :pattern ((t2tb60 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb60 (tb2t60 j)) j) :pattern ((t2tb60 (tb2t60 j))) )))

(declare-fun t2tb61 ((tuple2 Int Bool)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Int Bool))) (sort (tuple21 int bool) (t2tb61 x))))

(declare-fun tb2t61 (uni) (tuple2 Int Bool))

;; BridgeL
  (assert
  (forall ((i (tuple2 Int Bool)))
  (! (= (tb2t61 (t2tb61 i)) i) :pattern ((t2tb61 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb61 (tb2t61 j)) j) :pattern ((t2tb61 (tb2t61 j))) )))

;; mem_relation
  (assert
  (forall ((f (set (tuple2 Int Bool))) (s (set Int)) (t (set Bool)))
  (= (mem (set1 (tuple21 int bool)) (t2tb60 f)
  (relation bool int (t2tb3 s) (t2tb2 t)))
  (forall ((x Int) (y Bool))
  (=> (mem (tuple21 int bool) (Tuple2 int bool (t2tb13 x) (t2tb12 y))
  (t2tb60 f)) (and (mem1 x s) (mem2 y t)))))))

(declare-fun t2tb62 ((set (set (tuple2 Int Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Int Int))))) (sort
  (set1 (set1 (tuple21 int int))) (t2tb62 x))))

(declare-fun tb2t62 (uni) (set (set (tuple2 Int Int))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Int Int)))))
  (! (= (tb2t62 (t2tb62 i)) i) :pattern ((t2tb62 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb62 (tb2t62 j)) j) :pattern ((t2tb62 (tb2t62 j))) )))

(declare-fun t2tb63 ((set (tuple2 Int Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int Int)))) (sort (set1 (tuple21 int int))
  (t2tb63 x))))

(declare-fun tb2t63 (uni) (set (tuple2 Int Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int Int))))
  (! (= (tb2t63 (t2tb63 i)) i) :pattern ((t2tb63 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb63 (tb2t63 j)) j) :pattern ((t2tb63 (tb2t63 j))) )))

(declare-fun t2tb64 ((tuple2 Int Int)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Int Int))) (sort (tuple21 int int) (t2tb64 x))))

(declare-fun tb2t64 (uni) (tuple2 Int Int))

;; BridgeL
  (assert
  (forall ((i (tuple2 Int Int)))
  (! (= (tb2t64 (t2tb64 i)) i) :pattern ((t2tb64 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb64 (tb2t64 j)) j) :pattern ((t2tb64 (tb2t64 j))) )))

;; mem_relation
  (assert
  (forall ((f (set (tuple2 Int Int))) (s (set Int)) (t (set Int)))
  (= (mem (set1 (tuple21 int int)) (t2tb63 f)
  (relation int int (t2tb3 s) (t2tb3 t)))
  (forall ((x Int) (y Int))
  (=> (mem (tuple21 int int) (Tuple2 int int (t2tb13 x) (t2tb13 y))
  (t2tb63 f)) (and (mem1 x s) (mem1 y t)))))))

;; mem_relation
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set Int)) (t uni))
  (and
  (=> (mem (set1 (tuple21 int b)) f (relation b int (t2tb3 s) t))
  (forall ((x Int) (y uni))
  (=> (mem (tuple21 int b) (Tuple2 int b (t2tb13 x) y) f)
  (and (mem1 x s) (mem b y t)))))
  (=>
  (forall ((x Int) (y uni))
  (=> (sort b y)
  (=> (mem (tuple21 int b) (Tuple2 int b (t2tb13 x) y) f)
  (and (mem1 x s) (mem b y t))))) (mem (set1 (tuple21 int b)) f
  (relation b int (t2tb3 s) t)))))))

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
  (forall ((r uni) (dom uni) (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))))
  (! (and
     (=> (mem4 y
     (tb2t
     (image
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     a r dom)))
     (exists ((x uni))
     (and (sort a x)
     (and (mem a x dom) (mem
     (tuple21 a
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
     (Tuple2 a
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     x (t2tb4 y)) r)))))
     (=>
     (exists ((x uni))
     (and (mem a x dom) (mem
     (tuple21 a
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
     (Tuple2 a
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     x (t2tb4 y)) r))) (mem4 y
     (tb2t
     (image
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     a r dom))))) :pattern ((mem4
  y
  (tb2t
  (image
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) a r
  dom)))) ))))

;; mem_image
  (assert
  (forall ((a ty))
  (forall ((r uni) (dom uni) (y (set Int)))
  (! (and
     (=> (mem3 y (tb2t1 (image (set1 int) a r dom)))
     (exists ((x uni))
     (and (sort a x)
     (and (mem a x dom) (mem (tuple21 a (set1 int))
     (Tuple2 a (set1 int) x (t2tb3 y)) r)))))
     (=>
     (exists ((x uni))
     (and (mem a x dom) (mem (tuple21 a (set1 int))
     (Tuple2 a (set1 int) x (t2tb3 y)) r))) (mem3 y
     (tb2t1 (image (set1 int) a r dom))))) :pattern ((mem3
  y (tb2t1 (image (set1 int) a r dom)))) ))))

;; mem_image
  (assert
  (forall ((a ty))
  (forall ((r uni) (dom uni) (y Bool))
  (! (and
     (=> (mem2 y (tb2t2 (image bool a r dom)))
     (exists ((x uni))
     (and (sort a x)
     (and (mem a x dom) (mem (tuple21 a bool) (Tuple2 a bool x (t2tb12 y))
     r)))))
     (=>
     (exists ((x uni))
     (and (mem a x dom) (mem (tuple21 a bool) (Tuple2 a bool x (t2tb12 y))
     r))) (mem2 y (tb2t2 (image bool a r dom))))) :pattern ((mem2
  y (tb2t2 (image bool a r dom)))) ))))

;; mem_image
  (assert
  (forall ((a ty))
  (forall ((r uni) (dom uni) (y Int))
  (! (and
     (=> (mem1 y (tb2t3 (image int a r dom)))
     (exists ((x uni))
     (and (sort a x)
     (and (mem a x dom) (mem (tuple21 a int) (Tuple2 a int x (t2tb13 y)) r)))))
     (=>
     (exists ((x uni))
     (and (mem a x dom) (mem (tuple21 a int) (Tuple2 a int x (t2tb13 y)) r)))
     (mem1 y (tb2t3 (image int a r dom))))) :pattern ((mem1
  y (tb2t3 (image int a r dom)))) ))))

;; mem_image
  (assert
  (forall ((r (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))))
  (dom (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))))
  (! (= (mem4 y
     (tb2t
     (image
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb21 r) (t2tb dom))))
     (exists ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
     (set Int)))))
     (and (mem4 x dom) (mem
     (tuple21
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
     (Tuple2
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb4 x) (t2tb4 y)) (t2tb21 r))))) :pattern ((mem4
  y
  (tb2t
  (image
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb21 r) (t2tb dom))))) )))

;; mem_image
  (assert
  (forall ((r (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))) (set Int))))
  (dom (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (y (set Int)))
  (! (= (mem3 y
     (tb2t1
     (image (set1 int)
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb23 r) (t2tb dom))))
     (exists ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
     (set Int)))))
     (and (mem4 x dom) (mem
     (tuple21
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (set1 int))
     (Tuple2
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (set1 int) (t2tb4 x) (t2tb3 y)) (t2tb23 r))))) :pattern ((mem3
  y
  (tb2t1
  (image (set1 int)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb23 r) (t2tb dom))))) )))

;; mem_image
  (assert
  (forall ((r (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))) Bool)))
  (dom (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (y Bool))
  (! (= (mem2 y
     (tb2t2
     (image bool
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb27 r) (t2tb dom))))
     (exists ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
     (set Int)))))
     (and (mem4 x dom) (mem
     (tuple21
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     bool)
     (Tuple2
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     bool (t2tb4 x) (t2tb12 y)) (t2tb27 r))))) :pattern ((mem2
  y
  (tb2t2
  (image bool
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb27 r) (t2tb dom))))) )))

;; mem_image
  (assert
  (forall ((r (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))) Int)))
  (dom (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (y Int))
  (! (= (mem1 y
     (tb2t3
     (image int
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb30 r) (t2tb dom))))
     (exists ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
     (set Int)))))
     (and (mem4 x dom) (mem
     (tuple21
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     int)
     (Tuple2
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     int (t2tb4 x) (t2tb13 y)) (t2tb30 r))))) :pattern ((mem1
  y
  (tb2t3
  (image int
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb30 r) (t2tb dom))))) )))

;; mem_image
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))) (y uni))
  (! (= (mem b y
     (image b
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     r (t2tb dom)))
     (exists ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
     (set Int)))))
     (and (mem4 x dom) (mem
     (tuple21
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     b)
     (Tuple2
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     b (t2tb4 x) y) r)))) :pattern ((mem
  b y
  (image b
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) r
  (t2tb dom)))) ))))

;; mem_image
  (assert
  (forall ((r (set (tuple2 (set Int)
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))))
  (dom (set (set Int))) (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))))
  (! (= (mem4 y
     (tb2t
     (image
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (set1 int) (t2tb33 r) (t2tb1 dom))))
     (exists ((x (set Int)))
     (and (mem3 x dom) (mem
     (tuple21 (set1 int)
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
     (Tuple2 (set1 int)
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb3 x) (t2tb4 y)) (t2tb33 r))))) :pattern ((mem4
  y
  (tb2t
  (image
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1 int) (t2tb33 r) (t2tb1 dom))))) )))

;; mem_image
  (assert
  (forall ((r (set (tuple2 (set Int) (set Int)))) (dom (set (set Int)))
  (y (set Int)))
  (! (= (mem3 y (tb2t1 (image (set1 int) (set1 int) (t2tb37 r) (t2tb1 dom))))
     (exists ((x (set Int)))
     (and (mem3 x dom) (mem (tuple21 (set1 int) (set1 int))
     (Tuple2 (set1 int) (set1 int) (t2tb3 x) (t2tb3 y)) (t2tb37 r))))) :pattern ((mem3
  y (tb2t1 (image (set1 int) (set1 int) (t2tb37 r) (t2tb1 dom))))) )))

;; mem_image
  (assert
  (forall ((r (set (tuple2 (set Int) Bool))) (dom (set (set Int))) (y Bool))
  (! (= (mem2 y (tb2t2 (image bool (set1 int) (t2tb39 r) (t2tb1 dom))))
     (exists ((x (set Int)))
     (and (mem3 x dom) (mem (tuple21 (set1 int) bool)
     (Tuple2 (set1 int) bool (t2tb3 x) (t2tb12 y)) (t2tb39 r))))) :pattern ((mem2
  y (tb2t2 (image bool (set1 int) (t2tb39 r) (t2tb1 dom))))) )))

;; mem_image
  (assert
  (forall ((r (set (tuple2 (set Int) Int))) (dom (set (set Int))) (y Int))
  (! (= (mem1 y (tb2t3 (image int (set1 int) (t2tb42 r) (t2tb1 dom))))
     (exists ((x (set Int)))
     (and (mem3 x dom) (mem (tuple21 (set1 int) int)
     (Tuple2 (set1 int) int (t2tb3 x) (t2tb13 y)) (t2tb42 r))))) :pattern ((mem1
  y (tb2t3 (image int (set1 int) (t2tb42 r) (t2tb1 dom))))) )))

;; mem_image
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom (set (set Int))) (y uni))
  (! (= (mem b y (image b (set1 int) r (t2tb1 dom)))
     (exists ((x (set Int)))
     (and (mem3 x dom) (mem (tuple21 (set1 int) b)
     (Tuple2 (set1 int) b (t2tb3 x) y) r)))) :pattern ((mem
  b y (image b (set1 int) r (t2tb1 dom)))) ))))

;; mem_image
  (assert
  (forall ((r (set (tuple2 Bool (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))))) (dom (set Bool))
  (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))
  (! (= (mem4 y
     (tb2t
     (image
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     bool (t2tb45 r) (t2tb2 dom))))
     (exists ((x Bool))
     (and (mem2 x dom) (mem
     (tuple21 bool
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
     (Tuple2 bool
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb12 x) (t2tb4 y)) (t2tb45 r))))) :pattern ((mem4
  y
  (tb2t
  (image
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  bool (t2tb45 r) (t2tb2 dom))))) )))

;; mem_image
  (assert
  (forall ((r (set (tuple2 Bool (set Int)))) (dom (set Bool)) (y (set Int)))
  (! (= (mem3 y (tb2t1 (image (set1 int) bool (t2tb48 r) (t2tb2 dom))))
     (exists ((x Bool))
     (and (mem2 x dom) (mem (tuple21 bool (set1 int))
     (Tuple2 bool (set1 int) (t2tb12 x) (t2tb3 y)) (t2tb48 r))))) :pattern ((mem3
  y (tb2t1 (image (set1 int) bool (t2tb48 r) (t2tb2 dom))))) )))

;; mem_image
  (assert
  (forall ((r (set (tuple2 Bool Bool))) (dom (set Bool)) (y Bool))
  (! (= (mem2 y (tb2t2 (image bool bool (t2tb7 r) (t2tb2 dom))))
     (exists ((x Bool))
     (and (mem2 x dom) (mem (tuple21 bool bool)
     (Tuple2 bool bool (t2tb12 x) (t2tb12 y)) (t2tb7 r))))) :pattern ((mem2
  y (tb2t2 (image bool bool (t2tb7 r) (t2tb2 dom))))) )))

;; mem_image
  (assert
  (forall ((r (set (tuple2 Bool Int))) (dom (set Bool)) (y Int))
  (! (= (mem1 y (tb2t3 (image int bool (t2tb51 r) (t2tb2 dom))))
     (exists ((x Bool))
     (and (mem2 x dom) (mem (tuple21 bool int)
     (Tuple2 bool int (t2tb12 x) (t2tb13 y)) (t2tb51 r))))) :pattern ((mem1
  y (tb2t3 (image int bool (t2tb51 r) (t2tb2 dom))))) )))

;; mem_image
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom (set Bool)) (y uni))
  (! (= (mem b y (image b bool r (t2tb2 dom)))
     (exists ((x Bool))
     (and (mem2 x dom) (mem (tuple21 bool b) (Tuple2 bool b (t2tb12 x) y) r)))) :pattern ((mem
  b y (image b bool r (t2tb2 dom)))) ))))

;; mem_image
  (assert
  (forall ((r (set (tuple2 Int (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))))) (dom (set Int))
  (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))
  (! (= (mem4 y
     (tb2t
     (image
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     int (t2tb54 r) (t2tb3 dom))))
     (exists ((x Int))
     (and (mem1 x dom) (mem
     (tuple21 int
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
     (Tuple2 int
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb13 x) (t2tb4 y)) (t2tb54 r))))) :pattern ((mem4
  y
  (tb2t
  (image
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) 
  int (t2tb54 r) (t2tb3 dom))))) )))

;; mem_image
  (assert
  (forall ((r (set (tuple2 Int (set Int)))) (dom (set Int)) (y (set Int)))
  (! (= (mem3 y (tb2t1 (image (set1 int) int (t2tb57 r) (t2tb3 dom))))
     (exists ((x Int))
     (and (mem1 x dom) (mem (tuple21 int (set1 int))
     (Tuple2 int (set1 int) (t2tb13 x) (t2tb3 y)) (t2tb57 r))))) :pattern ((mem3
  y (tb2t1 (image (set1 int) int (t2tb57 r) (t2tb3 dom))))) )))

;; mem_image
  (assert
  (forall ((r (set (tuple2 Int Bool))) (dom (set Int)) (y Bool))
  (! (= (mem2 y (tb2t2 (image bool int (t2tb60 r) (t2tb3 dom))))
     (exists ((x Int))
     (and (mem1 x dom) (mem (tuple21 int bool)
     (Tuple2 int bool (t2tb13 x) (t2tb12 y)) (t2tb60 r))))) :pattern ((mem2
  y (tb2t2 (image bool int (t2tb60 r) (t2tb3 dom))))) )))

;; mem_image
  (assert
  (forall ((r (set (tuple2 Int Int))) (dom (set Int)) (y Int))
  (! (= (mem1 y (tb2t3 (image int int (t2tb63 r) (t2tb3 dom))))
     (exists ((x Int))
     (and (mem1 x dom) (mem (tuple21 int int)
     (Tuple2 int int (t2tb13 x) (t2tb13 y)) (t2tb63 r))))) :pattern ((mem1
  y (tb2t3 (image int int (t2tb63 r) (t2tb3 dom))))) )))

;; mem_image
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom (set Int)) (y uni))
  (! (= (mem b y (image b int r (t2tb3 dom)))
     (exists ((x Int))
     (and (mem1 x dom) (mem (tuple21 int b) (Tuple2 int b (t2tb13 x) y) r)))) :pattern ((mem
  b y (image b int r (t2tb3 dom)))) ))))

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
  (forall ((r uni) (dom (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))) (x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))))
  (= (image b
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     r (t2tb (add4 x dom))) (union b
                            (image b
                            (set1
                            (tuple21
                            (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
                            (set1 int))) r (t2tb (add4 x empty8)))
                            (image b
                            (set1
                            (tuple21
                            (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
                            (set1 int))) r (t2tb dom)))))))

;; image_add
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))) (x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))
  (= (image b
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)) r
     (add
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
     (t2tb8 x) (t2tb4 dom))) (union b
                             (image b
                             (tuple21
                             (tuple21 (tuple21 (tuple21 bool bool) bool)
                             bool) (set1 int)) r
                             (add
                             (tuple21
                             (tuple21 (tuple21 (tuple21 bool bool) bool)
                             bool) (set1 int)) (t2tb8 x) (t2tb4 empty4)))
                             (image b
                             (tuple21
                             (tuple21 (tuple21 (tuple21 bool bool) bool)
                             bool) (set1 int)) r (t2tb4 dom)))))))

;; image_add
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (= (image b (tuple21 (tuple21 (tuple21 bool bool) bool) bool) r
     (add (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
     (t2tb5 dom))) (union b
                   (image b (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
                   r
                   (add (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
                   (t2tb9 x) (t2tb5 empty5)))
                   (image b (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
                   r (t2tb5 dom)))))))

;; image_add
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom (set (tuple2 (tuple2 Bool Bool) Bool)))
  (x (tuple2 (tuple2 Bool Bool) Bool)))
  (= (image b (tuple21 (tuple21 bool bool) bool) r
     (add (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb6 dom))) 
  (union b
  (image b (tuple21 (tuple21 bool bool) bool) r
  (add (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb6 empty6)))
  (image b (tuple21 (tuple21 bool bool) bool) r (t2tb6 dom)))))))

;; image_add
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom (set (set Int))) (x (set Int)))
  (= (image b (set1 int) r (t2tb1 (add3 x dom))) (union b
                                                 (image b (set1 int) r
                                                 (t2tb1 (add3 x empty3)))
                                                 (image b (set1 int) r
                                                 (t2tb1 dom)))))))

;; image_add
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom (set (tuple2 Bool Bool))) (x (tuple2 Bool Bool)))
  (= (image b (tuple21 bool bool) r
     (add (tuple21 bool bool) (t2tb11 x) (t2tb7 dom))) (union b
                                                       (image b
                                                       (tuple21 bool bool) r
                                                       (add
                                                       (tuple21 bool bool)
                                                       (t2tb11 x)
                                                       (t2tb7 empty7)))
                                                       (image b
                                                       (tuple21 bool bool) r
                                                       (t2tb7 dom)))))))

;; image_add
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom (set Bool)) (x Bool))
  (= (image b bool r (t2tb2 (add1 x dom))) (union b
                                           (image b bool r
                                           (t2tb2 (add1 x empty1)))
                                           (image b bool r (t2tb2 dom)))))))

;; image_add
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom (set Int)) (x Int))
  (= (image b int r (t2tb3 (add2 x dom))) (union b
                                          (image b int r
                                          (t2tb3 (add2 x empty2)))
                                          (image b int r (t2tb3 dom)))))))

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

(declare-fun infix_plmngt1 ((set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool)) (set (set Int))) (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))))

;; mem_function
  (assert
  (forall ((a ty))
  (forall ((f uni) (s uni) (t (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))))
  (and
  (=> (mem
  (set1
  (tuple21 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))) f
  (infix_plmngt
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) a s
  (t2tb t)))
  (and
  (forall ((x uni) (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))))
  (=> (mem
  (tuple21 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) x
  (t2tb4 y)) f) (and (mem a x s) (mem4 y t))))
  (forall ((x uni) (y1 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))) (y2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))))
  (=>
  (and (mem
  (tuple21 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) x
  (t2tb4 y1)) f) (mem
  (tuple21 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) x
  (t2tb4 y2)) f)) (= y1 y2)))))
  (=>
  (and
  (forall ((x uni) (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))))
  (=> (sort a x)
  (=> (mem
  (tuple21 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) x
  (t2tb4 y)) f) (and (mem a x s) (mem4 y t)))))
  (forall ((x uni) (y1 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))) (y2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))))
  (=> (sort a x)
  (=>
  (and (mem
  (tuple21 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) x
  (t2tb4 y1)) f) (mem
  (tuple21 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) x
  (t2tb4 y2)) f)) (= y1 y2))))) (mem
  (set1
  (tuple21 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))) f
  (infix_plmngt
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) a s
  (t2tb t))))))))

;; mem_function
  (assert
  (forall ((a ty))
  (forall ((f uni) (s uni) (t (set (set Int))))
  (and
  (=> (mem (set1 (tuple21 a (set1 int))) f
  (infix_plmngt (set1 int) a s (t2tb1 t)))
  (and
  (forall ((x uni) (y (set Int)))
  (=> (mem (tuple21 a (set1 int)) (Tuple2 a (set1 int) x (t2tb3 y)) f)
  (and (mem a x s) (mem3 y t))))
  (forall ((x uni) (y1 (set Int)) (y2 (set Int)))
  (=>
  (and (mem (tuple21 a (set1 int)) (Tuple2 a (set1 int) x (t2tb3 y1)) f) (mem
  (tuple21 a (set1 int)) (Tuple2 a (set1 int) x (t2tb3 y2)) f)) (= y1 y2)))))
  (=>
  (and
  (forall ((x uni) (y (set Int)))
  (=> (sort a x)
  (=> (mem (tuple21 a (set1 int)) (Tuple2 a (set1 int) x (t2tb3 y)) f)
  (and (mem a x s) (mem3 y t)))))
  (forall ((x uni) (y1 (set Int)) (y2 (set Int)))
  (=> (sort a x)
  (=>
  (and (mem (tuple21 a (set1 int)) (Tuple2 a (set1 int) x (t2tb3 y1)) f) (mem
  (tuple21 a (set1 int)) (Tuple2 a (set1 int) x (t2tb3 y2)) f)) (= y1 y2)))))
  (mem (set1 (tuple21 a (set1 int))) f
  (infix_plmngt (set1 int) a s (t2tb1 t))))))))

;; mem_function
  (assert
  (forall ((a ty))
  (forall ((f uni) (s uni) (t (set Bool)))
  (and
  (=> (mem (set1 (tuple21 a bool)) f (infix_plmngt bool a s (t2tb2 t)))
  (and
  (forall ((x uni) (y Bool))
  (=> (mem (tuple21 a bool) (Tuple2 a bool x (t2tb12 y)) f)
  (and (mem a x s) (mem2 y t))))
  (forall ((x uni) (y1 Bool) (y2 Bool))
  (=>
  (and (mem (tuple21 a bool) (Tuple2 a bool x (t2tb12 y1)) f) (mem
  (tuple21 a bool) (Tuple2 a bool x (t2tb12 y2)) f)) (= y1 y2)))))
  (=>
  (and
  (forall ((x uni) (y Bool))
  (=> (sort a x)
  (=> (mem (tuple21 a bool) (Tuple2 a bool x (t2tb12 y)) f)
  (and (mem a x s) (mem2 y t)))))
  (forall ((x uni) (y1 Bool) (y2 Bool))
  (=> (sort a x)
  (=>
  (and (mem (tuple21 a bool) (Tuple2 a bool x (t2tb12 y1)) f) (mem
  (tuple21 a bool) (Tuple2 a bool x (t2tb12 y2)) f)) (= y1 y2))))) (mem
  (set1 (tuple21 a bool)) f (infix_plmngt bool a s (t2tb2 t))))))))

;; mem_function
  (assert
  (forall ((a ty))
  (forall ((f uni) (s uni) (t (set Int)))
  (and
  (=> (mem (set1 (tuple21 a int)) f (infix_plmngt int a s (t2tb3 t)))
  (and
  (forall ((x uni) (y Int))
  (=> (mem (tuple21 a int) (Tuple2 a int x (t2tb13 y)) f)
  (and (mem a x s) (mem1 y t))))
  (forall ((x uni) (y1 Int) (y2 Int))
  (=>
  (and (mem (tuple21 a int) (Tuple2 a int x (t2tb13 y1)) f) (mem
  (tuple21 a int) (Tuple2 a int x (t2tb13 y2)) f)) (= y1 y2)))))
  (=>
  (and
  (forall ((x uni) (y Int))
  (=> (sort a x)
  (=> (mem (tuple21 a int) (Tuple2 a int x (t2tb13 y)) f)
  (and (mem a x s) (mem1 y t)))))
  (forall ((x uni) (y1 Int) (y2 Int))
  (=> (sort a x)
  (=>
  (and (mem (tuple21 a int) (Tuple2 a int x (t2tb13 y1)) f) (mem
  (tuple21 a int) (Tuple2 a int x (t2tb13 y2)) f)) (= y1 y2))))) (mem
  (set1 (tuple21 a int)) f (infix_plmngt int a s (t2tb3 t))))))))

;; mem_function
  (assert
  (forall ((f (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))))
  (s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (t (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))))
  (= (mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (t2tb21 f)
  (infix_plmngt
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s) (t2tb t)))
  (and
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))
  (=> (mem
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb4 x) (t2tb4 y)) (t2tb21 f)) (and (mem4 x s) (mem4 y t))))
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (y1 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))) (y2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))))
  (=>
  (and (mem
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb4 x) (t2tb4 y1)) (t2tb21 f)) (mem
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb4 x) (t2tb4 y2)) (t2tb21 f))) (= y1 y2)))))))

;; mem_function
  (assert
  (forall ((f (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))) (set Int))))
  (s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (t (set (set Int))))
  (= (mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1 int))) (t2tb23 f)
  (infix_plmngt (set1 int)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s) (t2tb1 t)))
  (and
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (y (set Int)))
  (=> (mem
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1 int))
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1 int) (t2tb4 x) (t2tb3 y)) (t2tb23 f)) (and (mem4 x s) (mem3 y t))))
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (y1 (set Int)) (y2 (set Int)))
  (=>
  (and (mem
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1 int))
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1 int) (t2tb4 x) (t2tb3 y1)) (t2tb23 f)) (mem
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1 int))
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1 int) (t2tb4 x) (t2tb3 y2)) (t2tb23 f))) (= y1 y2)))))))

;; mem_function
  (assert
  (forall ((f (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))) Bool)))
  (s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (t (set Bool)))
  (= (mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  bool)) (t2tb27 f)
  (infix_plmngt bool
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s) (t2tb2 t)))
  (and
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (y Bool))
  (=> (mem
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  bool)
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  bool (t2tb4 x) (t2tb12 y)) (t2tb27 f)) (and (mem4 x s) (mem2 y t))))
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (y1 Bool) (y2 Bool))
  (=>
  (and (mem
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  bool)
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  bool (t2tb4 x) (t2tb12 y1)) (t2tb27 f)) (mem
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  bool)
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  bool (t2tb4 x) (t2tb12 y2)) (t2tb27 f))) (= y1 y2)))))))

;; mem_function
  (assert
  (forall ((f (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))) Int)))
  (s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (t (set Int)))
  (= (mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  int)) (t2tb30 f)
  (infix_plmngt int
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s) (t2tb3 t)))
  (and
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (y Int))
  (=> (mem
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  int)
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) 
  int (t2tb4 x) (t2tb13 y)) (t2tb30 f)) (and (mem4 x s) (mem1 y t))))
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (y1 Int) (y2 Int))
  (=>
  (and (mem
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  int)
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) 
  int (t2tb4 x) (t2tb13 y1)) (t2tb30 f)) (mem
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  int)
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) 
  int (t2tb4 x) (t2tb13 y2)) (t2tb30 f))) (= y1 y2)))))))

;; mem_function
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))) (t uni))
  (and
  (=> (mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b))
  f
  (infix_plmngt b
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s) t))
  (and
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (y uni))
  (=> (mem
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b)
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b
  (t2tb4 x) y) f) (and (mem4 x s) (mem b y t))))
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (y1 uni) (y2 uni))
  (=> (sort b y1)
  (=> (sort b y2)
  (=>
  (and (mem
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b)
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b
  (t2tb4 x) y1) f) (mem
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b)
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b
  (t2tb4 x) y2) f)) (= y1 y2)))))))
  (=>
  (and
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (y uni))
  (=> (sort b y)
  (=> (mem
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b)
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b
  (t2tb4 x) y) f) (and (mem4 x s) (mem b y t)))))
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (y1 uni) (y2 uni))
  (=> (sort b y1)
  (=> (sort b y2)
  (=>
  (and (mem
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b)
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b
  (t2tb4 x) y1) f) (mem
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b)
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b
  (t2tb4 x) y2) f)) (= y1 y2)))))) (mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b))
  f
  (infix_plmngt b
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s) t)))))))

;; mem_function
  (assert
  (forall ((f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (t (set (set Int))))
  (= (mem4 f (infix_plmngt1 s t))
  (and
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)) (y (set Int)))
  (=> (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb9 x) (t2tb3 y)) (t2tb4 f))
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
  (t2tb5 s)) (mem3 y t))))
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)) (y1 (set Int))
  (y2 (set Int)))
  (=>
  (and (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb9 x) (t2tb3 y1)) (t2tb4 f)) (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb9 x) (t2tb3 y2)) (t2tb4 f))) (= y1 y2)))))))

;; mem_function
  (assert
  (forall ((f (set (tuple2 (set Int)
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))))
  (s (set (set Int))) (t (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))))
  (= (mem
  (set1
  (tuple21 (set1 int)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (t2tb33 f)
  (infix_plmngt
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1 int) (t2tb1 s) (t2tb t)))
  (and
  (forall ((x (set Int)) (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))))
  (=> (mem
  (tuple21 (set1 int)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2 (set1 int)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb3 x) (t2tb4 y)) (t2tb33 f)) (and (mem3 x s) (mem4 y t))))
  (forall ((x (set Int)) (y1 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))) (y2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))))
  (=>
  (and (mem
  (tuple21 (set1 int)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2 (set1 int)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb3 x) (t2tb4 y1)) (t2tb33 f)) (mem
  (tuple21 (set1 int)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2 (set1 int)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb3 x) (t2tb4 y2)) (t2tb33 f))) (= y1 y2)))))))

;; mem_function
  (assert
  (forall ((f (set (tuple2 (set Int) (set Int)))) (s (set (set Int)))
  (t (set (set Int))))
  (= (mem (set1 (tuple21 (set1 int) (set1 int))) (t2tb37 f)
  (infix_plmngt (set1 int) (set1 int) (t2tb1 s) (t2tb1 t)))
  (and
  (forall ((x (set Int)) (y (set Int)))
  (=> (mem (tuple21 (set1 int) (set1 int))
  (Tuple2 (set1 int) (set1 int) (t2tb3 x) (t2tb3 y)) (t2tb37 f))
  (and (mem3 x s) (mem3 y t))))
  (forall ((x (set Int)) (y1 (set Int)) (y2 (set Int)))
  (=>
  (and (mem (tuple21 (set1 int) (set1 int))
  (Tuple2 (set1 int) (set1 int) (t2tb3 x) (t2tb3 y1)) (t2tb37 f)) (mem
  (tuple21 (set1 int) (set1 int))
  (Tuple2 (set1 int) (set1 int) (t2tb3 x) (t2tb3 y2)) (t2tb37 f))) (= y1 y2)))))))

;; mem_function
  (assert
  (forall ((f (set (tuple2 (set Int) Bool))) (s (set (set Int)))
  (t (set Bool)))
  (= (mem (set1 (tuple21 (set1 int) bool)) (t2tb39 f)
  (infix_plmngt bool (set1 int) (t2tb1 s) (t2tb2 t)))
  (and
  (forall ((x (set Int)) (y Bool))
  (=> (mem (tuple21 (set1 int) bool)
  (Tuple2 (set1 int) bool (t2tb3 x) (t2tb12 y)) (t2tb39 f))
  (and (mem3 x s) (mem2 y t))))
  (forall ((x (set Int)) (y1 Bool) (y2 Bool))
  (=>
  (and (mem (tuple21 (set1 int) bool)
  (Tuple2 (set1 int) bool (t2tb3 x) (t2tb12 y1)) (t2tb39 f)) (mem
  (tuple21 (set1 int) bool) (Tuple2 (set1 int) bool (t2tb3 x) (t2tb12 y2))
  (t2tb39 f))) (= y1 y2)))))))

;; mem_function
  (assert
  (forall ((f (set (tuple2 (set Int) Int))) (s (set (set Int)))
  (t (set Int)))
  (= (mem (set1 (tuple21 (set1 int) int)) (t2tb42 f)
  (infix_plmngt int (set1 int) (t2tb1 s) (t2tb3 t)))
  (and
  (forall ((x (set Int)) (y Int))
  (=> (mem (tuple21 (set1 int) int)
  (Tuple2 (set1 int) int (t2tb3 x) (t2tb13 y)) (t2tb42 f))
  (and (mem3 x s) (mem1 y t))))
  (forall ((x (set Int)) (y1 Int) (y2 Int))
  (=>
  (and (mem (tuple21 (set1 int) int)
  (Tuple2 (set1 int) int (t2tb3 x) (t2tb13 y1)) (t2tb42 f)) (mem
  (tuple21 (set1 int) int) (Tuple2 (set1 int) int (t2tb3 x) (t2tb13 y2))
  (t2tb42 f))) (= y1 y2)))))))

;; mem_function
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set (set Int))) (t uni))
  (and
  (=> (mem (set1 (tuple21 (set1 int) b)) f
  (infix_plmngt b (set1 int) (t2tb1 s) t))
  (and
  (forall ((x (set Int)) (y uni))
  (=> (mem (tuple21 (set1 int) b) (Tuple2 (set1 int) b (t2tb3 x) y) f)
  (and (mem3 x s) (mem b y t))))
  (forall ((x (set Int)) (y1 uni) (y2 uni))
  (=> (sort b y1)
  (=> (sort b y2)
  (=>
  (and (mem (tuple21 (set1 int) b) (Tuple2 (set1 int) b (t2tb3 x) y1) f) (mem
  (tuple21 (set1 int) b) (Tuple2 (set1 int) b (t2tb3 x) y2) f)) (= y1 y2)))))))
  (=>
  (and
  (forall ((x (set Int)) (y uni))
  (=> (sort b y)
  (=> (mem (tuple21 (set1 int) b) (Tuple2 (set1 int) b (t2tb3 x) y) f)
  (and (mem3 x s) (mem b y t)))))
  (forall ((x (set Int)) (y1 uni) (y2 uni))
  (=> (sort b y1)
  (=> (sort b y2)
  (=>
  (and (mem (tuple21 (set1 int) b) (Tuple2 (set1 int) b (t2tb3 x) y1) f) (mem
  (tuple21 (set1 int) b) (Tuple2 (set1 int) b (t2tb3 x) y2) f)) (= y1 y2))))))
  (mem (set1 (tuple21 (set1 int) b)) f
  (infix_plmngt b (set1 int) (t2tb1 s) t)))))))

;; mem_function
  (assert
  (forall ((f (set (tuple2 Bool (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))))) (s (set Bool))
  (t (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))))
  (= (mem
  (set1
  (tuple21 bool
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (t2tb45 f)
  (infix_plmngt
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  bool (t2tb2 s) (t2tb t)))
  (and
  (forall ((x Bool) (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))))
  (=> (mem
  (tuple21 bool
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2 bool
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb12 x) (t2tb4 y)) (t2tb45 f)) (and (mem2 x s) (mem4 y t))))
  (forall ((x Bool) (y1 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))) (y2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))))
  (=>
  (and (mem
  (tuple21 bool
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2 bool
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb12 x) (t2tb4 y1)) (t2tb45 f)) (mem
  (tuple21 bool
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2 bool
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb12 x) (t2tb4 y2)) (t2tb45 f))) (= y1 y2)))))))

;; mem_function
  (assert
  (forall ((f (set (tuple2 Bool (set Int)))) (s (set Bool))
  (t (set (set Int))))
  (= (mem (set1 (tuple21 bool (set1 int))) (t2tb48 f)
  (infix_plmngt (set1 int) bool (t2tb2 s) (t2tb1 t)))
  (and
  (forall ((x Bool) (y (set Int)))
  (=> (mem (tuple21 bool (set1 int))
  (Tuple2 bool (set1 int) (t2tb12 x) (t2tb3 y)) (t2tb48 f))
  (and (mem2 x s) (mem3 y t))))
  (forall ((x Bool) (y1 (set Int)) (y2 (set Int)))
  (=>
  (and (mem (tuple21 bool (set1 int))
  (Tuple2 bool (set1 int) (t2tb12 x) (t2tb3 y1)) (t2tb48 f)) (mem
  (tuple21 bool (set1 int)) (Tuple2 bool (set1 int) (t2tb12 x) (t2tb3 y2))
  (t2tb48 f))) (= y1 y2)))))))

;; mem_function
  (assert
  (forall ((f (set (tuple2 Bool Bool))) (s (set Bool)) (t (set Bool)))
  (= (mem (set1 (tuple21 bool bool)) (t2tb7 f)
  (infix_plmngt bool bool (t2tb2 s) (t2tb2 t)))
  (and
  (forall ((x Bool) (y Bool))
  (=> (mem (tuple21 bool bool) (Tuple2 bool bool (t2tb12 x) (t2tb12 y))
  (t2tb7 f)) (and (mem2 x s) (mem2 y t))))
  (forall ((x Bool) (y1 Bool) (y2 Bool))
  (=>
  (and (mem (tuple21 bool bool) (Tuple2 bool bool (t2tb12 x) (t2tb12 y1))
  (t2tb7 f)) (mem (tuple21 bool bool)
  (Tuple2 bool bool (t2tb12 x) (t2tb12 y2)) (t2tb7 f))) (= y1 y2)))))))

;; mem_function
  (assert
  (forall ((f (set (tuple2 Bool Int))) (s (set Bool)) (t (set Int)))
  (= (mem (set1 (tuple21 bool int)) (t2tb51 f)
  (infix_plmngt int bool (t2tb2 s) (t2tb3 t)))
  (and
  (forall ((x Bool) (y Int))
  (=> (mem (tuple21 bool int) (Tuple2 bool int (t2tb12 x) (t2tb13 y))
  (t2tb51 f)) (and (mem2 x s) (mem1 y t))))
  (forall ((x Bool) (y1 Int) (y2 Int))
  (=>
  (and (mem (tuple21 bool int) (Tuple2 bool int (t2tb12 x) (t2tb13 y1))
  (t2tb51 f)) (mem (tuple21 bool int)
  (Tuple2 bool int (t2tb12 x) (t2tb13 y2)) (t2tb51 f))) (= y1 y2)))))))

;; mem_function
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set Bool)) (t uni))
  (and
  (=> (mem (set1 (tuple21 bool b)) f (infix_plmngt b bool (t2tb2 s) t))
  (and
  (forall ((x Bool) (y uni))
  (=> (mem (tuple21 bool b) (Tuple2 bool b (t2tb12 x) y) f)
  (and (mem2 x s) (mem b y t))))
  (forall ((x Bool) (y1 uni) (y2 uni))
  (=> (sort b y1)
  (=> (sort b y2)
  (=>
  (and (mem (tuple21 bool b) (Tuple2 bool b (t2tb12 x) y1) f) (mem
  (tuple21 bool b) (Tuple2 bool b (t2tb12 x) y2) f)) (= y1 y2)))))))
  (=>
  (and
  (forall ((x Bool) (y uni))
  (=> (sort b y)
  (=> (mem (tuple21 bool b) (Tuple2 bool b (t2tb12 x) y) f)
  (and (mem2 x s) (mem b y t)))))
  (forall ((x Bool) (y1 uni) (y2 uni))
  (=> (sort b y1)
  (=> (sort b y2)
  (=>
  (and (mem (tuple21 bool b) (Tuple2 bool b (t2tb12 x) y1) f) (mem
  (tuple21 bool b) (Tuple2 bool b (t2tb12 x) y2) f)) (= y1 y2)))))) (mem
  (set1 (tuple21 bool b)) f (infix_plmngt b bool (t2tb2 s) t)))))))

;; mem_function
  (assert
  (forall ((f (set (tuple2 Int (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))))) (s (set Int))
  (t (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))))
  (= (mem
  (set1
  (tuple21 int
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (t2tb54 f)
  (infix_plmngt
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) 
  int (t2tb3 s) (t2tb t)))
  (and
  (forall ((x Int) (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))))
  (=> (mem
  (tuple21 int
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2 int
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb13 x) (t2tb4 y)) (t2tb54 f)) (and (mem1 x s) (mem4 y t))))
  (forall ((x Int) (y1 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))) (y2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))))
  (=>
  (and (mem
  (tuple21 int
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2 int
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb13 x) (t2tb4 y1)) (t2tb54 f)) (mem
  (tuple21 int
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2 int
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb13 x) (t2tb4 y2)) (t2tb54 f))) (= y1 y2)))))))

;; mem_function
  (assert
  (forall ((f (set (tuple2 Int (set Int)))) (s (set Int))
  (t (set (set Int))))
  (= (mem (set1 (tuple21 int (set1 int))) (t2tb57 f)
  (infix_plmngt (set1 int) int (t2tb3 s) (t2tb1 t)))
  (and
  (forall ((x Int) (y (set Int)))
  (=> (mem (tuple21 int (set1 int))
  (Tuple2 int (set1 int) (t2tb13 x) (t2tb3 y)) (t2tb57 f))
  (and (mem1 x s) (mem3 y t))))
  (forall ((x Int) (y1 (set Int)) (y2 (set Int)))
  (=>
  (and (mem (tuple21 int (set1 int))
  (Tuple2 int (set1 int) (t2tb13 x) (t2tb3 y1)) (t2tb57 f)) (mem
  (tuple21 int (set1 int)) (Tuple2 int (set1 int) (t2tb13 x) (t2tb3 y2))
  (t2tb57 f))) (= y1 y2)))))))

;; mem_function
  (assert
  (forall ((f (set (tuple2 Int Bool))) (s (set Int)) (t (set Bool)))
  (= (mem (set1 (tuple21 int bool)) (t2tb60 f)
  (infix_plmngt bool int (t2tb3 s) (t2tb2 t)))
  (and
  (forall ((x Int) (y Bool))
  (=> (mem (tuple21 int bool) (Tuple2 int bool (t2tb13 x) (t2tb12 y))
  (t2tb60 f)) (and (mem1 x s) (mem2 y t))))
  (forall ((x Int) (y1 Bool) (y2 Bool))
  (=>
  (and (mem (tuple21 int bool) (Tuple2 int bool (t2tb13 x) (t2tb12 y1))
  (t2tb60 f)) (mem (tuple21 int bool)
  (Tuple2 int bool (t2tb13 x) (t2tb12 y2)) (t2tb60 f))) (= y1 y2)))))))

;; mem_function
  (assert
  (forall ((f (set (tuple2 Int Int))) (s (set Int)) (t (set Int)))
  (= (mem (set1 (tuple21 int int)) (t2tb63 f)
  (infix_plmngt int int (t2tb3 s) (t2tb3 t)))
  (and
  (forall ((x Int) (y Int))
  (=> (mem (tuple21 int int) (Tuple2 int int (t2tb13 x) (t2tb13 y))
  (t2tb63 f)) (and (mem1 x s) (mem1 y t))))
  (forall ((x Int) (y1 Int) (y2 Int))
  (=>
  (and (mem (tuple21 int int) (Tuple2 int int (t2tb13 x) (t2tb13 y1))
  (t2tb63 f)) (mem (tuple21 int int) (Tuple2 int int (t2tb13 x) (t2tb13 y2))
  (t2tb63 f))) (= y1 y2)))))))

;; mem_function
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set Int)) (t uni))
  (and
  (=> (mem (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb3 s) t))
  (and
  (forall ((x Int) (y uni))
  (=> (mem (tuple21 int b) (Tuple2 int b (t2tb13 x) y) f)
  (and (mem1 x s) (mem b y t))))
  (forall ((x Int) (y1 uni) (y2 uni))
  (=> (sort b y1)
  (=> (sort b y2)
  (=>
  (and (mem (tuple21 int b) (Tuple2 int b (t2tb13 x) y1) f) (mem
  (tuple21 int b) (Tuple2 int b (t2tb13 x) y2) f)) (= y1 y2)))))))
  (=>
  (and
  (forall ((x Int) (y uni))
  (=> (sort b y)
  (=> (mem (tuple21 int b) (Tuple2 int b (t2tb13 x) y) f)
  (and (mem1 x s) (mem b y t)))))
  (forall ((x Int) (y1 uni) (y2 uni))
  (=> (sort b y1)
  (=> (sort b y2)
  (=>
  (and (mem (tuple21 int b) (Tuple2 int b (t2tb13 x) y1) f) (mem
  (tuple21 int b) (Tuple2 int b (t2tb13 x) y2) f)) (= y1 y2)))))) (mem
  (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb3 s) t)))))))

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
  (forall ((f uni) (s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))) (t uni)
  (x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))
  (y uni))
  (=> (mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b))
  f
  (infix_plmngt b
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s) t))
  (=> (mem
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b)
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b
  (t2tb4 x) y) f) (mem4 x s))))))

;; domain_function
  (assert
  (forall ((f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (t (set (set Int))) (x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (y (set Int)))
  (=> (mem4 f (infix_plmngt1 s t))
  (=> (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb9 x) (t2tb3 y)) (t2tb4 f)) (mem
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x) (t2tb5 s))))))

;; domain_function
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set (set Int))) (t uni) (x (set Int)) (y uni))
  (=> (mem (set1 (tuple21 (set1 int) b)) f
  (infix_plmngt b (set1 int) (t2tb1 s) t))
  (=> (mem (tuple21 (set1 int) b) (Tuple2 (set1 int) b (t2tb3 x) y) f) (mem3
  x s))))))

;; domain_function
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set Bool)) (t uni) (x Bool) (y uni))
  (=> (mem (set1 (tuple21 bool b)) f (infix_plmngt b bool (t2tb2 s) t))
  (=> (mem (tuple21 bool b) (Tuple2 bool b (t2tb12 x) y) f) (mem2 x s))))))

;; domain_function
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set Int)) (t uni) (x Int) (y uni))
  (=> (mem (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb3 s) t))
  (=> (mem (tuple21 int b) (Tuple2 int b (t2tb13 x) y) f) (mem1 x s))))))

;; domain_function
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni) (x uni) (y uni))
  (=> (mem (set1 (tuple21 a b)) f (infix_plmngt b a s t))
  (=> (mem (tuple21 a b) (Tuple2 a b x y) f) (mem a x s))))))

;; range_function
  (assert
  (forall ((a ty))
  (forall ((f uni) (s uni) (t (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))) (x uni)
  (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))
  (=> (mem
  (set1
  (tuple21 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))) f
  (infix_plmngt
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) a s
  (t2tb t)))
  (=> (mem
  (tuple21 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) x
  (t2tb4 y)) f) (mem4 y t))))))

;; range_function
  (assert
  (forall ((a ty))
  (forall ((f uni) (s uni) (t (set (set Int))) (x uni) (y (set Int)))
  (=> (mem (set1 (tuple21 a (set1 int))) f
  (infix_plmngt (set1 int) a s (t2tb1 t)))
  (=> (mem (tuple21 a (set1 int)) (Tuple2 a (set1 int) x (t2tb3 y)) f) (mem3
  y t))))))

;; range_function
  (assert
  (forall ((a ty))
  (forall ((f uni) (s uni) (t (set Bool)) (x uni) (y Bool))
  (=> (mem (set1 (tuple21 a bool)) f (infix_plmngt bool a s (t2tb2 t)))
  (=> (mem (tuple21 a bool) (Tuple2 a bool x (t2tb12 y)) f) (mem2 y t))))))

;; range_function
  (assert
  (forall ((a ty))
  (forall ((f uni) (s uni) (t (set Int)) (x uni) (y Int))
  (=> (mem (set1 (tuple21 a int)) f (infix_plmngt int a s (t2tb3 t)))
  (=> (mem (tuple21 a int) (Tuple2 a int x (t2tb13 y)) f) (mem1 y t))))))

;; range_function
  (assert
  (forall ((f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (t (set (set Int))) (x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (y (set Int)))
  (=> (mem4 f (infix_plmngt1 s t))
  (=> (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb9 x) (t2tb3 y)) (t2tb4 f)) (mem3 y t)))))

;; range_function
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni) (x uni) (y uni))
  (=> (mem (set1 (tuple21 a b)) f (infix_plmngt b a s t))
  (=> (mem (tuple21 a b) (Tuple2 a b x y) f) (mem b y t))))))

;; function_extend_range
  (assert
  (forall ((f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (t (set (set Int))) (u (set (set Int))))
  (=> (subset (set1 int) (t2tb1 t) (t2tb1 u))
  (=> (mem4 f (infix_plmngt1 s t)) (mem4 f (infix_plmngt1 s u))))))

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
  (forall ((f uni) (s uni) (t (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))))
  (u (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))))
  (=> (subset
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb u) (t2tb t))
  (=> (mem
  (set1
  (tuple21 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))) f
  (infix_plmngt
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) a s
  (t2tb t)))
  (=>
  (forall ((x uni) (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))))
  (=> (sort a x)
  (=> (mem
  (tuple21 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) x
  (t2tb4 y)) f) (mem4 y u)))) (mem
  (set1
  (tuple21 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))) f
  (infix_plmngt
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) a s
  (t2tb u)))))))))

;; function_reduce_range
  (assert
  (forall ((a ty))
  (forall ((f uni) (s uni) (t (set (set Int))) (u (set (set Int))))
  (=> (subset (set1 int) (t2tb1 u) (t2tb1 t))
  (=> (mem (set1 (tuple21 a (set1 int))) f
  (infix_plmngt (set1 int) a s (t2tb1 t)))
  (=>
  (forall ((x uni) (y (set Int)))
  (=> (sort a x)
  (=> (mem (tuple21 a (set1 int)) (Tuple2 a (set1 int) x (t2tb3 y)) f) (mem3
  y u)))) (mem (set1 (tuple21 a (set1 int))) f
  (infix_plmngt (set1 int) a s (t2tb1 u)))))))))

;; function_reduce_range
  (assert
  (forall ((a ty))
  (forall ((f uni) (s uni) (t (set Bool)) (u (set Bool)))
  (=> (subset bool (t2tb2 u) (t2tb2 t))
  (=> (mem (set1 (tuple21 a bool)) f (infix_plmngt bool a s (t2tb2 t)))
  (=>
  (forall ((x uni) (y Bool))
  (=> (sort a x)
  (=> (mem (tuple21 a bool) (Tuple2 a bool x (t2tb12 y)) f) (mem2 y u))))
  (mem (set1 (tuple21 a bool)) f (infix_plmngt bool a s (t2tb2 u)))))))))

;; function_reduce_range
  (assert
  (forall ((a ty))
  (forall ((f uni) (s uni) (t (set Int)) (u (set Int)))
  (=> (subset int (t2tb3 u) (t2tb3 t))
  (=> (mem (set1 (tuple21 a int)) f (infix_plmngt int a s (t2tb3 t)))
  (=>
  (forall ((x uni) (y Int))
  (=> (sort a x)
  (=> (mem (tuple21 a int) (Tuple2 a int x (t2tb13 y)) f) (mem1 y u)))) (mem
  (set1 (tuple21 a int)) f (infix_plmngt int a s (t2tb3 u)))))))))

;; function_reduce_range
  (assert
  (forall ((f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (t (set (set Int))) (u (set (set Int))))
  (=> (subset (set1 int) (t2tb1 u) (t2tb1 t))
  (=> (mem4 f (infix_plmngt1 s t))
  (=>
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)) (y (set Int)))
  (=> (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb9 x) (t2tb3 y)) (t2tb4 f)) (mem3 y u))) (mem4 f (infix_plmngt1 s u)))))))

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
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))
  (and
  (=> (mem4 x
  (tb2t
  (dom b
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) r)))
  (exists ((y uni))
  (and (sort b y) (mem
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b)
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b
  (t2tb4 x) y) r))))
  (=>
  (exists ((y uni)) (mem
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b)
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b
  (t2tb4 x) y) r)) (mem4 x
  (tb2t
  (dom b
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) r)))))))))

;; dom_def
  (assert
  (forall ((b ty))
  (forall ((r uni))
  (forall ((x (set Int)))
  (and
  (=> (mem3 x (tb2t1 (dom b (set1 int) r)))
  (exists ((y uni))
  (and (sort b y) (mem (tuple21 (set1 int) b)
  (Tuple2 (set1 int) b (t2tb3 x) y) r))))
  (=>
  (exists ((y uni)) (mem (tuple21 (set1 int) b)
  (Tuple2 (set1 int) b (t2tb3 x) y) r)) (mem3 x
  (tb2t1 (dom b (set1 int) r)))))))))

;; dom_def
  (assert
  (forall ((b ty))
  (forall ((r uni))
  (forall ((x Bool))
  (and
  (=> (mem2 x (tb2t2 (dom b bool r)))
  (exists ((y uni))
  (and (sort b y) (mem (tuple21 bool b) (Tuple2 bool b (t2tb12 x) y) r))))
  (=>
  (exists ((y uni)) (mem (tuple21 bool b) (Tuple2 bool b (t2tb12 x) y) r))
  (mem2 x (tb2t2 (dom b bool r)))))))))

;; dom_def
  (assert
  (forall ((b ty))
  (forall ((r uni))
  (forall ((x Int))
  (and
  (=> (mem1 x (tb2t3 (dom b int r)))
  (exists ((y uni))
  (and (sort b y) (mem (tuple21 int b) (Tuple2 int b (t2tb13 x) y) r))))
  (=> (exists ((y uni)) (mem (tuple21 int b) (Tuple2 int b (t2tb13 x) y) r))
  (mem1 x (tb2t3 (dom b int r)))))))))

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
  (forall ((y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))
  (and
  (=> (mem4 y
  (tb2t
  (ran
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) a
  r)))
  (exists ((x uni))
  (and (sort a x) (mem
  (tuple21 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) x
  (t2tb4 y)) r))))
  (=>
  (exists ((x uni)) (mem
  (tuple21 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) x
  (t2tb4 y)) r)) (mem4 y
  (tb2t
  (ran
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) a
  r)))))))))

;; ran_def
  (assert
  (forall ((a ty))
  (forall ((r uni))
  (forall ((y (set Int)))
  (and
  (=> (mem3 y (tb2t1 (ran (set1 int) a r)))
  (exists ((x uni))
  (and (sort a x) (mem (tuple21 a (set1 int))
  (Tuple2 a (set1 int) x (t2tb3 y)) r))))
  (=>
  (exists ((x uni)) (mem (tuple21 a (set1 int))
  (Tuple2 a (set1 int) x (t2tb3 y)) r)) (mem3 y
  (tb2t1 (ran (set1 int) a r)))))))))

;; ran_def
  (assert
  (forall ((a ty))
  (forall ((r uni))
  (forall ((y Bool))
  (and
  (=> (mem2 y (tb2t2 (ran bool a r)))
  (exists ((x uni))
  (and (sort a x) (mem (tuple21 a bool) (Tuple2 a bool x (t2tb12 y)) r))))
  (=>
  (exists ((x uni)) (mem (tuple21 a bool) (Tuple2 a bool x (t2tb12 y)) r))
  (mem2 y (tb2t2 (ran bool a r)))))))))

;; ran_def
  (assert
  (forall ((a ty))
  (forall ((r uni))
  (forall ((y Int))
  (and
  (=> (mem1 y (tb2t3 (ran int a r)))
  (exists ((x uni))
  (and (sort a x) (mem (tuple21 a int) (Tuple2 a int x (t2tb13 y)) r))))
  (=> (exists ((x uni)) (mem (tuple21 a int) (Tuple2 a int x (t2tb13 y)) r))
  (mem1 y (tb2t3 (ran int a r)))))))))

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
     (dom b
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (empty
     (tuple21
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     b)))) empty8)))

;; dom_empty
  (assert
  (forall ((b ty))
  (= (tb2t4
     (dom b
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
     (empty
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
     b)))) empty4)))

;; dom_empty
  (assert
  (= (tb2t5
     (dom (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (t2tb4 empty4))) empty5))

;; dom_empty
  (assert
  (forall ((b ty))
  (= (tb2t5
     (dom b (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (empty (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) b)))) 
  empty5)))

;; dom_empty
  (assert
  (= (tb2t6 (dom bool (tuple21 (tuple21 bool bool) bool) (t2tb5 empty5))) 
  empty6))

;; dom_empty
  (assert
  (forall ((b ty))
  (= (tb2t6
     (dom b (tuple21 (tuple21 bool bool) bool)
     (empty (tuple21 (tuple21 (tuple21 bool bool) bool) b)))) empty6)))

;; dom_empty
  (assert
  (forall ((b ty))
  (= (tb2t1 (dom b (set1 int) (empty (tuple21 (set1 int) b)))) empty3)))

;; dom_empty
  (assert (= (tb2t7 (dom bool (tuple21 bool bool) (t2tb6 empty6))) empty7))

;; dom_empty
  (assert
  (forall ((b ty))
  (= (tb2t7
     (dom b (tuple21 bool bool) (empty (tuple21 (tuple21 bool bool) b)))) 
  empty7)))

;; dom_empty
  (assert (= (tb2t2 (dom bool bool (t2tb7 empty7))) empty1))

;; dom_empty
  (assert
  (forall ((b ty)) (= (tb2t2 (dom b bool (empty (tuple21 bool b)))) empty1)))

;; dom_empty
  (assert
  (forall ((b ty)) (= (tb2t3 (dom b int (empty (tuple21 int b)))) empty2)))

;; dom_empty
  (assert
  (forall ((a ty) (b ty)) (= (dom b a (empty (tuple21 a b))) (empty a))))

;; dom_add
  (assert
  (forall ((b ty))
  (forall ((f uni) (x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))) (y uni))
  (= (tb2t
     (dom b
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (add
     (tuple21
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     b)
     (Tuple2
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     b (t2tb4 x) y) f))) (add4 x
                         (tb2t
                         (dom b
                         (set1
                         (tuple21
                         (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
                         (set1 int))) f)))))))

;; dom_add
  (assert
  (forall ((b ty))
  (forall ((f uni) (x (set Int)) (y uni))
  (= (tb2t1
     (dom b (set1 int)
     (add (tuple21 (set1 int) b) (Tuple2 (set1 int) b (t2tb3 x) y) f))) 
  (add3 x (tb2t1 (dom b (set1 int) f)))))))

;; dom_add
  (assert
  (forall ((b ty))
  (forall ((f uni) (x Bool) (y uni))
  (= (tb2t2
     (dom b bool (add (tuple21 bool b) (Tuple2 bool b (t2tb12 x) y) f))) 
  (add1 x (tb2t2 (dom b bool f)))))))

;; dom_add
  (assert
  (forall ((b ty))
  (forall ((f uni) (x Int) (y uni))
  (= (tb2t3 (dom b int (add (tuple21 int b) (Tuple2 int b (t2tb13 x) y) f))) 
  (add2 x (tb2t3 (dom b int f)))))))

;; dom_add
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (x uni) (y uni))
  (= (dom b a (add (tuple21 a b) (Tuple2 a b x y) f)) (add a x (dom b a f))))))

;; dom_singleton
  (assert
  (forall ((b ty))
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (y uni))
  (= (tb2t
     (dom b
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (add
     (tuple21
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     b)
     (Tuple2
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     b (t2tb4 x) y)
     (empty
     (tuple21
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     b))))) (add4 x empty8)))))

;; dom_singleton
  (assert
  (forall ((b ty))
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))) (y uni))
  (= (tb2t4
     (dom b
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
     (add
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
     b)
     (Tuple2
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)) b
     (t2tb8 x) y)
     (empty
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
     b))))) (tb2t4
            (add
            (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
            (set1 int)) (t2tb8 x) (t2tb4 empty4)))))))

;; dom_singleton
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)) (y (set Int)))
  (= (tb2t5
     (dom (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (add
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
     (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
     (t2tb9 x) (t2tb3 y)) (t2tb4 empty4)))) (tb2t5
                                            (add
                                            (tuple21
                                            (tuple21 (tuple21 bool bool)
                                            bool) bool) (t2tb9 x)
                                            (t2tb5 empty5))))))

;; dom_singleton
  (assert
  (forall ((b ty))
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)) (y uni))
  (= (tb2t5
     (dom b (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) b)
     (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) b (t2tb9 x) y)
     (empty (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) b))))) 
  (tb2t5
  (add (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
  (t2tb5 empty5)))))))

;; dom_singleton
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)) (y Bool))
  (= (tb2t6
     (dom bool (tuple21 (tuple21 bool bool) bool)
     (add (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (Tuple2 (tuple21 (tuple21 bool bool) bool) bool (t2tb10 x) (t2tb12 y))
     (t2tb5 empty5)))) (tb2t6
                       (add (tuple21 (tuple21 bool bool) bool) (t2tb10 x)
                       (t2tb6 empty6))))))

;; dom_singleton
  (assert
  (forall ((b ty))
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)) (y uni))
  (= (tb2t6
     (dom b (tuple21 (tuple21 bool bool) bool)
     (add (tuple21 (tuple21 (tuple21 bool bool) bool) b)
     (Tuple2 (tuple21 (tuple21 bool bool) bool) b (t2tb10 x) y)
     (empty (tuple21 (tuple21 (tuple21 bool bool) bool) b))))) (tb2t6
                                                               (add
                                                               (tuple21
                                                               (tuple21 
                                                               bool bool)
                                                               bool)
                                                               (t2tb10 x)
                                                               (t2tb6 empty6)))))))

;; dom_singleton
  (assert
  (forall ((b ty))
  (forall ((x (set Int)) (y uni))
  (= (tb2t1
     (dom b (set1 int)
     (add (tuple21 (set1 int) b) (Tuple2 (set1 int) b (t2tb3 x) y)
     (empty (tuple21 (set1 int) b))))) (add3 x empty3)))))

;; dom_singleton
  (assert
  (forall ((x (tuple2 Bool Bool)) (y Bool))
  (= (tb2t7
     (dom bool (tuple21 bool bool)
     (add (tuple21 (tuple21 bool bool) bool)
     (Tuple2 (tuple21 bool bool) bool (t2tb11 x) (t2tb12 y)) (t2tb6 empty6)))) 
  (tb2t7 (add (tuple21 bool bool) (t2tb11 x) (t2tb7 empty7))))))

;; dom_singleton
  (assert
  (forall ((b ty))
  (forall ((x (tuple2 Bool Bool)) (y uni))
  (= (tb2t7
     (dom b (tuple21 bool bool)
     (add (tuple21 (tuple21 bool bool) b)
     (Tuple2 (tuple21 bool bool) b (t2tb11 x) y)
     (empty (tuple21 (tuple21 bool bool) b))))) (tb2t7
                                                (add (tuple21 bool bool)
                                                (t2tb11 x) (t2tb7 empty7)))))))

;; dom_singleton
  (assert
  (forall ((x Bool) (y Bool))
  (= (tb2t2
     (dom bool bool
     (add (tuple21 bool bool) (Tuple2 bool bool (t2tb12 x) (t2tb12 y))
     (t2tb7 empty7)))) (add1 x empty1))))

;; dom_singleton
  (assert
  (forall ((b ty))
  (forall ((x Bool) (y uni))
  (= (tb2t2
     (dom b bool
     (add (tuple21 bool b) (Tuple2 bool b (t2tb12 x) y)
     (empty (tuple21 bool b))))) (add1 x empty1)))))

;; dom_singleton
  (assert
  (forall ((b ty))
  (forall ((x Int) (y uni))
  (= (tb2t3
     (dom b int
     (add (tuple21 int b) (Tuple2 int b (t2tb13 x) y)
     (empty (tuple21 int b))))) (add2 x empty2)))))

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
  (forall ((f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (t (set (set Int))))
  (= (mem4 f
  (tb2t
  (infix_mnmngt (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 s) (t2tb1 t))))
  (and (mem4 f (infix_plmngt1 s t))
  (= (tb2t5
     (dom (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (t2tb4 f))) s)))))

;; mem_total_functions
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni))
  (=> (sort (set1 a) s)
  (= (mem (set1 (tuple21 a b)) f (infix_mnmngt b a s t))
  (and (mem (set1 (tuple21 a b)) f (infix_plmngt b a s t)) (= (dom b a f) s)))))))

;; total_function_is_function
  (assert
  (forall ((f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (t (set (set Int))))
  (! (=> (mem4 f
     (tb2t
     (infix_mnmngt (set1 int)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb5 s) (t2tb1 t))))
     (mem4 f (infix_plmngt1 s t))) :pattern ((mem4
  f
  (tb2t
  (infix_mnmngt (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 s) (t2tb1 t))))) )))

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
  (forall ((s uni) (t (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))) (x uni)
  (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))
  (=> (and (mem a x s) (mem4 y t)) (mem
  (set1
  (tuple21 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (add
  (tuple21 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) x
  (t2tb4 y))
  (empty
  (tuple21 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))))
  (infix_plmngt
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) a s
  (t2tb t)))))))

;; singleton_is_partial_function
  (assert
  (forall ((a ty))
  (forall ((s uni) (t (set (set Int))) (x uni) (y (set Int)))
  (=> (and (mem a x s) (mem3 y t)) (mem (set1 (tuple21 a (set1 int)))
  (add (tuple21 a (set1 int)) (Tuple2 a (set1 int) x (t2tb3 y))
  (empty (tuple21 a (set1 int)))) (infix_plmngt (set1 int) a s (t2tb1 t)))))))

;; singleton_is_partial_function
  (assert
  (forall ((a ty))
  (forall ((s uni) (t (set Bool)) (x uni) (y Bool))
  (=> (and (mem a x s) (mem2 y t)) (mem (set1 (tuple21 a bool))
  (add (tuple21 a bool) (Tuple2 a bool x (t2tb12 y))
  (empty (tuple21 a bool))) (infix_plmngt bool a s (t2tb2 t)))))))

;; singleton_is_partial_function
  (assert
  (forall ((a ty))
  (forall ((s uni) (t (set Int)) (x uni) (y Int))
  (=> (and (mem a x s) (mem1 y t)) (mem (set1 (tuple21 a int))
  (add (tuple21 a int) (Tuple2 a int x (t2tb13 y)) (empty (tuple21 a int)))
  (infix_plmngt int a s (t2tb3 t)))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (t (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))) (x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))) (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))))
  (=> (and (mem4 x s) (mem4 y t)) (mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (add
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb4 x) (t2tb4 y))
  (empty
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))))
  (infix_plmngt
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s) (t2tb t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (t (set (set Int)))
  (x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))
  (y (set Int)))
  (=> (and (mem4 x s) (mem3 y t)) (mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1 int)))
  (add
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1 int))
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1 int) (t2tb4 x) (t2tb3 y))
  (empty
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1 int))))
  (infix_plmngt (set1 int)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s) (t2tb1 t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (t (set Bool))
  (x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))
  (y Bool))
  (=> (and (mem4 x s) (mem2 y t)) (mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  bool))
  (add
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  bool)
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  bool (t2tb4 x) (t2tb12 y))
  (empty
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  bool)))
  (infix_plmngt bool
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s) (t2tb2 t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (t (set Int))
  (x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))
  (y Int))
  (=> (and (mem4 x s) (mem1 y t)) (mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  int))
  (add
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  int)
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) 
  int (t2tb4 x) (t2tb13 y))
  (empty
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  int)))
  (infix_plmngt int
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s) (t2tb3 t))))))

;; singleton_is_partial_function
  (assert
  (forall ((b ty))
  (forall ((s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (t uni) (x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))) (y uni))
  (=> (and (mem4 x s) (mem b y t)) (mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b))
  (add
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b)
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b
  (t2tb4 x) y)
  (empty
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b)))
  (infix_plmngt b
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s) t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (t (set (set Int))) (x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (y (set Int)))
  (=>
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
  (t2tb5 s)) (mem3 y t)) (mem4
  (tb2t4
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb9 x) (t2tb3 y)) (t2tb4 empty4))) (infix_plmngt1 s t)))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set (tuple2 (tuple2 Bool Bool) Bool))) (t (set Bool))
  (x (tuple2 (tuple2 Bool Bool) Bool)) (y Bool))
  (=>
  (and (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb6 s)) (mem2 y
  t)) (mem (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (add (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (Tuple2 (tuple21 (tuple21 bool bool) bool) bool (t2tb10 x) (t2tb12 y))
  (t2tb5 empty5))
  (infix_plmngt bool (tuple21 (tuple21 bool bool) bool) (t2tb6 s) (t2tb2 t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set (set Int)))
  (t (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (x (set Int)) (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))))
  (=> (and (mem3 x s) (mem4 y t)) (mem
  (set1
  (tuple21 (set1 int)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (add
  (tuple21 (set1 int)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2 (set1 int)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb3 x) (t2tb4 y))
  (empty
  (tuple21 (set1 int)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))))
  (infix_plmngt
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1 int) (t2tb1 s) (t2tb t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set (set Int))) (t (set (set Int))) (x (set Int))
  (y (set Int)))
  (=> (and (mem3 x s) (mem3 y t)) (mem (set1 (tuple21 (set1 int) (set1 int)))
  (add (tuple21 (set1 int) (set1 int))
  (Tuple2 (set1 int) (set1 int) (t2tb3 x) (t2tb3 y))
  (empty (tuple21 (set1 int) (set1 int))))
  (infix_plmngt (set1 int) (set1 int) (t2tb1 s) (t2tb1 t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set (set Int))) (t (set Bool)) (x (set Int)) (y Bool))
  (=> (and (mem3 x s) (mem2 y t)) (mem (set1 (tuple21 (set1 int) bool))
  (add (tuple21 (set1 int) bool)
  (Tuple2 (set1 int) bool (t2tb3 x) (t2tb12 y))
  (empty (tuple21 (set1 int) bool)))
  (infix_plmngt bool (set1 int) (t2tb1 s) (t2tb2 t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set (set Int))) (t (set Int)) (x (set Int)) (y Int))
  (=> (and (mem3 x s) (mem1 y t)) (mem (set1 (tuple21 (set1 int) int))
  (add (tuple21 (set1 int) int) (Tuple2 (set1 int) int (t2tb3 x) (t2tb13 y))
  (empty (tuple21 (set1 int) int)))
  (infix_plmngt int (set1 int) (t2tb1 s) (t2tb3 t))))))

;; singleton_is_partial_function
  (assert
  (forall ((b ty))
  (forall ((s (set (set Int))) (t uni) (x (set Int)) (y uni))
  (=> (and (mem3 x s) (mem b y t)) (mem (set1 (tuple21 (set1 int) b))
  (add (tuple21 (set1 int) b) (Tuple2 (set1 int) b (t2tb3 x) y)
  (empty (tuple21 (set1 int) b))) (infix_plmngt b (set1 int) (t2tb1 s) t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set (tuple2 Bool Bool))) (t (set Bool)) (x (tuple2 Bool Bool))
  (y Bool))
  (=> (and (mem (tuple21 bool bool) (t2tb11 x) (t2tb7 s)) (mem2 y t)) (mem
  (set1 (tuple21 (tuple21 bool bool) bool))
  (add (tuple21 (tuple21 bool bool) bool)
  (Tuple2 (tuple21 bool bool) bool (t2tb11 x) (t2tb12 y)) (t2tb6 empty6))
  (infix_plmngt bool (tuple21 bool bool) (t2tb7 s) (t2tb2 t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set Bool)) (t (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))) (x Bool)
  (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))
  (=> (and (mem2 x s) (mem4 y t)) (mem
  (set1
  (tuple21 bool
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (add
  (tuple21 bool
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2 bool
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb12 x) (t2tb4 y))
  (empty
  (tuple21 bool
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))))
  (infix_plmngt
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  bool (t2tb2 s) (t2tb t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set Bool)) (t (set (set Int))) (x Bool) (y (set Int)))
  (=> (and (mem2 x s) (mem3 y t)) (mem (set1 (tuple21 bool (set1 int)))
  (add (tuple21 bool (set1 int))
  (Tuple2 bool (set1 int) (t2tb12 x) (t2tb3 y))
  (empty (tuple21 bool (set1 int))))
  (infix_plmngt (set1 int) bool (t2tb2 s) (t2tb1 t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set Bool)) (t (set Bool)) (x Bool) (y Bool))
  (=> (and (mem2 x s) (mem2 y t)) (mem (set1 (tuple21 bool bool))
  (add (tuple21 bool bool) (Tuple2 bool bool (t2tb12 x) (t2tb12 y))
  (t2tb7 empty7)) (infix_plmngt bool bool (t2tb2 s) (t2tb2 t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set Bool)) (t (set Int)) (x Bool) (y Int))
  (=> (and (mem2 x s) (mem1 y t)) (mem (set1 (tuple21 bool int))
  (add (tuple21 bool int) (Tuple2 bool int (t2tb12 x) (t2tb13 y))
  (empty (tuple21 bool int))) (infix_plmngt int bool (t2tb2 s) (t2tb3 t))))))

;; singleton_is_partial_function
  (assert
  (forall ((b ty))
  (forall ((s (set Bool)) (t uni) (x Bool) (y uni))
  (=> (and (mem2 x s) (mem b y t)) (mem (set1 (tuple21 bool b))
  (add (tuple21 bool b) (Tuple2 bool b (t2tb12 x) y)
  (empty (tuple21 bool b))) (infix_plmngt b bool (t2tb2 s) t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set Int)) (t (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))) (x Int)
  (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))
  (=> (and (mem1 x s) (mem4 y t)) (mem
  (set1
  (tuple21 int
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (add
  (tuple21 int
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2 int
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb13 x) (t2tb4 y))
  (empty
  (tuple21 int
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))))
  (infix_plmngt
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) 
  int (t2tb3 s) (t2tb t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set Int)) (t (set (set Int))) (x Int) (y (set Int)))
  (=> (and (mem1 x s) (mem3 y t)) (mem (set1 (tuple21 int (set1 int)))
  (add (tuple21 int (set1 int)) (Tuple2 int (set1 int) (t2tb13 x) (t2tb3 y))
  (empty (tuple21 int (set1 int))))
  (infix_plmngt (set1 int) int (t2tb3 s) (t2tb1 t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set Int)) (t (set Bool)) (x Int) (y Bool))
  (=> (and (mem1 x s) (mem2 y t)) (mem (set1 (tuple21 int bool))
  (add (tuple21 int bool) (Tuple2 int bool (t2tb13 x) (t2tb12 y))
  (empty (tuple21 int bool))) (infix_plmngt bool int (t2tb3 s) (t2tb2 t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set Int)) (t (set Int)) (x Int) (y Int))
  (=> (and (mem1 x s) (mem1 y t)) (mem (set1 (tuple21 int int))
  (add (tuple21 int int) (Tuple2 int int (t2tb13 x) (t2tb13 y))
  (empty (tuple21 int int))) (infix_plmngt int int (t2tb3 s) (t2tb3 t))))))

;; singleton_is_partial_function
  (assert
  (forall ((b ty))
  (forall ((s (set Int)) (t uni) (x Int) (y uni))
  (=> (and (mem1 x s) (mem b y t)) (mem (set1 (tuple21 int b))
  (add (tuple21 int b) (Tuple2 int b (t2tb13 x) y) (empty (tuple21 int b)))
  (infix_plmngt b int (t2tb3 s) t))))))

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
  (forall ((x uni) (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (! (mem
  (set1
  (tuple21 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (add
  (tuple21 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) x
  (t2tb4 y))
  (empty
  (tuple21 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))))
  (infix_mnmngt
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) a
  (add a x (empty a)) (t2tb (add4 y empty8)))) :pattern ((add
                                                         (tuple21 a
                                                         (set1
                                                         (tuple21
                                                         (tuple21
                                                         (tuple21
                                                         (tuple21 bool bool)
                                                         bool) bool)
                                                         (set1 int))))
                                                         (Tuple2 a
                                                         (set1
                                                         (tuple21
                                                         (tuple21
                                                         (tuple21
                                                         (tuple21 bool bool)
                                                         bool) bool)
                                                         (set1 int))) x
                                                         (t2tb4 y))
                                                         (empty
                                                         (tuple21 a
                                                         (set1
                                                         (tuple21
                                                         (tuple21
                                                         (tuple21
                                                         (tuple21 bool bool)
                                                         bool) bool)
                                                         (set1 int))))))) ))))

;; singleton_is_function
  (assert
  (forall ((a ty))
  (forall ((x uni) (y (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (! (mem
  (set1
  (tuple21 a
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (add
  (tuple21 a
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (Tuple2 a
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)) x
  (t2tb8 y))
  (empty
  (tuple21 a
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (infix_mnmngt
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)) a
  (add a x (empty a))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb8 y) (t2tb4 empty4)))) :pattern ((add
                                        (tuple21 a
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int)))
                                        (Tuple2 a
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int)) x (t2tb8 y))
                                        (empty
                                        (tuple21 a
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int)))))) ))))

;; singleton_is_function
  (assert
  (forall ((a ty))
  (forall ((x uni) (y (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (! (mem
  (set1 (tuple21 a (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))
  (add (tuple21 a (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (Tuple2 a (tuple21 (tuple21 (tuple21 bool bool) bool) bool) x (t2tb9 y))
  (empty (tuple21 a (tuple21 (tuple21 (tuple21 bool bool) bool) bool))))
  (infix_mnmngt (tuple21 (tuple21 (tuple21 bool bool) bool) bool) a
  (add a x (empty a))
  (add (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 y)
  (t2tb5 empty5)))) :pattern ((add
                              (tuple21 a
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool))
                              (Tuple2 a
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool) x (t2tb9 y))
                              (empty
                              (tuple21 a
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool))))) ))))

;; singleton_is_function
  (assert
  (forall ((a ty))
  (forall ((x uni) (y (tuple2 (tuple2 Bool Bool) Bool))) (! (mem
  (set1 (tuple21 a (tuple21 (tuple21 bool bool) bool)))
  (add (tuple21 a (tuple21 (tuple21 bool bool) bool))
  (Tuple2 a (tuple21 (tuple21 bool bool) bool) x (t2tb10 y))
  (empty (tuple21 a (tuple21 (tuple21 bool bool) bool))))
  (infix_mnmngt (tuple21 (tuple21 bool bool) bool) a (add a x (empty a))
  (add (tuple21 (tuple21 bool bool) bool) (t2tb10 y) (t2tb6 empty6)))) :pattern (
  (add (tuple21 a (tuple21 (tuple21 bool bool) bool))
  (Tuple2 a (tuple21 (tuple21 bool bool) bool) x (t2tb10 y))
  (empty (tuple21 a (tuple21 (tuple21 bool bool) bool))))) ))))

;; singleton_is_function
  (assert
  (forall ((a ty))
  (forall ((x uni) (y (set Int))) (! (mem (set1 (tuple21 a (set1 int)))
  (add (tuple21 a (set1 int)) (Tuple2 a (set1 int) x (t2tb3 y))
  (empty (tuple21 a (set1 int))))
  (infix_mnmngt (set1 int) a (add a x (empty a)) (t2tb1 (add3 y empty3)))) :pattern (
  (add (tuple21 a (set1 int)) (Tuple2 a (set1 int) x (t2tb3 y))
  (empty (tuple21 a (set1 int))))) ))))

;; singleton_is_function
  (assert
  (forall ((a ty))
  (forall ((x uni) (y (tuple2 Bool Bool))) (! (mem
  (set1 (tuple21 a (tuple21 bool bool)))
  (add (tuple21 a (tuple21 bool bool))
  (Tuple2 a (tuple21 bool bool) x (t2tb11 y))
  (empty (tuple21 a (tuple21 bool bool))))
  (infix_mnmngt (tuple21 bool bool) a (add a x (empty a))
  (add (tuple21 bool bool) (t2tb11 y) (t2tb7 empty7)))) :pattern ((add
                                                                  (tuple21 a
                                                                  (tuple21
                                                                  bool 
                                                                  bool))
                                                                  (Tuple2 a
                                                                  (tuple21
                                                                  bool 
                                                                  bool) x
                                                                  (t2tb11 y))
                                                                  (empty
                                                                  (tuple21 a
                                                                  (tuple21
                                                                  bool 
                                                                  bool))))) ))))

;; singleton_is_function
  (assert
  (forall ((a ty))
  (forall ((x uni) (y Bool)) (! (mem (set1 (tuple21 a bool))
  (add (tuple21 a bool) (Tuple2 a bool x (t2tb12 y))
  (empty (tuple21 a bool)))
  (infix_mnmngt bool a (add a x (empty a)) (t2tb2 (add1 y empty1)))) :pattern (
  (add (tuple21 a bool) (Tuple2 a bool x (t2tb12 y))
  (empty (tuple21 a bool)))) ))))

;; singleton_is_function
  (assert
  (forall ((a ty))
  (forall ((x uni) (y Int)) (! (mem (set1 (tuple21 a int))
  (add (tuple21 a int) (Tuple2 a int x (t2tb13 y)) (empty (tuple21 a int)))
  (infix_mnmngt int a (add a x (empty a)) (t2tb3 (add2 y empty2)))) :pattern (
  (add (tuple21 a int) (Tuple2 a int x (t2tb13 y)) (empty (tuple21 a int)))) ))))

;; singleton_is_function
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (! (mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (add
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb4 x) (t2tb4 y))
  (empty
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))))
  (infix_mnmngt
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb (add4 x empty8)) (t2tb (add4 y empty8)))) :pattern ((tb2t21
                                                            (add
                                                            (tuple21
                                                            (set1
                                                            (tuple21
                                                            (tuple21
                                                            (tuple21
                                                            (tuple21 
                                                            bool bool) 
                                                            bool) bool)
                                                            (set1 int)))
                                                            (set1
                                                            (tuple21
                                                            (tuple21
                                                            (tuple21
                                                            (tuple21 
                                                            bool bool) 
                                                            bool) bool)
                                                            (set1 int))))
                                                            (Tuple2
                                                            (set1
                                                            (tuple21
                                                            (tuple21
                                                            (tuple21
                                                            (tuple21 
                                                            bool bool) 
                                                            bool) bool)
                                                            (set1 int)))
                                                            (set1
                                                            (tuple21
                                                            (tuple21
                                                            (tuple21
                                                            (tuple21 
                                                            bool bool) 
                                                            bool) bool)
                                                            (set1 int)))
                                                            (t2tb4 x)
                                                            (t2tb4 y))
                                                            (empty
                                                            (tuple21
                                                            (set1
                                                            (tuple21
                                                            (tuple21
                                                            (tuple21
                                                            (tuple21 
                                                            bool bool) 
                                                            bool) bool)
                                                            (set1 int)))
                                                            (set1
                                                            (tuple21
                                                            (tuple21
                                                            (tuple21
                                                            (tuple21 
                                                            bool bool) 
                                                            bool) bool)
                                                            (set1 int)))))))) )))

(declare-fun t2tb65 ((set (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))))) (sort
  (set1
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (t2tb65 x))))

(declare-fun tb2t65 (uni) (set (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))))))
  (! (= (tb2t65 (t2tb65 i)) i) :pattern ((t2tb65 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb65 (tb2t65 j)) j) :pattern ((t2tb65 (tb2t65 j))) )))

(declare-fun t2tb66 ((set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))))) (sort
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (t2tb66 x))))

(declare-fun tb2t66 (uni) (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))))) (! (= (tb2t66 (t2tb66 i)) i) :pattern ((t2tb66 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb66 (tb2t66 j)) j) :pattern ((t2tb66 (tb2t66 j))) )))

(declare-fun t2tb67 ((tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (sort
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb67 x))))

(declare-fun tb2t67 (uni) (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))

;; BridgeL
  (assert
  (forall ((i (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (! (= (tb2t67 (t2tb67 i)) i) :pattern ((t2tb67 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb67 (tb2t67 j)) j) :pattern ((t2tb67 (tb2t67 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (y (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (! (mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (add
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb4 x) (t2tb8 y))
  (empty
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (infix_mnmngt
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb (add4 x empty8))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb8 y) (t2tb4 empty4)))) :pattern ((tb2t66
                                        (add
                                        (tuple21
                                        (set1
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int)))
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int)))
                                        (Tuple2
                                        (set1
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int)))
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int)) (t2tb4 x)
                                        (t2tb8 y))
                                        (empty
                                        (tuple21
                                        (set1
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int)))
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int))))))) )))

(declare-fun t2tb68 ((tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))) (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))) (sort
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb68 x))))

(declare-fun tb2t68 (uni) (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))) (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (! (= (tb2t68 (t2tb68 i)) i) :pattern ((t2tb68 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb68 (tb2t68 j)) j) :pattern ((t2tb68 (tb2t68 j))) )))

(declare-fun t2tb69 ((set (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool)))))) (sort
  (set1
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))) (t2tb69 x))))

(declare-fun tb2t69 (uni) (set (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool)))))) (! (= (tb2t69 (t2tb69 i)) i) :pattern ((t2tb69 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb69 (tb2t69 j)) j) :pattern ((t2tb69 (tb2t69 j))) )))

(declare-fun t2tb70 ((set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))) (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))))
  (sort
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))) (t2tb70 x))))

(declare-fun tb2t70 (uni) (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))) (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))))
  (! (= (tb2t70 (t2tb70 i)) i) :pattern ((t2tb70 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb70 (tb2t70 j)) j) :pattern ((t2tb70 (tb2t70 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (y (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))) (! (mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))
  (add
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb4 x) (t2tb9 y))
  (empty
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))))
  (infix_mnmngt (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb (add4 x empty8))
  (add (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 y)
  (t2tb5 empty5)))) :pattern ((tb2t70
                              (add
                              (tuple21
                              (set1
                              (tuple21
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool) (set1 int)))
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool))
                              (Tuple2
                              (set1
                              (tuple21
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool) (set1 int)))
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool) (t2tb4 x) (t2tb9 y))
                              (empty
                              (tuple21
                              (set1
                              (tuple21
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool) (set1 int)))
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool)))))) )))

(declare-fun t2tb71 ((set (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (tuple2 (tuple2 Bool Bool) Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (tuple2 (tuple2 Bool Bool) Bool)))))) (sort
  (set1
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (tuple21 (tuple21 bool bool) bool)))) (t2tb71 x))))

(declare-fun tb2t71 (uni) (set (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (tuple2 (tuple2 Bool Bool) Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (tuple2 (tuple2 Bool Bool) Bool))))))
  (! (= (tb2t71 (t2tb71 i)) i) :pattern ((t2tb71 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb71 (tb2t71 j)) j) :pattern ((t2tb71 (tb2t71 j))) )))

(declare-fun t2tb72 ((set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (tuple2 (tuple2 Bool Bool) Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))) (tuple2 (tuple2 Bool Bool) Bool))))) (sort
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (tuple21 (tuple21 bool bool) bool))) (t2tb72 x))))

(declare-fun tb2t72 (uni) (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (tuple2 (tuple2 Bool Bool) Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))) (tuple2 (tuple2 Bool Bool) Bool)))))
  (! (= (tb2t72 (t2tb72 i)) i) :pattern ((t2tb72 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb72 (tb2t72 j)) j) :pattern ((t2tb72 (tb2t72 j))) )))

(declare-fun t2tb73 ((tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))) (tuple2 (tuple2 Bool Bool) Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))) (tuple2 (tuple2 Bool Bool) Bool)))) (sort
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (tuple21 (tuple21 bool bool) bool)) (t2tb73 x))))

(declare-fun tb2t73 (uni) (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (tuple2 (tuple2 Bool Bool) Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))) (tuple2 (tuple2 Bool Bool) Bool))))
  (! (= (tb2t73 (t2tb73 i)) i) :pattern ((t2tb73 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb73 (tb2t73 j)) j) :pattern ((t2tb73 (tb2t73 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (y (tuple2 (tuple2 Bool Bool) Bool))) (! (mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (tuple21 (tuple21 bool bool) bool)))
  (add
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (tuple21 (tuple21 bool bool) bool))
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (tuple21 (tuple21 bool bool) bool) (t2tb4 x) (t2tb10 y))
  (empty
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (tuple21 (tuple21 bool bool) bool))))
  (infix_mnmngt (tuple21 (tuple21 bool bool) bool)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb (add4 x empty8))
  (add (tuple21 (tuple21 bool bool) bool) (t2tb10 y) (t2tb6 empty6)))) :pattern (
  (tb2t72
  (add
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (tuple21 (tuple21 bool bool) bool))
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (tuple21 (tuple21 bool bool) bool) (t2tb4 x) (t2tb10 y))
  (empty
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (tuple21 (tuple21 bool bool) bool)))))) )))

;; singleton_is_function
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (y (set Int))) (! (mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1 int)))
  (add
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1 int))
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1 int) (t2tb4 x) (t2tb3 y))
  (empty
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1 int))))
  (infix_mnmngt (set1 int)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb (add4 x empty8)) (t2tb1 (add3 y empty3)))) :pattern ((tb2t23
                                                             (add
                                                             (tuple21
                                                             (set1
                                                             (tuple21
                                                             (tuple21
                                                             (tuple21
                                                             (tuple21 
                                                             bool bool) 
                                                             bool) bool)
                                                             (set1 int)))
                                                             (set1 int))
                                                             (Tuple2
                                                             (set1
                                                             (tuple21
                                                             (tuple21
                                                             (tuple21
                                                             (tuple21 
                                                             bool bool) 
                                                             bool) bool)
                                                             (set1 int)))
                                                             (set1 int)
                                                             (t2tb4 x)
                                                             (t2tb3 y))
                                                             (empty
                                                             (tuple21
                                                             (set1
                                                             (tuple21
                                                             (tuple21
                                                             (tuple21
                                                             (tuple21 
                                                             bool bool) 
                                                             bool) bool)
                                                             (set1 int)))
                                                             (set1 int)))))) )))

(declare-fun t2tb74 ((set (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (tuple2 Bool Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (tuple2 Bool Bool)))))) (sort
  (set1
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (tuple21 bool bool)))) (t2tb74 x))))

(declare-fun tb2t74 (uni) (set (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (tuple2 Bool Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (tuple2 Bool Bool))))))
  (! (= (tb2t74 (t2tb74 i)) i) :pattern ((t2tb74 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb74 (tb2t74 j)) j) :pattern ((t2tb74 (tb2t74 j))) )))

(declare-fun t2tb75 ((set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (tuple2 Bool Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))) (tuple2 Bool Bool))))) (sort
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (tuple21 bool bool))) (t2tb75 x))))

(declare-fun tb2t75 (uni) (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (tuple2 Bool Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))) (tuple2 Bool Bool)))))
  (! (= (tb2t75 (t2tb75 i)) i) :pattern ((t2tb75 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb75 (tb2t75 j)) j) :pattern ((t2tb75 (tb2t75 j))) )))

(declare-fun t2tb76 ((tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))) (tuple2 Bool Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))) (tuple2 Bool Bool)))) (sort
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (tuple21 bool bool)) (t2tb76 x))))

(declare-fun tb2t76 (uni) (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (tuple2 Bool Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))) (tuple2 Bool Bool))))
  (! (= (tb2t76 (t2tb76 i)) i) :pattern ((t2tb76 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb76 (tb2t76 j)) j) :pattern ((t2tb76 (tb2t76 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (y (tuple2 Bool Bool))) (! (mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (tuple21 bool bool)))
  (add
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (tuple21 bool bool))
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (tuple21 bool bool) (t2tb4 x) (t2tb11 y))
  (empty
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (tuple21 bool bool))))
  (infix_mnmngt (tuple21 bool bool)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb (add4 x empty8)) (add (tuple21 bool bool) (t2tb11 y) (t2tb7 empty7)))) :pattern (
  (tb2t75
  (add
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (tuple21 bool bool))
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (tuple21 bool bool) (t2tb4 x) (t2tb11 y))
  (empty
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (tuple21 bool bool)))))) )))

;; singleton_is_function
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (y Bool)) (! (mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  bool))
  (add
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  bool)
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  bool (t2tb4 x) (t2tb12 y))
  (empty
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  bool)))
  (infix_mnmngt bool
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb (add4 x empty8)) (t2tb2 (add1 y empty1)))) :pattern ((tb2t27
                                                             (add
                                                             (tuple21
                                                             (set1
                                                             (tuple21
                                                             (tuple21
                                                             (tuple21
                                                             (tuple21 
                                                             bool bool) 
                                                             bool) bool)
                                                             (set1 int)))
                                                             bool)
                                                             (Tuple2
                                                             (set1
                                                             (tuple21
                                                             (tuple21
                                                             (tuple21
                                                             (tuple21 
                                                             bool bool) 
                                                             bool) bool)
                                                             (set1 int)))
                                                             bool (t2tb4 x)
                                                             (t2tb12 y))
                                                             (empty
                                                             (tuple21
                                                             (set1
                                                             (tuple21
                                                             (tuple21
                                                             (tuple21
                                                             (tuple21 
                                                             bool bool) 
                                                             bool) bool)
                                                             (set1 int)))
                                                             bool))))) )))

;; singleton_is_function
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (y Int)) (! (mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  int))
  (add
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  int)
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) 
  int (t2tb4 x) (t2tb13 y))
  (empty
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  int)))
  (infix_mnmngt int
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb (add4 x empty8)) (t2tb3 (add2 y empty2)))) :pattern ((tb2t30
                                                             (add
                                                             (tuple21
                                                             (set1
                                                             (tuple21
                                                             (tuple21
                                                             (tuple21
                                                             (tuple21 
                                                             bool bool) 
                                                             bool) bool)
                                                             (set1 int)))
                                                             int)
                                                             (Tuple2
                                                             (set1
                                                             (tuple21
                                                             (tuple21
                                                             (tuple21
                                                             (tuple21 
                                                             bool bool) 
                                                             bool) bool)
                                                             (set1 int))) 
                                                             int (t2tb4 x)
                                                             (t2tb13 y))
                                                             (empty
                                                             (tuple21
                                                             (set1
                                                             (tuple21
                                                             (tuple21
                                                             (tuple21
                                                             (tuple21 
                                                             bool bool) 
                                                             bool) bool)
                                                             (set1 int)))
                                                             int))))) )))

;; singleton_is_function
  (assert
  (forall ((b ty))
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (y uni)) (! (mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b))
  (add
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b)
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b
  (t2tb4 x) y)
  (empty
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b)))
  (infix_mnmngt b
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb (add4 x empty8)) (add b y (empty b)))) :pattern ((add
                                                         (tuple21
                                                         (set1
                                                         (tuple21
                                                         (tuple21
                                                         (tuple21
                                                         (tuple21 bool bool)
                                                         bool) bool)
                                                         (set1 int))) b)
                                                         (Tuple2
                                                         (set1
                                                         (tuple21
                                                         (tuple21
                                                         (tuple21
                                                         (tuple21 bool bool)
                                                         bool) bool)
                                                         (set1 int))) b
                                                         (t2tb4 x) y)
                                                         (empty
                                                         (tuple21
                                                         (set1
                                                         (tuple21
                                                         (tuple21
                                                         (tuple21
                                                         (tuple21 bool bool)
                                                         bool) bool)
                                                         (set1 int))) b)))) ))))

(declare-fun t2tb77 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))))))) (sort
  (set1
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))))
  (t2tb77 x))))

(declare-fun tb2t77 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))))))
  (! (= (tb2t77 (t2tb77 i)) i) :pattern ((t2tb77 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb77 (tb2t77 j)) j) :pattern ((t2tb77 (tb2t77 j))) )))

(declare-fun t2tb78 ((set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))))) (sort
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (t2tb78 x))))

(declare-fun tb2t78 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))))) (! (= (tb2t78 (t2tb78 i)) i) :pattern ((t2tb78 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb78 (tb2t78 j)) j) :pattern ((t2tb78 (tb2t78 j))) )))

(declare-fun t2tb79 ((tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))) (sort
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (t2tb79 x))))

(declare-fun tb2t79 (uni) (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))) (! (= (tb2t79 (t2tb79 i)) i) :pattern ((t2tb79 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb79 (tb2t79 j)) j) :pattern ((t2tb79 (tb2t79 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))) (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (! (mem
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (add
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb8 x) (t2tb4 y))
  (empty
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))))
  (infix_mnmngt
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb8 x) (t2tb4 empty4)) (t2tb (add4 y empty8)))) :pattern ((tb2t78
                                                               (add
                                                               (tuple21
                                                               (tuple21
                                                               (tuple21
                                                               (tuple21
                                                               (tuple21 
                                                               bool bool)
                                                               bool) 
                                                               bool)
                                                               (set1 int))
                                                               (set1
                                                               (tuple21
                                                               (tuple21
                                                               (tuple21
                                                               (tuple21 
                                                               bool bool)
                                                               bool) 
                                                               bool)
                                                               (set1 int))))
                                                               (Tuple2
                                                               (tuple21
                                                               (tuple21
                                                               (tuple21
                                                               (tuple21 
                                                               bool bool)
                                                               bool) 
                                                               bool)
                                                               (set1 int))
                                                               (set1
                                                               (tuple21
                                                               (tuple21
                                                               (tuple21
                                                               (tuple21 
                                                               bool bool)
                                                               bool) 
                                                               bool)
                                                               (set1 int)))
                                                               (t2tb8 x)
                                                               (t2tb4 y))
                                                               (empty
                                                               (tuple21
                                                               (tuple21
                                                               (tuple21
                                                               (tuple21
                                                               (tuple21 
                                                               bool bool)
                                                               bool) 
                                                               bool)
                                                               (set1 int))
                                                               (set1
                                                               (tuple21
                                                               (tuple21
                                                               (tuple21
                                                               (tuple21 
                                                               bool bool)
                                                               bool) 
                                                               bool)
                                                               (set1 int)))))))) )))

(declare-fun t2tb80 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))))) (sort
  (set1
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (t2tb80 x))))

(declare-fun tb2t80 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))))) (! (= (tb2t80 (t2tb80 i)) i) :pattern ((t2tb80 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb80 (tb2t80 j)) j) :pattern ((t2tb80 (tb2t80 j))) )))

(declare-fun t2tb81 ((set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))) (sort
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (t2tb81 x))))

(declare-fun tb2t81 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))) (! (= (tb2t81 (t2tb81 i)) i) :pattern ((t2tb81 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb81 (tb2t81 j)) j) :pattern ((t2tb81 (tb2t81 j))) )))

(declare-fun t2tb82 ((tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (sort
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb82 x))))

(declare-fun tb2t82 (uni) (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (! (= (tb2t82 (t2tb82 i)) i) :pattern ((t2tb82 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb82 (tb2t82 j)) j) :pattern ((t2tb82 (tb2t82 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))) (y (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (! (mem
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (add
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (Tuple2
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb8 x) (t2tb8 y))
  (empty
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (infix_mnmngt
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb8 x) (t2tb4 empty4))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb8 y) (t2tb4 empty4)))) :pattern ((tb2t81
                                        (add
                                        (tuple21
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int))
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int)))
                                        (Tuple2
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int))
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int)) (t2tb8 x)
                                        (t2tb8 y))
                                        (empty
                                        (tuple21
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int))
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int))))))) )))

(declare-fun t2tb83 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))))
  (sort
  (set1
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))) (t2tb83 x))))

(declare-fun tb2t83 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))))
  (! (= (tb2t83 (t2tb83 i)) i) :pattern ((t2tb83 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb83 (tb2t83 j)) j) :pattern ((t2tb83 (tb2t83 j))) )))

(declare-fun t2tb84 ((set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)) (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))) (sort
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))) (t2tb84 x))))

(declare-fun tb2t84 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)) (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))))
  (! (= (tb2t84 (t2tb84 i)) i) :pattern ((t2tb84 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb84 (tb2t84 j)) j) :pattern ((t2tb84 (tb2t84 j))) )))

(declare-fun t2tb85 ((tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)) (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)) (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))) (sort
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb85 x))))

(declare-fun tb2t85 (uni) (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)) (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (! (= (tb2t85 (t2tb85 i)) i) :pattern ((t2tb85 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb85 (tb2t85 j)) j) :pattern ((t2tb85 (tb2t85 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))) (y (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))) (! (mem
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))
  (add
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (Tuple2
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 x) (t2tb9 y))
  (empty
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))))
  (infix_mnmngt (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb8 x) (t2tb4 empty4))
  (add (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 y)
  (t2tb5 empty5)))) :pattern ((tb2t84
                              (add
                              (tuple21
                              (tuple21
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool) (set1 int))
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool))
                              (Tuple2
                              (tuple21
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool) (set1 int))
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool) (t2tb8 x) (t2tb9 y))
                              (empty
                              (tuple21
                              (tuple21
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool) (set1 int))
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool)))))) )))

(declare-fun t2tb86 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) (tuple2 (tuple2 Bool Bool) Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (tuple2 (tuple2 Bool Bool) Bool)))))) (sort
  (set1
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 bool bool) bool)))) (t2tb86 x))))

(declare-fun tb2t86 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) (tuple2 (tuple2 Bool Bool) Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (tuple2 (tuple2 Bool Bool) Bool))))))
  (! (= (tb2t86 (t2tb86 i)) i) :pattern ((t2tb86 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb86 (tb2t86 j)) j) :pattern ((t2tb86 (tb2t86 j))) )))

(declare-fun t2tb87 ((set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (tuple2 (tuple2 Bool Bool) Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)) (tuple2 (tuple2 Bool Bool) Bool))))) (sort
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 bool bool) bool))) (t2tb87 x))))

(declare-fun tb2t87 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) (tuple2 (tuple2 Bool Bool) Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)) (tuple2 (tuple2 Bool Bool) Bool)))))
  (! (= (tb2t87 (t2tb87 i)) i) :pattern ((t2tb87 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb87 (tb2t87 j)) j) :pattern ((t2tb87 (tb2t87 j))) )))

(declare-fun t2tb88 ((tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)) (tuple2 (tuple2 Bool Bool) Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)) (tuple2 (tuple2 Bool Bool) Bool)))) (sort
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 bool bool) bool)) (t2tb88 x))))

(declare-fun tb2t88 (uni) (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (tuple2 (tuple2 Bool Bool) Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)) (tuple2 (tuple2 Bool Bool) Bool))))
  (! (= (tb2t88 (t2tb88 i)) i) :pattern ((t2tb88 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb88 (tb2t88 j)) j) :pattern ((t2tb88 (tb2t88 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))) (y (tuple2 (tuple2 Bool Bool) Bool))) (! (mem
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 bool bool) bool)))
  (add
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 bool bool) bool))
  (Tuple2
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 bool bool) bool) (t2tb8 x) (t2tb10 y))
  (empty
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 bool bool) bool))))
  (infix_mnmngt (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb8 x) (t2tb4 empty4))
  (add (tuple21 (tuple21 bool bool) bool) (t2tb10 y) (t2tb6 empty6)))) :pattern (
  (tb2t87
  (add
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 bool bool) bool))
  (Tuple2
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 bool bool) bool) (t2tb8 x) (t2tb10 y))
  (empty
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 bool bool) bool)))))) )))

(declare-fun t2tb89 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) (set Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (set Int)))))) (sort
  (set1
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (set1 int)))) (t2tb89 x))))

(declare-fun tb2t89 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) (set Int)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (set Int))))))
  (! (= (tb2t89 (t2tb89 i)) i) :pattern ((t2tb89 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb89 (tb2t89 j)) j) :pattern ((t2tb89 (tb2t89 j))) )))

(declare-fun t2tb90 ((set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (set Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)) (set Int))))) (sort
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (set1 int))) (t2tb90 x))))

(declare-fun tb2t90 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) (set Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)) (set Int)))))
  (! (= (tb2t90 (t2tb90 i)) i) :pattern ((t2tb90 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb90 (tb2t90 j)) j) :pattern ((t2tb90 (tb2t90 j))) )))

(declare-fun t2tb91 ((tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)) (set Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)) (set Int)))) (sort
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (set1 int)) (t2tb91 x))))

(declare-fun tb2t91 (uni) (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (set Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)) (set Int))))
  (! (= (tb2t91 (t2tb91 i)) i) :pattern ((t2tb91 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb91 (tb2t91 j)) j) :pattern ((t2tb91 (tb2t91 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))) (y (set Int))) (! (mem
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (set1 int)))
  (add
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (set1 int))
  (Tuple2
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (set1 int) (t2tb8 x) (t2tb3 y))
  (empty
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (set1 int))))
  (infix_mnmngt (set1 int)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb8 x) (t2tb4 empty4)) (t2tb1 (add3 y empty3)))) :pattern ((tb2t90
                                                                (add
                                                                (tuple21
                                                                (tuple21
                                                                (tuple21
                                                                (tuple21
                                                                (tuple21 
                                                                bool 
                                                                bool) 
                                                                bool) 
                                                                bool)
                                                                (set1 int))
                                                                (set1 int))
                                                                (Tuple2
                                                                (tuple21
                                                                (tuple21
                                                                (tuple21
                                                                (tuple21 
                                                                bool 
                                                                bool) 
                                                                bool) 
                                                                bool)
                                                                (set1 int))
                                                                (set1 int)
                                                                (t2tb8 x)
                                                                (t2tb3 y))
                                                                (empty
                                                                (tuple21
                                                                (tuple21
                                                                (tuple21
                                                                (tuple21
                                                                (tuple21 
                                                                bool 
                                                                bool) 
                                                                bool) 
                                                                bool)
                                                                (set1 int))
                                                                (set1 int)))))) )))

(declare-fun t2tb92 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) (tuple2 Bool Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (tuple2 Bool Bool)))))) (sort
  (set1
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 bool bool)))) (t2tb92 x))))

(declare-fun tb2t92 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) (tuple2 Bool Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (tuple2 Bool Bool))))))
  (! (= (tb2t92 (t2tb92 i)) i) :pattern ((t2tb92 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb92 (tb2t92 j)) j) :pattern ((t2tb92 (tb2t92 j))) )))

(declare-fun t2tb93 ((set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (tuple2 Bool Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)) (tuple2 Bool Bool))))) (sort
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 bool bool))) (t2tb93 x))))

(declare-fun tb2t93 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) (tuple2 Bool Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)) (tuple2 Bool Bool)))))
  (! (= (tb2t93 (t2tb93 i)) i) :pattern ((t2tb93 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb93 (tb2t93 j)) j) :pattern ((t2tb93 (tb2t93 j))) )))

(declare-fun t2tb94 ((tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)) (tuple2 Bool Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)) (tuple2 Bool Bool)))) (sort
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 bool bool)) (t2tb94 x))))

(declare-fun tb2t94 (uni) (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (tuple2 Bool Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)) (tuple2 Bool Bool))))
  (! (= (tb2t94 (t2tb94 i)) i) :pattern ((t2tb94 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb94 (tb2t94 j)) j) :pattern ((t2tb94 (tb2t94 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))) (y (tuple2 Bool Bool))) (! (mem
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 bool bool)))
  (add
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 bool bool))
  (Tuple2
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 bool bool) (t2tb8 x) (t2tb11 y))
  (empty
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 bool bool))))
  (infix_mnmngt (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb8 x) (t2tb4 empty4))
  (add (tuple21 bool bool) (t2tb11 y) (t2tb7 empty7)))) :pattern ((tb2t93
                                                                  (add
                                                                  (tuple21
                                                                  (tuple21
                                                                  (tuple21
                                                                  (tuple21
                                                                  (tuple21
                                                                  bool 
                                                                  bool) 
                                                                  bool) 
                                                                  bool)
                                                                  (set1 int))
                                                                  (tuple21
                                                                  bool 
                                                                  bool))
                                                                  (Tuple2
                                                                  (tuple21
                                                                  (tuple21
                                                                  (tuple21
                                                                  (tuple21
                                                                  bool 
                                                                  bool) 
                                                                  bool) 
                                                                  bool)
                                                                  (set1 int))
                                                                  (tuple21
                                                                  bool 
                                                                  bool)
                                                                  (t2tb8 x)
                                                                  (t2tb11 y))
                                                                  (empty
                                                                  (tuple21
                                                                  (tuple21
                                                                  (tuple21
                                                                  (tuple21
                                                                  (tuple21
                                                                  bool 
                                                                  bool) 
                                                                  bool) 
                                                                  bool)
                                                                  (set1 int))
                                                                  (tuple21
                                                                  bool 
                                                                  bool)))))) )))

(declare-fun t2tb95 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) Bool))))) (sort
  (set1
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  bool))) (t2tb95 x))))

(declare-fun tb2t95 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) Bool))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) Bool)))))
  (! (= (tb2t95 (t2tb95 i)) i) :pattern ((t2tb95 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb95 (tb2t95 j)) j) :pattern ((t2tb95 (tb2t95 j))) )))

(declare-fun t2tb96 ((set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)) Bool)))) (sort
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  bool)) (t2tb96 x))))

(declare-fun tb2t96 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) Bool)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)) Bool))))
  (! (= (tb2t96 (t2tb96 i)) i) :pattern ((t2tb96 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb96 (tb2t96 j)) j) :pattern ((t2tb96 (tb2t96 j))) )))

(declare-fun t2tb97 ((tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)) Bool)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)) Bool))) (sort
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  bool) (t2tb97 x))))

(declare-fun tb2t97 (uni) (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) Bool))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)) Bool))) (! (= (tb2t97 (t2tb97 i)) i) :pattern ((t2tb97 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb97 (tb2t97 j)) j) :pattern ((t2tb97 (tb2t97 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))) (y Bool)) (! (mem
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  bool))
  (add
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  bool)
  (Tuple2
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)) 
  bool (t2tb8 x) (t2tb12 y))
  (empty
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  bool)))
  (infix_mnmngt bool
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb8 x) (t2tb4 empty4)) (t2tb2 (add1 y empty1)))) :pattern ((tb2t96
                                                                (add
                                                                (tuple21
                                                                (tuple21
                                                                (tuple21
                                                                (tuple21
                                                                (tuple21 
                                                                bool 
                                                                bool) 
                                                                bool) 
                                                                bool)
                                                                (set1 int))
                                                                bool)
                                                                (Tuple2
                                                                (tuple21
                                                                (tuple21
                                                                (tuple21
                                                                (tuple21 
                                                                bool 
                                                                bool) 
                                                                bool) 
                                                                bool)
                                                                (set1 int))
                                                                bool
                                                                (t2tb8 x)
                                                                (t2tb12 y))
                                                                (empty
                                                                (tuple21
                                                                (tuple21
                                                                (tuple21
                                                                (tuple21
                                                                (tuple21 
                                                                bool 
                                                                bool) 
                                                                bool) 
                                                                bool)
                                                                (set1 int))
                                                                bool))))) )))

(declare-fun t2tb98 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) Int))))) (sort
  (set1
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)) 
  int))) (t2tb98 x))))

(declare-fun tb2t98 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) Int))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) Int)))))
  (! (= (tb2t98 (t2tb98 i)) i) :pattern ((t2tb98 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb98 (tb2t98 j)) j) :pattern ((t2tb98 (tb2t98 j))) )))

(declare-fun t2tb99 ((set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)) Int)))) (sort
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)) 
  int)) (t2tb99 x))))

(declare-fun tb2t99 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)) Int))))
  (! (= (tb2t99 (t2tb99 i)) i) :pattern ((t2tb99 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb99 (tb2t99 j)) j) :pattern ((t2tb99 (tb2t99 j))) )))

(declare-fun t2tb100 ((tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) Int)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)) Int))) (sort
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)) 
  int) (t2tb100 x))))

(declare-fun tb2t100 (uni) (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) Int))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)) Int))) (! (= (tb2t100 (t2tb100 i)) i) :pattern ((t2tb100 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb100 (tb2t100 j)) j) :pattern ((t2tb100 (tb2t100 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))) (y Int)) (! (mem
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)) 
  int))
  (add
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)) 
  int)
  (Tuple2
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)) 
  int (t2tb8 x) (t2tb13 y))
  (empty
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)) 
  int)))
  (infix_mnmngt int
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb8 x) (t2tb4 empty4)) (t2tb3 (add2 y empty2)))) :pattern ((tb2t99
                                                                (add
                                                                (tuple21
                                                                (tuple21
                                                                (tuple21
                                                                (tuple21
                                                                (tuple21 
                                                                bool 
                                                                bool) 
                                                                bool) 
                                                                bool)
                                                                (set1 int))
                                                                int)
                                                                (Tuple2
                                                                (tuple21
                                                                (tuple21
                                                                (tuple21
                                                                (tuple21 
                                                                bool 
                                                                bool) 
                                                                bool) 
                                                                bool)
                                                                (set1 int))
                                                                int (t2tb8 x)
                                                                (t2tb13 y))
                                                                (empty
                                                                (tuple21
                                                                (tuple21
                                                                (tuple21
                                                                (tuple21
                                                                (tuple21 
                                                                bool 
                                                                bool) 
                                                                bool) 
                                                                bool)
                                                                (set1 int))
                                                                int))))) )))

;; singleton_is_function
  (assert
  (forall ((b ty))
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))) (y uni)) (! (mem
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)) b))
  (add
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)) b)
  (Tuple2
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)) b
  (t2tb8 x) y)
  (empty
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)) b)))
  (infix_mnmngt b
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb8 x) (t2tb4 empty4)) (add b y (empty b)))) :pattern ((add
                                                            (tuple21
                                                            (tuple21
                                                            (tuple21
                                                            (tuple21
                                                            (tuple21 
                                                            bool bool) 
                                                            bool) bool)
                                                            (set1 int)) b)
                                                            (Tuple2
                                                            (tuple21
                                                            (tuple21
                                                            (tuple21
                                                            (tuple21 
                                                            bool bool) 
                                                            bool) bool)
                                                            (set1 int)) b
                                                            (t2tb8 x) y)
                                                            (empty
                                                            (tuple21
                                                            (tuple21
                                                            (tuple21
                                                            (tuple21
                                                            (tuple21 
                                                            bool bool) 
                                                            bool) bool)
                                                            (set1 int)) b)))) ))))

(declare-fun t2tb101 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))))
  (t2tb101 x))))

(declare-fun tb2t101 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))))) (! (= (tb2t101 (t2tb101 i)) i) :pattern ((t2tb101 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb101 (tb2t101 j)) j) :pattern ((t2tb101 (tb2t101 j))) )))

(declare-fun t2tb102 ((set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))))
  (sort
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (t2tb102 x))))

(declare-fun tb2t102 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))))
  (! (= (tb2t102 (t2tb102 i)) i) :pattern ((t2tb102 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb102 (tb2t102 j)) j) :pattern ((t2tb102 (tb2t102 j))) )))

(declare-fun t2tb103 ((tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))))
  (sort
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (t2tb103 x))))

(declare-fun tb2t103 (uni) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))))
  (! (= (tb2t103 (t2tb103 i)) i) :pattern ((t2tb103 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb103 (tb2t103 j)) j) :pattern ((t2tb103 (tb2t103 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (! (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb9 x) (t2tb4 y))
  (empty
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))))
  (infix_mnmngt
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (add (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
  (t2tb5 empty5)) (t2tb (add4 y empty8)))) :pattern ((tb2t102
                                                     (add
                                                     (tuple21
                                                     (tuple21
                                                     (tuple21
                                                     (tuple21 bool bool)
                                                     bool) bool)
                                                     (set1
                                                     (tuple21
                                                     (tuple21
                                                     (tuple21
                                                     (tuple21 bool bool)
                                                     bool) bool) (set1 int))))
                                                     (Tuple2
                                                     (tuple21
                                                     (tuple21
                                                     (tuple21 bool bool)
                                                     bool) bool)
                                                     (set1
                                                     (tuple21
                                                     (tuple21
                                                     (tuple21
                                                     (tuple21 bool bool)
                                                     bool) bool) (set1 int)))
                                                     (t2tb9 x) (t2tb4 y))
                                                     (empty
                                                     (tuple21
                                                     (tuple21
                                                     (tuple21
                                                     (tuple21 bool bool)
                                                     bool) bool)
                                                     (set1
                                                     (tuple21
                                                     (tuple21
                                                     (tuple21
                                                     (tuple21 bool bool)
                                                     bool) bool) (set1 int)))))))) )))

(declare-fun t2tb104 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (t2tb104 x))))

(declare-fun tb2t104 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))))) (! (= (tb2t104 (t2tb104 i)) i) :pattern ((t2tb104 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb104 (tb2t104 j)) j) :pattern ((t2tb104 (tb2t104 j))) )))

(declare-fun t2tb105 ((set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))) (sort
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (t2tb105 x))))

(declare-fun tb2t105 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))))
  (! (= (tb2t105 (t2tb105 i)) i) :pattern ((t2tb105 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb105 (tb2t105 j)) j) :pattern ((t2tb105 (tb2t105 j))) )))

(declare-fun t2tb106 ((tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))) (sort
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb106 x))))

(declare-fun tb2t106 (uni) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))
  (! (= (tb2t106 (t2tb106 i)) i) :pattern ((t2tb106 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb106 (tb2t106 j)) j) :pattern ((t2tb106 (tb2t106 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (y (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))
  (! (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb9 x) (t2tb8 y))
  (empty
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (infix_mnmngt
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (add (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
  (t2tb5 empty5))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb8 y) (t2tb4 empty4)))) :pattern ((tb2t105
                                        (add
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool)
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int)))
                                        (Tuple2
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool)
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int)) (t2tb9 x)
                                        (t2tb8 y))
                                        (empty
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool)
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int))))))) )))

(declare-fun t2tb107 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))) (t2tb107 x))))

(declare-fun tb2t107 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))))
  (! (= (tb2t107 (t2tb107 i)) i) :pattern ((t2tb107 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))) j)
     (= (t2tb107 (tb2t107 j)) j)) :pattern ((t2tb107 (tb2t107 j))) )))

(declare-fun t2tb108 ((set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))) (sort
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))) (t2tb108 x))))

(declare-fun tb2t108 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))))
  (! (= (tb2t108 (t2tb108 i)) i) :pattern ((t2tb108 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool))) j)
     (= (t2tb108 (tb2t108 j)) j)) :pattern ((t2tb108 (tb2t108 j))) )))

(declare-fun t2tb109 ((tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))) (sort
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb109 x))))

(declare-fun tb2t109 (uni) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (! (= (tb2t109 (t2tb109 i)) i) :pattern ((t2tb109 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) j)
     (= (t2tb109 (tb2t109 j)) j)) :pattern ((t2tb109 (tb2t109 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (y (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))) (! (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x) (t2tb9 y))
  (empty
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))))
  (infix_mnmngt (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (add (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
  (t2tb5 empty5))
  (add (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 y)
  (t2tb5 empty5)))) :pattern ((tb2t108
                              (add
                              (tuple21
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool)
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool))
                              (Tuple2
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool)
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool) (t2tb9 x) (t2tb9 y))
                              (empty
                              (tuple21
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool)
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool)))))) )))

(declare-fun t2tb110 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (tuple2 (tuple2 Bool Bool) Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (tuple2 (tuple2 Bool Bool) Bool)))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 bool bool) bool)))) (t2tb110 x))))

(declare-fun tb2t110 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (tuple2 (tuple2 Bool Bool) Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (tuple2 (tuple2 Bool Bool) Bool))))))
  (! (= (tb2t110 (t2tb110 i)) i) :pattern ((t2tb110 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (tuple21 (tuple21 bool bool) bool)))) j) (= (t2tb110 (tb2t110 j)) j)) :pattern (
  (t2tb110 (tb2t110 j))) )))

(declare-fun t2tb111 ((set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (tuple2 (tuple2 Bool Bool) Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 (tuple2 Bool Bool) Bool))))) (sort
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 bool bool) bool))) (t2tb111 x))))

(declare-fun tb2t111 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (tuple2 (tuple2 Bool Bool) Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 (tuple2 Bool Bool) Bool)))))
  (! (= (tb2t111 (t2tb111 i)) i) :pattern ((t2tb111 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (tuple21 (tuple21 bool bool) bool))) j) (= (t2tb111 (tb2t111 j)) j)) :pattern (
  (t2tb111 (tb2t111 j))) )))

(declare-fun t2tb112 ((tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 (tuple2 Bool Bool) Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 (tuple2 Bool Bool) Bool)))) (sort
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 bool bool) bool)) (t2tb112 x))))

(declare-fun tb2t112 (uni) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (tuple2 (tuple2 Bool Bool) Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 (tuple2 Bool Bool) Bool))))
  (! (= (tb2t112 (t2tb112 i)) i) :pattern ((t2tb112 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (tuple21 (tuple21 bool bool) bool)) j) (= (t2tb112 (tb2t112 j)) j)) :pattern (
  (t2tb112 (tb2t112 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (y (tuple2 (tuple2 Bool Bool) Bool))) (! (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 bool bool) bool)))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 bool bool) bool))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 bool bool) bool) (t2tb9 x) (t2tb10 y))
  (empty
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 bool bool) bool))))
  (infix_mnmngt (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (add (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
  (t2tb5 empty5))
  (add (tuple21 (tuple21 bool bool) bool) (t2tb10 y) (t2tb6 empty6)))) :pattern (
  (tb2t111
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 bool bool) bool))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 bool bool) bool) (t2tb9 x) (t2tb10 y))
  (empty
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 bool bool) bool)))))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)) (y (set Int)))
  (! (mem4
  (tb2t4
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb9 x) (t2tb3 y)) (t2tb4 empty4)))
  (tb2t
  (infix_mnmngt (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (add (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
  (t2tb5 empty5)) (t2tb1 (add3 y empty3))))) :pattern ((tb2t4
                                                       (add
                                                       (tuple21
                                                       (tuple21
                                                       (tuple21
                                                       (tuple21 bool bool)
                                                       bool) bool)
                                                       (set1 int))
                                                       (Tuple2
                                                       (tuple21
                                                       (tuple21
                                                       (tuple21 bool bool)
                                                       bool) bool) (set1 int)
                                                       (t2tb9 x) (t2tb3 y))
                                                       (t2tb4 empty4)))) )))

(declare-fun t2tb113 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (tuple2 Bool Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (tuple2 Bool Bool)))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 bool bool)))) (t2tb113 x))))

(declare-fun tb2t113 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (tuple2 Bool Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (tuple2 Bool Bool))))))
  (! (= (tb2t113 (t2tb113 i)) i) :pattern ((t2tb113 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (tuple21 bool bool)))) j) (= (t2tb113 (tb2t113 j)) j)) :pattern (
  (t2tb113 (tb2t113 j))) )))

(declare-fun t2tb114 ((set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (tuple2 Bool Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 Bool Bool))))) (sort
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 bool bool))) (t2tb114 x))))

(declare-fun tb2t114 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (tuple2 Bool Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 Bool Bool)))))
  (! (= (tb2t114 (t2tb114 i)) i) :pattern ((t2tb114 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (tuple21 bool bool))) j) (= (t2tb114 (tb2t114 j)) j)) :pattern (
  (t2tb114 (tb2t114 j))) )))

(declare-fun t2tb115 ((tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 Bool Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 Bool Bool)))) (sort
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 bool bool)) (t2tb115 x))))

(declare-fun tb2t115 (uni) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (tuple2 Bool Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 Bool Bool))))
  (! (= (tb2t115 (t2tb115 i)) i) :pattern ((t2tb115 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (tuple21 bool bool)) j) (= (t2tb115 (tb2t115 j)) j)) :pattern ((t2tb115
                                                                    (tb2t115
                                                                    j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)) (y (tuple2 Bool
  Bool))) (! (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 bool bool)))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 bool bool))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 bool bool) (t2tb9 x) (t2tb11 y))
  (empty
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 bool bool))))
  (infix_mnmngt (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (add (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
  (t2tb5 empty5)) (add (tuple21 bool bool) (t2tb11 y) (t2tb7 empty7)))) :pattern (
  (tb2t114
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 bool bool))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 bool bool) (t2tb9 x) (t2tb11 y))
  (empty
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 bool bool)))))) )))

(declare-fun t2tb116 ((set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  Bool)))) (sort
  (set1 (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) bool))
  (t2tb116 x))))

(declare-fun tb2t116 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) Bool)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  Bool)))) (! (= (tb2t116 (t2tb116 i)) i) :pattern ((t2tb116 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1 (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) bool))
     j) (= (t2tb116 (tb2t116 j)) j)) :pattern ((t2tb116 (tb2t116 j))) )))

(declare-fun t2tb117 ((tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  Bool)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) Bool)))
  (sort (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) bool)
  (t2tb117 x))))

(declare-fun tb2t117 (uni) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) Bool))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) Bool)))
  (! (= (tb2t117 (t2tb117 i)) i) :pattern ((t2tb117 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) bool) j)
     (= (t2tb117 (tb2t117 j)) j)) :pattern ((t2tb117 (tb2t117 j))) )))

(declare-fun t2tb118 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) Bool))))) (sort
  (set1
  (set1 (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) bool)))
  (t2tb118 x))))

(declare-fun tb2t118 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) Bool))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) Bool))))) (! (= (tb2t118 (t2tb118 i)) i) :pattern ((t2tb118 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1 (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) bool)))
     j) (= (t2tb118 (tb2t118 j)) j)) :pattern ((t2tb118 (tb2t118 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)) (y Bool))
  (! (mem
  (set1 (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) bool))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) bool)
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) bool (t2tb9 x)
  (t2tb12 y))
  (empty (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) bool)))
  (infix_mnmngt bool (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (add (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
  (t2tb5 empty5)) (t2tb2 (add1 y empty1)))) :pattern ((tb2t116
                                                      (add
                                                      (tuple21
                                                      (tuple21
                                                      (tuple21
                                                      (tuple21 bool bool)
                                                      bool) bool) bool)
                                                      (Tuple2
                                                      (tuple21
                                                      (tuple21
                                                      (tuple21 bool bool)
                                                      bool) bool) bool
                                                      (t2tb9 x) (t2tb12 y))
                                                      (empty
                                                      (tuple21
                                                      (tuple21
                                                      (tuple21
                                                      (tuple21 bool bool)
                                                      bool) bool) bool))))) )))

(declare-fun t2tb119 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) Int))))) (sort
  (set1
  (set1 (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) int)))
  (t2tb119 x))))

(declare-fun tb2t119 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) Int))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) Int))))) (! (= (tb2t119 (t2tb119 i)) i) :pattern ((t2tb119 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb119 (tb2t119 j)) j) :pattern ((t2tb119 (tb2t119 j))) )))

(declare-fun t2tb120 ((set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  Int)))) (sort
  (set1 (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) int))
  (t2tb120 x))))

(declare-fun tb2t120 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  Int)))) (! (= (tb2t120 (t2tb120 i)) i) :pattern ((t2tb120 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb120 (tb2t120 j)) j) :pattern ((t2tb120 (tb2t120 j))) )))

(declare-fun t2tb121 ((tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  Int)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) Int)))
  (sort (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) int)
  (t2tb121 x))))

(declare-fun tb2t121 (uni) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) Int))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) Int)))
  (! (= (tb2t121 (t2tb121 i)) i) :pattern ((t2tb121 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb121 (tb2t121 j)) j) :pattern ((t2tb121 (tb2t121 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)) (y Int))
  (! (mem
  (set1 (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) int))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) int)
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) int (t2tb9 x)
  (t2tb13 y))
  (empty (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) int)))
  (infix_mnmngt int (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (add (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
  (t2tb5 empty5)) (t2tb3 (add2 y empty2)))) :pattern ((tb2t120
                                                      (add
                                                      (tuple21
                                                      (tuple21
                                                      (tuple21
                                                      (tuple21 bool bool)
                                                      bool) bool) int)
                                                      (Tuple2
                                                      (tuple21
                                                      (tuple21
                                                      (tuple21 bool bool)
                                                      bool) bool) int
                                                      (t2tb9 x) (t2tb13 y))
                                                      (empty
                                                      (tuple21
                                                      (tuple21
                                                      (tuple21
                                                      (tuple21 bool bool)
                                                      bool) bool) int))))) )))

;; singleton_is_function
  (assert
  (forall ((b ty))
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)) (y uni))
  (! (mem
  (set1 (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) b))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) b)
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) b (t2tb9 x) y)
  (empty (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) b)))
  (infix_mnmngt b (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (add (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
  (t2tb5 empty5)) (add b y (empty b)))) :pattern ((add
                                                  (tuple21
                                                  (tuple21
                                                  (tuple21
                                                  (tuple21 bool bool) 
                                                  bool) bool) b)
                                                  (Tuple2
                                                  (tuple21
                                                  (tuple21
                                                  (tuple21 bool bool) 
                                                  bool) bool) b (t2tb9 x) y)
                                                  (empty
                                                  (tuple21
                                                  (tuple21
                                                  (tuple21
                                                  (tuple21 bool bool) 
                                                  bool) bool) b)))) ))))

(declare-fun t2tb122 ((set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))))
  (t2tb122 x))))

(declare-fun tb2t122 (uni) (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))))) (! (= (tb2t122 (t2tb122 i)) i) :pattern ((t2tb122 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb122 (tb2t122 j)) j) :pattern ((t2tb122 (tb2t122 j))) )))

(declare-fun t2tb123 ((set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))))
  (sort
  (set1
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (t2tb123 x))))

(declare-fun tb2t123 (uni) (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))))
  (! (= (tb2t123 (t2tb123 i)) i) :pattern ((t2tb123 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb123 (tb2t123 j)) j) :pattern ((t2tb123 (tb2t123 j))) )))

(declare-fun t2tb124 ((tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))))
  (sort
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (t2tb124 x))))

(declare-fun tb2t124 (uni) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))))
  (! (= (tb2t124 (t2tb124 i)) i) :pattern ((t2tb124 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb124 (tb2t124 j)) j) :pattern ((t2tb124 (tb2t124 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool))
  (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (! (mem
  (set1
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (add
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2 (tuple21 (tuple21 bool bool) bool)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb10 x) (t2tb4 y))
  (empty
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))))
  (infix_mnmngt
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (tuple21 (tuple21 bool bool) bool)
  (add (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb6 empty6))
  (t2tb (add4 y empty8)))) :pattern ((tb2t123
                                     (add
                                     (tuple21
                                     (tuple21 (tuple21 bool bool) bool)
                                     (set1
                                     (tuple21
                                     (tuple21
                                     (tuple21 (tuple21 bool bool) bool) 
                                     bool) (set1 int))))
                                     (Tuple2
                                     (tuple21 (tuple21 bool bool) bool)
                                     (set1
                                     (tuple21
                                     (tuple21
                                     (tuple21 (tuple21 bool bool) bool) 
                                     bool) (set1 int))) (t2tb10 x) (t2tb4 y))
                                     (empty
                                     (tuple21
                                     (tuple21 (tuple21 bool bool) bool)
                                     (set1
                                     (tuple21
                                     (tuple21
                                     (tuple21 (tuple21 bool bool) bool) 
                                     bool) (set1 int)))))))) )))

(declare-fun t2tb125 ((set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))))
  (sort
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (t2tb125 x))))

(declare-fun tb2t125 (uni) (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))))
  (! (= (tb2t125 (t2tb125 i)) i) :pattern ((t2tb125 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb125 (tb2t125 j)) j) :pattern ((t2tb125 (tb2t125 j))) )))

(declare-fun t2tb126 ((set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))) (sort
  (set1
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (t2tb126 x))))

(declare-fun tb2t126 (uni) (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))))
  (! (= (tb2t126 (t2tb126 i)) i) :pattern ((t2tb126 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb126 (tb2t126 j)) j) :pattern ((t2tb126 (tb2t126 j))) )))

(declare-fun t2tb127 ((tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))) (sort
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb127 x))))

(declare-fun tb2t127 (uni) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))
  (! (= (tb2t127 (t2tb127 i)) i) :pattern ((t2tb127 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb127 (tb2t127 j)) j) :pattern ((t2tb127 (tb2t127 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool))
  (y (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))
  (! (mem
  (set1
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (add
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (Tuple2 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb10 x) (t2tb8 y))
  (empty
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (infix_mnmngt
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 bool bool) bool)
  (add (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb6 empty6))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb8 y) (t2tb4 empty4)))) :pattern ((tb2t126
                                        (add
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int)))
                                        (Tuple2
                                        (tuple21 (tuple21 bool bool) bool)
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int)) (t2tb10 x)
                                        (t2tb8 y))
                                        (empty
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int))))))) )))

(declare-fun t2tb128 ((set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))) (t2tb128 x))))

(declare-fun tb2t128 (uni) (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))))
  (! (= (tb2t128 (t2tb128 i)) i) :pattern ((t2tb128 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21 (tuple21 (tuple21 bool bool) bool)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))) j)
     (= (t2tb128 (tb2t128 j)) j)) :pattern ((t2tb128 (tb2t128 j))) )))

(declare-fun t2tb129 ((set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))) (sort
  (set1
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))) (t2tb129 x))))

(declare-fun tb2t129 (uni) (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))))
  (! (= (tb2t129 (t2tb129 i)) i) :pattern ((t2tb129 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21 (tuple21 (tuple21 bool bool) bool)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool))) j)
     (= (t2tb129 (tb2t129 j)) j)) :pattern ((t2tb129 (tb2t129 j))) )))

(declare-fun t2tb130 ((tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))) (sort
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb130 x))))

(declare-fun tb2t130 (uni) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (! (= (tb2t130 (t2tb130 i)) i) :pattern ((t2tb130 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 (tuple21 (tuple21 bool bool) bool)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) j)
     (= (t2tb130 (tb2t130 j)) j)) :pattern ((t2tb130 (tb2t130 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool))
  (y (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))) (! (mem
  (set1
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))
  (add
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (Tuple2 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb10 x) (t2tb9 y))
  (empty
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))))
  (infix_mnmngt (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 bool bool) bool)
  (add (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb6 empty6))
  (add (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 y)
  (t2tb5 empty5)))) :pattern ((tb2t129
                              (add
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool))
                              (Tuple2 (tuple21 (tuple21 bool bool) bool)
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool) (t2tb10 x) (t2tb9 y))
                              (empty
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool)))))) )))

(declare-fun t2tb131 ((set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 Bool Bool) Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 Bool Bool) Bool))))) (sort
  (set1
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 bool bool) bool))) (t2tb131 x))))

(declare-fun tb2t131 (uni) (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 Bool Bool) Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 Bool Bool) Bool)))))
  (! (= (tb2t131 (t2tb131 i)) i) :pattern ((t2tb131 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21 (tuple21 (tuple21 bool bool) bool)
     (tuple21 (tuple21 bool bool) bool))) j) (= (t2tb131 (tb2t131 j)) j)) :pattern (
  (t2tb131 (tb2t131 j))) )))

(declare-fun t2tb132 ((tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 Bool Bool) Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) (tuple2 (tuple2 Bool
  Bool) Bool)))) (sort
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 bool bool) bool)) (t2tb132 x))))

(declare-fun tb2t132 (uni) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 Bool Bool) Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 Bool Bool) Bool) (tuple2 (tuple2 Bool
  Bool) Bool)))) (! (= (tb2t132 (t2tb132 i)) i) :pattern ((t2tb132 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 (tuple21 (tuple21 bool bool) bool)
     (tuple21 (tuple21 bool bool) bool)) j) (= (t2tb132 (tb2t132 j)) j)) :pattern (
  (t2tb132 (tb2t132 j))) )))

(declare-fun t2tb133 ((set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 Bool Bool) Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 Bool Bool) Bool)))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 bool bool) bool)))) (t2tb133 x))))

(declare-fun tb2t133 (uni) (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 Bool Bool) Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 Bool Bool) Bool))))))
  (! (= (tb2t133 (t2tb133 i)) i) :pattern ((t2tb133 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21 (tuple21 (tuple21 bool bool) bool)
     (tuple21 (tuple21 bool bool) bool)))) j) (= (t2tb133 (tb2t133 j)) j)) :pattern (
  (t2tb133 (tb2t133 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)) (y (tuple2 (tuple2 Bool Bool)
  Bool))) (! (mem
  (set1
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 bool bool) bool)))
  (add
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 bool bool) bool))
  (Tuple2 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb10 y))
  (empty
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 bool bool) bool))))
  (infix_mnmngt (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 bool bool) bool)
  (add (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb6 empty6))
  (add (tuple21 (tuple21 bool bool) bool) (t2tb10 y) (t2tb6 empty6)))) :pattern (
  (tb2t131
  (add
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 bool bool) bool))
  (Tuple2 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb10 y))
  (empty
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 bool bool) bool)))))) )))

(declare-fun t2tb134 ((set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (set Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (set Int)))))) (sort
  (set1 (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) (set1 int))))
  (t2tb134 x))))

(declare-fun tb2t134 (uni) (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (set Int)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (set Int)))))) (! (= (tb2t134 (t2tb134 i)) i) :pattern ((t2tb134 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb134 (tb2t134 j)) j) :pattern ((t2tb134 (tb2t134 j))) )))

(declare-fun t2tb135 ((set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (set Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) (set Int)))))
  (sort (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) (set1 int)))
  (t2tb135 x))))

(declare-fun tb2t135 (uni) (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (set Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) (set Int)))))
  (! (= (tb2t135 (t2tb135 i)) i) :pattern ((t2tb135 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb135 (tb2t135 j)) j) :pattern ((t2tb135 (tb2t135 j))) )))

(declare-fun t2tb136 ((tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (set Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) (set Int)))) (sort
  (tuple21 (tuple21 (tuple21 bool bool) bool) (set1 int)) (t2tb136 x))))

(declare-fun tb2t136 (uni) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (set Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 Bool Bool) Bool) (set Int))))
  (! (= (tb2t136 (t2tb136 i)) i) :pattern ((t2tb136 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb136 (tb2t136 j)) j) :pattern ((t2tb136 (tb2t136 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)) (y (set Int))) (! (mem
  (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) (set1 int)))
  (add (tuple21 (tuple21 (tuple21 bool bool) bool) (set1 int))
  (Tuple2 (tuple21 (tuple21 bool bool) bool) (set1 int) (t2tb10 x) (t2tb3 y))
  (empty (tuple21 (tuple21 (tuple21 bool bool) bool) (set1 int))))
  (infix_mnmngt (set1 int) (tuple21 (tuple21 bool bool) bool)
  (add (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb6 empty6))
  (t2tb1 (add3 y empty3)))) :pattern ((tb2t135
                                      (add
                                      (tuple21
                                      (tuple21 (tuple21 bool bool) bool)
                                      (set1 int))
                                      (Tuple2
                                      (tuple21 (tuple21 bool bool) bool)
                                      (set1 int) (t2tb10 x) (t2tb3 y))
                                      (empty
                                      (tuple21
                                      (tuple21 (tuple21 bool bool) bool)
                                      (set1 int)))))) )))

(declare-fun t2tb137 ((set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 Bool Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) (tuple2 Bool
  Bool)))))) (sort
  (set1
  (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool))))
  (t2tb137 x))))

(declare-fun tb2t137 (uni) (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 Bool Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) (tuple2 Bool
  Bool)))))) (! (= (tb2t137 (t2tb137 i)) i) :pattern ((t2tb137 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool))))
     j) (= (t2tb137 (tb2t137 j)) j)) :pattern ((t2tb137 (tb2t137 j))) )))

(declare-fun t2tb138 ((set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 Bool Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) (tuple2 Bool
  Bool))))) (sort
  (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool)))
  (t2tb138 x))))

(declare-fun tb2t138 (uni) (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 Bool Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) (tuple2 Bool
  Bool))))) (! (= (tb2t138 (t2tb138 i)) i) :pattern ((t2tb138 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool)))
     j) (= (t2tb138 (tb2t138 j)) j)) :pattern ((t2tb138 (tb2t138 j))) )))

(declare-fun t2tb139 ((tuple2 (tuple2 (tuple2 Bool Bool) Bool) (tuple2 Bool
  Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) (tuple2 Bool Bool))))
  (sort (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool))
  (t2tb139 x))))

(declare-fun tb2t139 (uni) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 Bool Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 Bool Bool) Bool) (tuple2 Bool Bool))))
  (! (= (tb2t139 (t2tb139 i)) i) :pattern ((t2tb139 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool)) j)
     (= (t2tb139 (tb2t139 j)) j)) :pattern ((t2tb139 (tb2t139 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)) (y (tuple2 Bool Bool)))
  (! (mem
  (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool)))
  (add (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool))
  (Tuple2 (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool) (t2tb10 x)
  (t2tb11 y))
  (empty (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool))))
  (infix_mnmngt (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool)
  (add (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb6 empty6))
  (add (tuple21 bool bool) (t2tb11 y) (t2tb7 empty7)))) :pattern ((tb2t138
                                                                  (add
                                                                  (tuple21
                                                                  (tuple21
                                                                  (tuple21
                                                                  bool 
                                                                  bool) 
                                                                  bool)
                                                                  (tuple21
                                                                  bool 
                                                                  bool))
                                                                  (Tuple2
                                                                  (tuple21
                                                                  (tuple21
                                                                  bool 
                                                                  bool) 
                                                                  bool)
                                                                  (tuple21
                                                                  bool 
                                                                  bool)
                                                                  (t2tb10 x)
                                                                  (t2tb11 y))
                                                                  (empty
                                                                  (tuple21
                                                                  (tuple21
                                                                  (tuple21
                                                                  bool 
                                                                  bool) 
                                                                  bool)
                                                                  (tuple21
                                                                  bool 
                                                                  bool)))))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)) (y Bool)) (! (mem
  (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (add (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (Tuple2 (tuple21 (tuple21 bool bool) bool) bool (t2tb10 x) (t2tb12 y))
  (t2tb5 empty5))
  (infix_mnmngt bool (tuple21 (tuple21 bool bool) bool)
  (add (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb6 empty6))
  (t2tb2 (add1 y empty1)))) :pattern ((tb2t5
                                      (add
                                      (tuple21
                                      (tuple21 (tuple21 bool bool) bool)
                                      bool)
                                      (Tuple2
                                      (tuple21 (tuple21 bool bool) bool) 
                                      bool (t2tb10 x) (t2tb12 y))
                                      (t2tb5 empty5)))) )))

(declare-fun t2tb140 ((set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Int)))))
  (sort (set1 (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) int)))
  (t2tb140 x))))

(declare-fun tb2t140 (uni) (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Int))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Int)))))
  (! (= (tb2t140 (t2tb140 i)) i) :pattern ((t2tb140 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb140 (tb2t140 j)) j) :pattern ((t2tb140 (tb2t140 j))) )))

(declare-fun t2tb141 ((set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Int)))) (sort
  (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) int)) (t2tb141 x))))

(declare-fun tb2t141 (uni) (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Int))))
  (! (= (tb2t141 (t2tb141 i)) i) :pattern ((t2tb141 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb141 (tb2t141 j)) j) :pattern ((t2tb141 (tb2t141 j))) )))

(declare-fun t2tb142 ((tuple2 (tuple2 (tuple2 Bool Bool) Bool) Int)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Int))) (sort
  (tuple21 (tuple21 (tuple21 bool bool) bool) int) (t2tb142 x))))

(declare-fun tb2t142 (uni) (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Int))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Int)))
  (! (= (tb2t142 (t2tb142 i)) i) :pattern ((t2tb142 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb142 (tb2t142 j)) j) :pattern ((t2tb142 (tb2t142 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)) (y Int)) (! (mem
  (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) int))
  (add (tuple21 (tuple21 (tuple21 bool bool) bool) int)
  (Tuple2 (tuple21 (tuple21 bool bool) bool) int (t2tb10 x) (t2tb13 y))
  (empty (tuple21 (tuple21 (tuple21 bool bool) bool) int)))
  (infix_mnmngt int (tuple21 (tuple21 bool bool) bool)
  (add (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb6 empty6))
  (t2tb3 (add2 y empty2)))) :pattern ((tb2t141
                                      (add
                                      (tuple21
                                      (tuple21 (tuple21 bool bool) bool) 
                                      int)
                                      (Tuple2
                                      (tuple21 (tuple21 bool bool) bool) 
                                      int (t2tb10 x) (t2tb13 y))
                                      (empty
                                      (tuple21
                                      (tuple21 (tuple21 bool bool) bool) 
                                      int))))) )))

;; singleton_is_function
  (assert
  (forall ((b ty))
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)) (y uni)) (! (mem
  (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) b))
  (add (tuple21 (tuple21 (tuple21 bool bool) bool) b)
  (Tuple2 (tuple21 (tuple21 bool bool) bool) b (t2tb10 x) y)
  (empty (tuple21 (tuple21 (tuple21 bool bool) bool) b)))
  (infix_mnmngt b (tuple21 (tuple21 bool bool) bool)
  (add (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb6 empty6))
  (add b y (empty b)))) :pattern ((add
                                  (tuple21 (tuple21 (tuple21 bool bool) bool)
                                  b)
                                  (Tuple2 (tuple21 (tuple21 bool bool) bool)
                                  b (t2tb10 x) y)
                                  (empty
                                  (tuple21 (tuple21 (tuple21 bool bool) bool)
                                  b)))) ))))

;; singleton_is_function
  (assert
  (forall ((x (set Int)) (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))) (! (mem
  (set1
  (tuple21 (set1 int)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (add
  (tuple21 (set1 int)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2 (set1 int)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb3 x) (t2tb4 y))
  (empty
  (tuple21 (set1 int)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))))
  (infix_mnmngt
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1 int) (t2tb1 (add3 x empty3)) (t2tb (add4 y empty8)))) :pattern (
  (tb2t33
  (add
  (tuple21 (set1 int)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2 (set1 int)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb3 x) (t2tb4 y))
  (empty
  (tuple21 (set1 int)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))))) )))

(declare-fun t2tb143 ((set (set (tuple2 (set Int)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (set Int)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))))
  (sort
  (set1
  (set1
  (tuple21 (set1 int)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (t2tb143 x))))

(declare-fun tb2t143 (uni) (set (set (tuple2 (set Int)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (set Int)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))))
  (! (= (tb2t143 (t2tb143 i)) i) :pattern ((t2tb143 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb143 (tb2t143 j)) j) :pattern ((t2tb143 (tb2t143 j))) )))

(declare-fun t2tb144 ((set (tuple2 (set Int)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (set Int) (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))))) (sort
  (set1
  (tuple21 (set1 int)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (t2tb144 x))))

(declare-fun tb2t144 (uni) (set (tuple2 (set Int)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (set Int) (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))))
  (! (= (tb2t144 (t2tb144 i)) i) :pattern ((t2tb144 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb144 (tb2t144 j)) j) :pattern ((t2tb144 (tb2t144 j))) )))

(declare-fun t2tb145 ((tuple2 (set Int) (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (set Int) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))) (sort
  (tuple21 (set1 int)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb145 x))))

(declare-fun tb2t145 (uni) (tuple2 (set Int)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))

;; BridgeL
  (assert
  (forall ((i (tuple2 (set Int) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))))
  (! (= (tb2t145 (t2tb145 i)) i) :pattern ((t2tb145 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb145 (tb2t145 j)) j) :pattern ((t2tb145 (tb2t145 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (set Int)) (y (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))) (! (mem
  (set1
  (tuple21 (set1 int)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (add
  (tuple21 (set1 int)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (Tuple2 (set1 int)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb3 x) (t2tb8 y))
  (empty
  (tuple21 (set1 int)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (infix_mnmngt
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (set1 int) (t2tb1 (add3 x empty3))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb8 y) (t2tb4 empty4)))) :pattern ((tb2t144
                                        (add
                                        (tuple21 (set1 int)
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int)))
                                        (Tuple2 (set1 int)
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int)) (t2tb3 x)
                                        (t2tb8 y))
                                        (empty
                                        (tuple21 (set1 int)
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int))))))) )))

(declare-fun t2tb146 ((set (tuple2 (set Int) (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (set Int) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))))) (sort
  (set1
  (tuple21 (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))
  (t2tb146 x))))

(declare-fun tb2t146 (uni) (set (tuple2 (set Int)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (set Int) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))))) (! (= (tb2t146 (t2tb146 i)) i) :pattern ((t2tb146 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb146 (tb2t146 j)) j) :pattern ((t2tb146 (tb2t146 j))) )))

(declare-fun t2tb147 ((tuple2 (set Int) (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (set Int) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool)))) (sort
  (tuple21 (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (t2tb147 x))))

(declare-fun tb2t147 (uni) (tuple2 (set Int) (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (set Int) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool)))) (! (= (tb2t147 (t2tb147 i)) i) :pattern ((t2tb147 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb147 (tb2t147 j)) j) :pattern ((t2tb147 (tb2t147 j))) )))

(declare-fun t2tb148 ((set (set (tuple2 (set Int)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (set Int) (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool)))))) (sort
  (set1
  (set1
  (tuple21 (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool))))
  (t2tb148 x))))

(declare-fun tb2t148 (uni) (set (set (tuple2 (set Int)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (set Int) (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool)))))) (! (= (tb2t148 (t2tb148 i)) i) :pattern ((t2tb148 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb148 (tb2t148 j)) j) :pattern ((t2tb148 (tb2t148 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (set Int)) (y (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (! (mem
  (set1
  (tuple21 (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))
  (add (tuple21 (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (Tuple2 (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb3 x) (t2tb9 y))
  (empty
  (tuple21 (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool))))
  (infix_mnmngt (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb1 (add3 x empty3))
  (add (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 y)
  (t2tb5 empty5)))) :pattern ((tb2t146
                              (add
                              (tuple21 (set1 int)
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool))
                              (Tuple2 (set1 int)
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool) (t2tb3 x) (t2tb9 y))
                              (empty
                              (tuple21 (set1 int)
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool)))))) )))

(declare-fun t2tb149 ((set (set (tuple2 (set Int) (tuple2 (tuple2 Bool Bool)
  Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (set Int) (tuple2 (tuple2 Bool Bool)
  Bool)))))) (sort
  (set1 (set1 (tuple21 (set1 int) (tuple21 (tuple21 bool bool) bool))))
  (t2tb149 x))))

(declare-fun tb2t149 (uni) (set (set (tuple2 (set Int) (tuple2 (tuple2 Bool
  Bool) Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (set Int) (tuple2 (tuple2 Bool Bool)
  Bool)))))) (! (= (tb2t149 (t2tb149 i)) i) :pattern ((t2tb149 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb149 (tb2t149 j)) j) :pattern ((t2tb149 (tb2t149 j))) )))

(declare-fun t2tb150 ((set (tuple2 (set Int) (tuple2 (tuple2 Bool Bool)
  Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (set Int) (tuple2 (tuple2 Bool Bool) Bool)))))
  (sort (set1 (tuple21 (set1 int) (tuple21 (tuple21 bool bool) bool)))
  (t2tb150 x))))

(declare-fun tb2t150 (uni) (set (tuple2 (set Int) (tuple2 (tuple2 Bool Bool)
  Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (set Int) (tuple2 (tuple2 Bool Bool) Bool)))))
  (! (= (tb2t150 (t2tb150 i)) i) :pattern ((t2tb150 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb150 (tb2t150 j)) j) :pattern ((t2tb150 (tb2t150 j))) )))

(declare-fun t2tb151 ((tuple2 (set Int) (tuple2 (tuple2 Bool Bool)
  Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (set Int) (tuple2 (tuple2 Bool Bool) Bool)))) (sort
  (tuple21 (set1 int) (tuple21 (tuple21 bool bool) bool)) (t2tb151 x))))

(declare-fun tb2t151 (uni) (tuple2 (set Int) (tuple2 (tuple2 Bool Bool)
  Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (set Int) (tuple2 (tuple2 Bool Bool) Bool))))
  (! (= (tb2t151 (t2tb151 i)) i) :pattern ((t2tb151 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb151 (tb2t151 j)) j) :pattern ((t2tb151 (tb2t151 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (set Int)) (y (tuple2 (tuple2 Bool Bool) Bool))) (! (mem
  (set1 (tuple21 (set1 int) (tuple21 (tuple21 bool bool) bool)))
  (add (tuple21 (set1 int) (tuple21 (tuple21 bool bool) bool))
  (Tuple2 (set1 int) (tuple21 (tuple21 bool bool) bool) (t2tb3 x) (t2tb10 y))
  (empty (tuple21 (set1 int) (tuple21 (tuple21 bool bool) bool))))
  (infix_mnmngt (tuple21 (tuple21 bool bool) bool) (set1 int)
  (t2tb1 (add3 x empty3))
  (add (tuple21 (tuple21 bool bool) bool) (t2tb10 y) (t2tb6 empty6)))) :pattern (
  (tb2t150
  (add (tuple21 (set1 int) (tuple21 (tuple21 bool bool) bool))
  (Tuple2 (set1 int) (tuple21 (tuple21 bool bool) bool) (t2tb3 x) (t2tb10 y))
  (empty (tuple21 (set1 int) (tuple21 (tuple21 bool bool) bool)))))) )))

;; singleton_is_function
  (assert
  (forall ((x (set Int)) (y (set Int))) (! (mem
  (set1 (tuple21 (set1 int) (set1 int)))
  (add (tuple21 (set1 int) (set1 int))
  (Tuple2 (set1 int) (set1 int) (t2tb3 x) (t2tb3 y))
  (empty (tuple21 (set1 int) (set1 int))))
  (infix_mnmngt (set1 int) (set1 int) (t2tb1 (add3 x empty3))
  (t2tb1 (add3 y empty3)))) :pattern ((tb2t37
                                      (add (tuple21 (set1 int) (set1 int))
                                      (Tuple2 (set1 int) (set1 int) (t2tb3 x)
                                      (t2tb3 y))
                                      (empty (tuple21 (set1 int) (set1 int)))))) )))

(declare-fun t2tb152 ((set (set (tuple2 (set Int) (tuple2 Bool Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (set Int) (tuple2 Bool Bool)))))) (sort
  (set1 (set1 (tuple21 (set1 int) (tuple21 bool bool)))) (t2tb152 x))))

(declare-fun tb2t152 (uni) (set (set (tuple2 (set Int) (tuple2 Bool Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (set Int) (tuple2 Bool Bool))))))
  (! (= (tb2t152 (t2tb152 i)) i) :pattern ((t2tb152 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb152 (tb2t152 j)) j) :pattern ((t2tb152 (tb2t152 j))) )))

(declare-fun t2tb153 ((set (tuple2 (set Int) (tuple2 Bool Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (set Int) (tuple2 Bool Bool))))) (sort
  (set1 (tuple21 (set1 int) (tuple21 bool bool))) (t2tb153 x))))

(declare-fun tb2t153 (uni) (set (tuple2 (set Int) (tuple2 Bool Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (set Int) (tuple2 Bool Bool)))))
  (! (= (tb2t153 (t2tb153 i)) i) :pattern ((t2tb153 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb153 (tb2t153 j)) j) :pattern ((t2tb153 (tb2t153 j))) )))

(declare-fun t2tb154 ((tuple2 (set Int) (tuple2 Bool Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (set Int) (tuple2 Bool Bool)))) (sort
  (tuple21 (set1 int) (tuple21 bool bool)) (t2tb154 x))))

(declare-fun tb2t154 (uni) (tuple2 (set Int) (tuple2 Bool Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (set Int) (tuple2 Bool Bool))))
  (! (= (tb2t154 (t2tb154 i)) i) :pattern ((t2tb154 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb154 (tb2t154 j)) j) :pattern ((t2tb154 (tb2t154 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (set Int)) (y (tuple2 Bool Bool))) (! (mem
  (set1 (tuple21 (set1 int) (tuple21 bool bool)))
  (add (tuple21 (set1 int) (tuple21 bool bool))
  (Tuple2 (set1 int) (tuple21 bool bool) (t2tb3 x) (t2tb11 y))
  (empty (tuple21 (set1 int) (tuple21 bool bool))))
  (infix_mnmngt (tuple21 bool bool) (set1 int) (t2tb1 (add3 x empty3))
  (add (tuple21 bool bool) (t2tb11 y) (t2tb7 empty7)))) :pattern ((tb2t153
                                                                  (add
                                                                  (tuple21
                                                                  (set1 int)
                                                                  (tuple21
                                                                  bool 
                                                                  bool))
                                                                  (Tuple2
                                                                  (set1 int)
                                                                  (tuple21
                                                                  bool 
                                                                  bool)
                                                                  (t2tb3 x)
                                                                  (t2tb11 y))
                                                                  (empty
                                                                  (tuple21
                                                                  (set1 int)
                                                                  (tuple21
                                                                  bool 
                                                                  bool)))))) )))

;; singleton_is_function
  (assert
  (forall ((x (set Int)) (y Bool)) (! (mem (set1 (tuple21 (set1 int) bool))
  (add (tuple21 (set1 int) bool)
  (Tuple2 (set1 int) bool (t2tb3 x) (t2tb12 y))
  (empty (tuple21 (set1 int) bool)))
  (infix_mnmngt bool (set1 int) (t2tb1 (add3 x empty3))
  (t2tb2 (add1 y empty1)))) :pattern ((tb2t39
                                      (add (tuple21 (set1 int) bool)
                                      (Tuple2 (set1 int) bool (t2tb3 x)
                                      (t2tb12 y))
                                      (empty (tuple21 (set1 int) bool))))) )))

;; singleton_is_function
  (assert
  (forall ((x (set Int)) (y Int)) (! (mem (set1 (tuple21 (set1 int) int))
  (add (tuple21 (set1 int) int) (Tuple2 (set1 int) int (t2tb3 x) (t2tb13 y))
  (empty (tuple21 (set1 int) int)))
  (infix_mnmngt int (set1 int) (t2tb1 (add3 x empty3))
  (t2tb3 (add2 y empty2)))) :pattern ((tb2t42
                                      (add (tuple21 (set1 int) int)
                                      (Tuple2 (set1 int) int (t2tb3 x)
                                      (t2tb13 y))
                                      (empty (tuple21 (set1 int) int))))) )))

;; singleton_is_function
  (assert
  (forall ((b ty))
  (forall ((x (set Int)) (y uni)) (! (mem (set1 (tuple21 (set1 int) b))
  (add (tuple21 (set1 int) b) (Tuple2 (set1 int) b (t2tb3 x) y)
  (empty (tuple21 (set1 int) b)))
  (infix_mnmngt b (set1 int) (t2tb1 (add3 x empty3)) (add b y (empty b)))) :pattern (
  (add (tuple21 (set1 int) b) (Tuple2 (set1 int) b (t2tb3 x) y)
  (empty (tuple21 (set1 int) b)))) ))))

(declare-fun t2tb155 ((set (set (tuple2 (tuple2 Bool Bool)
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 Bool Bool)
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 bool bool)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))))
  (t2tb155 x))))

(declare-fun tb2t155 (uni) (set (set (tuple2 (tuple2 Bool Bool)
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 Bool Bool)
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))))) (! (= (tb2t155 (t2tb155 i)) i) :pattern ((t2tb155 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb155 (tb2t155 j)) j) :pattern ((t2tb155 (tb2t155 j))) )))

(declare-fun t2tb156 ((set (tuple2 (tuple2 Bool Bool)
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Bool Bool)
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))))
  (sort
  (set1
  (tuple21 (tuple21 bool bool)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (t2tb156 x))))

(declare-fun tb2t156 (uni) (set (tuple2 (tuple2 Bool Bool)
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Bool Bool)
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))))
  (! (= (tb2t156 (t2tb156 i)) i) :pattern ((t2tb156 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb156 (tb2t156 j)) j) :pattern ((t2tb156 (tb2t156 j))) )))

(declare-fun t2tb157 ((tuple2 (tuple2 Bool Bool)
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool)
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))))
  (sort
  (tuple21 (tuple21 bool bool)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (t2tb157 x))))

(declare-fun tb2t157 (uni) (tuple2 (tuple2 Bool Bool)
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 Bool Bool)
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))))
  (! (= (tb2t157 (t2tb157 i)) i) :pattern ((t2tb157 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb157 (tb2t157 j)) j) :pattern ((t2tb157 (tb2t157 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 Bool Bool))
  (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (! (mem
  (set1
  (tuple21 (tuple21 bool bool)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (add
  (tuple21 (tuple21 bool bool)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2 (tuple21 bool bool)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb11 x) (t2tb4 y))
  (empty
  (tuple21 (tuple21 bool bool)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))))
  (infix_mnmngt
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (tuple21 bool bool) (add (tuple21 bool bool) (t2tb11 x) (t2tb7 empty7))
  (t2tb (add4 y empty8)))) :pattern ((tb2t156
                                     (add
                                     (tuple21 (tuple21 bool bool)
                                     (set1
                                     (tuple21
                                     (tuple21
                                     (tuple21 (tuple21 bool bool) bool) 
                                     bool) (set1 int))))
                                     (Tuple2 (tuple21 bool bool)
                                     (set1
                                     (tuple21
                                     (tuple21
                                     (tuple21 (tuple21 bool bool) bool) 
                                     bool) (set1 int))) (t2tb11 x) (t2tb4 y))
                                     (empty
                                     (tuple21 (tuple21 bool bool)
                                     (set1
                                     (tuple21
                                     (tuple21
                                     (tuple21 (tuple21 bool bool) bool) 
                                     bool) (set1 int)))))))) )))

(declare-fun t2tb158 ((set (set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))))
  (sort
  (set1
  (set1
  (tuple21 (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (t2tb158 x))))

(declare-fun tb2t158 (uni) (set (set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))))
  (! (= (tb2t158 (t2tb158 i)) i) :pattern ((t2tb158 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb158 (tb2t158 j)) j) :pattern ((t2tb158 (tb2t158 j))) )))

(declare-fun t2tb159 ((set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))) (sort
  (set1
  (tuple21 (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (t2tb159 x))))

(declare-fun tb2t159 (uni) (set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))))
  (! (= (tb2t159 (t2tb159 i)) i) :pattern ((t2tb159 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb159 (tb2t159 j)) j) :pattern ((t2tb159 (tb2t159 j))) )))

(declare-fun t2tb160 ((tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))) (sort
  (tuple21 (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb160 x))))

(declare-fun tb2t160 (uni) (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))))
  (! (= (tb2t160 (t2tb160 i)) i) :pattern ((t2tb160 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb160 (tb2t160 j)) j) :pattern ((t2tb160 (tb2t160 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 Bool Bool)) (y (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))) (! (mem
  (set1
  (tuple21 (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (add
  (tuple21 (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (Tuple2 (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb11 x) (t2tb8 y))
  (empty
  (tuple21 (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (infix_mnmngt
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 bool bool) (add (tuple21 bool bool) (t2tb11 x) (t2tb7 empty7))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb8 y) (t2tb4 empty4)))) :pattern ((tb2t159
                                        (add
                                        (tuple21 (tuple21 bool bool)
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int)))
                                        (Tuple2 (tuple21 bool bool)
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int)) (t2tb11 x)
                                        (t2tb8 y))
                                        (empty
                                        (tuple21 (tuple21 bool bool)
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int))))))) )))

(declare-fun t2tb161 ((tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool)))) (sort
  (tuple21 (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb161 x))))

(declare-fun tb2t161 (uni) (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool)))) (! (= (tb2t161 (t2tb161 i)) i) :pattern ((t2tb161 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 (tuple21 bool bool)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) j)
     (= (t2tb161 (tb2t161 j)) j)) :pattern ((t2tb161 (tb2t161 j))) )))

(declare-fun t2tb162 ((set (set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))) (t2tb162 x))))

(declare-fun tb2t162 (uni) (set (set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))))
  (! (= (tb2t162 (t2tb162 i)) i) :pattern ((t2tb162 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21 (tuple21 bool bool)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))) j)
     (= (t2tb162 (tb2t162 j)) j)) :pattern ((t2tb162 (tb2t162 j))) )))

(declare-fun t2tb163 ((set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool))))) (sort
  (set1
  (tuple21 (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))) (t2tb163 x))))

(declare-fun tb2t163 (uni) (set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool)))))
  (! (= (tb2t163 (t2tb163 i)) i) :pattern ((t2tb163 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21 (tuple21 bool bool)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool))) j)
     (= (t2tb163 (tb2t163 j)) j)) :pattern ((t2tb163 (tb2t163 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 Bool Bool)) (y (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))) (! (mem
  (set1
  (tuple21 (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))
  (add
  (tuple21 (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (Tuple2 (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb11 x) (t2tb9 y))
  (empty
  (tuple21 (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))))
  (infix_mnmngt (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 bool bool) (add (tuple21 bool bool) (t2tb11 x) (t2tb7 empty7))
  (add (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 y)
  (t2tb5 empty5)))) :pattern ((tb2t163
                              (add
                              (tuple21 (tuple21 bool bool)
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool))
                              (Tuple2 (tuple21 bool bool)
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool) (t2tb11 x) (t2tb9 y))
                              (empty
                              (tuple21 (tuple21 bool bool)
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool)))))) )))

(declare-fun t2tb164 ((set (set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 Bool Bool) Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 Bool Bool)
  Bool)))))) (sort
  (set1
  (set1 (tuple21 (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool))))
  (t2tb164 x))))

(declare-fun tb2t164 (uni) (set (set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 Bool Bool) Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 Bool Bool)
  Bool)))))) (! (= (tb2t164 (t2tb164 i)) i) :pattern ((t2tb164 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1 (tuple21 (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool))))
     j) (= (t2tb164 (tb2t164 j)) j)) :pattern ((t2tb164 (tb2t164 j))) )))

(declare-fun t2tb165 ((set (tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 Bool
  Bool) Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 Bool Bool)
  Bool))))) (sort
  (set1 (tuple21 (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool)))
  (t2tb165 x))))

(declare-fun tb2t165 (uni) (set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 Bool Bool) Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 Bool Bool)
  Bool))))) (! (= (tb2t165 (t2tb165 i)) i) :pattern ((t2tb165 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1 (tuple21 (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool)))
     j) (= (t2tb165 (tb2t165 j)) j)) :pattern ((t2tb165 (tb2t165 j))) )))

(declare-fun t2tb166 ((tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 Bool Bool)
  Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 Bool Bool) Bool))))
  (sort (tuple21 (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool))
  (t2tb166 x))))

(declare-fun tb2t166 (uni) (tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 Bool
  Bool) Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 Bool Bool) Bool))))
  (! (= (tb2t166 (t2tb166 i)) i) :pattern ((t2tb166 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool)) j)
     (= (t2tb166 (tb2t166 j)) j)) :pattern ((t2tb166 (tb2t166 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 Bool Bool)) (y (tuple2 (tuple2 Bool Bool) Bool)))
  (! (mem
  (set1 (tuple21 (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool)))
  (add (tuple21 (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool))
  (Tuple2 (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool) (t2tb11 x)
  (t2tb10 y))
  (empty (tuple21 (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool))))
  (infix_mnmngt (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool)
  (add (tuple21 bool bool) (t2tb11 x) (t2tb7 empty7))
  (add (tuple21 (tuple21 bool bool) bool) (t2tb10 y) (t2tb6 empty6)))) :pattern (
  (tb2t165
  (add (tuple21 (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool))
  (Tuple2 (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool) (t2tb11 x)
  (t2tb10 y))
  (empty (tuple21 (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool)))))) )))

(declare-fun t2tb167 ((set (set (tuple2 (tuple2 Bool Bool) (set Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 Bool Bool) (set Int)))))) (sort
  (set1 (set1 (tuple21 (tuple21 bool bool) (set1 int)))) (t2tb167 x))))

(declare-fun tb2t167 (uni) (set (set (tuple2 (tuple2 Bool Bool) (set Int)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 Bool Bool) (set Int))))))
  (! (= (tb2t167 (t2tb167 i)) i) :pattern ((t2tb167 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb167 (tb2t167 j)) j) :pattern ((t2tb167 (tb2t167 j))) )))

(declare-fun t2tb168 ((set (tuple2 (tuple2 Bool Bool) (set Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Bool Bool) (set Int))))) (sort
  (set1 (tuple21 (tuple21 bool bool) (set1 int))) (t2tb168 x))))

(declare-fun tb2t168 (uni) (set (tuple2 (tuple2 Bool Bool) (set Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Bool Bool) (set Int)))))
  (! (= (tb2t168 (t2tb168 i)) i) :pattern ((t2tb168 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb168 (tb2t168 j)) j) :pattern ((t2tb168 (tb2t168 j))) )))

(declare-fun t2tb169 ((tuple2 (tuple2 Bool Bool) (set Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) (set Int)))) (sort
  (tuple21 (tuple21 bool bool) (set1 int)) (t2tb169 x))))

(declare-fun tb2t169 (uni) (tuple2 (tuple2 Bool Bool) (set Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 Bool Bool) (set Int))))
  (! (= (tb2t169 (t2tb169 i)) i) :pattern ((t2tb169 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb169 (tb2t169 j)) j) :pattern ((t2tb169 (tb2t169 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 Bool Bool)) (y (set Int))) (! (mem
  (set1 (tuple21 (tuple21 bool bool) (set1 int)))
  (add (tuple21 (tuple21 bool bool) (set1 int))
  (Tuple2 (tuple21 bool bool) (set1 int) (t2tb11 x) (t2tb3 y))
  (empty (tuple21 (tuple21 bool bool) (set1 int))))
  (infix_mnmngt (set1 int) (tuple21 bool bool)
  (add (tuple21 bool bool) (t2tb11 x) (t2tb7 empty7))
  (t2tb1 (add3 y empty3)))) :pattern ((tb2t168
                                      (add
                                      (tuple21 (tuple21 bool bool)
                                      (set1 int))
                                      (Tuple2 (tuple21 bool bool) (set1 int)
                                      (t2tb11 x) (t2tb3 y))
                                      (empty
                                      (tuple21 (tuple21 bool bool)
                                      (set1 int)))))) )))

(declare-fun t2tb170 ((set (set (tuple2 (tuple2 Bool Bool) (tuple2 Bool
  Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 Bool Bool) (tuple2 Bool Bool))))))
  (sort (set1 (set1 (tuple21 (tuple21 bool bool) (tuple21 bool bool))))
  (t2tb170 x))))

(declare-fun tb2t170 (uni) (set (set (tuple2 (tuple2 Bool Bool) (tuple2 Bool
  Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 Bool Bool) (tuple2 Bool Bool))))))
  (! (= (tb2t170 (t2tb170 i)) i) :pattern ((t2tb170 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1 (set1 (tuple21 (tuple21 bool bool) (tuple21 bool bool)))) j)
     (= (t2tb170 (tb2t170 j)) j)) :pattern ((t2tb170 (tb2t170 j))) )))

(declare-fun t2tb171 ((set (tuple2 (tuple2 Bool Bool) (tuple2 Bool
  Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Bool Bool) (tuple2 Bool Bool))))) (sort
  (set1 (tuple21 (tuple21 bool bool) (tuple21 bool bool))) (t2tb171 x))))

(declare-fun tb2t171 (uni) (set (tuple2 (tuple2 Bool Bool) (tuple2 Bool
  Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Bool Bool) (tuple2 Bool Bool)))))
  (! (= (tb2t171 (t2tb171 i)) i) :pattern ((t2tb171 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (tuple21 (tuple21 bool bool) (tuple21 bool bool))) j)
     (= (t2tb171 (tb2t171 j)) j)) :pattern ((t2tb171 (tb2t171 j))) )))

(declare-fun t2tb172 ((tuple2 (tuple2 Bool Bool) (tuple2 Bool Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) (tuple2 Bool Bool)))) (sort
  (tuple21 (tuple21 bool bool) (tuple21 bool bool)) (t2tb172 x))))

(declare-fun tb2t172 (uni) (tuple2 (tuple2 Bool Bool) (tuple2 Bool Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 Bool Bool) (tuple2 Bool Bool))))
  (! (= (tb2t172 (t2tb172 i)) i) :pattern ((t2tb172 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (tuple21 (tuple21 bool bool) (tuple21 bool bool)) j)
     (= (t2tb172 (tb2t172 j)) j)) :pattern ((t2tb172 (tb2t172 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 Bool Bool)) (y (tuple2 Bool Bool))) (! (mem
  (set1 (tuple21 (tuple21 bool bool) (tuple21 bool bool)))
  (add (tuple21 (tuple21 bool bool) (tuple21 bool bool))
  (Tuple2 (tuple21 bool bool) (tuple21 bool bool) (t2tb11 x) (t2tb11 y))
  (empty (tuple21 (tuple21 bool bool) (tuple21 bool bool))))
  (infix_mnmngt (tuple21 bool bool) (tuple21 bool bool)
  (add (tuple21 bool bool) (t2tb11 x) (t2tb7 empty7))
  (add (tuple21 bool bool) (t2tb11 y) (t2tb7 empty7)))) :pattern ((tb2t171
                                                                  (add
                                                                  (tuple21
                                                                  (tuple21
                                                                  bool 
                                                                  bool)
                                                                  (tuple21
                                                                  bool 
                                                                  bool))
                                                                  (Tuple2
                                                                  (tuple21
                                                                  bool 
                                                                  bool)
                                                                  (tuple21
                                                                  bool 
                                                                  bool)
                                                                  (t2tb11 x)
                                                                  (t2tb11 y))
                                                                  (empty
                                                                  (tuple21
                                                                  (tuple21
                                                                  bool 
                                                                  bool)
                                                                  (tuple21
                                                                  bool 
                                                                  bool)))))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 Bool Bool)) (y Bool)) (! (mem
  (set1 (tuple21 (tuple21 bool bool) bool))
  (add (tuple21 (tuple21 bool bool) bool)
  (Tuple2 (tuple21 bool bool) bool (t2tb11 x) (t2tb12 y)) (t2tb6 empty6))
  (infix_mnmngt bool (tuple21 bool bool)
  (add (tuple21 bool bool) (t2tb11 x) (t2tb7 empty7))
  (t2tb2 (add1 y empty1)))) :pattern ((tb2t6
                                      (add (tuple21 (tuple21 bool bool) bool)
                                      (Tuple2 (tuple21 bool bool) bool
                                      (t2tb11 x) (t2tb12 y)) (t2tb6 empty6)))) )))

(declare-fun t2tb173 ((set (set (tuple2 (tuple2 Bool Bool) Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 Bool Bool) Int))))) (sort
  (set1 (set1 (tuple21 (tuple21 bool bool) int))) (t2tb173 x))))

(declare-fun tb2t173 (uni) (set (set (tuple2 (tuple2 Bool Bool) Int))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 Bool Bool) Int)))))
  (! (= (tb2t173 (t2tb173 i)) i) :pattern ((t2tb173 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb173 (tb2t173 j)) j) :pattern ((t2tb173 (tb2t173 j))) )))

(declare-fun t2tb174 ((set (tuple2 (tuple2 Bool Bool) Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Bool Bool) Int)))) (sort
  (set1 (tuple21 (tuple21 bool bool) int)) (t2tb174 x))))

(declare-fun tb2t174 (uni) (set (tuple2 (tuple2 Bool Bool) Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Bool Bool) Int))))
  (! (= (tb2t174 (t2tb174 i)) i) :pattern ((t2tb174 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb174 (tb2t174 j)) j) :pattern ((t2tb174 (tb2t174 j))) )))

(declare-fun t2tb175 ((tuple2 (tuple2 Bool Bool) Int)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) Int))) (sort
  (tuple21 (tuple21 bool bool) int) (t2tb175 x))))

(declare-fun tb2t175 (uni) (tuple2 (tuple2 Bool Bool) Int))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 Bool Bool) Int)))
  (! (= (tb2t175 (t2tb175 i)) i) :pattern ((t2tb175 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb175 (tb2t175 j)) j) :pattern ((t2tb175 (tb2t175 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 Bool Bool)) (y Int)) (! (mem
  (set1 (tuple21 (tuple21 bool bool) int))
  (add (tuple21 (tuple21 bool bool) int)
  (Tuple2 (tuple21 bool bool) int (t2tb11 x) (t2tb13 y))
  (empty (tuple21 (tuple21 bool bool) int)))
  (infix_mnmngt int (tuple21 bool bool)
  (add (tuple21 bool bool) (t2tb11 x) (t2tb7 empty7))
  (t2tb3 (add2 y empty2)))) :pattern ((tb2t174
                                      (add (tuple21 (tuple21 bool bool) int)
                                      (Tuple2 (tuple21 bool bool) int
                                      (t2tb11 x) (t2tb13 y))
                                      (empty
                                      (tuple21 (tuple21 bool bool) int))))) )))

;; singleton_is_function
  (assert
  (forall ((b ty))
  (forall ((x (tuple2 Bool Bool)) (y uni)) (! (mem
  (set1 (tuple21 (tuple21 bool bool) b))
  (add (tuple21 (tuple21 bool bool) b)
  (Tuple2 (tuple21 bool bool) b (t2tb11 x) y)
  (empty (tuple21 (tuple21 bool bool) b)))
  (infix_mnmngt b (tuple21 bool bool)
  (add (tuple21 bool bool) (t2tb11 x) (t2tb7 empty7)) (add b y (empty b)))) :pattern (
  (add (tuple21 (tuple21 bool bool) b)
  (Tuple2 (tuple21 bool bool) b (t2tb11 x) y)
  (empty (tuple21 (tuple21 bool bool) b)))) ))))

;; singleton_is_function
  (assert
  (forall ((x Bool) (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (! (mem
  (set1
  (tuple21 bool
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (add
  (tuple21 bool
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2 bool
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb12 x) (t2tb4 y))
  (empty
  (tuple21 bool
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))))
  (infix_mnmngt
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  bool (t2tb2 (add1 x empty1)) (t2tb (add4 y empty8)))) :pattern ((tb2t45
                                                                  (add
                                                                  (tuple21
                                                                  bool
                                                                  (set1
                                                                  (tuple21
                                                                  (tuple21
                                                                  (tuple21
                                                                  (tuple21
                                                                  bool 
                                                                  bool) 
                                                                  bool) 
                                                                  bool)
                                                                  (set1 int))))
                                                                  (Tuple2
                                                                  bool
                                                                  (set1
                                                                  (tuple21
                                                                  (tuple21
                                                                  (tuple21
                                                                  (tuple21
                                                                  bool 
                                                                  bool) 
                                                                  bool) 
                                                                  bool)
                                                                  (set1 int)))
                                                                  (t2tb12 x)
                                                                  (t2tb4 y))
                                                                  (empty
                                                                  (tuple21
                                                                  bool
                                                                  (set1
                                                                  (tuple21
                                                                  (tuple21
                                                                  (tuple21
                                                                  (tuple21
                                                                  bool 
                                                                  bool) 
                                                                  bool) 
                                                                  bool)
                                                                  (set1 int)))))))) )))

(declare-fun t2tb176 ((tuple2 Bool (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Bool (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (sort
  (tuple21 bool
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb176 x))))

(declare-fun tb2t176 (uni) (tuple2 Bool (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))

;; BridgeL
  (assert
  (forall ((i (tuple2 Bool (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))))
  (! (= (tb2t176 (t2tb176 i)) i) :pattern ((t2tb176 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb176 (tb2t176 j)) j) :pattern ((t2tb176 (tb2t176 j))) )))

(declare-fun t2tb177 ((set (set (tuple2 Bool
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Bool (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))))) (sort
  (set1
  (set1
  (tuple21 bool
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (t2tb177 x))))

(declare-fun tb2t177 (uni) (set (set (tuple2 Bool
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Bool (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))))))
  (! (= (tb2t177 (t2tb177 i)) i) :pattern ((t2tb177 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb177 (tb2t177 j)) j) :pattern ((t2tb177 (tb2t177 j))) )))

(declare-fun t2tb178 ((set (tuple2 Bool (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Bool (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))))) (sort
  (set1
  (tuple21 bool
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (t2tb178 x))))

(declare-fun tb2t178 (uni) (set (tuple2 Bool
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Bool (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))))
  (! (= (tb2t178 (t2tb178 i)) i) :pattern ((t2tb178 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb178 (tb2t178 j)) j) :pattern ((t2tb178 (tb2t178 j))) )))

;; singleton_is_function
  (assert
  (forall ((x Bool) (y (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (! (mem
  (set1
  (tuple21 bool
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (add
  (tuple21 bool
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (Tuple2 bool
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb12 x) (t2tb8 y))
  (empty
  (tuple21 bool
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (infix_mnmngt
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)) 
  bool (t2tb2 (add1 x empty1))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb8 y) (t2tb4 empty4)))) :pattern ((tb2t178
                                        (add
                                        (tuple21 bool
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int)))
                                        (Tuple2 bool
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int)) (t2tb12 x)
                                        (t2tb8 y))
                                        (empty
                                        (tuple21 bool
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int))))))) )))

(declare-fun t2tb179 ((set (set (tuple2 Bool (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Bool (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool)))))) (sort
  (set1
  (set1 (tuple21 bool (tuple21 (tuple21 (tuple21 bool bool) bool) bool))))
  (t2tb179 x))))

(declare-fun tb2t179 (uni) (set (set (tuple2 Bool
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Bool (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool)))))) (! (= (tb2t179 (t2tb179 i)) i) :pattern ((t2tb179 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1 (tuple21 bool (tuple21 (tuple21 (tuple21 bool bool) bool) bool))))
     j) (= (t2tb179 (tb2t179 j)) j)) :pattern ((t2tb179 (tb2t179 j))) )))

(declare-fun t2tb180 ((set (tuple2 Bool (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Bool (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))))) (sort
  (set1 (tuple21 bool (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))
  (t2tb180 x))))

(declare-fun tb2t180 (uni) (set (tuple2 Bool (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Bool (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))))) (! (= (tb2t180 (t2tb180 i)) i) :pattern ((t2tb180 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1 (tuple21 bool (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))
     j) (= (t2tb180 (tb2t180 j)) j)) :pattern ((t2tb180 (tb2t180 j))) )))

(declare-fun t2tb181 ((tuple2 Bool (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Bool (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (sort (tuple21 bool (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (t2tb181 x))))

(declare-fun tb2t181 (uni) (tuple2 Bool (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 Bool (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (! (= (tb2t181 (t2tb181 i)) i) :pattern ((t2tb181 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 bool (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) j)
     (= (t2tb181 (tb2t181 j)) j)) :pattern ((t2tb181 (tb2t181 j))) )))

;; singleton_is_function
  (assert
  (forall ((x Bool) (y (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (! (mem
  (set1 (tuple21 bool (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))
  (add (tuple21 bool (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (Tuple2 bool (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb12 x)
  (t2tb9 y))
  (empty (tuple21 bool (tuple21 (tuple21 (tuple21 bool bool) bool) bool))))
  (infix_mnmngt (tuple21 (tuple21 (tuple21 bool bool) bool) bool) bool
  (t2tb2 (add1 x empty1))
  (add (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 y)
  (t2tb5 empty5)))) :pattern ((tb2t180
                              (add
                              (tuple21 bool
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool))
                              (Tuple2 bool
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool) (t2tb12 x) (t2tb9 y))
                              (empty
                              (tuple21 bool
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool)))))) )))

(declare-fun t2tb182 ((set (set (tuple2 Bool (tuple2 (tuple2 Bool Bool)
  Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Bool (tuple2 (tuple2 Bool Bool) Bool))))))
  (sort (set1 (set1 (tuple21 bool (tuple21 (tuple21 bool bool) bool))))
  (t2tb182 x))))

(declare-fun tb2t182 (uni) (set (set (tuple2 Bool (tuple2 (tuple2 Bool Bool)
  Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Bool (tuple2 (tuple2 Bool Bool) Bool))))))
  (! (= (tb2t182 (t2tb182 i)) i) :pattern ((t2tb182 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1 (set1 (tuple21 bool (tuple21 (tuple21 bool bool) bool)))) j)
     (= (t2tb182 (tb2t182 j)) j)) :pattern ((t2tb182 (tb2t182 j))) )))

(declare-fun t2tb183 ((set (tuple2 Bool (tuple2 (tuple2 Bool Bool)
  Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Bool (tuple2 (tuple2 Bool Bool) Bool))))) (sort
  (set1 (tuple21 bool (tuple21 (tuple21 bool bool) bool))) (t2tb183 x))))

(declare-fun tb2t183 (uni) (set (tuple2 Bool (tuple2 (tuple2 Bool Bool)
  Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Bool (tuple2 (tuple2 Bool Bool) Bool)))))
  (! (= (tb2t183 (t2tb183 i)) i) :pattern ((t2tb183 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (tuple21 bool (tuple21 (tuple21 bool bool) bool))) j)
     (= (t2tb183 (tb2t183 j)) j)) :pattern ((t2tb183 (tb2t183 j))) )))

(declare-fun t2tb184 ((tuple2 Bool (tuple2 (tuple2 Bool Bool) Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Bool (tuple2 (tuple2 Bool Bool) Bool)))) (sort
  (tuple21 bool (tuple21 (tuple21 bool bool) bool)) (t2tb184 x))))

(declare-fun tb2t184 (uni) (tuple2 Bool (tuple2 (tuple2 Bool Bool) Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 Bool (tuple2 (tuple2 Bool Bool) Bool))))
  (! (= (tb2t184 (t2tb184 i)) i) :pattern ((t2tb184 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (tuple21 bool (tuple21 (tuple21 bool bool) bool)) j)
     (= (t2tb184 (tb2t184 j)) j)) :pattern ((t2tb184 (tb2t184 j))) )))

;; singleton_is_function
  (assert
  (forall ((x Bool) (y (tuple2 (tuple2 Bool Bool) Bool))) (! (mem
  (set1 (tuple21 bool (tuple21 (tuple21 bool bool) bool)))
  (add (tuple21 bool (tuple21 (tuple21 bool bool) bool))
  (Tuple2 bool (tuple21 (tuple21 bool bool) bool) (t2tb12 x) (t2tb10 y))
  (empty (tuple21 bool (tuple21 (tuple21 bool bool) bool))))
  (infix_mnmngt (tuple21 (tuple21 bool bool) bool) bool
  (t2tb2 (add1 x empty1))
  (add (tuple21 (tuple21 bool bool) bool) (t2tb10 y) (t2tb6 empty6)))) :pattern (
  (tb2t183
  (add (tuple21 bool (tuple21 (tuple21 bool bool) bool))
  (Tuple2 bool (tuple21 (tuple21 bool bool) bool) (t2tb12 x) (t2tb10 y))
  (empty (tuple21 bool (tuple21 (tuple21 bool bool) bool)))))) )))

;; singleton_is_function
  (assert
  (forall ((x Bool) (y (set Int))) (! (mem (set1 (tuple21 bool (set1 int)))
  (add (tuple21 bool (set1 int))
  (Tuple2 bool (set1 int) (t2tb12 x) (t2tb3 y))
  (empty (tuple21 bool (set1 int))))
  (infix_mnmngt (set1 int) bool (t2tb2 (add1 x empty1))
  (t2tb1 (add3 y empty3)))) :pattern ((tb2t48
                                      (add (tuple21 bool (set1 int))
                                      (Tuple2 bool (set1 int) (t2tb12 x)
                                      (t2tb3 y))
                                      (empty (tuple21 bool (set1 int)))))) )))

(declare-fun t2tb185 ((set (set (tuple2 Bool (tuple2 Bool Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Bool (tuple2 Bool Bool)))))) (sort
  (set1 (set1 (tuple21 bool (tuple21 bool bool)))) (t2tb185 x))))

(declare-fun tb2t185 (uni) (set (set (tuple2 Bool (tuple2 Bool Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Bool (tuple2 Bool Bool))))))
  (! (= (tb2t185 (t2tb185 i)) i) :pattern ((t2tb185 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (set1 (tuple21 bool (tuple21 bool bool)))) j)
     (= (t2tb185 (tb2t185 j)) j)) :pattern ((t2tb185 (tb2t185 j))) )))

(declare-fun t2tb186 ((set (tuple2 Bool (tuple2 Bool Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Bool (tuple2 Bool Bool))))) (sort
  (set1 (tuple21 bool (tuple21 bool bool))) (t2tb186 x))))

(declare-fun tb2t186 (uni) (set (tuple2 Bool (tuple2 Bool Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Bool (tuple2 Bool Bool)))))
  (! (= (tb2t186 (t2tb186 i)) i) :pattern ((t2tb186 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (tuple21 bool (tuple21 bool bool))) j)
     (= (t2tb186 (tb2t186 j)) j)) :pattern ((t2tb186 (tb2t186 j))) )))

(declare-fun t2tb187 ((tuple2 Bool (tuple2 Bool Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Bool (tuple2 Bool Bool)))) (sort
  (tuple21 bool (tuple21 bool bool)) (t2tb187 x))))

(declare-fun tb2t187 (uni) (tuple2 Bool (tuple2 Bool Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 Bool (tuple2 Bool Bool))))
  (! (= (tb2t187 (t2tb187 i)) i) :pattern ((t2tb187 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (tuple21 bool (tuple21 bool bool)) j)
     (= (t2tb187 (tb2t187 j)) j)) :pattern ((t2tb187 (tb2t187 j))) )))

;; singleton_is_function
  (assert
  (forall ((x Bool) (y (tuple2 Bool Bool))) (! (mem
  (set1 (tuple21 bool (tuple21 bool bool)))
  (add (tuple21 bool (tuple21 bool bool))
  (Tuple2 bool (tuple21 bool bool) (t2tb12 x) (t2tb11 y))
  (empty (tuple21 bool (tuple21 bool bool))))
  (infix_mnmngt (tuple21 bool bool) bool (t2tb2 (add1 x empty1))
  (add (tuple21 bool bool) (t2tb11 y) (t2tb7 empty7)))) :pattern ((tb2t186
                                                                  (add
                                                                  (tuple21
                                                                  bool
                                                                  (tuple21
                                                                  bool 
                                                                  bool))
                                                                  (Tuple2
                                                                  bool
                                                                  (tuple21
                                                                  bool 
                                                                  bool)
                                                                  (t2tb12 x)
                                                                  (t2tb11 y))
                                                                  (empty
                                                                  (tuple21
                                                                  bool
                                                                  (tuple21
                                                                  bool 
                                                                  bool)))))) )))

;; singleton_is_function
  (assert
  (forall ((x Bool) (y Bool)) (! (mem (set1 (tuple21 bool bool))
  (add (tuple21 bool bool) (Tuple2 bool bool (t2tb12 x) (t2tb12 y))
  (t2tb7 empty7))
  (infix_mnmngt bool bool (t2tb2 (add1 x empty1)) (t2tb2 (add1 y empty1)))) :pattern (
  (tb2t7
  (add (tuple21 bool bool) (Tuple2 bool bool (t2tb12 x) (t2tb12 y))
  (t2tb7 empty7)))) )))

;; singleton_is_function
  (assert
  (forall ((x Bool) (y Int)) (! (mem (set1 (tuple21 bool int))
  (add (tuple21 bool int) (Tuple2 bool int (t2tb12 x) (t2tb13 y))
  (empty (tuple21 bool int)))
  (infix_mnmngt int bool (t2tb2 (add1 x empty1)) (t2tb3 (add2 y empty2)))) :pattern (
  (tb2t51
  (add (tuple21 bool int) (Tuple2 bool int (t2tb12 x) (t2tb13 y))
  (empty (tuple21 bool int))))) )))

;; singleton_is_function
  (assert
  (forall ((b ty))
  (forall ((x Bool) (y uni)) (! (mem (set1 (tuple21 bool b))
  (add (tuple21 bool b) (Tuple2 bool b (t2tb12 x) y)
  (empty (tuple21 bool b)))
  (infix_mnmngt b bool (t2tb2 (add1 x empty1)) (add b y (empty b)))) :pattern (
  (add (tuple21 bool b) (Tuple2 bool b (t2tb12 x) y)
  (empty (tuple21 bool b)))) ))))

;; singleton_is_function
  (assert
  (forall ((x Int) (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (! (mem
  (set1
  (tuple21 int
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (add
  (tuple21 int
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2 int
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb13 x) (t2tb4 y))
  (empty
  (tuple21 int
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))))
  (infix_mnmngt
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) 
  int (t2tb3 (add2 x empty2)) (t2tb (add4 y empty8)))) :pattern ((tb2t54
                                                                 (add
                                                                 (tuple21 
                                                                 int
                                                                 (set1
                                                                 (tuple21
                                                                 (tuple21
                                                                 (tuple21
                                                                 (tuple21
                                                                 bool 
                                                                 bool) 
                                                                 bool) 
                                                                 bool)
                                                                 (set1 int))))
                                                                 (Tuple2 
                                                                 int
                                                                 (set1
                                                                 (tuple21
                                                                 (tuple21
                                                                 (tuple21
                                                                 (tuple21
                                                                 bool 
                                                                 bool) 
                                                                 bool) 
                                                                 bool)
                                                                 (set1 int)))
                                                                 (t2tb13 x)
                                                                 (t2tb4 y))
                                                                 (empty
                                                                 (tuple21 
                                                                 int
                                                                 (set1
                                                                 (tuple21
                                                                 (tuple21
                                                                 (tuple21
                                                                 (tuple21
                                                                 bool 
                                                                 bool) 
                                                                 bool) 
                                                                 bool)
                                                                 (set1 int)))))))) )))

(declare-fun t2tb188 ((set (set (tuple2 Int
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Int (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))))) (sort
  (set1
  (set1
  (tuple21 int
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (t2tb188 x))))

(declare-fun tb2t188 (uni) (set (set (tuple2 Int
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Int (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))))))
  (! (= (tb2t188 (t2tb188 i)) i) :pattern ((t2tb188 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb188 (tb2t188 j)) j) :pattern ((t2tb188 (tb2t188 j))) )))

(declare-fun t2tb189 ((set (tuple2 Int (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))))) (sort
  (set1
  (tuple21 int
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (t2tb189 x))))

(declare-fun tb2t189 (uni) (set (tuple2 Int
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))))
  (! (= (tb2t189 (t2tb189 i)) i) :pattern ((t2tb189 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb189 (tb2t189 j)) j) :pattern ((t2tb189 (tb2t189 j))) )))

(declare-fun t2tb190 ((tuple2 Int (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Int (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (sort
  (tuple21 int
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb190 x))))

(declare-fun tb2t190 (uni) (tuple2 Int (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))

;; BridgeL
  (assert
  (forall ((i (tuple2 Int (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))))
  (! (= (tb2t190 (t2tb190 i)) i) :pattern ((t2tb190 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb190 (tb2t190 j)) j) :pattern ((t2tb190 (tb2t190 j))) )))

;; singleton_is_function
  (assert
  (forall ((x Int) (y (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (! (mem
  (set1
  (tuple21 int
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (add
  (tuple21 int
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (Tuple2 int
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb13 x) (t2tb8 y))
  (empty
  (tuple21 int
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (infix_mnmngt
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)) 
  int (t2tb3 (add2 x empty2))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb8 y) (t2tb4 empty4)))) :pattern ((tb2t189
                                        (add
                                        (tuple21 int
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int)))
                                        (Tuple2 int
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int)) (t2tb13 x)
                                        (t2tb8 y))
                                        (empty
                                        (tuple21 int
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int))))))) )))

(declare-fun t2tb191 ((set (set (tuple2 Int (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Int (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool)))))) (sort
  (set1
  (set1 (tuple21 int (tuple21 (tuple21 (tuple21 bool bool) bool) bool))))
  (t2tb191 x))))

(declare-fun tb2t191 (uni) (set (set (tuple2 Int (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Int (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool)))))) (! (= (tb2t191 (t2tb191 i)) i) :pattern ((t2tb191 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb191 (tb2t191 j)) j) :pattern ((t2tb191 (tb2t191 j))) )))

(declare-fun t2tb192 ((set (tuple2 Int (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))))) (sort
  (set1 (tuple21 int (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))
  (t2tb192 x))))

(declare-fun tb2t192 (uni) (set (tuple2 Int (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))))) (! (= (tb2t192 (t2tb192 i)) i) :pattern ((t2tb192 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb192 (tb2t192 j)) j) :pattern ((t2tb192 (tb2t192 j))) )))

(declare-fun t2tb193 ((tuple2 Int (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Int (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (sort (tuple21 int (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (t2tb193 x))))

(declare-fun tb2t193 (uni) (tuple2 Int (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 Int (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (! (= (tb2t193 (t2tb193 i)) i) :pattern ((t2tb193 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb193 (tb2t193 j)) j) :pattern ((t2tb193 (tb2t193 j))) )))

;; singleton_is_function
  (assert
  (forall ((x Int) (y (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (! (mem
  (set1 (tuple21 int (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))
  (add (tuple21 int (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (Tuple2 int (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb13 x)
  (t2tb9 y))
  (empty (tuple21 int (tuple21 (tuple21 (tuple21 bool bool) bool) bool))))
  (infix_mnmngt (tuple21 (tuple21 (tuple21 bool bool) bool) bool) int
  (t2tb3 (add2 x empty2))
  (add (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 y)
  (t2tb5 empty5)))) :pattern ((tb2t192
                              (add
                              (tuple21 int
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool))
                              (Tuple2 int
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool) (t2tb13 x) (t2tb9 y))
                              (empty
                              (tuple21 int
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool)))))) )))

(declare-fun t2tb194 ((set (set (tuple2 Int (tuple2 (tuple2 Bool Bool)
  Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Int (tuple2 (tuple2 Bool Bool) Bool))))))
  (sort (set1 (set1 (tuple21 int (tuple21 (tuple21 bool bool) bool))))
  (t2tb194 x))))

(declare-fun tb2t194 (uni) (set (set (tuple2 Int (tuple2 (tuple2 Bool Bool)
  Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Int (tuple2 (tuple2 Bool Bool) Bool))))))
  (! (= (tb2t194 (t2tb194 i)) i) :pattern ((t2tb194 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb194 (tb2t194 j)) j) :pattern ((t2tb194 (tb2t194 j))) )))

(declare-fun t2tb195 ((set (tuple2 Int (tuple2 (tuple2 Bool Bool)
  Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int (tuple2 (tuple2 Bool Bool) Bool))))) (sort
  (set1 (tuple21 int (tuple21 (tuple21 bool bool) bool))) (t2tb195 x))))

(declare-fun tb2t195 (uni) (set (tuple2 Int (tuple2 (tuple2 Bool Bool)
  Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int (tuple2 (tuple2 Bool Bool) Bool)))))
  (! (= (tb2t195 (t2tb195 i)) i) :pattern ((t2tb195 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb195 (tb2t195 j)) j) :pattern ((t2tb195 (tb2t195 j))) )))

(declare-fun t2tb196 ((tuple2 Int (tuple2 (tuple2 Bool Bool) Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Int (tuple2 (tuple2 Bool Bool) Bool)))) (sort
  (tuple21 int (tuple21 (tuple21 bool bool) bool)) (t2tb196 x))))

(declare-fun tb2t196 (uni) (tuple2 Int (tuple2 (tuple2 Bool Bool) Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 Int (tuple2 (tuple2 Bool Bool) Bool))))
  (! (= (tb2t196 (t2tb196 i)) i) :pattern ((t2tb196 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb196 (tb2t196 j)) j) :pattern ((t2tb196 (tb2t196 j))) )))

;; singleton_is_function
  (assert
  (forall ((x Int) (y (tuple2 (tuple2 Bool Bool) Bool))) (! (mem
  (set1 (tuple21 int (tuple21 (tuple21 bool bool) bool)))
  (add (tuple21 int (tuple21 (tuple21 bool bool) bool))
  (Tuple2 int (tuple21 (tuple21 bool bool) bool) (t2tb13 x) (t2tb10 y))
  (empty (tuple21 int (tuple21 (tuple21 bool bool) bool))))
  (infix_mnmngt (tuple21 (tuple21 bool bool) bool) int
  (t2tb3 (add2 x empty2))
  (add (tuple21 (tuple21 bool bool) bool) (t2tb10 y) (t2tb6 empty6)))) :pattern (
  (tb2t195
  (add (tuple21 int (tuple21 (tuple21 bool bool) bool))
  (Tuple2 int (tuple21 (tuple21 bool bool) bool) (t2tb13 x) (t2tb10 y))
  (empty (tuple21 int (tuple21 (tuple21 bool bool) bool)))))) )))

;; singleton_is_function
  (assert
  (forall ((x Int) (y (set Int))) (! (mem (set1 (tuple21 int (set1 int)))
  (add (tuple21 int (set1 int)) (Tuple2 int (set1 int) (t2tb13 x) (t2tb3 y))
  (empty (tuple21 int (set1 int))))
  (infix_mnmngt (set1 int) int (t2tb3 (add2 x empty2))
  (t2tb1 (add3 y empty3)))) :pattern ((tb2t57
                                      (add (tuple21 int (set1 int))
                                      (Tuple2 int (set1 int) (t2tb13 x)
                                      (t2tb3 y))
                                      (empty (tuple21 int (set1 int)))))) )))

(declare-fun t2tb197 ((set (set (tuple2 Int (tuple2 Bool Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Int (tuple2 Bool Bool)))))) (sort
  (set1 (set1 (tuple21 int (tuple21 bool bool)))) (t2tb197 x))))

(declare-fun tb2t197 (uni) (set (set (tuple2 Int (tuple2 Bool Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Int (tuple2 Bool Bool))))))
  (! (= (tb2t197 (t2tb197 i)) i) :pattern ((t2tb197 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb197 (tb2t197 j)) j) :pattern ((t2tb197 (tb2t197 j))) )))

(declare-fun t2tb198 ((set (tuple2 Int (tuple2 Bool Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int (tuple2 Bool Bool))))) (sort
  (set1 (tuple21 int (tuple21 bool bool))) (t2tb198 x))))

(declare-fun tb2t198 (uni) (set (tuple2 Int (tuple2 Bool Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int (tuple2 Bool Bool)))))
  (! (= (tb2t198 (t2tb198 i)) i) :pattern ((t2tb198 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb198 (tb2t198 j)) j) :pattern ((t2tb198 (tb2t198 j))) )))

(declare-fun t2tb199 ((tuple2 Int (tuple2 Bool Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Int (tuple2 Bool Bool)))) (sort
  (tuple21 int (tuple21 bool bool)) (t2tb199 x))))

(declare-fun tb2t199 (uni) (tuple2 Int (tuple2 Bool Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 Int (tuple2 Bool Bool))))
  (! (= (tb2t199 (t2tb199 i)) i) :pattern ((t2tb199 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb199 (tb2t199 j)) j) :pattern ((t2tb199 (tb2t199 j))) )))

;; singleton_is_function
  (assert
  (forall ((x Int) (y (tuple2 Bool Bool))) (! (mem
  (set1 (tuple21 int (tuple21 bool bool)))
  (add (tuple21 int (tuple21 bool bool))
  (Tuple2 int (tuple21 bool bool) (t2tb13 x) (t2tb11 y))
  (empty (tuple21 int (tuple21 bool bool))))
  (infix_mnmngt (tuple21 bool bool) int (t2tb3 (add2 x empty2))
  (add (tuple21 bool bool) (t2tb11 y) (t2tb7 empty7)))) :pattern ((tb2t198
                                                                  (add
                                                                  (tuple21
                                                                  int
                                                                  (tuple21
                                                                  bool 
                                                                  bool))
                                                                  (Tuple2 
                                                                  int
                                                                  (tuple21
                                                                  bool 
                                                                  bool)
                                                                  (t2tb13 x)
                                                                  (t2tb11 y))
                                                                  (empty
                                                                  (tuple21
                                                                  int
                                                                  (tuple21
                                                                  bool 
                                                                  bool)))))) )))

;; singleton_is_function
  (assert
  (forall ((x Int) (y Bool)) (! (mem (set1 (tuple21 int bool))
  (add (tuple21 int bool) (Tuple2 int bool (t2tb13 x) (t2tb12 y))
  (empty (tuple21 int bool)))
  (infix_mnmngt bool int (t2tb3 (add2 x empty2)) (t2tb2 (add1 y empty1)))) :pattern (
  (tb2t60
  (add (tuple21 int bool) (Tuple2 int bool (t2tb13 x) (t2tb12 y))
  (empty (tuple21 int bool))))) )))

;; singleton_is_function
  (assert
  (forall ((x Int) (y Int)) (! (mem (set1 (tuple21 int int))
  (add (tuple21 int int) (Tuple2 int int (t2tb13 x) (t2tb13 y))
  (empty (tuple21 int int)))
  (infix_mnmngt int int (t2tb3 (add2 x empty2)) (t2tb3 (add2 y empty2)))) :pattern (
  (tb2t63
  (add (tuple21 int int) (Tuple2 int int (t2tb13 x) (t2tb13 y))
  (empty (tuple21 int int))))) )))

;; singleton_is_function
  (assert
  (forall ((b ty))
  (forall ((x Int) (y uni)) (! (mem (set1 (tuple21 int b))
  (add (tuple21 int b) (Tuple2 int b (t2tb13 x) y) (empty (tuple21 int b)))
  (infix_mnmngt b int (t2tb3 (add2 x empty2)) (add b y (empty b)))) :pattern (
  (add (tuple21 int b) (Tuple2 int b (t2tb13 x) y) (empty (tuple21 int b)))) ))))

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
  (forall ((f uni) (s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))) (t uni)
  (a (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))
  (=>
  (and (mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b))
  f
  (infix_plmngt b
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s) t)) (mem4 a
  (tb2t
  (dom b
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) f))))
  (mem
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b)
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b
  (t2tb4 a)
  (apply b
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) f
  (t2tb4 a))) f)))))

;; apply_def0
  (assert
  (forall ((f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (t (set (set Int))) (a (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (=>
  (and (mem4 f (infix_plmngt1 s t)) (mem
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 a)
  (dom (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb4 f)))) (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb9 a)
  (apply (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb4 f) (t2tb9 a))) (t2tb4 f)))))

;; apply_def0
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set (set Int))) (t uni) (a (set Int)))
  (=>
  (and (mem (set1 (tuple21 (set1 int) b)) f
  (infix_plmngt b (set1 int) (t2tb1 s) t)) (mem3 a
  (tb2t1 (dom b (set1 int) f)))) (mem (tuple21 (set1 int) b)
  (Tuple2 (set1 int) b (t2tb3 a) (apply b (set1 int) f (t2tb3 a))) f)))))

;; apply_def0
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set Bool)) (t uni) (a Bool))
  (=>
  (and (mem (set1 (tuple21 bool b)) f (infix_plmngt b bool (t2tb2 s) t))
  (mem2 a (tb2t2 (dom b bool f)))) (mem (tuple21 bool b)
  (Tuple2 bool b (t2tb12 a) (apply b bool f (t2tb12 a))) f)))))

;; apply_def0
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set Int)) (t uni) (a Int))
  (=>
  (and (mem (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb3 s) t)) (mem1
  a (tb2t3 (dom b int f)))) (mem (tuple21 int b)
  (Tuple2 int b (t2tb13 a) (apply b int f (t2tb13 a))) f)))))

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
  (forall ((f uni) (s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))) (t uni)
  (a (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))
  (=>
  (and (mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b))
  f
  (infix_mnmngt b
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s) t)) (mem4 a s)) (mem
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b)
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b
  (t2tb4 a)
  (apply b
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) f
  (t2tb4 a))) f)))))

;; apply_def1
  (assert
  (forall ((f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (t (set (set Int))) (a (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (=>
  (and (mem4 f
  (tb2t
  (infix_mnmngt (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 s) (t2tb1 t)))) (mem
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 a) (t2tb5 s)))
  (mem (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb9 a)
  (apply (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb4 f) (t2tb9 a))) (t2tb4 f)))))

;; apply_def1
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set (set Int))) (t uni) (a (set Int)))
  (=>
  (and (mem (set1 (tuple21 (set1 int) b)) f
  (infix_mnmngt b (set1 int) (t2tb1 s) t)) (mem3 a s)) (mem
  (tuple21 (set1 int) b)
  (Tuple2 (set1 int) b (t2tb3 a) (apply b (set1 int) f (t2tb3 a))) f)))))

;; apply_def1
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set Bool)) (t uni) (a Bool))
  (=>
  (and (mem (set1 (tuple21 bool b)) f (infix_mnmngt b bool (t2tb2 s) t))
  (mem2 a s)) (mem (tuple21 bool b)
  (Tuple2 bool b (t2tb12 a) (apply b bool f (t2tb12 a))) f)))))

;; apply_def1
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set Int)) (t uni) (a Int))
  (=>
  (and (mem (set1 (tuple21 int b)) f (infix_mnmngt b int (t2tb3 s) t)) (mem1
  a s)) (mem (tuple21 int b)
  (Tuple2 int b (t2tb13 a) (apply b int f (t2tb13 a))) f)))))

;; apply_def1
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni) (a1 uni))
  (=> (and (mem (set1 (tuple21 a b)) f (infix_mnmngt b a s t)) (mem a a1 s))
  (mem (tuple21 a b) (Tuple2 a b a1 (apply b a f a1)) f)))))

;; apply_def2
  (assert
  (forall ((f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (t (set (set Int))) (a (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (b (set Int)))
  (=>
  (and (mem4 f (infix_plmngt1 s t)) (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb9 a) (t2tb3 b)) (t2tb4 f)))
  (= (tb2t3
     (apply (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (t2tb4 f) (t2tb9 a))) b))))

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
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)) (y (set Int)))
  (= (tb2t3
     (apply (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (add
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
     (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
     (t2tb9 x) (t2tb3 y)) (t2tb4 empty4)) (t2tb9 x))) y)))

;; apply_singleton
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)) (y Bool))
  (= (tb2t12
     (apply bool (tuple21 (tuple21 bool bool) bool)
     (add (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (Tuple2 (tuple21 (tuple21 bool bool) bool) bool (t2tb10 x) (t2tb12 y))
     (t2tb5 empty5)) (t2tb10 x))) y)))

;; apply_singleton
  (assert
  (forall ((x (tuple2 Bool Bool)) (y Bool))
  (= (tb2t12
     (apply bool (tuple21 bool bool)
     (add (tuple21 (tuple21 bool bool) bool)
     (Tuple2 (tuple21 bool bool) bool (t2tb11 x) (t2tb12 y)) (t2tb6 empty6))
     (t2tb11 x))) y)))

;; apply_singleton
  (assert
  (forall ((x Bool) (y Bool))
  (= (tb2t12
     (apply bool bool
     (add (tuple21 bool bool) (Tuple2 bool bool (t2tb12 x) (t2tb12 y))
     (t2tb7 empty7)) (t2tb12 x))) y)))

;; apply_singleton
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (y uni))
  (=> (sort b y)
  (= (apply b a (add (tuple21 a b) (Tuple2 a b x y) (empty (tuple21 a b))) x) y)))))

;; apply_range
  (assert
  (forall ((a ty))
  (forall ((x uni) (f uni) (s uni)
  (t (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))))
  (! (=>
     (and (mem
     (set1
     (tuple21 a
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
     f
     (infix_plmngt
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     a s (t2tb t))) (mem a x
     (dom
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     a f))) (mem4
     (tb2t4
     (apply
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     a f x)) t)) :pattern ((mem
  (set1
  (tuple21 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))) f
  (infix_plmngt
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) a s
  (t2tb t)))
  (tb2t4
  (apply
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) a f
  x))) ))))

;; apply_range
  (assert
  (forall ((a ty))
  (forall ((x uni) (f uni) (s uni) (t (set (set Int))))
  (! (=>
     (and (mem (set1 (tuple21 a (set1 int))) f
     (infix_plmngt (set1 int) a s (t2tb1 t))) (mem a x (dom (set1 int) a f)))
     (mem3 (tb2t3 (apply (set1 int) a f x)) t)) :pattern ((mem
  (set1 (tuple21 a (set1 int))) f (infix_plmngt (set1 int) a s (t2tb1 t)))
  (tb2t3 (apply (set1 int) a f x))) ))))

;; apply_range
  (assert
  (forall ((a ty))
  (forall ((x uni) (f uni) (s uni) (t (set Bool)))
  (! (=>
     (and (mem (set1 (tuple21 a bool)) f (infix_plmngt bool a s (t2tb2 t)))
     (mem a x (dom bool a f))) (mem2 (tb2t12 (apply bool a f x)) t)) :pattern ((mem
  (set1 (tuple21 a bool)) f (infix_plmngt bool a s (t2tb2 t)))
  (tb2t12 (apply bool a f x))) ))))

;; apply_range
  (assert
  (forall ((a ty))
  (forall ((x uni) (f uni) (s uni) (t (set Int)))
  (! (=>
     (and (mem (set1 (tuple21 a int)) f (infix_plmngt int a s (t2tb3 t)))
     (mem a x (dom int a f))) (mem1 (tb2t13 (apply int a f x)) t)) :pattern ((mem
  (set1 (tuple21 a int)) f (infix_plmngt int a s (t2tb3 t)))
  (tb2t13 (apply int a f x))) ))))

;; apply_range
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (f (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))))
  (s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (t (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))))
  (! (=>
     (and (mem
     (set1
     (tuple21
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
     (t2tb21 f)
     (infix_plmngt
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb s) (t2tb t))) (mem4 x
     (tb2t
     (dom
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb21 f))))) (mem4
     (tb2t4
     (apply
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb21 f) (t2tb4 x))) t)) :pattern ((mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (t2tb21 f)
  (infix_plmngt
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s) (t2tb t)))
  (tb2t4
  (apply
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb21 f) (t2tb4 x)))) )))

;; apply_range
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (f (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (set Int))))
  (s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (t (set (set Int))))
  (! (=>
     (and (mem
     (set1
     (tuple21
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (set1 int))) (t2tb23 f)
     (infix_plmngt (set1 int)
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb s) (t2tb1 t))) (mem4 x
     (tb2t
     (dom (set1 int)
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb23 f))))) (mem3
     (tb2t3
     (apply (set1 int)
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb23 f) (t2tb4 x))) t)) :pattern ((mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1 int))) (t2tb23 f)
  (infix_plmngt (set1 int)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s) (t2tb1 t)))
  (tb2t3
  (apply (set1 int)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb23 f) (t2tb4 x)))) )))

;; apply_range
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (f (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) Bool)))
  (s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (t (set Bool)))
  (! (=>
     (and (mem
     (set1
     (tuple21
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     bool)) (t2tb27 f)
     (infix_plmngt bool
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb s) (t2tb2 t))) (mem4 x
     (tb2t
     (dom bool
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb27 f))))) (mem2
     (tb2t12
     (apply bool
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb27 f) (t2tb4 x))) t)) :pattern ((mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  bool)) (t2tb27 f)
  (infix_plmngt bool
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s) (t2tb2 t)))
  (tb2t12
  (apply bool
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb27 f) (t2tb4 x)))) )))

;; apply_range
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (f (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) Int)))
  (s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (t (set Int)))
  (! (=>
     (and (mem
     (set1
     (tuple21
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     int)) (t2tb30 f)
     (infix_plmngt int
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb s) (t2tb3 t))) (mem4 x
     (tb2t
     (dom int
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb30 f))))) (mem1
     (tb2t13
     (apply int
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb30 f) (t2tb4 x))) t)) :pattern ((mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  int)) (t2tb30 f)
  (infix_plmngt int
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s) (t2tb3 t)))
  (tb2t13
  (apply int
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb30 f) (t2tb4 x)))) )))

;; apply_range
  (assert
  (forall ((b ty))
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (f uni) (s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))) (t uni))
  (! (=>
     (and (mem
     (set1
     (tuple21
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     b)) f
     (infix_plmngt b
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb s) t)) (mem4 x
     (tb2t
     (dom b
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     f)))) (mem b
     (apply b
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     f (t2tb4 x)) t)) :pattern ((mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b))
  f
  (infix_plmngt b
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s) t))
  (apply b
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) f
  (t2tb4 x))) ))))

;; apply_range
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))
  (s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (t (set (set Int))))
  (! (=>
     (and (mem4 f (infix_plmngt1 s t)) (mem
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
     (dom (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (t2tb4 f)))) (mem3
     (tb2t3
     (apply (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (t2tb4 f) (t2tb9 x))) t)) :pattern ((mem4
  f (infix_plmngt1 s t))
  (tb2t3
  (apply (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb4 f) (t2tb9 x)))) )))

;; apply_range
  (assert
  (forall ((x (set Int)) (f (set (tuple2 (set Int)
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))))
  (s (set (set Int))) (t (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))))
  (! (=>
     (and (mem
     (set1
     (tuple21 (set1 int)
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
     (t2tb33 f)
     (infix_plmngt
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (set1 int) (t2tb1 s) (t2tb t))) (mem3 x
     (tb2t1
     (dom
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (set1 int) (t2tb33 f))))) (mem4
     (tb2t4
     (apply
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (set1 int) (t2tb33 f) (t2tb3 x))) t)) :pattern ((mem
  (set1
  (tuple21 (set1 int)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (t2tb33 f)
  (infix_plmngt
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1 int) (t2tb1 s) (t2tb t)))
  (tb2t4
  (apply
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1 int) (t2tb33 f) (t2tb3 x)))) )))

;; apply_range
  (assert
  (forall ((x (set Int)) (f (set (tuple2 (set Int) (set Int))))
  (s (set (set Int))) (t (set (set Int))))
  (! (=>
     (and (mem (set1 (tuple21 (set1 int) (set1 int))) (t2tb37 f)
     (infix_plmngt (set1 int) (set1 int) (t2tb1 s) (t2tb1 t))) (mem3 x
     (tb2t1 (dom (set1 int) (set1 int) (t2tb37 f))))) (mem3
     (tb2t3 (apply (set1 int) (set1 int) (t2tb37 f) (t2tb3 x))) t)) :pattern ((mem
  (set1 (tuple21 (set1 int) (set1 int))) (t2tb37 f)
  (infix_plmngt (set1 int) (set1 int) (t2tb1 s) (t2tb1 t)))
  (tb2t3 (apply (set1 int) (set1 int) (t2tb37 f) (t2tb3 x)))) )))

;; apply_range
  (assert
  (forall ((x (set Int)) (f (set (tuple2 (set Int) Bool)))
  (s (set (set Int))) (t (set Bool)))
  (! (=>
     (and (mem (set1 (tuple21 (set1 int) bool)) (t2tb39 f)
     (infix_plmngt bool (set1 int) (t2tb1 s) (t2tb2 t))) (mem3 x
     (tb2t1 (dom bool (set1 int) (t2tb39 f))))) (mem2
     (tb2t12 (apply bool (set1 int) (t2tb39 f) (t2tb3 x))) t)) :pattern ((mem
  (set1 (tuple21 (set1 int) bool)) (t2tb39 f)
  (infix_plmngt bool (set1 int) (t2tb1 s) (t2tb2 t)))
  (tb2t12 (apply bool (set1 int) (t2tb39 f) (t2tb3 x)))) )))

;; apply_range
  (assert
  (forall ((x (set Int)) (f (set (tuple2 (set Int) Int))) (s (set (set Int)))
  (t (set Int)))
  (! (=>
     (and (mem (set1 (tuple21 (set1 int) int)) (t2tb42 f)
     (infix_plmngt int (set1 int) (t2tb1 s) (t2tb3 t))) (mem3 x
     (tb2t1 (dom int (set1 int) (t2tb42 f))))) (mem1
     (tb2t13 (apply int (set1 int) (t2tb42 f) (t2tb3 x))) t)) :pattern ((mem
  (set1 (tuple21 (set1 int) int)) (t2tb42 f)
  (infix_plmngt int (set1 int) (t2tb1 s) (t2tb3 t)))
  (tb2t13 (apply int (set1 int) (t2tb42 f) (t2tb3 x)))) )))

;; apply_range
  (assert
  (forall ((b ty))
  (forall ((x (set Int)) (f uni) (s (set (set Int))) (t uni))
  (! (=>
     (and (mem (set1 (tuple21 (set1 int) b)) f
     (infix_plmngt b (set1 int) (t2tb1 s) t)) (mem3 x
     (tb2t1 (dom b (set1 int) f)))) (mem b (apply b (set1 int) f (t2tb3 x))
     t)) :pattern ((mem
  (set1 (tuple21 (set1 int) b)) f (infix_plmngt b (set1 int) (t2tb1 s) t))
  (apply b (set1 int) f (t2tb3 x))) ))))

;; apply_range
  (assert
  (forall ((x Bool) (f (set (tuple2 Bool
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))))
  (s (set Bool)) (t (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))))
  (! (=>
     (and (mem
     (set1
     (tuple21 bool
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
     (t2tb45 f)
     (infix_plmngt
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     bool (t2tb2 s) (t2tb t))) (mem2 x
     (tb2t2
     (dom
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     bool (t2tb45 f))))) (mem4
     (tb2t4
     (apply
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     bool (t2tb45 f) (t2tb12 x))) t)) :pattern ((mem
  (set1
  (tuple21 bool
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (t2tb45 f)
  (infix_plmngt
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  bool (t2tb2 s) (t2tb t)))
  (tb2t4
  (apply
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  bool (t2tb45 f) (t2tb12 x)))) )))

;; apply_range
  (assert
  (forall ((x Bool) (f (set (tuple2 Bool (set Int)))) (s (set Bool))
  (t (set (set Int))))
  (! (=>
     (and (mem (set1 (tuple21 bool (set1 int))) (t2tb48 f)
     (infix_plmngt (set1 int) bool (t2tb2 s) (t2tb1 t))) (mem2 x
     (tb2t2 (dom (set1 int) bool (t2tb48 f))))) (mem3
     (tb2t3 (apply (set1 int) bool (t2tb48 f) (t2tb12 x))) t)) :pattern ((mem
  (set1 (tuple21 bool (set1 int))) (t2tb48 f)
  (infix_plmngt (set1 int) bool (t2tb2 s) (t2tb1 t)))
  (tb2t3 (apply (set1 int) bool (t2tb48 f) (t2tb12 x)))) )))

;; apply_range
  (assert
  (forall ((x Bool) (f (set (tuple2 Bool Bool))) (s (set Bool))
  (t (set Bool)))
  (! (=>
     (and (mem (set1 (tuple21 bool bool)) (t2tb7 f)
     (infix_plmngt bool bool (t2tb2 s) (t2tb2 t))) (mem2 x
     (tb2t2 (dom bool bool (t2tb7 f))))) (mem2
     (tb2t12 (apply bool bool (t2tb7 f) (t2tb12 x))) t)) :pattern ((mem
  (set1 (tuple21 bool bool)) (t2tb7 f)
  (infix_plmngt bool bool (t2tb2 s) (t2tb2 t)))
  (tb2t12 (apply bool bool (t2tb7 f) (t2tb12 x)))) )))

;; apply_range
  (assert
  (forall ((x Bool) (f (set (tuple2 Bool Int))) (s (set Bool)) (t (set Int)))
  (! (=>
     (and (mem (set1 (tuple21 bool int)) (t2tb51 f)
     (infix_plmngt int bool (t2tb2 s) (t2tb3 t))) (mem2 x
     (tb2t2 (dom int bool (t2tb51 f))))) (mem1
     (tb2t13 (apply int bool (t2tb51 f) (t2tb12 x))) t)) :pattern ((mem
  (set1 (tuple21 bool int)) (t2tb51 f)
  (infix_plmngt int bool (t2tb2 s) (t2tb3 t)))
  (tb2t13 (apply int bool (t2tb51 f) (t2tb12 x)))) )))

;; apply_range
  (assert
  (forall ((b ty))
  (forall ((x Bool) (f uni) (s (set Bool)) (t uni))
  (! (=>
     (and (mem (set1 (tuple21 bool b)) f (infix_plmngt b bool (t2tb2 s) t))
     (mem2 x (tb2t2 (dom b bool f)))) (mem b (apply b bool f (t2tb12 x)) t)) :pattern ((mem
  (set1 (tuple21 bool b)) f (infix_plmngt b bool (t2tb2 s) t))
  (apply b bool f (t2tb12 x))) ))))

;; apply_range
  (assert
  (forall ((x Int) (f (set (tuple2 Int
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))))
  (s (set Int)) (t (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))))
  (! (=>
     (and (mem
     (set1
     (tuple21 int
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
     (t2tb54 f)
     (infix_plmngt
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     int (t2tb3 s) (t2tb t))) (mem1 x
     (tb2t3
     (dom
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     int (t2tb54 f))))) (mem4
     (tb2t4
     (apply
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     int (t2tb54 f) (t2tb13 x))) t)) :pattern ((mem
  (set1
  (tuple21 int
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (t2tb54 f)
  (infix_plmngt
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) 
  int (t2tb3 s) (t2tb t)))
  (tb2t4
  (apply
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) 
  int (t2tb54 f) (t2tb13 x)))) )))

;; apply_range
  (assert
  (forall ((x Int) (f (set (tuple2 Int (set Int)))) (s (set Int))
  (t (set (set Int))))
  (! (=>
     (and (mem (set1 (tuple21 int (set1 int))) (t2tb57 f)
     (infix_plmngt (set1 int) int (t2tb3 s) (t2tb1 t))) (mem1 x
     (tb2t3 (dom (set1 int) int (t2tb57 f))))) (mem3
     (tb2t3 (apply (set1 int) int (t2tb57 f) (t2tb13 x))) t)) :pattern ((mem
  (set1 (tuple21 int (set1 int))) (t2tb57 f)
  (infix_plmngt (set1 int) int (t2tb3 s) (t2tb1 t)))
  (tb2t3 (apply (set1 int) int (t2tb57 f) (t2tb13 x)))) )))

;; apply_range
  (assert
  (forall ((x Int) (f (set (tuple2 Int Bool))) (s (set Int)) (t (set Bool)))
  (! (=>
     (and (mem (set1 (tuple21 int bool)) (t2tb60 f)
     (infix_plmngt bool int (t2tb3 s) (t2tb2 t))) (mem1 x
     (tb2t3 (dom bool int (t2tb60 f))))) (mem2
     (tb2t12 (apply bool int (t2tb60 f) (t2tb13 x))) t)) :pattern ((mem
  (set1 (tuple21 int bool)) (t2tb60 f)
  (infix_plmngt bool int (t2tb3 s) (t2tb2 t)))
  (tb2t12 (apply bool int (t2tb60 f) (t2tb13 x)))) )))

;; apply_range
  (assert
  (forall ((x Int) (f (set (tuple2 Int Int))) (s (set Int)) (t (set Int)))
  (! (=>
     (and (mem (set1 (tuple21 int int)) (t2tb63 f)
     (infix_plmngt int int (t2tb3 s) (t2tb3 t))) (mem1 x
     (tb2t3 (dom int int (t2tb63 f))))) (mem1
     (tb2t13 (apply int int (t2tb63 f) (t2tb13 x))) t)) :pattern ((mem
  (set1 (tuple21 int int)) (t2tb63 f)
  (infix_plmngt int int (t2tb3 s) (t2tb3 t)))
  (tb2t13 (apply int int (t2tb63 f) (t2tb13 x)))) )))

;; apply_range
  (assert
  (forall ((b ty))
  (forall ((x Int) (f uni) (s (set Int)) (t uni))
  (! (=>
     (and (mem (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb3 s) t))
     (mem1 x (tb2t3 (dom b int f)))) (mem b (apply b int f (t2tb13 x)) t)) :pattern ((mem
  (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb3 s) t))
  (apply b int f (t2tb13 x))) ))))

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
  (forall ((f uni) (g (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))) (s uni) (t (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))) (u (set (set Int))))
  (=>
  (and (mem
  (set1 (tuple21 a (tuple21 (tuple21 (tuple21 bool bool) bool) bool))) f
  (infix_plmngt (tuple21 (tuple21 (tuple21 bool bool) bool) bool) a s
  (t2tb5 t))) (mem4 g (infix_plmngt1 t u))) (mem
  (set1 (tuple21 a (set1 int)))
  (semicolon (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool) a f
  (t2tb4 g)) (infix_plmngt (set1 int) a s (t2tb1 u)))))))

;; semicolon_is_function
  (assert
  (forall ((b ty))
  (forall ((f uni) (g uni) (s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))) (t uni) (u (set (set Int))))
  (=>
  (and (mem
  (set1 (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) b)) f
  (infix_plmngt b (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb5 s)
  t)) (mem (set1 (tuple21 b (set1 int))) g
  (infix_plmngt (set1 int) b t (t2tb1 u)))) (mem4
  (tb2t4
  (semicolon (set1 int) b (tuple21 (tuple21 (tuple21 bool bool) bool) bool) f
  g)) (infix_plmngt1 s u))))))

;; semicolon_is_function
  (assert
  (forall ((f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (g (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))
  (s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (t (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (u (set (set Int))))
  (=>
  (and (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))) (t2tb108 f)
  (infix_plmngt (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb5 s) (t2tb5 t)))
  (mem4 g (infix_plmngt1 t u))) (mem4
  (tb2t4
  (semicolon (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb108 f) (t2tb4 g)))
  (infix_plmngt1 s u)))))

;; semicolon_is_function
  (assert
  (forall ((f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (g (set (tuple2 (set Int) (set Int))))
  (s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (t (set (set Int))) (u (set (set Int))))
  (=>
  (and (mem4 f (infix_plmngt1 s t)) (mem
  (set1 (tuple21 (set1 int) (set1 int))) (t2tb37 g)
  (infix_plmngt (set1 int) (set1 int) (t2tb1 t) (t2tb1 u)))) (mem4
  (tb2t4
  (semicolon (set1 int) (set1 int)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb4 f) (t2tb37 g)))
  (infix_plmngt1 s u)))))

;; semicolon_is_function
  (assert
  (forall ((c ty))
  (forall ((f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (g uni) (s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))) (t (set (set Int))) (u uni))
  (=>
  (and (mem4 f (infix_plmngt1 s t)) (mem (set1 (tuple21 (set1 int) c)) g
  (infix_plmngt c (set1 int) (t2tb1 t) u))) (mem
  (set1 (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) c))
  (semicolon c (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb4 f) g)
  (infix_plmngt c (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb5 s)
  u))))))

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
  (forall ((x uni) (f uni) (g uni) (s uni)
  (t (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (u uni))
  (=>
  (and (mem
  (set1
  (tuple21 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))) f
  (infix_plmngt
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) a s
  (t2tb t)))
  (and (mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) c))
  g
  (infix_plmngt c
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb t) u))
  (and (mem a x
  (dom
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) a
  f)) (mem4
  (tb2t4
  (apply
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) a f
  x))
  (tb2t
  (dom c
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) g))))))
  (= (apply c a
     (semicolon c
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     a f g) x) (apply c
               (set1
               (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
               (set1 int))) g
               (apply
               (set1
               (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
               (set1 int))) a f x)))))))

;; apply_compose
  (assert
  (forall ((a ty))
  (forall ((x uni) (f uni) (g (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))) (s uni) (t (set (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool))) (u (set (set Int))))
  (=>
  (and (mem
  (set1 (tuple21 a (tuple21 (tuple21 (tuple21 bool bool) bool) bool))) f
  (infix_plmngt (tuple21 (tuple21 (tuple21 bool bool) bool) bool) a s
  (t2tb5 t)))
  (and (mem4 g (infix_plmngt1 t u))
  (and (mem a x (dom (tuple21 (tuple21 (tuple21 bool bool) bool) bool) a f))
  (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (apply (tuple21 (tuple21 (tuple21 bool bool) bool) bool) a f x)
  (dom (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb4 g))))))
  (= (tb2t3
     (apply (set1 int) a
     (semicolon (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     a f (t2tb4 g)) x)) (tb2t3
                        (apply (set1 int)
                        (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
                        (t2tb4 g)
                        (apply
                        (tuple21 (tuple21 (tuple21 bool bool) bool) bool) a f
                        x))))))))

;; apply_compose
  (assert
  (forall ((a ty) (c ty))
  (forall ((x uni) (f uni) (g uni) (s uni) (t (set (set Int))) (u uni))
  (=>
  (and (mem (set1 (tuple21 a (set1 int))) f
  (infix_plmngt (set1 int) a s (t2tb1 t)))
  (and (mem (set1 (tuple21 (set1 int) c)) g
  (infix_plmngt c (set1 int) (t2tb1 t) u))
  (and (mem a x (dom (set1 int) a f)) (mem3 (tb2t3 (apply (set1 int) a f x))
  (tb2t1 (dom c (set1 int) g))))))
  (= (apply c a (semicolon c (set1 int) a f g) x) (apply c (set1 int) g
                                                  (apply (set1 int) a f x)))))))

;; apply_compose
  (assert
  (forall ((a ty) (c ty))
  (forall ((x uni) (f uni) (g uni) (s uni) (t (set Bool)) (u uni))
  (=>
  (and (mem (set1 (tuple21 a bool)) f (infix_plmngt bool a s (t2tb2 t)))
  (and (mem (set1 (tuple21 bool c)) g (infix_plmngt c bool (t2tb2 t) u))
  (and (mem a x (dom bool a f)) (mem2 (tb2t12 (apply bool a f x))
  (tb2t2 (dom c bool g))))))
  (= (apply c a (semicolon c bool a f g) x) (apply c bool g
                                            (apply bool a f x)))))))

;; apply_compose
  (assert
  (forall ((a ty) (c ty))
  (forall ((x uni) (f uni) (g uni) (s uni) (t (set Int)) (u uni))
  (=>
  (and (mem (set1 (tuple21 a int)) f (infix_plmngt int a s (t2tb3 t)))
  (and (mem (set1 (tuple21 int c)) g (infix_plmngt c int (t2tb3 t) u))
  (and (mem a x (dom int a f)) (mem1 (tb2t13 (apply int a f x))
  (tb2t3 (dom c int g))))))
  (= (apply c a (semicolon c int a f g) x) (apply c int g (apply int a f x)))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (f (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))))) (g uni)
  (s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (t (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (u uni))
  (=>
  (and (mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (t2tb21 f)
  (infix_plmngt
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s) (t2tb t)))
  (and (mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) c))
  g
  (infix_plmngt c
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb t) u))
  (and (mem4 x
  (tb2t
  (dom
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb21 f)))) (mem4
  (tb2t4
  (apply
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb21 f) (t2tb4 x)))
  (tb2t
  (dom c
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) g))))))
  (= (apply c
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (semicolon c
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb21 f) g) (t2tb4 x)) (apply c
                              (set1
                              (tuple21
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool) (set1 int))) g
                              (apply
                              (set1
                              (tuple21
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool) (set1 int)))
                              (set1
                              (tuple21
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool) (set1 int))) (t2tb21 f) (t2tb4 x))))))))

;; apply_compose
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (f (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool)))) (g (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (t (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))) (u (set (set Int))))
  (=>
  (and (mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))) (t2tb70 f)
  (infix_plmngt (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s) (t2tb5 t)))
  (and (mem4 g (infix_plmngt1 t u))
  (and (mem4 x
  (tb2t
  (dom (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb70 f)))) (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (apply (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb70 f) (t2tb4 x))
  (dom (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb4 g))))))
  (= (tb2t3
     (apply (set1 int)
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (semicolon (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb70 f) (t2tb4 g)) (t2tb4 x))) (tb2t3
                                       (apply (set1 int)
                                       (tuple21
                                       (tuple21 (tuple21 bool bool) bool)
                                       bool) (t2tb4 g)
                                       (apply
                                       (tuple21
                                       (tuple21 (tuple21 bool bool) bool)
                                       bool)
                                       (set1
                                       (tuple21
                                       (tuple21
                                       (tuple21 (tuple21 bool bool) bool)
                                       bool) (set1 int))) (t2tb70 f)
                                       (t2tb4 x))))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (f (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) (set Int)))) (g uni)
  (s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (t (set (set Int))) (u uni))
  (=>
  (and (mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1 int))) (t2tb23 f)
  (infix_plmngt (set1 int)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s) (t2tb1 t)))
  (and (mem (set1 (tuple21 (set1 int) c)) g
  (infix_plmngt c (set1 int) (t2tb1 t) u))
  (and (mem4 x
  (tb2t
  (dom (set1 int)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb23 f)))) (mem3
  (tb2t3
  (apply (set1 int)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb23 f) (t2tb4 x))) (tb2t1 (dom c (set1 int) g))))))
  (= (apply c
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (semicolon c (set1 int)
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb23 f) g) (t2tb4 x)) (apply c (set1 int) g
                              (apply (set1 int)
                              (set1
                              (tuple21
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool) (set1 int))) (t2tb23 f) (t2tb4 x))))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (f (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) Bool))) (g uni)
  (s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (t (set Bool)) (u uni))
  (=>
  (and (mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  bool)) (t2tb27 f)
  (infix_plmngt bool
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s) (t2tb2 t)))
  (and (mem (set1 (tuple21 bool c)) g (infix_plmngt c bool (t2tb2 t) u))
  (and (mem4 x
  (tb2t
  (dom bool
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb27 f)))) (mem2
  (tb2t12
  (apply bool
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb27 f) (t2tb4 x))) (tb2t2 (dom c bool g))))))
  (= (apply c
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (semicolon c bool
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb27 f) g) (t2tb4 x)) (apply c bool g
                              (apply bool
                              (set1
                              (tuple21
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool) (set1 int))) (t2tb27 f) (t2tb4 x))))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (f (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))) Int))) (g uni)
  (s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (t (set Int)) (u uni))
  (=>
  (and (mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  int)) (t2tb30 f)
  (infix_plmngt int
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s) (t2tb3 t)))
  (and (mem (set1 (tuple21 int c)) g (infix_plmngt c int (t2tb3 t) u))
  (and (mem4 x
  (tb2t
  (dom int
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb30 f)))) (mem1
  (tb2t13
  (apply int
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb30 f) (t2tb4 x))) (tb2t3 (dom c int g))))))
  (= (apply c
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (semicolon c int
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb30 f) g) (t2tb4 x)) (apply c int g
                              (apply int
                              (set1
                              (tuple21
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool) (set1 int))) (t2tb30 f) (t2tb4 x))))))))

;; apply_compose
  (assert
  (forall ((b ty) (c ty))
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (f uni) (g uni)
  (s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (t uni) (u uni))
  (=>
  (and (mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b))
  f
  (infix_plmngt b
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s) t))
  (and (mem (set1 (tuple21 b c)) g (infix_plmngt c b t u))
  (and (mem4 x
  (tb2t
  (dom b
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) f)))
  (mem b
  (apply b
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) f
  (t2tb4 x)) (dom c b g)))))
  (= (apply c
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (semicolon c b
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     f g) (t2tb4 x)) (apply c b g
                     (apply b
                     (set1
                     (tuple21
                     (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
                     (set1 int))) f (t2tb4 x))))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))
  (g uni) (s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (t (set (set Int))) (u uni))
  (=>
  (and (mem4 f (infix_plmngt1 s t))
  (and (mem (set1 (tuple21 (set1 int) c)) g
  (infix_plmngt c (set1 int) (t2tb1 t) u))
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
  (dom (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb4 f))) (mem3
  (tb2t3
  (apply (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb4 f) (t2tb9 x))) (tb2t1 (dom c (set1 int) g))))))
  (= (apply c (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (semicolon c (set1 int)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb4 f) g)
     (t2tb9 x)) (apply c (set1 int) g
                (apply (set1 int)
                (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb4 f)
                (t2tb9 x))))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x (set Int)) (f (set (tuple2 (set Int)
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))))
  (g uni) (s (set (set Int)))
  (t (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (u uni))
  (=>
  (and (mem
  (set1
  (tuple21 (set1 int)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (t2tb33 f)
  (infix_plmngt
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1 int) (t2tb1 s) (t2tb t)))
  (and (mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) c))
  g
  (infix_plmngt c
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb t) u))
  (and (mem3 x
  (tb2t1
  (dom
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1 int) (t2tb33 f)))) (mem4
  (tb2t4
  (apply
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1 int) (t2tb33 f) (t2tb3 x)))
  (tb2t
  (dom c
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) g))))))
  (= (apply c (set1 int)
     (semicolon c
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (set1 int) (t2tb33 f) g) (t2tb3 x)) (apply c
                                         (set1
                                         (tuple21
                                         (tuple21
                                         (tuple21 (tuple21 bool bool) bool)
                                         bool) (set1 int))) g
                                         (apply
                                         (set1
                                         (tuple21
                                         (tuple21
                                         (tuple21 (tuple21 bool bool) bool)
                                         bool) (set1 int))) (set1 int)
                                         (t2tb33 f) (t2tb3 x))))))))

;; apply_compose
  (assert
  (forall ((x (set Int)) (f (set (tuple2 (set Int)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (g (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))
  (s (set (set Int))) (t (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))) (u (set (set Int))))
  (=>
  (and (mem
  (set1
  (tuple21 (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))
  (t2tb146 f)
  (infix_plmngt (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb1 s) (t2tb5 t)))
  (and (mem4 g (infix_plmngt1 t u))
  (and (mem3 x
  (tb2t1
  (dom (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb146 f)))) (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (apply (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb146 f) (t2tb3 x))
  (dom (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb4 g))))))
  (= (tb2t3
     (apply (set1 int) (set1 int)
     (semicolon (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 int) (t2tb146 f) (t2tb4 g)) (t2tb3 x))) (tb2t3
                                                   (apply (set1 int)
                                                   (tuple21
                                                   (tuple21
                                                   (tuple21 bool bool) 
                                                   bool) bool) (t2tb4 g)
                                                   (apply
                                                   (tuple21
                                                   (tuple21
                                                   (tuple21 bool bool) 
                                                   bool) bool) (set1 int)
                                                   (t2tb146 f) (t2tb3 x))))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x (set Int)) (f (set (tuple2 (set Int) (set Int)))) (g uni)
  (s (set (set Int))) (t (set (set Int))) (u uni))
  (=>
  (and (mem (set1 (tuple21 (set1 int) (set1 int))) (t2tb37 f)
  (infix_plmngt (set1 int) (set1 int) (t2tb1 s) (t2tb1 t)))
  (and (mem (set1 (tuple21 (set1 int) c)) g
  (infix_plmngt c (set1 int) (t2tb1 t) u))
  (and (mem3 x (tb2t1 (dom (set1 int) (set1 int) (t2tb37 f)))) (mem3
  (tb2t3 (apply (set1 int) (set1 int) (t2tb37 f) (t2tb3 x)))
  (tb2t1 (dom c (set1 int) g))))))
  (= (apply c (set1 int) (semicolon c (set1 int) (set1 int) (t2tb37 f) g)
     (t2tb3 x)) (apply c (set1 int) g
                (apply (set1 int) (set1 int) (t2tb37 f) (t2tb3 x))))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x (set Int)) (f (set (tuple2 (set Int) Bool))) (g uni)
  (s (set (set Int))) (t (set Bool)) (u uni))
  (=>
  (and (mem (set1 (tuple21 (set1 int) bool)) (t2tb39 f)
  (infix_plmngt bool (set1 int) (t2tb1 s) (t2tb2 t)))
  (and (mem (set1 (tuple21 bool c)) g (infix_plmngt c bool (t2tb2 t) u))
  (and (mem3 x (tb2t1 (dom bool (set1 int) (t2tb39 f)))) (mem2
  (tb2t12 (apply bool (set1 int) (t2tb39 f) (t2tb3 x)))
  (tb2t2 (dom c bool g))))))
  (= (apply c (set1 int) (semicolon c bool (set1 int) (t2tb39 f) g)
     (t2tb3 x)) (apply c bool g (apply bool (set1 int) (t2tb39 f) (t2tb3 x))))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x (set Int)) (f (set (tuple2 (set Int) Int))) (g uni)
  (s (set (set Int))) (t (set Int)) (u uni))
  (=>
  (and (mem (set1 (tuple21 (set1 int) int)) (t2tb42 f)
  (infix_plmngt int (set1 int) (t2tb1 s) (t2tb3 t)))
  (and (mem (set1 (tuple21 int c)) g (infix_plmngt c int (t2tb3 t) u))
  (and (mem3 x (tb2t1 (dom int (set1 int) (t2tb42 f)))) (mem1
  (tb2t13 (apply int (set1 int) (t2tb42 f) (t2tb3 x)))
  (tb2t3 (dom c int g))))))
  (= (apply c (set1 int) (semicolon c int (set1 int) (t2tb42 f) g) (t2tb3 x)) 
  (apply c int g (apply int (set1 int) (t2tb42 f) (t2tb3 x))))))))

;; apply_compose
  (assert
  (forall ((b ty) (c ty))
  (forall ((x (set Int)) (f uni) (g uni) (s (set (set Int))) (t uni) (u uni))
  (=>
  (and (mem (set1 (tuple21 (set1 int) b)) f
  (infix_plmngt b (set1 int) (t2tb1 s) t))
  (and (mem (set1 (tuple21 b c)) g (infix_plmngt c b t u))
  (and (mem3 x (tb2t1 (dom b (set1 int) f))) (mem b
  (apply b (set1 int) f (t2tb3 x)) (dom c b g)))))
  (= (apply c (set1 int) (semicolon c b (set1 int) f g) (t2tb3 x)) (apply c b
                                                                   g
                                                                   (apply b
                                                                   (set1 int)
                                                                   f
                                                                   (t2tb3 x))))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x Bool) (f (set (tuple2 Bool
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))))
  (g uni) (s (set Bool)) (t (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))) (u uni))
  (=>
  (and (mem
  (set1
  (tuple21 bool
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (t2tb45 f)
  (infix_plmngt
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  bool (t2tb2 s) (t2tb t)))
  (and (mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) c))
  g
  (infix_plmngt c
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb t) u))
  (and (mem2 x
  (tb2t2
  (dom
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  bool (t2tb45 f)))) (mem4
  (tb2t4
  (apply
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  bool (t2tb45 f) (t2tb12 x)))
  (tb2t
  (dom c
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) g))))))
  (= (apply c bool
     (semicolon c
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     bool (t2tb45 f) g) (t2tb12 x)) (apply c
                                    (set1
                                    (tuple21
                                    (tuple21
                                    (tuple21 (tuple21 bool bool) bool) 
                                    bool) (set1 int))) g
                                    (apply
                                    (set1
                                    (tuple21
                                    (tuple21
                                    (tuple21 (tuple21 bool bool) bool) 
                                    bool) (set1 int))) bool (t2tb45 f)
                                    (t2tb12 x))))))))

;; apply_compose
  (assert
  (forall ((x Bool) (f (set (tuple2 Bool (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool)))) (g (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))) (s (set Bool)) (t (set (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool))) (u (set (set Int))))
  (=>
  (and (mem
  (set1 (tuple21 bool (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))
  (t2tb180 f)
  (infix_plmngt (tuple21 (tuple21 (tuple21 bool bool) bool) bool) bool
  (t2tb2 s) (t2tb5 t)))
  (and (mem4 g (infix_plmngt1 t u))
  (and (mem2 x
  (tb2t2
  (dom (tuple21 (tuple21 (tuple21 bool bool) bool) bool) bool (t2tb180 f))))
  (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (apply (tuple21 (tuple21 (tuple21 bool bool) bool) bool) bool (t2tb180 f)
  (t2tb12 x))
  (dom (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb4 g))))))
  (= (tb2t3
     (apply (set1 int) bool
     (semicolon (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     bool (t2tb180 f) (t2tb4 g)) (t2tb12 x))) (tb2t3
                                              (apply (set1 int)
                                              (tuple21
                                              (tuple21 (tuple21 bool bool)
                                              bool) bool) (t2tb4 g)
                                              (apply
                                              (tuple21
                                              (tuple21 (tuple21 bool bool)
                                              bool) bool) bool (t2tb180 f)
                                              (t2tb12 x))))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x Bool) (f (set (tuple2 Bool (set Int)))) (g uni) (s (set Bool))
  (t (set (set Int))) (u uni))
  (=>
  (and (mem (set1 (tuple21 bool (set1 int))) (t2tb48 f)
  (infix_plmngt (set1 int) bool (t2tb2 s) (t2tb1 t)))
  (and (mem (set1 (tuple21 (set1 int) c)) g
  (infix_plmngt c (set1 int) (t2tb1 t) u))
  (and (mem2 x (tb2t2 (dom (set1 int) bool (t2tb48 f)))) (mem3
  (tb2t3 (apply (set1 int) bool (t2tb48 f) (t2tb12 x)))
  (tb2t1 (dom c (set1 int) g))))))
  (= (apply c bool (semicolon c (set1 int) bool (t2tb48 f) g) (t2tb12 x)) 
  (apply c (set1 int) g (apply (set1 int) bool (t2tb48 f) (t2tb12 x))))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x Bool) (f (set (tuple2 Bool Bool))) (g uni) (s (set Bool))
  (t (set Bool)) (u uni))
  (=>
  (and (mem (set1 (tuple21 bool bool)) (t2tb7 f)
  (infix_plmngt bool bool (t2tb2 s) (t2tb2 t)))
  (and (mem (set1 (tuple21 bool c)) g (infix_plmngt c bool (t2tb2 t) u))
  (and (mem2 x (tb2t2 (dom bool bool (t2tb7 f)))) (mem2
  (tb2t12 (apply bool bool (t2tb7 f) (t2tb12 x))) (tb2t2 (dom c bool g))))))
  (= (apply c bool (semicolon c bool bool (t2tb7 f) g) (t2tb12 x)) (apply c
                                                                   bool g
                                                                   (apply
                                                                   bool 
                                                                   bool
                                                                   (t2tb7 f)
                                                                   (t2tb12 x))))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x Bool) (f (set (tuple2 Bool Int))) (g uni) (s (set Bool))
  (t (set Int)) (u uni))
  (=>
  (and (mem (set1 (tuple21 bool int)) (t2tb51 f)
  (infix_plmngt int bool (t2tb2 s) (t2tb3 t)))
  (and (mem (set1 (tuple21 int c)) g (infix_plmngt c int (t2tb3 t) u))
  (and (mem2 x (tb2t2 (dom int bool (t2tb51 f)))) (mem1
  (tb2t13 (apply int bool (t2tb51 f) (t2tb12 x))) (tb2t3 (dom c int g))))))
  (= (apply c bool (semicolon c int bool (t2tb51 f) g) (t2tb12 x)) (apply c
                                                                   int g
                                                                   (apply 
                                                                   int 
                                                                   bool
                                                                   (t2tb51 f)
                                                                   (t2tb12 x))))))))

;; apply_compose
  (assert
  (forall ((b ty) (c ty))
  (forall ((x Bool) (f uni) (g uni) (s (set Bool)) (t uni) (u uni))
  (=>
  (and (mem (set1 (tuple21 bool b)) f (infix_plmngt b bool (t2tb2 s) t))
  (and (mem (set1 (tuple21 b c)) g (infix_plmngt c b t u))
  (and (mem2 x (tb2t2 (dom b bool f))) (mem b (apply b bool f (t2tb12 x))
  (dom c b g)))))
  (= (apply c bool (semicolon c b bool f g) (t2tb12 x)) (apply c b g
                                                        (apply b bool f
                                                        (t2tb12 x))))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x Int) (f (set (tuple2 Int
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))))
  (g uni) (s (set Int)) (t (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))) (u uni))
  (=>
  (and (mem
  (set1
  (tuple21 int
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (t2tb54 f)
  (infix_plmngt
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) 
  int (t2tb3 s) (t2tb t)))
  (and (mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) c))
  g
  (infix_plmngt c
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb t) u))
  (and (mem1 x
  (tb2t3
  (dom
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) 
  int (t2tb54 f)))) (mem4
  (tb2t4
  (apply
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) 
  int (t2tb54 f) (t2tb13 x)))
  (tb2t
  (dom c
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) g))))))
  (= (apply c int
     (semicolon c
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     int (t2tb54 f) g) (t2tb13 x)) (apply c
                                   (set1
                                   (tuple21
                                   (tuple21
                                   (tuple21 (tuple21 bool bool) bool) 
                                   bool) (set1 int))) g
                                   (apply
                                   (set1
                                   (tuple21
                                   (tuple21
                                   (tuple21 (tuple21 bool bool) bool) 
                                   bool) (set1 int))) int (t2tb54 f)
                                   (t2tb13 x))))))))

;; apply_compose
  (assert
  (forall ((x Int) (f (set (tuple2 Int (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool)))) (g (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))) (s (set Int)) (t (set (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool))) (u (set (set Int))))
  (=>
  (and (mem
  (set1 (tuple21 int (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))
  (t2tb192 f)
  (infix_plmngt (tuple21 (tuple21 (tuple21 bool bool) bool) bool) int
  (t2tb3 s) (t2tb5 t)))
  (and (mem4 g (infix_plmngt1 t u))
  (and (mem1 x
  (tb2t3
  (dom (tuple21 (tuple21 (tuple21 bool bool) bool) bool) int (t2tb192 f))))
  (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (apply (tuple21 (tuple21 (tuple21 bool bool) bool) bool) int (t2tb192 f)
  (t2tb13 x))
  (dom (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb4 g))))))
  (= (tb2t3
     (apply (set1 int) int
     (semicolon (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     int (t2tb192 f) (t2tb4 g)) (t2tb13 x))) (tb2t3
                                             (apply (set1 int)
                                             (tuple21
                                             (tuple21 (tuple21 bool bool)
                                             bool) bool) (t2tb4 g)
                                             (apply
                                             (tuple21
                                             (tuple21 (tuple21 bool bool)
                                             bool) bool) int (t2tb192 f)
                                             (t2tb13 x))))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x Int) (f (set (tuple2 Int (set Int)))) (g uni) (s (set Int))
  (t (set (set Int))) (u uni))
  (=>
  (and (mem (set1 (tuple21 int (set1 int))) (t2tb57 f)
  (infix_plmngt (set1 int) int (t2tb3 s) (t2tb1 t)))
  (and (mem (set1 (tuple21 (set1 int) c)) g
  (infix_plmngt c (set1 int) (t2tb1 t) u))
  (and (mem1 x (tb2t3 (dom (set1 int) int (t2tb57 f)))) (mem3
  (tb2t3 (apply (set1 int) int (t2tb57 f) (t2tb13 x)))
  (tb2t1 (dom c (set1 int) g))))))
  (= (apply c int (semicolon c (set1 int) int (t2tb57 f) g) (t2tb13 x)) 
  (apply c (set1 int) g (apply (set1 int) int (t2tb57 f) (t2tb13 x))))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x Int) (f (set (tuple2 Int Bool))) (g uni) (s (set Int))
  (t (set Bool)) (u uni))
  (=>
  (and (mem (set1 (tuple21 int bool)) (t2tb60 f)
  (infix_plmngt bool int (t2tb3 s) (t2tb2 t)))
  (and (mem (set1 (tuple21 bool c)) g (infix_plmngt c bool (t2tb2 t) u))
  (and (mem1 x (tb2t3 (dom bool int (t2tb60 f)))) (mem2
  (tb2t12 (apply bool int (t2tb60 f) (t2tb13 x))) (tb2t2 (dom c bool g))))))
  (= (apply c int (semicolon c bool int (t2tb60 f) g) (t2tb13 x)) (apply c
                                                                  bool g
                                                                  (apply 
                                                                  bool 
                                                                  int
                                                                  (t2tb60 f)
                                                                  (t2tb13 x))))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x Int) (f (set (tuple2 Int Int))) (g uni) (s (set Int))
  (t (set Int)) (u uni))
  (=>
  (and (mem (set1 (tuple21 int int)) (t2tb63 f)
  (infix_plmngt int int (t2tb3 s) (t2tb3 t)))
  (and (mem (set1 (tuple21 int c)) g (infix_plmngt c int (t2tb3 t) u))
  (and (mem1 x (tb2t3 (dom int int (t2tb63 f)))) (mem1
  (tb2t13 (apply int int (t2tb63 f) (t2tb13 x))) (tb2t3 (dom c int g))))))
  (= (apply c int (semicolon c int int (t2tb63 f) g) (t2tb13 x)) (apply c 
                                                                 int g
                                                                 (apply 
                                                                 int 
                                                                 int
                                                                 (t2tb63 f)
                                                                 (t2tb13 x))))))))

;; apply_compose
  (assert
  (forall ((b ty) (c ty))
  (forall ((x Int) (f uni) (g uni) (s (set Int)) (t uni) (u uni))
  (=>
  (and (mem (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb3 s) t))
  (and (mem (set1 (tuple21 b c)) g (infix_plmngt c b t u))
  (and (mem1 x (tb2t3 (dom b int f))) (mem b (apply b int f (t2tb13 x))
  (dom c b g)))))
  (= (apply c int (semicolon c b int f g) (t2tb13 x)) (apply c b g
                                                      (apply b int f
                                                      (t2tb13 x))))))))

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
  (forall ((f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (t (set (set Int))))
  (= (mem4 f
  (tb2t
  (infix_gtplgt (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 s) (t2tb1 t))))
  (and (mem4 f (infix_plmngt1 s t)) (mem
  (set1
  (tuple21 (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))
  (inverse (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb4 f))
  (infix_plmngt (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb1 t) (t2tb5 s)))))))

;; mem_partial_injection
  (assert
  (forall ((f (set (tuple2 (set Int) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool)))) (s (set (set Int))) (t (set (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool))))
  (= (mem
  (set1
  (tuple21 (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))
  (t2tb146 f)
  (infix_gtplgt (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb1 s) (t2tb5 t)))
  (and (mem
  (set1
  (tuple21 (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))
  (t2tb146 f)
  (infix_plmngt (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb1 s) (t2tb5 t))) (mem4
  (tb2t4
  (inverse (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb146 f))) (infix_plmngt1 t s))))))

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
  (forall ((f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (t (set (set Int))))
  (= (mem4 f
  (tb2t
  (infix_gtmngt (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 s) (t2tb1 t))))
  (and (mem4 f
  (tb2t
  (infix_gtplgt (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 s) (t2tb1 t)))) (mem4 f
  (tb2t
  (infix_mnmngt (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 s) (t2tb1 t))))))))

;; mem_total_injection
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni))
  (= (mem (set1 (tuple21 a b)) f (infix_gtmngt b a s t))
  (and (mem (set1 (tuple21 a b)) f (infix_gtplgt b a s t)) (mem
  (set1 (tuple21 a b)) f (infix_mnmngt b a s t)))))))

;; mem_total_injection_alt
  (assert
  (forall ((f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (t (set (set Int))))
  (= (mem4 f
  (tb2t
  (infix_gtmngt (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 s) (t2tb1 t))))
  (and (mem4 f
  (tb2t
  (infix_mnmngt (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 s) (t2tb1 t)))) (mem
  (set1
  (tuple21 (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))
  (inverse (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb4 f))
  (infix_plmngt (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb1 t) (t2tb5 s)))))))

;; mem_total_injection_alt
  (assert
  (forall ((f (set (tuple2 (set Int) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool)))) (s (set (set Int))) (t (set (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool))))
  (= (mem
  (set1
  (tuple21 (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))
  (t2tb146 f)
  (infix_gtmngt (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb1 s) (t2tb5 t)))
  (and (mem
  (set1
  (tuple21 (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))
  (t2tb146 f)
  (infix_mnmngt (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb1 s) (t2tb5 t))) (mem4
  (tb2t4
  (inverse (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb146 f))) (infix_plmngt1 t s))))))

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
  (forall ((f uni) (s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))) (t uni))
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))
  (=> (mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b))
  f
  (infix_gtmngt b
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s) t))
  (=> (mem4 x s)
  (=> (mem4 y s)
  (=>
  (= (apply b
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     f (t2tb4 x)) (apply b
                  (set1
                  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
                  (set1 int))) f (t2tb4 y)))
  (= x y)))))))))

;; injection
  (assert
  (forall ((f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (t (set (set Int))))
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (y (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (=> (mem4 f
  (tb2t
  (infix_gtmngt (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 s) (t2tb1 t))))
  (=> (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
  (t2tb5 s))
  (=> (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 y)
  (t2tb5 s))
  (=>
  (= (tb2t3
     (apply (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (t2tb4 f) (t2tb9 x))) (tb2t3
                           (apply (set1 int)
                           (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
                           (t2tb4 f) (t2tb9 y))))
  (= x y))))))))

;; injection
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set (set Int))) (t uni))
  (forall ((x (set Int)) (y (set Int)))
  (=> (mem (set1 (tuple21 (set1 int) b)) f
  (infix_gtmngt b (set1 int) (t2tb1 s) t))
  (=> (mem3 x s)
  (=> (mem3 y s)
  (=> (= (apply b (set1 int) f (t2tb3 x)) (apply b (set1 int) f (t2tb3 y)))
  (= x y)))))))))

;; injection
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set Bool)) (t uni))
  (forall ((x Bool) (y Bool))
  (=> (mem (set1 (tuple21 bool b)) f (infix_gtmngt b bool (t2tb2 s) t))
  (=> (mem2 x s)
  (=> (mem2 y s)
  (=> (= (apply b bool f (t2tb12 x)) (apply b bool f (t2tb12 y))) (= x y)))))))))

;; injection
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set Int)) (t uni))
  (forall ((x Int) (y Int))
  (=> (mem (set1 (tuple21 int b)) f (infix_gtmngt b int (t2tb3 s) t))
  (=> (mem1 x s)
  (=> (mem1 y s)
  (=> (= (apply b int f (t2tb13 x)) (apply b int f (t2tb13 y))) (= x y)))))))))

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
  (forall ((f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (t (set (set Int))))
  (= (mem4 f
  (tb2t
  (infix_plmngtgt (set1 int)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb5 s) (t2tb1 t))))
  (and (mem4 f (infix_plmngt1 s t))
  (= (tb2t1
     (ran (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (t2tb4 f))) t)))))

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
  (forall ((f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (t (set (set Int))))
  (= (mem4 f
  (tb2t
  (infix_mnmngtgt (set1 int)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb5 s) (t2tb1 t))))
  (and (mem4 f
  (tb2t
  (infix_plmngtgt (set1 int)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb5 s) (t2tb1 t))))
  (mem4 f
  (tb2t
  (infix_mnmngt (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 s) (t2tb1 t))))))))

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
  (forall ((f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (t (set (set Int))))
  (= (mem4 f
  (tb2t
  (infix_gtplgtgt (set1 int)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb5 s) (t2tb1 t))))
  (and (mem4 f
  (tb2t
  (infix_gtplgt (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 s) (t2tb1 t)))) (mem4 f
  (tb2t
  (infix_plmngtgt (set1 int)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb5 s) (t2tb1 t))))))))

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
  (forall ((f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (t (set (set Int))))
  (= (mem4 f
  (tb2t
  (infix_gtmngtgt (set1 int)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb5 s) (t2tb1 t))))
  (and (mem4 f
  (tb2t
  (infix_gtmngt (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 s) (t2tb1 t)))) (mem4 f
  (tb2t
  (infix_mnmngtgt (set1 int)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb5 s) (t2tb1 t))))))))

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
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))))
  (= (mem
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb4 x) (t2tb4 y))
  (id
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s))) (and (mem4 x s) (= x y)))))

;; id_def
  (assert
  (forall ((x (set Int)) (y (set Int)) (s (set (set Int))))
  (= (mem (tuple21 (set1 int) (set1 int))
  (Tuple2 (set1 int) (set1 int) (t2tb3 x) (t2tb3 y))
  (id (set1 int) (t2tb1 s))) (and (mem3 x s) (= x y)))))

;; id_def
  (assert
  (forall ((x Bool) (y Bool) (s (set Bool)))
  (= (mem (tuple21 bool bool) (Tuple2 bool bool (t2tb12 x) (t2tb12 y))
  (id bool (t2tb2 s))) (and (mem2 x s) (= x y)))))

;; id_def
  (assert
  (forall ((x Int) (y Int) (s (set Int)))
  (= (mem (tuple21 int int) (Tuple2 int int (t2tb13 x) (t2tb13 y))
  (id int (t2tb3 s))) (and (mem1 x s) (= x y)))))

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
  (= (seq_length a n s) (infix_mnmngt a int (t2tb3 (mk 1 n)) s)))))

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
  (infix_mnmngt a int (t2tb3 (mk 1 (size a r))) s))))))

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
  (forall ((s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))))) (is_finite_subset
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb empty8) (t2tb s) 0)))

;; Empty
  (assert
  (forall ((s (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (is_finite_subset
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb4 empty4) (t2tb4 s) 0)))

;; Empty
  (assert
  (forall ((s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (is_finite_subset (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 empty5) (t2tb5 s) 0)))

;; Empty
  (assert
  (forall ((s (set (tuple2 (tuple2 Bool Bool) Bool)))) (is_finite_subset
  (tuple21 (tuple21 bool bool) bool) (t2tb6 empty6) (t2tb6 s) 0)))

;; Empty
  (assert
  (forall ((s (set (set Int)))) (is_finite_subset (set1 int) (t2tb1 empty3)
  (t2tb1 s) 0)))

;; Empty
  (assert
  (forall ((s (set (tuple2 Bool Bool)))) (is_finite_subset
  (tuple21 bool bool) (t2tb7 empty7) (t2tb7 s) 0)))

;; Empty
  (assert
  (forall ((s (set Bool))) (is_finite_subset bool (t2tb2 empty1) (t2tb2 s)
  0)))

;; Empty
  (assert
  (forall ((s (set Int))) (is_finite_subset int (t2tb3 empty2) (t2tb3 s) 0)))

;; Empty
  (assert
  (forall ((a ty)) (forall ((s uni)) (is_finite_subset a (empty a) s 0))))

;; Add_mem
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s1 (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (s2 (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))) (c Int))
  (=> (is_finite_subset
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s1) (t2tb s2) c)
  (=> (mem4 x s2)
  (=> (mem4 x s1) (is_finite_subset
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb (add4 x s1)) (t2tb s2) c))))))

;; Add_mem
  (assert
  (forall ((x (set Int)) (s1 (set (set Int))) (s2 (set (set Int))) (c Int))
  (=> (is_finite_subset (set1 int) (t2tb1 s1) (t2tb1 s2) c)
  (=> (mem3 x s2)
  (=> (mem3 x s1) (is_finite_subset (set1 int) (t2tb1 (add3 x s1)) (t2tb1 s2)
  c))))))

;; Add_mem
  (assert
  (forall ((x Bool) (s1 (set Bool)) (s2 (set Bool)) (c Int))
  (=> (is_finite_subset bool (t2tb2 s1) (t2tb2 s2) c)
  (=> (mem2 x s2)
  (=> (mem2 x s1) (is_finite_subset bool (t2tb2 (add1 x s1)) (t2tb2 s2) c))))))

;; Add_mem
  (assert
  (forall ((x Int) (s1 (set Int)) (s2 (set Int)) (c Int))
  (=> (is_finite_subset int (t2tb3 s1) (t2tb3 s2) c)
  (=> (mem1 x s2)
  (=> (mem1 x s1) (is_finite_subset int (t2tb3 (add2 x s1)) (t2tb3 s2) c))))))

;; Add_mem
  (assert
  (forall ((a ty))
  (forall ((x uni) (s1 uni) (s2 uni) (c Int))
  (=> (is_finite_subset a s1 s2 c)
  (=> (mem a x s2) (=> (mem a x s1) (is_finite_subset a (add a x s1) s2 c)))))))

;; Add_notmem
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s1 (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (s2 (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))) (c Int))
  (=> (is_finite_subset
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s1) (t2tb s2) c)
  (=> (mem4 x s2)
  (=> (not (mem4 x s1)) (is_finite_subset
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb (add4 x s1)) (t2tb s2) (+ c 1)))))))

;; Add_notmem
  (assert
  (forall ((x (set Int)) (s1 (set (set Int))) (s2 (set (set Int))) (c Int))
  (=> (is_finite_subset (set1 int) (t2tb1 s1) (t2tb1 s2) c)
  (=> (mem3 x s2)
  (=> (not (mem3 x s1)) (is_finite_subset (set1 int) (t2tb1 (add3 x s1))
  (t2tb1 s2) (+ c 1)))))))

;; Add_notmem
  (assert
  (forall ((x Bool) (s1 (set Bool)) (s2 (set Bool)) (c Int))
  (=> (is_finite_subset bool (t2tb2 s1) (t2tb2 s2) c)
  (=> (mem2 x s2)
  (=> (not (mem2 x s1)) (is_finite_subset bool (t2tb2 (add1 x s1)) (t2tb2 s2)
  (+ c 1)))))))

;; Add_notmem
  (assert
  (forall ((x Int) (s1 (set Int)) (s2 (set Int)) (c Int))
  (=> (is_finite_subset int (t2tb3 s1) (t2tb3 s2) c)
  (=> (mem1 x s2)
  (=> (not (mem1 x s1)) (is_finite_subset int (t2tb3 (add2 x s1)) (t2tb3 s2)
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
  (forall ((z (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (z1 (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))) (z2 Int))
  (=> (is_finite_subset
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb z) (t2tb z1) z2)
  (or
  (or
  (exists ((s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))))) (and (and (= z empty8) (= z1 s)) (= z2 0)))
  (exists ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s1 (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (s2 (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))) (c Int))
  (and (is_finite_subset
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s1) (t2tb s2) c)
  (and (mem4 x s2)
  (and (mem4 x s1) (and (and (= z (add4 x s1)) (= z1 s2)) (= z2 c)))))))
  (exists ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s1 (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (s2 (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))) (c Int))
  (and (is_finite_subset
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s1) (t2tb s2) c)
  (and (mem4 x s2)
  (and (not (mem4 x s1))
  (and (and (= z (add4 x s1)) (= z1 s2)) (= z2 (+ c 1)))))))))))

;; is_finite_subset_inversion
  (assert
  (forall ((z (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (z1 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))) (z2 Int))
  (=> (is_finite_subset
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb4 z) (t2tb4 z1) z2)
  (or
  (or
  (exists ((s (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (and (and (= z empty4) (= z1 s)) (= z2 0)))
  (exists ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))) (s1 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))) (c Int))
  (and (is_finite_subset
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb4 s1) (t2tb4 s2) c)
  (and (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb8 x) (t2tb4 s2))
  (and (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb8 x) (t2tb4 s1))
  (and
  (and
  (= z (tb2t4
       (add
       (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
       (t2tb8 x) (t2tb4 s1))))
  (= z1 s2)) (= z2 c)))))))
  (exists ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))) (s1 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))) (c Int))
  (and (is_finite_subset
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb4 s1) (t2tb4 s2) c)
  (and (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb8 x) (t2tb4 s2))
  (and
  (not (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb8 x) (t2tb4 s1)))
  (and
  (and
  (= z (tb2t4
       (add
       (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
       (t2tb8 x) (t2tb4 s1))))
  (= z1 s2)) (= z2 (+ c 1)))))))))))

;; is_finite_subset_inversion
  (assert
  (forall ((z (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (z1 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))) (z2 Int))
  (=> (is_finite_subset (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 z) (t2tb5 z1) z2)
  (or
  (or
  (exists ((s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (and (and (= z empty5) (= z1 s)) (= z2 0)))
  (exists ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (s1 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (s2 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))) (c Int))
  (and (is_finite_subset (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 s1) (t2tb5 s2) c)
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
  (t2tb5 s2))
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
  (t2tb5 s1))
  (and
  (and
  (= z (tb2t5
       (add (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
       (t2tb5 s1))))
  (= z1 s2)) (= z2 c)))))))
  (exists ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (s1 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (s2 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))) (c Int))
  (and (is_finite_subset (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 s1) (t2tb5 s2) c)
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
  (t2tb5 s2))
  (and
  (not (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
  (t2tb5 s1)))
  (and
  (and
  (= z (tb2t5
       (add (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
       (t2tb5 s1))))
  (= z1 s2)) (= z2 (+ c 1)))))))))))

;; is_finite_subset_inversion
  (assert
  (forall ((z (set (tuple2 (tuple2 Bool Bool) Bool)))
  (z1 (set (tuple2 (tuple2 Bool Bool) Bool))) (z2 Int))
  (=> (is_finite_subset (tuple21 (tuple21 bool bool) bool) (t2tb6 z)
  (t2tb6 z1) z2)
  (or
  (or
  (exists ((s (set (tuple2 (tuple2 Bool Bool) Bool))))
  (and (and (= z empty6) (= z1 s)) (= z2 0)))
  (exists ((x (tuple2 (tuple2 Bool Bool) Bool)) (s1 (set (tuple2 (tuple2 Bool
  Bool) Bool))) (s2 (set (tuple2 (tuple2 Bool Bool) Bool))) (c Int))
  (and (is_finite_subset (tuple21 (tuple21 bool bool) bool) (t2tb6 s1)
  (t2tb6 s2) c)
  (and (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb6 s2))
  (and (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb6 s1))
  (and
  (and
  (= z (tb2t6 (add (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb6 s1))))
  (= z1 s2)) (= z2 c)))))))
  (exists ((x (tuple2 (tuple2 Bool Bool) Bool)) (s1 (set (tuple2 (tuple2 Bool
  Bool) Bool))) (s2 (set (tuple2 (tuple2 Bool Bool) Bool))) (c Int))
  (and (is_finite_subset (tuple21 (tuple21 bool bool) bool) (t2tb6 s1)
  (t2tb6 s2) c)
  (and (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb6 s2))
  (and (not (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb6 s1)))
  (and
  (and
  (= z (tb2t6 (add (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb6 s1))))
  (= z1 s2)) (= z2 (+ c 1)))))))))))

;; is_finite_subset_inversion
  (assert
  (forall ((z (set (set Int))) (z1 (set (set Int))) (z2 Int))
  (=> (is_finite_subset (set1 int) (t2tb1 z) (t2tb1 z1) z2)
  (or
  (or
  (exists ((s (set (set Int)))) (and (and (= z empty3) (= z1 s)) (= z2 0)))
  (exists ((x (set Int)) (s1 (set (set Int))) (s2 (set (set Int))) (c Int))
  (and (is_finite_subset (set1 int) (t2tb1 s1) (t2tb1 s2) c)
  (and (mem3 x s2)
  (and (mem3 x s1) (and (and (= z (add3 x s1)) (= z1 s2)) (= z2 c)))))))
  (exists ((x (set Int)) (s1 (set (set Int))) (s2 (set (set Int))) (c Int))
  (and (is_finite_subset (set1 int) (t2tb1 s1) (t2tb1 s2) c)
  (and (mem3 x s2)
  (and (not (mem3 x s1))
  (and (and (= z (add3 x s1)) (= z1 s2)) (= z2 (+ c 1)))))))))))

;; is_finite_subset_inversion
  (assert
  (forall ((z (set (tuple2 Bool Bool))) (z1 (set (tuple2 Bool Bool)))
  (z2 Int))
  (=> (is_finite_subset (tuple21 bool bool) (t2tb7 z) (t2tb7 z1) z2)
  (or
  (or
  (exists ((s (set (tuple2 Bool Bool))))
  (and (and (= z empty7) (= z1 s)) (= z2 0)))
  (exists ((x (tuple2 Bool Bool)) (s1 (set (tuple2 Bool Bool)))
  (s2 (set (tuple2 Bool Bool))) (c Int))
  (and (is_finite_subset (tuple21 bool bool) (t2tb7 s1) (t2tb7 s2) c)
  (and (mem (tuple21 bool bool) (t2tb11 x) (t2tb7 s2))
  (and (mem (tuple21 bool bool) (t2tb11 x) (t2tb7 s1))
  (and
  (and (= z (tb2t7 (add (tuple21 bool bool) (t2tb11 x) (t2tb7 s1))))
  (= z1 s2)) (= z2 c)))))))
  (exists ((x (tuple2 Bool Bool)) (s1 (set (tuple2 Bool Bool)))
  (s2 (set (tuple2 Bool Bool))) (c Int))
  (and (is_finite_subset (tuple21 bool bool) (t2tb7 s1) (t2tb7 s2) c)
  (and (mem (tuple21 bool bool) (t2tb11 x) (t2tb7 s2))
  (and (not (mem (tuple21 bool bool) (t2tb11 x) (t2tb7 s1)))
  (and
  (and (= z (tb2t7 (add (tuple21 bool bool) (t2tb11 x) (t2tb7 s1))))
  (= z1 s2)) (= z2 (+ c 1)))))))))))

;; is_finite_subset_inversion
  (assert
  (forall ((z (set Bool)) (z1 (set Bool)) (z2 Int))
  (=> (is_finite_subset bool (t2tb2 z) (t2tb2 z1) z2)
  (or
  (or (exists ((s (set Bool))) (and (and (= z empty1) (= z1 s)) (= z2 0)))
  (exists ((x Bool) (s1 (set Bool)) (s2 (set Bool)) (c Int))
  (and (is_finite_subset bool (t2tb2 s1) (t2tb2 s2) c)
  (and (mem2 x s2)
  (and (mem2 x s1) (and (and (= z (add1 x s1)) (= z1 s2)) (= z2 c)))))))
  (exists ((x Bool) (s1 (set Bool)) (s2 (set Bool)) (c Int))
  (and (is_finite_subset bool (t2tb2 s1) (t2tb2 s2) c)
  (and (mem2 x s2)
  (and (not (mem2 x s1))
  (and (and (= z (add1 x s1)) (= z1 s2)) (= z2 (+ c 1)))))))))))

;; is_finite_subset_inversion
  (assert
  (forall ((z (set Int)) (z1 (set Int)) (z2 Int))
  (=> (is_finite_subset int (t2tb3 z) (t2tb3 z1) z2)
  (or
  (or (exists ((s (set Int))) (and (and (= z empty2) (= z1 s)) (= z2 0)))
  (exists ((x Int) (s1 (set Int)) (s2 (set Int)) (c Int))
  (and (is_finite_subset int (t2tb3 s1) (t2tb3 s2) c)
  (and (mem1 x s2)
  (and (mem1 x s1) (and (and (= z (add2 x s1)) (= z1 s2)) (= z2 c)))))))
  (exists ((x Int) (s1 (set Int)) (s2 (set Int)) (c Int))
  (and (is_finite_subset int (t2tb3 s1) (t2tb3 s2) c)
  (and (mem1 x s2)
  (and (not (mem1 x s1))
  (and (and (= z (add2 x s1)) (= z1 s2)) (= z2 (+ c 1)))))))))))

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
  (=> (<= a b) (is_finite_subset int (t2tb3 (mk a b)) (t2tb3 integer)
  (+ (- b a) 1)))))

;; finite_interval_empty
  (assert
  (forall ((a Int) (b Int))
  (=> (< b a) (is_finite_subset int (t2tb3 (mk a b)) (t2tb3 integer) 0))))

(declare-fun finite_subsets (ty uni) uni)

;; finite_subsets_sort
  (assert
  (forall ((a ty))
  (forall ((x uni)) (sort (set1 (set1 a)) (finite_subsets a x)))))

;; finite_subsets_def
  (assert
  (forall ((s (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))
  (= (mem4 x
  (tb2t
  (finite_subsets
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb4 s))))
  (exists ((c Int)) (is_finite_subset
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb4 x) (t2tb4 s) c)))))

;; finite_subsets_def
  (assert
  (forall ((s (set Int)) (x (set Int)))
  (= (mem3 x (tb2t1 (finite_subsets int (t2tb3 s))))
  (exists ((c Int)) (is_finite_subset int (t2tb3 x) (t2tb3 s) c)))))

;; finite_subsets_def
  (assert
  (forall ((a ty))
  (forall ((s uni) (x uni))
  (= (mem (set1 a) x (finite_subsets a s))
  (exists ((c Int)) (is_finite_subset a x s c))))))

;; finite_Empty
  (assert
  (forall ((s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))))) (mem
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (t2tb empty8)
  (finite_subsets
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s)))))

;; finite_Empty
  (assert
  (forall ((s (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (mem4 empty4
  (tb2t
  (finite_subsets
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb4 s))))))

;; finite_Empty
  (assert
  (forall ((s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))) (mem
  (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb5 empty5)
  (finite_subsets (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 s)))))

;; finite_Empty
  (assert
  (forall ((s (set (tuple2 (tuple2 Bool Bool) Bool)))) (mem
  (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb6 empty6)
  (finite_subsets (tuple21 (tuple21 bool bool) bool) (t2tb6 s)))))

;; finite_Empty
  (assert
  (forall ((s (set (set Int)))) (mem (set1 (set1 int)) (t2tb1 empty3)
  (finite_subsets (set1 int) (t2tb1 s)))))

;; finite_Empty
  (assert
  (forall ((s (set (tuple2 Bool Bool)))) (mem (set1 (tuple21 bool bool))
  (t2tb7 empty7) (finite_subsets (tuple21 bool bool) (t2tb7 s)))))

;; finite_Empty
  (assert
  (forall ((s (set Bool))) (mem (set1 bool) (t2tb2 empty1)
  (finite_subsets bool (t2tb2 s)))))

;; finite_Empty
  (assert
  (forall ((s (set Int))) (mem3 empty2
  (tb2t1 (finite_subsets int (t2tb3 s))))))

;; finite_Empty
  (assert
  (forall ((a ty))
  (forall ((s uni)) (mem (set1 a) (empty a) (finite_subsets a s)))))

;; finite_Add
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s1 (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (s2 (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))))
  (=> (mem
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (t2tb s1)
  (finite_subsets
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s2)))
  (=> (mem4 x s2) (mem
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (t2tb (add4 x s1))
  (finite_subsets
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s2)))))))

;; finite_Add
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))) (s1 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))))
  (=> (mem4 s1
  (tb2t
  (finite_subsets
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb4 s2))))
  (=> (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb8 x) (t2tb4 s2)) (mem4
  (tb2t4
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb8 x) (t2tb4 s1)))
  (tb2t
  (finite_subsets
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb4 s2))))))))

;; finite_Add
  (assert
  (forall ((x (set Int)) (s1 (set (set Int))) (s2 (set (set Int))))
  (=> (mem (set1 (set1 int)) (t2tb1 s1)
  (finite_subsets (set1 int) (t2tb1 s2)))
  (=> (mem3 x s2) (mem (set1 (set1 int)) (t2tb1 (add3 x s1))
  (finite_subsets (set1 int) (t2tb1 s2)))))))

;; finite_Add
  (assert
  (forall ((x Bool) (s1 (set Bool)) (s2 (set Bool)))
  (=> (mem (set1 bool) (t2tb2 s1) (finite_subsets bool (t2tb2 s2)))
  (=> (mem2 x s2) (mem (set1 bool) (t2tb2 (add1 x s1))
  (finite_subsets bool (t2tb2 s2)))))))

;; finite_Add
  (assert
  (forall ((x Int) (s1 (set Int)) (s2 (set Int)))
  (=> (mem3 s1 (tb2t1 (finite_subsets int (t2tb3 s2))))
  (=> (mem1 x s2) (mem3 (add2 x s1) (tb2t1 (finite_subsets int (t2tb3 s2))))))))

;; finite_Add
  (assert
  (forall ((a ty))
  (forall ((x uni) (s1 uni) (s2 uni))
  (=> (mem (set1 a) s1 (finite_subsets a s2))
  (=> (mem a x s2) (mem (set1 a) (add a x s1) (finite_subsets a s2)))))))

;; finite_Union
  (assert
  (forall ((s1 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))) (s3 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))))
  (=> (mem4 s1
  (tb2t
  (finite_subsets
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb4 s3))))
  (=> (mem4 s2
  (tb2t
  (finite_subsets
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb4 s3)))) (mem4
  (tb2t4
  (union
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb4 s1) (t2tb4 s2)))
  (tb2t
  (finite_subsets
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb4 s3))))))))

;; finite_Union
  (assert
  (forall ((s1 (set Int)) (s2 (set Int)) (s3 (set Int)))
  (=> (mem3 s1 (tb2t1 (finite_subsets int (t2tb3 s3))))
  (=> (mem3 s2 (tb2t1 (finite_subsets int (t2tb3 s3)))) (mem3
  (tb2t3 (union int (t2tb3 s1) (t2tb3 s2)))
  (tb2t1 (finite_subsets int (t2tb3 s3))))))))

;; finite_Union
  (assert
  (forall ((a ty))
  (forall ((s1 uni) (s2 uni) (s3 uni))
  (=> (mem (set1 a) s1 (finite_subsets a s3))
  (=> (mem (set1 a) s2 (finite_subsets a s3)) (mem (set1 a) (union a s1 s2)
  (finite_subsets a s3)))))))

;; finite_inversion
  (assert
  (forall ((s1 (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (s2 (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))))
  (=> (mem
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (t2tb s1)
  (finite_subsets
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s2)))
  (or (= s1 empty8)
  (exists ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s3 (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))))
  (and (= s1 (add4 x s3)) (mem
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (t2tb s3)
  (finite_subsets
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s2)))))))))

;; finite_inversion
  (assert
  (forall ((s1 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))))
  (=> (mem4 s1
  (tb2t
  (finite_subsets
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb4 s2))))
  (or (= s1 empty4)
  (exists ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))) (s3 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))
  (and
  (= s1 (tb2t4
        (add
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int)) (t2tb8 x) (t2tb4 s3))))
  (mem4 s3
  (tb2t
  (finite_subsets
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb4 s2))))))))))

;; finite_inversion
  (assert
  (forall ((s1 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (s2 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (=> (mem (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (t2tb5 s1)
  (finite_subsets (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 s2)))
  (or (= s1 empty5)
  (exists ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (s3 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (and
  (= s1 (tb2t5
        (add (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
        (t2tb5 s3))))
  (mem (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb5 s3)
  (finite_subsets (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 s2)))))))))

;; finite_inversion
  (assert
  (forall ((s1 (set (tuple2 (tuple2 Bool Bool) Bool)))
  (s2 (set (tuple2 (tuple2 Bool Bool) Bool))))
  (=> (mem (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb6 s1)
  (finite_subsets (tuple21 (tuple21 bool bool) bool) (t2tb6 s2)))
  (or (= s1 empty6)
  (exists ((x (tuple2 (tuple2 Bool Bool) Bool)) (s3 (set (tuple2 (tuple2 Bool
  Bool) Bool))))
  (and
  (= s1 (tb2t6
        (add (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb6 s3))))
  (mem (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb6 s3)
  (finite_subsets (tuple21 (tuple21 bool bool) bool) (t2tb6 s2)))))))))

;; finite_inversion
  (assert
  (forall ((s1 (set (set Int))) (s2 (set (set Int))))
  (=> (mem (set1 (set1 int)) (t2tb1 s1)
  (finite_subsets (set1 int) (t2tb1 s2)))
  (or (= s1 empty3)
  (exists ((x (set Int)) (s3 (set (set Int))))
  (and (= s1 (add3 x s3)) (mem (set1 (set1 int)) (t2tb1 s3)
  (finite_subsets (set1 int) (t2tb1 s2)))))))))

;; finite_inversion
  (assert
  (forall ((s1 (set (tuple2 Bool Bool))) (s2 (set (tuple2 Bool Bool))))
  (=> (mem (set1 (tuple21 bool bool)) (t2tb7 s1)
  (finite_subsets (tuple21 bool bool) (t2tb7 s2)))
  (or (= s1 empty7)
  (exists ((x (tuple2 Bool Bool)) (s3 (set (tuple2 Bool Bool))))
  (and (= s1 (tb2t7 (add (tuple21 bool bool) (t2tb11 x) (t2tb7 s3)))) (mem
  (set1 (tuple21 bool bool)) (t2tb7 s3)
  (finite_subsets (tuple21 bool bool) (t2tb7 s2)))))))))

;; finite_inversion
  (assert
  (forall ((s1 (set Bool)) (s2 (set Bool)))
  (=> (mem (set1 bool) (t2tb2 s1) (finite_subsets bool (t2tb2 s2)))
  (or (= s1 empty1)
  (exists ((x Bool) (s3 (set Bool)))
  (and (= s1 (add1 x s3)) (mem (set1 bool) (t2tb2 s3)
  (finite_subsets bool (t2tb2 s2)))))))))

;; finite_inversion
  (assert
  (forall ((s1 (set Int)) (s2 (set Int)))
  (=> (mem3 s1 (tb2t1 (finite_subsets int (t2tb3 s2))))
  (or (= s1 empty2)
  (exists ((x Int) (s3 (set Int)))
  (and (= s1 (add2 x s3)) (mem3 s3 (tb2t1 (finite_subsets int (t2tb3 s2))))))))))

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
  (forall ((s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (x (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))))
  (= (mem
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (t2tb x)
  (non_empty_finite_subsets
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s)))
  (exists ((c Int))
  (and (is_finite_subset
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb x) (t2tb s) c) (not (= x empty8)))))))

;; non_empty_finite_subsets_def
  (assert
  (forall ((s (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))
  (= (mem4 x
  (tb2t
  (non_empty_finite_subsets
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb4 s))))
  (exists ((c Int))
  (and (is_finite_subset
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb4 x) (t2tb4 s) c) (not (= x empty4)))))))

;; non_empty_finite_subsets_def
  (assert
  (forall ((s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (x (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (= (mem (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb5 x)
  (non_empty_finite_subsets (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 s)))
  (exists ((c Int))
  (and (is_finite_subset (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 x) (t2tb5 s) c) (not (= x empty5)))))))

;; non_empty_finite_subsets_def
  (assert
  (forall ((s (set (tuple2 (tuple2 Bool Bool) Bool)))
  (x (set (tuple2 (tuple2 Bool Bool) Bool))))
  (= (mem (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb6 x)
  (non_empty_finite_subsets (tuple21 (tuple21 bool bool) bool) (t2tb6 s)))
  (exists ((c Int))
  (and (is_finite_subset (tuple21 (tuple21 bool bool) bool) (t2tb6 x)
  (t2tb6 s) c) (not (= x empty6)))))))

;; non_empty_finite_subsets_def
  (assert
  (forall ((s (set (set Int))) (x (set (set Int))))
  (= (mem (set1 (set1 int)) (t2tb1 x)
  (non_empty_finite_subsets (set1 int) (t2tb1 s)))
  (exists ((c Int))
  (and (is_finite_subset (set1 int) (t2tb1 x) (t2tb1 s) c)
  (not (= x empty3)))))))

;; non_empty_finite_subsets_def
  (assert
  (forall ((s (set (tuple2 Bool Bool))) (x (set (tuple2 Bool Bool))))
  (= (mem (set1 (tuple21 bool bool)) (t2tb7 x)
  (non_empty_finite_subsets (tuple21 bool bool) (t2tb7 s)))
  (exists ((c Int))
  (and (is_finite_subset (tuple21 bool bool) (t2tb7 x) (t2tb7 s) c)
  (not (= x empty7)))))))

;; non_empty_finite_subsets_def
  (assert
  (forall ((s (set Bool)) (x (set Bool)))
  (= (mem (set1 bool) (t2tb2 x) (non_empty_finite_subsets bool (t2tb2 s)))
  (exists ((c Int))
  (and (is_finite_subset bool (t2tb2 x) (t2tb2 s) c) (not (= x empty1)))))))

;; non_empty_finite_subsets_def
  (assert
  (forall ((s (set Int)) (x (set Int)))
  (= (mem3 x (tb2t1 (non_empty_finite_subsets int (t2tb3 s))))
  (exists ((c Int))
  (and (is_finite_subset int (t2tb3 x) (t2tb3 s) c) (not (= x empty2)))))))

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
  (= (card
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb empty8)) 0))

;; card_Empty
  (assert
  (= (card
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
     (t2tb4 empty4)) 0))

;; card_Empty
  (assert
  (= (card (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb5 empty5)) 0))

;; card_Empty
  (assert (= (card (tuple21 (tuple21 bool bool) bool) (t2tb6 empty6)) 0))

;; card_Empty
  (assert (= (card (set1 int) (t2tb1 empty3)) 0))

;; card_Empty
  (assert (= (card (tuple21 bool bool) (t2tb7 empty7)) 0))

;; card_Empty
  (assert (= (card bool (t2tb2 empty1)) 0))

;; card_Empty
  (assert (= (card int (t2tb3 empty2)) 0))

;; card_Empty
  (assert (forall ((a ty)) (= (card a (empty a)) 0)))

;; card_Add_not_mem
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s1 (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (s2 (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))))
  (! (=> (mem
     (set1
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
     (t2tb s1)
     (finite_subsets
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb s2)))
     (=> (not (mem4 x s1))
     (= (card
        (set1
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int))) (t2tb (add4 x s1))) (+ (card
                                            (set1
                                            (tuple21
                                            (tuple21
                                            (tuple21 (tuple21 bool bool)
                                            bool) bool) (set1 int)))
                                            (t2tb s1)) 1)))) :pattern ((mem
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (t2tb s1)
  (finite_subsets
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s2)))
  (card
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb (add4 x s1)))) )))

;; card_Add_not_mem
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))) (s1 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))))
  (! (=> (mem4 s1
     (tb2t
     (finite_subsets
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
     (t2tb4 s2))))
     (=>
     (not (mem
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
     (t2tb8 x) (t2tb4 s1)))
     (= (card
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int))
        (add
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int)) (t2tb8 x) (t2tb4 s1))) (+ (card
                                              (tuple21
                                              (tuple21
                                              (tuple21 (tuple21 bool bool)
                                              bool) bool) (set1 int))
                                              (t2tb4 s1)) 1)))) :pattern ((mem4
  s1
  (tb2t
  (finite_subsets
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb4 s2))))
  (card
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb8 x) (t2tb4 s1)))) )))

;; card_Add_not_mem
  (assert
  (forall ((x (set Int)) (s1 (set (set Int))) (s2 (set (set Int))))
  (! (=> (mem (set1 (set1 int)) (t2tb1 s1)
     (finite_subsets (set1 int) (t2tb1 s2)))
     (=> (not (mem3 x s1))
     (= (card (set1 int) (t2tb1 (add3 x s1))) (+ (card (set1 int) (t2tb1 s1)) 1)))) :pattern ((mem
  (set1 (set1 int)) (t2tb1 s1) (finite_subsets (set1 int) (t2tb1 s2)))
  (card (set1 int) (t2tb1 (add3 x s1)))) )))

;; card_Add_not_mem
  (assert
  (forall ((x Bool) (s1 (set Bool)) (s2 (set Bool)))
  (! (=> (mem (set1 bool) (t2tb2 s1) (finite_subsets bool (t2tb2 s2)))
     (=> (not (mem2 x s1))
     (= (card bool (t2tb2 (add1 x s1))) (+ (card bool (t2tb2 s1)) 1)))) :pattern ((mem
  (set1 bool) (t2tb2 s1) (finite_subsets bool (t2tb2 s2)))
  (card bool (t2tb2 (add1 x s1)))) )))

;; card_Add_not_mem
  (assert
  (forall ((x Int) (s1 (set Int)) (s2 (set Int)))
  (! (=> (mem3 s1 (tb2t1 (finite_subsets int (t2tb3 s2))))
     (=> (not (mem1 x s1))
     (= (card int (t2tb3 (add2 x s1))) (+ (card int (t2tb3 s1)) 1)))) :pattern ((mem3
  s1 (tb2t1 (finite_subsets int (t2tb3 s2))))
  (card int (t2tb3 (add2 x s1)))) )))

;; card_Add_not_mem
  (assert
  (forall ((a ty))
  (forall ((x uni) (s1 uni) (s2 uni))
  (! (=> (mem (set1 a) s1 (finite_subsets a s2))
     (=> (not (mem a x s1)) (= (card a (add a x s1)) (+ (card a s1) 1)))) :pattern ((mem
  (set1 a) s1 (finite_subsets a s2)) (card a (add a x s1))) ))))

;; card_Add_mem
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s1 (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (s2 (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))))
  (! (=> (mem
     (set1
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
     (t2tb s1)
     (finite_subsets
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb s2)))
     (=> (mem4 x s1)
     (= (card
        (set1
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int))) (t2tb (add4 x s1))) (card
                                         (set1
                                         (tuple21
                                         (tuple21
                                         (tuple21 (tuple21 bool bool) bool)
                                         bool) (set1 int))) (t2tb s1))))) :pattern ((mem
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (t2tb s1)
  (finite_subsets
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s2)))
  (card
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb (add4 x s1)))) )))

;; card_Add_mem
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))) (s1 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))))
  (! (=> (mem4 s1
     (tb2t
     (finite_subsets
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
     (t2tb4 s2))))
     (=> (mem
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
     (t2tb8 x) (t2tb4 s1))
     (= (card
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int))
        (add
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int)) (t2tb8 x) (t2tb4 s1))) (card
                                           (tuple21
                                           (tuple21
                                           (tuple21 (tuple21 bool bool) bool)
                                           bool) (set1 int)) (t2tb4 s1))))) :pattern ((mem4
  s1
  (tb2t
  (finite_subsets
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb4 s2))))
  (card
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb8 x) (t2tb4 s1)))) )))

;; card_Add_mem
  (assert
  (forall ((x (set Int)) (s1 (set (set Int))) (s2 (set (set Int))))
  (! (=> (mem (set1 (set1 int)) (t2tb1 s1)
     (finite_subsets (set1 int) (t2tb1 s2)))
     (=> (mem3 x s1)
     (= (card (set1 int) (t2tb1 (add3 x s1))) (card (set1 int) (t2tb1 s1))))) :pattern ((mem
  (set1 (set1 int)) (t2tb1 s1) (finite_subsets (set1 int) (t2tb1 s2)))
  (card (set1 int) (t2tb1 (add3 x s1)))) )))

;; card_Add_mem
  (assert
  (forall ((x Bool) (s1 (set Bool)) (s2 (set Bool)))
  (! (=> (mem (set1 bool) (t2tb2 s1) (finite_subsets bool (t2tb2 s2)))
     (=> (mem2 x s1)
     (= (card bool (t2tb2 (add1 x s1))) (card bool (t2tb2 s1))))) :pattern ((mem
  (set1 bool) (t2tb2 s1) (finite_subsets bool (t2tb2 s2)))
  (card bool (t2tb2 (add1 x s1)))) )))

;; card_Add_mem
  (assert
  (forall ((x Int) (s1 (set Int)) (s2 (set Int)))
  (! (=> (mem3 s1 (tb2t1 (finite_subsets int (t2tb3 s2))))
     (=> (mem1 x s1)
     (= (card int (t2tb3 (add2 x s1))) (card int (t2tb3 s1))))) :pattern ((mem3
  s1 (tb2t1 (finite_subsets int (t2tb3 s2))))
  (card int (t2tb3 (add2 x s1)))) )))

;; card_Add_mem
  (assert
  (forall ((a ty))
  (forall ((x uni) (s1 uni) (s2 uni))
  (! (=> (mem (set1 a) s1 (finite_subsets a s2))
     (=> (mem a x s1) (= (card a (add a x s1)) (card a s1)))) :pattern ((mem
  (set1 a) s1 (finite_subsets a s2)) (card a (add a x s1))) ))))

;; card_Union
  (assert
  (forall ((s1 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))) (s3 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))))
  (! (=> (mem4 s1
     (tb2t
     (finite_subsets
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
     (t2tb4 s3))))
     (=> (mem4 s2
     (tb2t
     (finite_subsets
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
     (t2tb4 s3))))
     (=> (is_empty
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
     (inter
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
     (t2tb4 s1) (t2tb4 s2)))
     (= (card
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int))
        (union
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int)) (t2tb4 s1) (t2tb4 s2))) (+ (card
                                               (tuple21
                                               (tuple21
                                               (tuple21 (tuple21 bool bool)
                                               bool) bool) (set1 int))
                                               (t2tb4 s1)) (card
                                                           (tuple21
                                                           (tuple21
                                                           (tuple21
                                                           (tuple21 bool
                                                           bool) bool) 
                                                           bool) (set1 int))
                                                           (t2tb4 s2))))))) :pattern ((mem4
  s1
  (tb2t
  (finite_subsets
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb4 s3)))) (mem4 s2
  (tb2t
  (finite_subsets
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb4 s3))))
  (card
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (union
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb4 s1) (t2tb4 s2)))) )))

;; card_Union
  (assert
  (forall ((s1 (set Int)) (s2 (set Int)) (s3 (set Int)))
  (! (=> (mem3 s1 (tb2t1 (finite_subsets int (t2tb3 s3))))
     (=> (mem3 s2 (tb2t1 (finite_subsets int (t2tb3 s3))))
     (=> (is_empty int (inter int (t2tb3 s1) (t2tb3 s2)))
     (= (card int (union int (t2tb3 s1) (t2tb3 s2))) (+ (card int (t2tb3 s1)) 
     (card int (t2tb3 s2))))))) :pattern ((mem3
  s1 (tb2t1 (finite_subsets int (t2tb3 s3)))) (mem3 s2
  (tb2t1 (finite_subsets int (t2tb3 s3))))
  (card int (union int (t2tb3 s1) (t2tb3 s2)))) )))

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

(declare-fun times1 ((set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (set (set Int))) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))

(declare-fun times2 ((set (tuple2 (tuple2 Bool Bool) Bool))
  (set Bool)) (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))

(declare-fun times3 ((set (tuple2 Bool Bool))
  (set Bool)) (set (tuple2 (tuple2 Bool Bool) Bool)))

(declare-fun times4 ((set Bool) (set Bool)) (set (tuple2 Bool Bool)))

;; times_def
  (assert
  (forall ((a ty))
  (forall ((a1 uni) (b (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))) (x uni)
  (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))
  (! (= (mem
     (tuple21 a
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
     (Tuple2 a
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     x (t2tb4 y))
     (times
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     a a1 (t2tb b))) (and (mem a x a1) (mem4 y b))) :pattern ((mem
  (tuple21 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) x
  (t2tb4 y))
  (times
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) a
  a1 (t2tb b)))) ))))

;; times_def
  (assert
  (forall ((a ty))
  (forall ((a1 uni) (b (set (set Int))) (x uni) (y (set Int)))
  (! (= (mem (tuple21 a (set1 int)) (Tuple2 a (set1 int) x (t2tb3 y))
     (times (set1 int) a a1 (t2tb1 b))) (and (mem a x a1) (mem3 y b))) :pattern ((mem
  (tuple21 a (set1 int)) (Tuple2 a (set1 int) x (t2tb3 y))
  (times (set1 int) a a1 (t2tb1 b)))) ))))

;; times_def
  (assert
  (forall ((a ty))
  (forall ((a1 uni) (b (set Bool)) (x uni) (y Bool))
  (! (= (mem (tuple21 a bool) (Tuple2 a bool x (t2tb12 y))
     (times bool a a1 (t2tb2 b))) (and (mem a x a1) (mem2 y b))) :pattern ((mem
  (tuple21 a bool) (Tuple2 a bool x (t2tb12 y))
  (times bool a a1 (t2tb2 b)))) ))))

;; times_def
  (assert
  (forall ((a ty))
  (forall ((a1 uni) (b (set Int)) (x uni) (y Int))
  (! (= (mem (tuple21 a int) (Tuple2 a int x (t2tb13 y))
     (times int a a1 (t2tb3 b))) (and (mem a x a1) (mem1 y b))) :pattern ((mem
  (tuple21 a int) (Tuple2 a int x (t2tb13 y)) (times int a a1 (t2tb3 b)))) ))))

;; times_def
  (assert
  (forall ((a (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (b (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))) (x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))) (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))))
  (! (= (mem
     (tuple21
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
     (Tuple2
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb4 x) (t2tb4 y))
     (times
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb a) (t2tb b))) (and (mem4 x a) (mem4 y b))) :pattern ((mem
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb4 x) (t2tb4 y))
  (times
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb a) (t2tb b)))) )))

;; times_def
  (assert
  (forall ((a (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (b (set (set Int)))
  (x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))
  (y (set Int)))
  (! (= (mem
     (tuple21
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (set1 int))
     (Tuple2
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (set1 int) (t2tb4 x) (t2tb3 y))
     (times (set1 int)
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb a) (t2tb1 b))) (and (mem4 x a) (mem3 y b))) :pattern ((mem
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1 int))
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1 int) (t2tb4 x) (t2tb3 y))
  (times (set1 int)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb a) (t2tb1 b)))) )))

;; times_def
  (assert
  (forall ((a (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (b (set Bool))
  (x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))
  (y Bool))
  (! (= (mem
     (tuple21
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     bool)
     (Tuple2
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     bool (t2tb4 x) (t2tb12 y))
     (times bool
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb a) (t2tb2 b))) (and (mem4 x a) (mem2 y b))) :pattern ((mem
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  bool)
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  bool (t2tb4 x) (t2tb12 y))
  (times bool
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb a) (t2tb2 b)))) )))

;; times_def
  (assert
  (forall ((a (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (b (set Int))
  (x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))
  (y Int))
  (! (= (mem
     (tuple21
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     int)
     (Tuple2
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     int (t2tb4 x) (t2tb13 y))
     (times int
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb a) (t2tb3 b))) (and (mem4 x a) (mem1 y b))) :pattern ((mem
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  int)
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) 
  int (t2tb4 x) (t2tb13 y))
  (times int
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb a) (t2tb3 b)))) )))

;; times_def
  (assert
  (forall ((b ty))
  (forall ((a (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (b1 uni) (x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))) (y uni))
  (! (= (mem
     (tuple21
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     b)
     (Tuple2
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     b (t2tb4 x) y)
     (times b
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb a) b1)) (and (mem4 x a) (mem b y b1))) :pattern ((mem
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b)
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b
  (t2tb4 x) y)
  (times b
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb a) b1))) ))))

;; times_def
  (assert
  (forall ((a (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (b (set (set Int))) (x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (y (set Int)))
  (! (= (mem
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
     (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
     (t2tb9 x) (t2tb3 y)) (t2tb4 (times1 a b)))
     (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
     (t2tb5 a)) (mem3 y b))) :pattern ((mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb9 x) (t2tb3 y)) (t2tb4 (times1 a b)))) )))

;; times_def
  (assert
  (forall ((a (set (tuple2 (tuple2 Bool Bool) Bool))) (b (set Bool))
  (x (tuple2 (tuple2 Bool Bool) Bool)) (y Bool))
  (! (= (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (Tuple2 (tuple21 (tuple21 bool bool) bool) bool (t2tb10 x) (t2tb12 y))
     (t2tb5 (times2 a b)))
     (and (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb6 a)) (mem2
     y b))) :pattern ((mem
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (Tuple2 (tuple21 (tuple21 bool bool) bool) bool (t2tb10 x) (t2tb12 y))
  (t2tb5 (times2 a b)))) )))

;; times_def
  (assert
  (forall ((a (set (set Int)))
  (b (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (x (set Int)) (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))))
  (! (= (mem
     (tuple21 (set1 int)
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
     (Tuple2 (set1 int)
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb3 x) (t2tb4 y))
     (times
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (set1 int) (t2tb1 a) (t2tb b))) (and (mem3 x a) (mem4 y b))) :pattern ((mem
  (tuple21 (set1 int)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2 (set1 int)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb3 x) (t2tb4 y))
  (times
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1 int) (t2tb1 a) (t2tb b)))) )))

;; times_def
  (assert
  (forall ((a (set (set Int))) (b (set (set Int))) (x (set Int))
  (y (set Int)))
  (! (= (mem (tuple21 (set1 int) (set1 int))
     (Tuple2 (set1 int) (set1 int) (t2tb3 x) (t2tb3 y))
     (times (set1 int) (set1 int) (t2tb1 a) (t2tb1 b)))
     (and (mem3 x a) (mem3 y b))) :pattern ((mem
  (tuple21 (set1 int) (set1 int))
  (Tuple2 (set1 int) (set1 int) (t2tb3 x) (t2tb3 y))
  (times (set1 int) (set1 int) (t2tb1 a) (t2tb1 b)))) )))

;; times_def
  (assert
  (forall ((a (set (set Int))) (b (set Bool)) (x (set Int)) (y Bool))
  (! (= (mem (tuple21 (set1 int) bool)
     (Tuple2 (set1 int) bool (t2tb3 x) (t2tb12 y))
     (times bool (set1 int) (t2tb1 a) (t2tb2 b)))
     (and (mem3 x a) (mem2 y b))) :pattern ((mem
  (tuple21 (set1 int) bool) (Tuple2 (set1 int) bool (t2tb3 x) (t2tb12 y))
  (times bool (set1 int) (t2tb1 a) (t2tb2 b)))) )))

;; times_def
  (assert
  (forall ((a (set (set Int))) (b (set Int)) (x (set Int)) (y Int))
  (! (= (mem (tuple21 (set1 int) int)
     (Tuple2 (set1 int) int (t2tb3 x) (t2tb13 y))
     (times int (set1 int) (t2tb1 a) (t2tb3 b))) (and (mem3 x a) (mem1 y b))) :pattern ((mem
  (tuple21 (set1 int) int) (Tuple2 (set1 int) int (t2tb3 x) (t2tb13 y))
  (times int (set1 int) (t2tb1 a) (t2tb3 b)))) )))

;; times_def
  (assert
  (forall ((b ty))
  (forall ((a (set (set Int))) (b1 uni) (x (set Int)) (y uni))
  (! (= (mem (tuple21 (set1 int) b) (Tuple2 (set1 int) b (t2tb3 x) y)
     (times b (set1 int) (t2tb1 a) b1)) (and (mem3 x a) (mem b y b1))) :pattern ((mem
  (tuple21 (set1 int) b) (Tuple2 (set1 int) b (t2tb3 x) y)
  (times b (set1 int) (t2tb1 a) b1))) ))))

;; times_def
  (assert
  (forall ((a (set (tuple2 Bool Bool))) (b (set Bool)) (x (tuple2 Bool Bool))
  (y Bool))
  (! (= (mem (tuple21 (tuple21 bool bool) bool)
     (Tuple2 (tuple21 bool bool) bool (t2tb11 x) (t2tb12 y))
     (t2tb6 (times3 a b)))
     (and (mem (tuple21 bool bool) (t2tb11 x) (t2tb7 a)) (mem2 y b))) :pattern ((mem
  (tuple21 (tuple21 bool bool) bool)
  (Tuple2 (tuple21 bool bool) bool (t2tb11 x) (t2tb12 y))
  (t2tb6 (times3 a b)))) )))

;; times_def
  (assert
  (forall ((a (set Bool)) (b (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))) (x Bool)
  (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))
  (! (= (mem
     (tuple21 bool
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
     (Tuple2 bool
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb12 x) (t2tb4 y))
     (times
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     bool (t2tb2 a) (t2tb b))) (and (mem2 x a) (mem4 y b))) :pattern ((mem
  (tuple21 bool
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2 bool
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb12 x) (t2tb4 y))
  (times
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  bool (t2tb2 a) (t2tb b)))) )))

;; times_def
  (assert
  (forall ((a (set Bool)) (b (set (set Int))) (x Bool) (y (set Int)))
  (! (= (mem (tuple21 bool (set1 int))
     (Tuple2 bool (set1 int) (t2tb12 x) (t2tb3 y))
     (times (set1 int) bool (t2tb2 a) (t2tb1 b)))
     (and (mem2 x a) (mem3 y b))) :pattern ((mem
  (tuple21 bool (set1 int)) (Tuple2 bool (set1 int) (t2tb12 x) (t2tb3 y))
  (times (set1 int) bool (t2tb2 a) (t2tb1 b)))) )))

;; times_def
  (assert
  (forall ((a (set Bool)) (b (set Bool)) (x Bool) (y Bool))
  (! (= (mem (tuple21 bool bool) (Tuple2 bool bool (t2tb12 x) (t2tb12 y))
     (t2tb7 (times4 a b))) (and (mem2 x a) (mem2 y b))) :pattern ((mem
  (tuple21 bool bool) (Tuple2 bool bool (t2tb12 x) (t2tb12 y))
  (t2tb7 (times4 a b)))) )))

;; times_def
  (assert
  (forall ((a (set Bool)) (b (set Int)) (x Bool) (y Int))
  (! (= (mem (tuple21 bool int) (Tuple2 bool int (t2tb12 x) (t2tb13 y))
     (times int bool (t2tb2 a) (t2tb3 b))) (and (mem2 x a) (mem1 y b))) :pattern ((mem
  (tuple21 bool int) (Tuple2 bool int (t2tb12 x) (t2tb13 y))
  (times int bool (t2tb2 a) (t2tb3 b)))) )))

;; times_def
  (assert
  (forall ((b ty))
  (forall ((a (set Bool)) (b1 uni) (x Bool) (y uni))
  (! (= (mem (tuple21 bool b) (Tuple2 bool b (t2tb12 x) y)
     (times b bool (t2tb2 a) b1)) (and (mem2 x a) (mem b y b1))) :pattern ((mem
  (tuple21 bool b) (Tuple2 bool b (t2tb12 x) y)
  (times b bool (t2tb2 a) b1))) ))))

;; times_def
  (assert
  (forall ((a (set Int)) (b (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))) (x Int)
  (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))
  (! (= (mem
     (tuple21 int
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
     (Tuple2 int
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb13 x) (t2tb4 y))
     (times
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     int (t2tb3 a) (t2tb b))) (and (mem1 x a) (mem4 y b))) :pattern ((mem
  (tuple21 int
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2 int
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb13 x) (t2tb4 y))
  (times
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) 
  int (t2tb3 a) (t2tb b)))) )))

;; times_def
  (assert
  (forall ((a (set Int)) (b (set (set Int))) (x Int) (y (set Int)))
  (! (= (mem (tuple21 int (set1 int))
     (Tuple2 int (set1 int) (t2tb13 x) (t2tb3 y))
     (times (set1 int) int (t2tb3 a) (t2tb1 b))) (and (mem1 x a) (mem3 y b))) :pattern ((mem
  (tuple21 int (set1 int)) (Tuple2 int (set1 int) (t2tb13 x) (t2tb3 y))
  (times (set1 int) int (t2tb3 a) (t2tb1 b)))) )))

;; times_def
  (assert
  (forall ((a (set Int)) (b (set Bool)) (x Int) (y Bool))
  (! (= (mem (tuple21 int bool) (Tuple2 int bool (t2tb13 x) (t2tb12 y))
     (times bool int (t2tb3 a) (t2tb2 b))) (and (mem1 x a) (mem2 y b))) :pattern ((mem
  (tuple21 int bool) (Tuple2 int bool (t2tb13 x) (t2tb12 y))
  (times bool int (t2tb3 a) (t2tb2 b)))) )))

;; times_def
  (assert
  (forall ((a (set Int)) (b (set Int)) (x Int) (y Int))
  (! (= (mem (tuple21 int int) (Tuple2 int int (t2tb13 x) (t2tb13 y))
     (times int int (t2tb3 a) (t2tb3 b))) (and (mem1 x a) (mem1 y b))) :pattern ((mem
  (tuple21 int int) (Tuple2 int int (t2tb13 x) (t2tb13 y))
  (times int int (t2tb3 a) (t2tb3 b)))) )))

;; times_def
  (assert
  (forall ((b ty))
  (forall ((a (set Int)) (b1 uni) (x Int) (y uni))
  (! (= (mem (tuple21 int b) (Tuple2 int b (t2tb13 x) y)
     (times b int (t2tb3 a) b1)) (and (mem1 x a) (mem b y b1))) :pattern ((mem
  (tuple21 int b) (Tuple2 int b (t2tb13 x) y) (times b int (t2tb3 a) b1))) ))))

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
  (forall ((u (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (v (set (set Int))))
  (= (tb2t
     (relations (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (t2tb5 u) (t2tb1 v))) (power2 (times1 u v)))))

;; relations_def
  (assert
  (forall ((u (set (tuple2 (tuple2 Bool Bool) Bool))) (v (set Bool)))
  (= (tb2t15
     (relations bool (tuple21 (tuple21 bool bool) bool) (t2tb6 u) (t2tb2 v))) 
  (tb2t15
  (power (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 (times2 u v)))))))

;; relations_def
  (assert
  (forall ((u (set (tuple2 Bool Bool))) (v (set Bool)))
  (= (tb2t16 (relations bool (tuple21 bool bool) (t2tb7 u) (t2tb2 v))) 
  (tb2t16 (power (tuple21 (tuple21 bool bool) bool) (t2tb6 (times3 u v)))))))

;; relations_def
  (assert
  (forall ((u (set Bool)) (v (set Bool)))
  (= (tb2t18 (relations bool bool (t2tb2 u) (t2tb2 v))) (tb2t18
                                                        (power
                                                        (tuple21 bool bool)
                                                        (t2tb7 (times4 u v)))))))

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
  (forall ((r (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (u (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (v (set (set Int))))
  (= (mem4 r (power2 (times1 u v))) (subset
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb4 r) (t2tb4 (times1 u v))))))

;; break_power_times
  (assert
  (forall ((r (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (u (set (tuple2 (tuple2 Bool Bool) Bool))) (v (set Bool)))
  (= (mem (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb5 r)
  (power (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 (times2 u v)))) (subset
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb5 r)
  (t2tb5 (times2 u v))))))

;; break_power_times
  (assert
  (forall ((r (set (tuple2 (tuple2 Bool Bool) Bool))) (u (set (tuple2 Bool
  Bool))) (v (set Bool)))
  (= (mem (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb6 r)
  (power (tuple21 (tuple21 bool bool) bool) (t2tb6 (times3 u v)))) (subset
  (tuple21 (tuple21 bool bool) bool) (t2tb6 r) (t2tb6 (times3 u v))))))

;; break_power_times
  (assert
  (forall ((r (set (tuple2 Bool Bool))) (u (set Bool)) (v (set Bool)))
  (= (mem (set1 (tuple21 bool bool)) (t2tb7 r)
  (power (tuple21 bool bool) (t2tb7 (times4 u v)))) (subset
  (tuple21 bool bool) (t2tb7 r) (t2tb7 (times4 u v))))))

;; break_power_times
  (assert
  (forall ((a ty) (b ty))
  (forall ((r uni) (u uni) (v uni))
  (= (mem (set1 (tuple21 a b)) r (power (tuple21 a b) (times b a u v)))
  (subset (tuple21 a b) r (times b a u v))))))

;; subset_of_times
  (assert
  (forall ((a ty))
  (forall ((r uni) (u uni) (v (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))))
  (and
  (=> (subset
  (tuple21 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))) r
  (times
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) a u
  (t2tb v)))
  (forall ((x uni) (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))))
  (=> (mem
  (tuple21 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) x
  (t2tb4 y)) r) (and (mem a x u) (mem4 y v)))))
  (=>
  (forall ((x uni) (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))))
  (=> (sort a x)
  (=> (mem
  (tuple21 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) x
  (t2tb4 y)) r) (and (mem a x u) (mem4 y v))))) (subset
  (tuple21 a
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))) r
  (times
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) a u
  (t2tb v))))))))

;; subset_of_times
  (assert
  (forall ((a ty))
  (forall ((r uni) (u uni) (v (set (set Int))))
  (and
  (=> (subset (tuple21 a (set1 int)) r (times (set1 int) a u (t2tb1 v)))
  (forall ((x uni) (y (set Int)))
  (=> (mem (tuple21 a (set1 int)) (Tuple2 a (set1 int) x (t2tb3 y)) r)
  (and (mem a x u) (mem3 y v)))))
  (=>
  (forall ((x uni) (y (set Int)))
  (=> (sort a x)
  (=> (mem (tuple21 a (set1 int)) (Tuple2 a (set1 int) x (t2tb3 y)) r)
  (and (mem a x u) (mem3 y v))))) (subset (tuple21 a (set1 int)) r
  (times (set1 int) a u (t2tb1 v))))))))

;; subset_of_times
  (assert
  (forall ((a ty))
  (forall ((r uni) (u uni) (v (set Bool)))
  (and
  (=> (subset (tuple21 a bool) r (times bool a u (t2tb2 v)))
  (forall ((x uni) (y Bool))
  (=> (mem (tuple21 a bool) (Tuple2 a bool x (t2tb12 y)) r)
  (and (mem a x u) (mem2 y v)))))
  (=>
  (forall ((x uni) (y Bool))
  (=> (sort a x)
  (=> (mem (tuple21 a bool) (Tuple2 a bool x (t2tb12 y)) r)
  (and (mem a x u) (mem2 y v))))) (subset (tuple21 a bool) r
  (times bool a u (t2tb2 v))))))))

;; subset_of_times
  (assert
  (forall ((a ty))
  (forall ((r uni) (u uni) (v (set Int)))
  (and
  (=> (subset (tuple21 a int) r (times int a u (t2tb3 v)))
  (forall ((x uni) (y Int))
  (=> (mem (tuple21 a int) (Tuple2 a int x (t2tb13 y)) r)
  (and (mem a x u) (mem1 y v)))))
  (=>
  (forall ((x uni) (y Int))
  (=> (sort a x)
  (=> (mem (tuple21 a int) (Tuple2 a int x (t2tb13 y)) r)
  (and (mem a x u) (mem1 y v))))) (subset (tuple21 a int) r
  (times int a u (t2tb3 v))))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))))
  (u (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (v (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))))
  (= (subset
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (t2tb21 r)
  (times
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb u) (t2tb v)))
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))
  (=> (mem
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb4 x) (t2tb4 y)) (t2tb21 r)) (and (mem4 x u) (mem4 y v)))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))) (set Int))))
  (u (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (v (set (set Int))))
  (= (subset
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1 int)) (t2tb23 r)
  (times (set1 int)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb u) (t2tb1 v)))
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (y (set Int)))
  (=> (mem
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1 int))
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1 int) (t2tb4 x) (t2tb3 y)) (t2tb23 r)) (and (mem4 x u) (mem3 y v)))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))) Bool)))
  (u (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (v (set Bool)))
  (= (subset
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  bool) (t2tb27 r)
  (times bool
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb u) (t2tb2 v)))
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (y Bool))
  (=> (mem
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  bool)
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  bool (t2tb4 x) (t2tb12 y)) (t2tb27 r)) (and (mem4 x u) (mem2 y v)))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))) Int)))
  (u (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (v (set Int)))
  (= (subset
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  int) (t2tb30 r)
  (times int
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb u) (t2tb3 v)))
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (y Int))
  (=> (mem
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  int)
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) 
  int (t2tb4 x) (t2tb13 y)) (t2tb30 r)) (and (mem4 x u) (mem1 y v)))))))

;; subset_of_times
  (assert
  (forall ((b ty))
  (forall ((r uni) (u (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))) (v uni))
  (and
  (=> (subset
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b)
  r
  (times b
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb u) v))
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (y uni))
  (=> (mem
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b)
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b
  (t2tb4 x) y) r) (and (mem4 x u) (mem b y v)))))
  (=>
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (y uni))
  (=> (sort b y)
  (=> (mem
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b)
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b
  (t2tb4 x) y) r) (and (mem4 x u) (mem b y v))))) (subset
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b)
  r
  (times b
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb u) v)))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (u (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (v (set (set Int))))
  (= (subset
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb4 r) (t2tb4 (times1 u v)))
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)) (y (set Int)))
  (=> (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb9 x) (t2tb3 y)) (t2tb4 r))
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
  (t2tb5 u)) (mem3 y v)))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (u (set (tuple2 (tuple2 Bool Bool) Bool))) (v (set Bool)))
  (= (subset (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb5 r)
  (t2tb5 (times2 u v)))
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)) (y Bool))
  (=> (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (Tuple2 (tuple21 (tuple21 bool bool) bool) bool (t2tb10 x) (t2tb12 y))
  (t2tb5 r))
  (and (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb6 u)) (mem2 y
  v)))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 (set Int)
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))))
  (u (set (set Int))) (v (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))))
  (= (subset
  (tuple21 (set1 int)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (t2tb33 r)
  (times
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1 int) (t2tb1 u) (t2tb v)))
  (forall ((x (set Int)) (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))))
  (=> (mem
  (tuple21 (set1 int)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2 (set1 int)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb3 x) (t2tb4 y)) (t2tb33 r)) (and (mem3 x u) (mem4 y v)))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 (set Int) (set Int)))) (u (set (set Int)))
  (v (set (set Int))))
  (= (subset (tuple21 (set1 int) (set1 int)) (t2tb37 r)
  (times (set1 int) (set1 int) (t2tb1 u) (t2tb1 v)))
  (forall ((x (set Int)) (y (set Int)))
  (=> (mem (tuple21 (set1 int) (set1 int))
  (Tuple2 (set1 int) (set1 int) (t2tb3 x) (t2tb3 y)) (t2tb37 r))
  (and (mem3 x u) (mem3 y v)))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 (set Int) Bool))) (u (set (set Int)))
  (v (set Bool)))
  (= (subset (tuple21 (set1 int) bool) (t2tb39 r)
  (times bool (set1 int) (t2tb1 u) (t2tb2 v)))
  (forall ((x (set Int)) (y Bool))
  (=> (mem (tuple21 (set1 int) bool)
  (Tuple2 (set1 int) bool (t2tb3 x) (t2tb12 y)) (t2tb39 r))
  (and (mem3 x u) (mem2 y v)))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 (set Int) Int))) (u (set (set Int)))
  (v (set Int)))
  (= (subset (tuple21 (set1 int) int) (t2tb42 r)
  (times int (set1 int) (t2tb1 u) (t2tb3 v)))
  (forall ((x (set Int)) (y Int))
  (=> (mem (tuple21 (set1 int) int)
  (Tuple2 (set1 int) int (t2tb3 x) (t2tb13 y)) (t2tb42 r))
  (and (mem3 x u) (mem1 y v)))))))

;; subset_of_times
  (assert
  (forall ((b ty))
  (forall ((r uni) (u (set (set Int))) (v uni))
  (and
  (=> (subset (tuple21 (set1 int) b) r (times b (set1 int) (t2tb1 u) v))
  (forall ((x (set Int)) (y uni))
  (=> (mem (tuple21 (set1 int) b) (Tuple2 (set1 int) b (t2tb3 x) y) r)
  (and (mem3 x u) (mem b y v)))))
  (=>
  (forall ((x (set Int)) (y uni))
  (=> (sort b y)
  (=> (mem (tuple21 (set1 int) b) (Tuple2 (set1 int) b (t2tb3 x) y) r)
  (and (mem3 x u) (mem b y v))))) (subset (tuple21 (set1 int) b) r
  (times b (set1 int) (t2tb1 u) v)))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 (tuple2 Bool Bool) Bool))) (u (set (tuple2 Bool
  Bool))) (v (set Bool)))
  (= (subset (tuple21 (tuple21 bool bool) bool) (t2tb6 r)
  (t2tb6 (times3 u v)))
  (forall ((x (tuple2 Bool Bool)) (y Bool))
  (=> (mem (tuple21 (tuple21 bool bool) bool)
  (Tuple2 (tuple21 bool bool) bool (t2tb11 x) (t2tb12 y)) (t2tb6 r))
  (and (mem (tuple21 bool bool) (t2tb11 x) (t2tb7 u)) (mem2 y v)))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 Bool (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))))) (u (set Bool))
  (v (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))))
  (= (subset
  (tuple21 bool
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (t2tb45 r)
  (times
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  bool (t2tb2 u) (t2tb v)))
  (forall ((x Bool) (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))))
  (=> (mem
  (tuple21 bool
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2 bool
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb12 x) (t2tb4 y)) (t2tb45 r)) (and (mem2 x u) (mem4 y v)))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 Bool (set Int)))) (u (set Bool))
  (v (set (set Int))))
  (= (subset (tuple21 bool (set1 int)) (t2tb48 r)
  (times (set1 int) bool (t2tb2 u) (t2tb1 v)))
  (forall ((x Bool) (y (set Int)))
  (=> (mem (tuple21 bool (set1 int))
  (Tuple2 bool (set1 int) (t2tb12 x) (t2tb3 y)) (t2tb48 r))
  (and (mem2 x u) (mem3 y v)))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 Bool Bool))) (u (set Bool)) (v (set Bool)))
  (= (subset (tuple21 bool bool) (t2tb7 r) (t2tb7 (times4 u v)))
  (forall ((x Bool) (y Bool))
  (=> (mem (tuple21 bool bool) (Tuple2 bool bool (t2tb12 x) (t2tb12 y))
  (t2tb7 r)) (and (mem2 x u) (mem2 y v)))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 Bool Int))) (u (set Bool)) (v (set Int)))
  (= (subset (tuple21 bool int) (t2tb51 r)
  (times int bool (t2tb2 u) (t2tb3 v)))
  (forall ((x Bool) (y Int))
  (=> (mem (tuple21 bool int) (Tuple2 bool int (t2tb12 x) (t2tb13 y))
  (t2tb51 r)) (and (mem2 x u) (mem1 y v)))))))

;; subset_of_times
  (assert
  (forall ((b ty))
  (forall ((r uni) (u (set Bool)) (v uni))
  (and
  (=> (subset (tuple21 bool b) r (times b bool (t2tb2 u) v))
  (forall ((x Bool) (y uni))
  (=> (mem (tuple21 bool b) (Tuple2 bool b (t2tb12 x) y) r)
  (and (mem2 x u) (mem b y v)))))
  (=>
  (forall ((x Bool) (y uni))
  (=> (sort b y)
  (=> (mem (tuple21 bool b) (Tuple2 bool b (t2tb12 x) y) r)
  (and (mem2 x u) (mem b y v))))) (subset (tuple21 bool b) r
  (times b bool (t2tb2 u) v)))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 Int (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))))) (u (set Int))
  (v (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))))
  (= (subset
  (tuple21 int
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (t2tb54 r)
  (times
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) 
  int (t2tb3 u) (t2tb v)))
  (forall ((x Int) (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))))
  (=> (mem
  (tuple21 int
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (Tuple2 int
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb13 x) (t2tb4 y)) (t2tb54 r)) (and (mem1 x u) (mem4 y v)))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 Int (set Int)))) (u (set Int))
  (v (set (set Int))))
  (= (subset (tuple21 int (set1 int)) (t2tb57 r)
  (times (set1 int) int (t2tb3 u) (t2tb1 v)))
  (forall ((x Int) (y (set Int)))
  (=> (mem (tuple21 int (set1 int))
  (Tuple2 int (set1 int) (t2tb13 x) (t2tb3 y)) (t2tb57 r))
  (and (mem1 x u) (mem3 y v)))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 Int Bool))) (u (set Int)) (v (set Bool)))
  (= (subset (tuple21 int bool) (t2tb60 r)
  (times bool int (t2tb3 u) (t2tb2 v)))
  (forall ((x Int) (y Bool))
  (=> (mem (tuple21 int bool) (Tuple2 int bool (t2tb13 x) (t2tb12 y))
  (t2tb60 r)) (and (mem1 x u) (mem2 y v)))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 Int Int))) (u (set Int)) (v (set Int)))
  (= (subset (tuple21 int int) (t2tb63 r)
  (times int int (t2tb3 u) (t2tb3 v)))
  (forall ((x Int) (y Int))
  (=> (mem (tuple21 int int) (Tuple2 int int (t2tb13 x) (t2tb13 y))
  (t2tb63 r)) (and (mem1 x u) (mem1 y v)))))))

;; subset_of_times
  (assert
  (forall ((b ty))
  (forall ((r uni) (u (set Int)) (v uni))
  (and
  (=> (subset (tuple21 int b) r (times b int (t2tb3 u) v))
  (forall ((x Int) (y uni))
  (=> (mem (tuple21 int b) (Tuple2 int b (t2tb13 x) y) r)
  (and (mem1 x u) (mem b y v)))))
  (=>
  (forall ((x Int) (y uni))
  (=> (sort b y)
  (=> (mem (tuple21 int b) (Tuple2 int b (t2tb13 x) y) r)
  (and (mem1 x u) (mem b y v))))) (subset (tuple21 int b) r
  (times b int (t2tb3 u) v)))))))

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
  (forall ((s uni) (x uni) (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))))
  (! (=> (mem a x s)
     (= (tb2t4
        (apply
        (set1
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int))) a
        (times
        (set1
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int))) a s (t2tb (add4 y empty8))) x)) y)) :pattern ((tb2t4
                                                                   (apply
                                                                   (set1
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   bool 
                                                                   bool)
                                                                   bool)
                                                                   bool)
                                                                   (set1 int)))
                                                                   a
                                                                   (times
                                                                   (set1
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   bool 
                                                                   bool)
                                                                   bool)
                                                                   bool)
                                                                   (set1 int)))
                                                                   a s
                                                                   (t2tb
                                                                   (add4 y
                                                                   empty8)))
                                                                   x))) ))))

;; apply_times
  (assert
  (forall ((a ty))
  (forall ((s uni) (x uni) (y (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))
  (! (=> (mem a x s)
     (= (tb2t8
        (apply
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int)) a
        (times
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int)) a s
        (add
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int)) (t2tb8 y) (t2tb4 empty4))) x)) y)) :pattern ((tb2t8
                                                                 (apply
                                                                 (tuple21
                                                                 (tuple21
                                                                 (tuple21
                                                                 (tuple21
                                                                 bool 
                                                                 bool) 
                                                                 bool) 
                                                                 bool)
                                                                 (set1 int))
                                                                 a
                                                                 (times
                                                                 (tuple21
                                                                 (tuple21
                                                                 (tuple21
                                                                 (tuple21
                                                                 bool 
                                                                 bool) 
                                                                 bool) 
                                                                 bool)
                                                                 (set1 int))
                                                                 a s
                                                                 (add
                                                                 (tuple21
                                                                 (tuple21
                                                                 (tuple21
                                                                 (tuple21
                                                                 bool 
                                                                 bool) 
                                                                 bool) 
                                                                 bool)
                                                                 (set1 int))
                                                                 (t2tb8 y)
                                                                 (t2tb4
                                                                 empty4))) x))) ))))

;; apply_times
  (assert
  (forall ((a ty))
  (forall ((s uni) (x uni) (y (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool)))
  (! (=> (mem a x s)
     (= (tb2t9
        (apply (tuple21 (tuple21 (tuple21 bool bool) bool) bool) a
        (times (tuple21 (tuple21 (tuple21 bool bool) bool) bool) a s
        (add (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 y)
        (t2tb5 empty5))) x)) y)) :pattern ((tb2t9
                                           (apply
                                           (tuple21
                                           (tuple21 (tuple21 bool bool) bool)
                                           bool) a
                                           (times
                                           (tuple21
                                           (tuple21 (tuple21 bool bool) bool)
                                           bool) a s
                                           (add
                                           (tuple21
                                           (tuple21 (tuple21 bool bool) bool)
                                           bool) (t2tb9 y) (t2tb5 empty5)))
                                           x))) ))))

;; apply_times
  (assert
  (forall ((a ty))
  (forall ((s uni) (x uni) (y (tuple2 (tuple2 Bool Bool) Bool)))
  (! (=> (mem a x s)
     (= (tb2t10
        (apply (tuple21 (tuple21 bool bool) bool) a
        (times (tuple21 (tuple21 bool bool) bool) a s
        (add (tuple21 (tuple21 bool bool) bool) (t2tb10 y) (t2tb6 empty6)))
        x)) y)) :pattern ((tb2t10
                          (apply (tuple21 (tuple21 bool bool) bool) a
                          (times (tuple21 (tuple21 bool bool) bool) a s
                          (add (tuple21 (tuple21 bool bool) bool) (t2tb10 y)
                          (t2tb6 empty6))) x))) ))))

;; apply_times
  (assert
  (forall ((a ty))
  (forall ((s uni) (x uni) (y (set Int)))
  (! (=> (mem a x s)
     (= (tb2t3
        (apply (set1 int) a (times (set1 int) a s (t2tb1 (add3 y empty3))) x)) y)) :pattern (
  (tb2t3
  (apply (set1 int) a (times (set1 int) a s (t2tb1 (add3 y empty3))) x))) ))))

;; apply_times
  (assert
  (forall ((a ty))
  (forall ((s uni) (x uni) (y (tuple2 Bool Bool)))
  (! (=> (mem a x s)
     (= (tb2t11
        (apply (tuple21 bool bool) a
        (times (tuple21 bool bool) a s
        (add (tuple21 bool bool) (t2tb11 y) (t2tb7 empty7))) x)) y)) :pattern (
  (tb2t11
  (apply (tuple21 bool bool) a
  (times (tuple21 bool bool) a s
  (add (tuple21 bool bool) (t2tb11 y) (t2tb7 empty7))) x))) ))))

;; apply_times
  (assert
  (forall ((a ty))
  (forall ((s uni) (x uni) (y Bool))
  (! (=> (mem a x s)
     (= (tb2t12 (apply bool a (times bool a s (t2tb2 (add1 y empty1))) x)) y)) :pattern (
  (tb2t12 (apply bool a (times bool a s (t2tb2 (add1 y empty1))) x))) ))))

;; apply_times
  (assert
  (forall ((a ty))
  (forall ((s uni) (x uni) (y Int))
  (! (=> (mem a x s)
     (= (tb2t13 (apply int a (times int a s (t2tb3 (add2 y empty2))) x)) y)) :pattern (
  (tb2t13 (apply int a (times int a s (t2tb3 (add2 y empty2))) x))) ))))

;; apply_times
  (assert
  (forall ((s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))) (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))))
  (! (=> (mem4 x s)
     (= (tb2t4
        (apply
        (set1
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int)))
        (set1
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int)))
        (times
        (set1
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int)))
        (set1
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int))) (t2tb s) (t2tb (add4 y empty8))) (t2tb4 x))) y)) :pattern (
  (tb2t4
  (apply
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (times
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s) (t2tb (add4 y empty8))) (t2tb4 x)))) )))

;; apply_times
  (assert
  (forall ((s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))) (y (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))
  (! (=> (mem4 x s)
     (= (tb2t8
        (apply
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int))
        (set1
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int)))
        (times
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int))
        (set1
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int))) (t2tb s)
        (add
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int)) (t2tb8 y) (t2tb4 empty4))) (t2tb4 x))) y)) :pattern (
  (tb2t8
  (apply
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (times
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s)
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb8 y) (t2tb4 empty4))) (t2tb4 x)))) )))

;; apply_times
  (assert
  (forall ((s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))) (y (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool)))
  (! (=> (mem4 x s)
     (= (tb2t9
        (apply (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int)))
        (times (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int))) (t2tb s)
        (add (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 y)
        (t2tb5 empty5))) (t2tb4 x))) y)) :pattern ((tb2t9
                                                   (apply
                                                   (tuple21
                                                   (tuple21
                                                   (tuple21 bool bool) 
                                                   bool) bool)
                                                   (set1
                                                   (tuple21
                                                   (tuple21
                                                   (tuple21
                                                   (tuple21 bool bool) 
                                                   bool) bool) (set1 int)))
                                                   (times
                                                   (tuple21
                                                   (tuple21
                                                   (tuple21 bool bool) 
                                                   bool) bool)
                                                   (set1
                                                   (tuple21
                                                   (tuple21
                                                   (tuple21
                                                   (tuple21 bool bool) 
                                                   bool) bool) (set1 int)))
                                                   (t2tb s)
                                                   (add
                                                   (tuple21
                                                   (tuple21
                                                   (tuple21 bool bool) 
                                                   bool) bool) (t2tb9 y)
                                                   (t2tb5 empty5)))
                                                   (t2tb4 x)))) )))

;; apply_times
  (assert
  (forall ((s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))) (y (tuple2 (tuple2 Bool Bool) Bool)))
  (! (=> (mem4 x s)
     (= (tb2t10
        (apply (tuple21 (tuple21 bool bool) bool)
        (set1
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int)))
        (times (tuple21 (tuple21 bool bool) bool)
        (set1
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int))) (t2tb s)
        (add (tuple21 (tuple21 bool bool) bool) (t2tb10 y) (t2tb6 empty6)))
        (t2tb4 x))) y)) :pattern ((tb2t10
                                  (apply (tuple21 (tuple21 bool bool) bool)
                                  (set1
                                  (tuple21
                                  (tuple21 (tuple21 (tuple21 bool bool) bool)
                                  bool) (set1 int)))
                                  (times (tuple21 (tuple21 bool bool) bool)
                                  (set1
                                  (tuple21
                                  (tuple21 (tuple21 (tuple21 bool bool) bool)
                                  bool) (set1 int))) (t2tb s)
                                  (add (tuple21 (tuple21 bool bool) bool)
                                  (t2tb10 y) (t2tb6 empty6))) (t2tb4 x)))) )))

;; apply_times
  (assert
  (forall ((s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))) (y (set Int)))
  (! (=> (mem4 x s)
     (= (tb2t3
        (apply (set1 int)
        (set1
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int)))
        (times (set1 int)
        (set1
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int))) (t2tb s) (t2tb1 (add3 y empty3))) (t2tb4 x))) y)) :pattern (
  (tb2t3
  (apply (set1 int)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (times (set1 int)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s) (t2tb1 (add3 y empty3))) (t2tb4 x)))) )))

;; apply_times
  (assert
  (forall ((s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))) (y (tuple2 Bool Bool)))
  (! (=> (mem4 x s)
     (= (tb2t11
        (apply (tuple21 bool bool)
        (set1
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int)))
        (times (tuple21 bool bool)
        (set1
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int))) (t2tb s)
        (add (tuple21 bool bool) (t2tb11 y) (t2tb7 empty7))) (t2tb4 x))) y)) :pattern (
  (tb2t11
  (apply (tuple21 bool bool)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (times (tuple21 bool bool)
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s) (add (tuple21 bool bool) (t2tb11 y) (t2tb7 empty7))) (t2tb4 x)))) )))

;; apply_times
  (assert
  (forall ((s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))) (y Bool))
  (! (=> (mem4 x s)
     (= (tb2t12
        (apply bool
        (set1
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int)))
        (times bool
        (set1
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int))) (t2tb s) (t2tb2 (add1 y empty1))) (t2tb4 x))) y)) :pattern (
  (tb2t12
  (apply bool
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (times bool
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s) (t2tb2 (add1 y empty1))) (t2tb4 x)))) )))

;; apply_times
  (assert
  (forall ((s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))) (y Int))
  (! (=> (mem4 x s)
     (= (tb2t13
        (apply int
        (set1
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int)))
        (times int
        (set1
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int))) (t2tb s) (t2tb3 (add2 y empty2))) (t2tb4 x))) y)) :pattern (
  (tb2t13
  (apply int
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (times int
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s) (t2tb3 (add2 y empty2))) (t2tb4 x)))) )))

;; apply_times
  (assert
  (forall ((b ty))
  (forall ((s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))) (y uni))
  (! (=> (sort b y)
     (=> (mem4 x s)
     (= (apply b
        (set1
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int)))
        (times b
        (set1
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int))) (t2tb s) (add b y (empty b))) (t2tb4 x)) y))) :pattern (
  (apply b
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (times b
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s) (add b y (empty b))) (t2tb4 x))) ))))

;; apply_times
  (assert
  (forall ((s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)) (y (set Int)))
  (! (=> (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
     (t2tb5 s))
     (= (tb2t3
        (apply (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (t2tb4 (times1 s (add3 y empty3))) (t2tb9 x))) y)) :pattern (
  (tb2t3
  (apply (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb4 (times1 s (add3 y empty3))) (t2tb9 x)))) )))

;; apply_times
  (assert
  (forall ((s (set (tuple2 (tuple2 Bool Bool) Bool))) (x (tuple2 (tuple2 Bool
  Bool) Bool)) (y Bool))
  (! (=> (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb6 s))
     (= (tb2t12
        (apply bool (tuple21 (tuple21 bool bool) bool)
        (t2tb5 (times2 s (add1 y empty1))) (t2tb10 x))) y)) :pattern (
  (tb2t12
  (apply bool (tuple21 (tuple21 bool bool) bool)
  (t2tb5 (times2 s (add1 y empty1))) (t2tb10 x)))) )))

;; apply_times
  (assert
  (forall ((s (set (set Int))) (x (set Int))
  (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))
  (! (=> (mem3 x s)
     (= (tb2t4
        (apply
        (set1
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int))) (set1 int)
        (times
        (set1
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int))) (set1 int) (t2tb1 s) (t2tb (add4 y empty8))) (t2tb3 x))) y)) :pattern (
  (tb2t4
  (apply
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1 int)
  (times
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (set1 int) (t2tb1 s) (t2tb (add4 y empty8))) (t2tb3 x)))) )))

;; apply_times
  (assert
  (forall ((s (set (set Int))) (x (set Int))
  (y (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))
  (! (=> (mem3 x s)
     (= (tb2t8
        (apply
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int)) (set1 int)
        (times
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int)) (set1 int) (t2tb1 s)
        (add
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int)) (t2tb8 y) (t2tb4 empty4))) (t2tb3 x))) y)) :pattern (
  (tb2t8
  (apply
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (set1 int)
  (times
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (set1 int) (t2tb1 s)
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb8 y) (t2tb4 empty4))) (t2tb3 x)))) )))

;; apply_times
  (assert
  (forall ((s (set (set Int))) (x (set Int)) (y (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool)))
  (! (=> (mem3 x s)
     (= (tb2t9
        (apply (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
        (times (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
        (t2tb1 s)
        (add (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 y)
        (t2tb5 empty5))) (t2tb3 x))) y)) :pattern ((tb2t9
                                                   (apply
                                                   (tuple21
                                                   (tuple21
                                                   (tuple21 bool bool) 
                                                   bool) bool) (set1 int)
                                                   (times
                                                   (tuple21
                                                   (tuple21
                                                   (tuple21 bool bool) 
                                                   bool) bool) (set1 int)
                                                   (t2tb1 s)
                                                   (add
                                                   (tuple21
                                                   (tuple21
                                                   (tuple21 bool bool) 
                                                   bool) bool) (t2tb9 y)
                                                   (t2tb5 empty5)))
                                                   (t2tb3 x)))) )))

;; apply_times
  (assert
  (forall ((s (set (set Int))) (x (set Int)) (y (tuple2 (tuple2 Bool Bool)
  Bool)))
  (! (=> (mem3 x s)
     (= (tb2t10
        (apply (tuple21 (tuple21 bool bool) bool) (set1 int)
        (times (tuple21 (tuple21 bool bool) bool) (set1 int) (t2tb1 s)
        (add (tuple21 (tuple21 bool bool) bool) (t2tb10 y) (t2tb6 empty6)))
        (t2tb3 x))) y)) :pattern ((tb2t10
                                  (apply (tuple21 (tuple21 bool bool) bool)
                                  (set1 int)
                                  (times (tuple21 (tuple21 bool bool) bool)
                                  (set1 int) (t2tb1 s)
                                  (add (tuple21 (tuple21 bool bool) bool)
                                  (t2tb10 y) (t2tb6 empty6))) (t2tb3 x)))) )))

;; apply_times
  (assert
  (forall ((s (set (set Int))) (x (set Int)) (y (set Int)))
  (! (=> (mem3 x s)
     (= (tb2t3
        (apply (set1 int) (set1 int)
        (times (set1 int) (set1 int) (t2tb1 s) (t2tb1 (add3 y empty3)))
        (t2tb3 x))) y)) :pattern ((tb2t3
                                  (apply (set1 int) (set1 int)
                                  (times (set1 int) (set1 int) (t2tb1 s)
                                  (t2tb1 (add3 y empty3))) (t2tb3 x)))) )))

;; apply_times
  (assert
  (forall ((s (set (set Int))) (x (set Int)) (y (tuple2 Bool Bool)))
  (! (=> (mem3 x s)
     (= (tb2t11
        (apply (tuple21 bool bool) (set1 int)
        (times (tuple21 bool bool) (set1 int) (t2tb1 s)
        (add (tuple21 bool bool) (t2tb11 y) (t2tb7 empty7))) (t2tb3 x))) y)) :pattern (
  (tb2t11
  (apply (tuple21 bool bool) (set1 int)
  (times (tuple21 bool bool) (set1 int) (t2tb1 s)
  (add (tuple21 bool bool) (t2tb11 y) (t2tb7 empty7))) (t2tb3 x)))) )))

;; apply_times
  (assert
  (forall ((s (set (set Int))) (x (set Int)) (y Bool))
  (! (=> (mem3 x s)
     (= (tb2t12
        (apply bool (set1 int)
        (times bool (set1 int) (t2tb1 s) (t2tb2 (add1 y empty1))) (t2tb3 x))) y)) :pattern (
  (tb2t12
  (apply bool (set1 int)
  (times bool (set1 int) (t2tb1 s) (t2tb2 (add1 y empty1))) (t2tb3 x)))) )))

;; apply_times
  (assert
  (forall ((s (set (set Int))) (x (set Int)) (y Int))
  (! (=> (mem3 x s)
     (= (tb2t13
        (apply int (set1 int)
        (times int (set1 int) (t2tb1 s) (t2tb3 (add2 y empty2))) (t2tb3 x))) y)) :pattern (
  (tb2t13
  (apply int (set1 int)
  (times int (set1 int) (t2tb1 s) (t2tb3 (add2 y empty2))) (t2tb3 x)))) )))

;; apply_times
  (assert
  (forall ((b ty))
  (forall ((s (set (set Int))) (x (set Int)) (y uni))
  (! (=> (sort b y)
     (=> (mem3 x s)
     (= (apply b (set1 int)
        (times b (set1 int) (t2tb1 s) (add b y (empty b))) (t2tb3 x)) y))) :pattern (
  (apply b (set1 int) (times b (set1 int) (t2tb1 s) (add b y (empty b)))
  (t2tb3 x))) ))))

;; apply_times
  (assert
  (forall ((s (set (tuple2 Bool Bool))) (x (tuple2 Bool Bool)) (y Bool))
  (! (=> (mem (tuple21 bool bool) (t2tb11 x) (t2tb7 s))
     (= (tb2t12
        (apply bool (tuple21 bool bool) (t2tb6 (times3 s (add1 y empty1)))
        (t2tb11 x))) y)) :pattern ((tb2t12
                                   (apply bool (tuple21 bool bool)
                                   (t2tb6 (times3 s (add1 y empty1)))
                                   (t2tb11 x)))) )))

;; apply_times
  (assert
  (forall ((s (set Bool)) (x Bool)
  (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))
  (! (=> (mem2 x s)
     (= (tb2t4
        (apply
        (set1
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int))) bool
        (times
        (set1
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int))) bool (t2tb2 s) (t2tb (add4 y empty8))) (t2tb12 x))) y)) :pattern (
  (tb2t4
  (apply
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  bool
  (times
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  bool (t2tb2 s) (t2tb (add4 y empty8))) (t2tb12 x)))) )))

;; apply_times
  (assert
  (forall ((s (set Bool)) (x Bool) (y (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))
  (! (=> (mem2 x s)
     (= (tb2t8
        (apply
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int)) bool
        (times
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int)) bool (t2tb2 s)
        (add
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int)) (t2tb8 y) (t2tb4 empty4))) (t2tb12 x))) y)) :pattern (
  (tb2t8
  (apply
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)) 
  bool
  (times
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)) 
  bool (t2tb2 s)
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb8 y) (t2tb4 empty4))) (t2tb12 x)))) )))

;; apply_times
  (assert
  (forall ((s (set Bool)) (x Bool) (y (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool)))
  (! (=> (mem2 x s)
     (= (tb2t9
        (apply (tuple21 (tuple21 (tuple21 bool bool) bool) bool) bool
        (times (tuple21 (tuple21 (tuple21 bool bool) bool) bool) bool
        (t2tb2 s)
        (add (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 y)
        (t2tb5 empty5))) (t2tb12 x))) y)) :pattern ((tb2t9
                                                    (apply
                                                    (tuple21
                                                    (tuple21
                                                    (tuple21 bool bool) 
                                                    bool) bool) bool
                                                    (times
                                                    (tuple21
                                                    (tuple21
                                                    (tuple21 bool bool) 
                                                    bool) bool) bool
                                                    (t2tb2 s)
                                                    (add
                                                    (tuple21
                                                    (tuple21
                                                    (tuple21 bool bool) 
                                                    bool) bool) (t2tb9 y)
                                                    (t2tb5 empty5)))
                                                    (t2tb12 x)))) )))

;; apply_times
  (assert
  (forall ((s (set Bool)) (x Bool) (y (tuple2 (tuple2 Bool Bool) Bool)))
  (! (=> (mem2 x s)
     (= (tb2t10
        (apply (tuple21 (tuple21 bool bool) bool) bool
        (times (tuple21 (tuple21 bool bool) bool) bool (t2tb2 s)
        (add (tuple21 (tuple21 bool bool) bool) (t2tb10 y) (t2tb6 empty6)))
        (t2tb12 x))) y)) :pattern ((tb2t10
                                   (apply (tuple21 (tuple21 bool bool) bool)
                                   bool
                                   (times (tuple21 (tuple21 bool bool) bool)
                                   bool (t2tb2 s)
                                   (add (tuple21 (tuple21 bool bool) bool)
                                   (t2tb10 y) (t2tb6 empty6))) (t2tb12 x)))) )))

;; apply_times
  (assert
  (forall ((s (set Bool)) (x Bool) (y (set Int)))
  (! (=> (mem2 x s)
     (= (tb2t3
        (apply (set1 int) bool
        (times (set1 int) bool (t2tb2 s) (t2tb1 (add3 y empty3))) (t2tb12 x))) y)) :pattern (
  (tb2t3
  (apply (set1 int) bool
  (times (set1 int) bool (t2tb2 s) (t2tb1 (add3 y empty3))) (t2tb12 x)))) )))

;; apply_times
  (assert
  (forall ((s (set Bool)) (x Bool) (y (tuple2 Bool Bool)))
  (! (=> (mem2 x s)
     (= (tb2t11
        (apply (tuple21 bool bool) bool
        (times (tuple21 bool bool) bool (t2tb2 s)
        (add (tuple21 bool bool) (t2tb11 y) (t2tb7 empty7))) (t2tb12 x))) y)) :pattern (
  (tb2t11
  (apply (tuple21 bool bool) bool
  (times (tuple21 bool bool) bool (t2tb2 s)
  (add (tuple21 bool bool) (t2tb11 y) (t2tb7 empty7))) (t2tb12 x)))) )))

;; apply_times
  (assert
  (forall ((s (set Bool)) (x Bool) (y Bool))
  (! (=> (mem2 x s)
     (= (tb2t12
        (apply bool bool (t2tb7 (times4 s (add1 y empty1))) (t2tb12 x))) y)) :pattern (
  (tb2t12 (apply bool bool (t2tb7 (times4 s (add1 y empty1))) (t2tb12 x)))) )))

;; apply_times
  (assert
  (forall ((s (set Bool)) (x Bool) (y Int))
  (! (=> (mem2 x s)
     (= (tb2t13
        (apply int bool (times int bool (t2tb2 s) (t2tb3 (add2 y empty2)))
        (t2tb12 x))) y)) :pattern ((tb2t13
                                   (apply int bool
                                   (times int bool (t2tb2 s)
                                   (t2tb3 (add2 y empty2))) (t2tb12 x)))) )))

;; apply_times
  (assert
  (forall ((b ty))
  (forall ((s (set Bool)) (x Bool) (y uni))
  (! (=> (sort b y)
     (=> (mem2 x s)
     (= (apply b bool (times b bool (t2tb2 s) (add b y (empty b)))
        (t2tb12 x)) y))) :pattern ((apply b bool
                                   (times b bool (t2tb2 s)
                                   (add b y (empty b))) (t2tb12 x))) ))))

;; apply_times
  (assert
  (forall ((s (set Int)) (x Int) (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))))
  (! (=> (mem1 x s)
     (= (tb2t4
        (apply
        (set1
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int))) int
        (times
        (set1
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int))) int (t2tb3 s) (t2tb (add4 y empty8))) (t2tb13 x))) y)) :pattern (
  (tb2t4
  (apply
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) 
  int
  (times
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) 
  int (t2tb3 s) (t2tb (add4 y empty8))) (t2tb13 x)))) )))

;; apply_times
  (assert
  (forall ((s (set Int)) (x Int) (y (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))
  (! (=> (mem1 x s)
     (= (tb2t8
        (apply
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int)) int
        (times
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int)) int (t2tb3 s)
        (add
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int)) (t2tb8 y) (t2tb4 empty4))) (t2tb13 x))) y)) :pattern (
  (tb2t8
  (apply
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)) 
  int
  (times
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)) 
  int (t2tb3 s)
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb8 y) (t2tb4 empty4))) (t2tb13 x)))) )))

;; apply_times
  (assert
  (forall ((s (set Int)) (x Int) (y (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool)))
  (! (=> (mem1 x s)
     (= (tb2t9
        (apply (tuple21 (tuple21 (tuple21 bool bool) bool) bool) int
        (times (tuple21 (tuple21 (tuple21 bool bool) bool) bool) int
        (t2tb3 s)
        (add (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 y)
        (t2tb5 empty5))) (t2tb13 x))) y)) :pattern ((tb2t9
                                                    (apply
                                                    (tuple21
                                                    (tuple21
                                                    (tuple21 bool bool) 
                                                    bool) bool) int
                                                    (times
                                                    (tuple21
                                                    (tuple21
                                                    (tuple21 bool bool) 
                                                    bool) bool) int (t2tb3 s)
                                                    (add
                                                    (tuple21
                                                    (tuple21
                                                    (tuple21 bool bool) 
                                                    bool) bool) (t2tb9 y)
                                                    (t2tb5 empty5)))
                                                    (t2tb13 x)))) )))

;; apply_times
  (assert
  (forall ((s (set Int)) (x Int) (y (tuple2 (tuple2 Bool Bool) Bool)))
  (! (=> (mem1 x s)
     (= (tb2t10
        (apply (tuple21 (tuple21 bool bool) bool) int
        (times (tuple21 (tuple21 bool bool) bool) int (t2tb3 s)
        (add (tuple21 (tuple21 bool bool) bool) (t2tb10 y) (t2tb6 empty6)))
        (t2tb13 x))) y)) :pattern ((tb2t10
                                   (apply (tuple21 (tuple21 bool bool) bool)
                                   int
                                   (times (tuple21 (tuple21 bool bool) bool)
                                   int (t2tb3 s)
                                   (add (tuple21 (tuple21 bool bool) bool)
                                   (t2tb10 y) (t2tb6 empty6))) (t2tb13 x)))) )))

;; apply_times
  (assert
  (forall ((s (set Int)) (x Int) (y (set Int)))
  (! (=> (mem1 x s)
     (= (tb2t3
        (apply (set1 int) int
        (times (set1 int) int (t2tb3 s) (t2tb1 (add3 y empty3))) (t2tb13 x))) y)) :pattern (
  (tb2t3
  (apply (set1 int) int
  (times (set1 int) int (t2tb3 s) (t2tb1 (add3 y empty3))) (t2tb13 x)))) )))

;; apply_times
  (assert
  (forall ((s (set Int)) (x Int) (y (tuple2 Bool Bool)))
  (! (=> (mem1 x s)
     (= (tb2t11
        (apply (tuple21 bool bool) int
        (times (tuple21 bool bool) int (t2tb3 s)
        (add (tuple21 bool bool) (t2tb11 y) (t2tb7 empty7))) (t2tb13 x))) y)) :pattern (
  (tb2t11
  (apply (tuple21 bool bool) int
  (times (tuple21 bool bool) int (t2tb3 s)
  (add (tuple21 bool bool) (t2tb11 y) (t2tb7 empty7))) (t2tb13 x)))) )))

;; apply_times
  (assert
  (forall ((s (set Int)) (x Int) (y Bool))
  (! (=> (mem1 x s)
     (= (tb2t12
        (apply bool int (times bool int (t2tb3 s) (t2tb2 (add1 y empty1)))
        (t2tb13 x))) y)) :pattern ((tb2t12
                                   (apply bool int
                                   (times bool int (t2tb3 s)
                                   (t2tb2 (add1 y empty1))) (t2tb13 x)))) )))

;; apply_times
  (assert
  (forall ((s (set Int)) (x Int) (y Int))
  (! (=> (mem1 x s)
     (= (tb2t13
        (apply int int (times int int (t2tb3 s) (t2tb3 (add2 y empty2)))
        (t2tb13 x))) y)) :pattern ((tb2t13
                                   (apply int int
                                   (times int int (t2tb3 s)
                                   (t2tb3 (add2 y empty2))) (t2tb13 x)))) )))

;; apply_times
  (assert
  (forall ((b ty))
  (forall ((s (set Int)) (x Int) (y uni))
  (! (=> (sort b y)
     (=> (mem1 x s)
     (= (apply b int (times b int (t2tb3 s) (add b y (empty b))) (t2tb13 x)) y))) :pattern (
  (apply b int (times b int (t2tb3 s) (add b y (empty b))) (t2tb13 x))) ))))

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
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (y uni) (q uni) (r uni))
  (= (mem
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b)
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b
  (t2tb4 x) y)
  (infix_lspl b
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) q
  r))
  (ite (mem4 x
  (tb2t
  (dom b
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) r)))
  (mem
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b)
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b
  (t2tb4 x) y) r) (mem
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b)
  (Tuple2
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b
  (t2tb4 x) y) q))))))

;; overriding_def
  (assert
  (forall ((b ty))
  (forall ((x (set Int)) (y uni) (q uni) (r uni))
  (= (mem (tuple21 (set1 int) b) (Tuple2 (set1 int) b (t2tb3 x) y)
  (infix_lspl b (set1 int) q r))
  (ite (mem3 x (tb2t1 (dom b (set1 int) r))) (mem (tuple21 (set1 int) b)
  (Tuple2 (set1 int) b (t2tb3 x) y) r) (mem (tuple21 (set1 int) b)
  (Tuple2 (set1 int) b (t2tb3 x) y) q))))))

;; overriding_def
  (assert
  (forall ((b ty))
  (forall ((x Bool) (y uni) (q uni) (r uni))
  (= (mem (tuple21 bool b) (Tuple2 bool b (t2tb12 x) y)
  (infix_lspl b bool q r))
  (ite (mem2 x (tb2t2 (dom b bool r))) (mem (tuple21 bool b)
  (Tuple2 bool b (t2tb12 x) y) r) (mem (tuple21 bool b)
  (Tuple2 bool b (t2tb12 x) y) q))))))

;; overriding_def
  (assert
  (forall ((b ty))
  (forall ((x Int) (y uni) (q uni) (r uni))
  (= (mem (tuple21 int b) (Tuple2 int b (t2tb13 x) y) (infix_lspl b int q r))
  (ite (mem1 x (tb2t3 (dom b int r))) (mem (tuple21 int b)
  (Tuple2 int b (t2tb13 x) y) r) (mem (tuple21 int b)
  (Tuple2 int b (t2tb13 x) y) q))))))

;; overriding_def
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (y uni) (q uni) (r uni))
  (= (mem (tuple21 a b) (Tuple2 a b x y) (infix_lspl b a q r))
  (ite (mem a x (dom b a r)) (mem (tuple21 a b) (Tuple2 a b x y) r) (mem
  (tuple21 a b) (Tuple2 a b x y) q))))))

;; function_overriding
  (assert
  (forall ((s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (t (set (set Int))) (f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))) (g (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))))
  (=> (and (mem4 f (infix_plmngt1 s t)) (mem4 g (infix_plmngt1 s t))) (mem4
  (tb2t4
  (infix_lspl (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb4 f) (t2tb4 g))) (infix_plmngt1 s t)))))

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
  (forall ((s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (t uni) (f uni) (g uni)
  (x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))
  (! (=>
     (and (mem
     (set1
     (tuple21
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     b)) f
     (infix_plmngt b
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb s) t)) (mem
     (set1
     (tuple21
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     b)) g
     (infix_plmngt b
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb s) t)))
     (=> (mem4 x
     (tb2t
     (dom b
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     g)))
     (= (apply b
        (set1
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int)))
        (infix_lspl b
        (set1
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int))) f g) (t2tb4 x)) (apply b
                                     (set1
                                     (tuple21
                                     (tuple21
                                     (tuple21 (tuple21 bool bool) bool) 
                                     bool) (set1 int))) g (t2tb4 x))))) :pattern ((mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b))
  f
  (infix_plmngt b
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s) t)) (mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b))
  g
  (infix_plmngt b
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s) t))
  (apply b
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (infix_lspl b
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) f
  g) (t2tb4 x))) ))))

;; apply_overriding_1
  (assert
  (forall ((s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (t (set (set Int))) (f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))) (g (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))) (x (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool)))
  (! (=> (and (mem4 f (infix_plmngt1 s t)) (mem4 g (infix_plmngt1 s t)))
     (=> (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
     (dom (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (t2tb4 g)))
     (= (tb2t3
        (apply (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (infix_lspl (set1 int)
        (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb4 f)
        (t2tb4 g)) (t2tb9 x))) (tb2t3
                               (apply (set1 int)
                               (tuple21 (tuple21 (tuple21 bool bool) bool)
                               bool) (t2tb4 g) (t2tb9 x)))))) :pattern ((mem4
  f (infix_plmngt1 s t)) (mem4 g (infix_plmngt1 s t))
  (tb2t3
  (apply (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (infix_lspl (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb4 f) (t2tb4 g)) (t2tb9 x)))) )))

;; apply_overriding_1
  (assert
  (forall ((b ty))
  (forall ((s (set (set Int))) (t uni) (f uni) (g uni) (x (set Int)))
  (! (=>
     (and (mem (set1 (tuple21 (set1 int) b)) f
     (infix_plmngt b (set1 int) (t2tb1 s) t)) (mem
     (set1 (tuple21 (set1 int) b)) g
     (infix_plmngt b (set1 int) (t2tb1 s) t)))
     (=> (mem3 x (tb2t1 (dom b (set1 int) g)))
     (= (apply b (set1 int) (infix_lspl b (set1 int) f g) (t2tb3 x)) 
     (apply b (set1 int) g (t2tb3 x))))) :pattern ((mem
  (set1 (tuple21 (set1 int) b)) f (infix_plmngt b (set1 int) (t2tb1 s) t))
  (mem (set1 (tuple21 (set1 int) b)) g
  (infix_plmngt b (set1 int) (t2tb1 s) t))
  (apply b (set1 int) (infix_lspl b (set1 int) f g) (t2tb3 x))) ))))

;; apply_overriding_1
  (assert
  (forall ((b ty))
  (forall ((s (set Bool)) (t uni) (f uni) (g uni) (x Bool))
  (! (=>
     (and (mem (set1 (tuple21 bool b)) f (infix_plmngt b bool (t2tb2 s) t))
     (mem (set1 (tuple21 bool b)) g (infix_plmngt b bool (t2tb2 s) t)))
     (=> (mem2 x (tb2t2 (dom b bool g)))
     (= (apply b bool (infix_lspl b bool f g) (t2tb12 x)) (apply b bool g
                                                          (t2tb12 x))))) :pattern ((mem
  (set1 (tuple21 bool b)) f (infix_plmngt b bool (t2tb2 s) t)) (mem
  (set1 (tuple21 bool b)) g (infix_plmngt b bool (t2tb2 s) t))
  (apply b bool (infix_lspl b bool f g) (t2tb12 x))) ))))

;; apply_overriding_1
  (assert
  (forall ((b ty))
  (forall ((s (set Int)) (t uni) (f uni) (g uni) (x Int))
  (! (=>
     (and (mem (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb3 s) t))
     (mem (set1 (tuple21 int b)) g (infix_plmngt b int (t2tb3 s) t)))
     (=> (mem1 x (tb2t3 (dom b int g)))
     (= (apply b int (infix_lspl b int f g) (t2tb13 x)) (apply b int g
                                                        (t2tb13 x))))) :pattern ((mem
  (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb3 s) t)) (mem
  (set1 (tuple21 int b)) g (infix_plmngt b int (t2tb3 s) t))
  (apply b int (infix_lspl b int f g) (t2tb13 x))) ))))

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
  (forall ((s (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (t uni) (f uni) (g uni)
  (x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))
  (! (=>
     (and (mem
     (set1
     (tuple21
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     b)) f
     (infix_plmngt b
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb s) t)) (mem
     (set1
     (tuple21
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     b)) g
     (infix_plmngt b
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb s) t)))
     (=>
     (not (mem4 x
     (tb2t
     (dom b
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     g))))
     (=> (mem4 x
     (tb2t
     (dom b
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     f)))
     (= (apply b
        (set1
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int)))
        (infix_lspl b
        (set1
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int))) f g) (t2tb4 x)) (apply b
                                     (set1
                                     (tuple21
                                     (tuple21
                                     (tuple21 (tuple21 bool bool) bool) 
                                     bool) (set1 int))) f (t2tb4 x)))))) :pattern ((mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b))
  f
  (infix_plmngt b
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s) t))
  (apply b
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (infix_lspl b
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) f
  g) (t2tb4 x))) :pattern ((mem
  (set1
  (tuple21
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) b))
  g
  (infix_plmngt b
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb s) t))
  (apply b
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (infix_lspl b
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))) f
  g) (t2tb4 x))) ))))

;; apply_overriding_2
  (assert
  (forall ((s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (t (set (set Int))) (f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))) (g (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))) (x (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool)))
  (! (=> (and (mem4 f (infix_plmngt1 s t)) (mem4 g (infix_plmngt1 s t)))
     (=>
     (not (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
     (dom (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (t2tb4 g))))
     (=> (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
     (dom (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (t2tb4 f)))
     (= (tb2t3
        (apply (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (infix_lspl (set1 int)
        (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb4 f)
        (t2tb4 g)) (t2tb9 x))) (tb2t3
                               (apply (set1 int)
                               (tuple21 (tuple21 (tuple21 bool bool) bool)
                               bool) (t2tb4 f) (t2tb9 x))))))) :pattern ((mem4
  f (infix_plmngt1 s t))
  (tb2t3
  (apply (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (infix_lspl (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb4 f) (t2tb4 g)) (t2tb9 x)))) :pattern ((mem4 g (infix_plmngt1 s t))
  (tb2t3
  (apply (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (infix_lspl (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb4 f) (t2tb4 g)) (t2tb9 x)))) )))

;; apply_overriding_2
  (assert
  (forall ((b ty))
  (forall ((s (set (set Int))) (t uni) (f uni) (g uni) (x (set Int)))
  (! (=>
     (and (mem (set1 (tuple21 (set1 int) b)) f
     (infix_plmngt b (set1 int) (t2tb1 s) t)) (mem
     (set1 (tuple21 (set1 int) b)) g
     (infix_plmngt b (set1 int) (t2tb1 s) t)))
     (=> (not (mem3 x (tb2t1 (dom b (set1 int) g))))
     (=> (mem3 x (tb2t1 (dom b (set1 int) f)))
     (= (apply b (set1 int) (infix_lspl b (set1 int) f g) (t2tb3 x)) 
     (apply b (set1 int) f (t2tb3 x)))))) :pattern ((mem
  (set1 (tuple21 (set1 int) b)) f (infix_plmngt b (set1 int) (t2tb1 s) t))
  (apply b (set1 int) (infix_lspl b (set1 int) f g) (t2tb3 x))) :pattern ((mem
  (set1 (tuple21 (set1 int) b)) g (infix_plmngt b (set1 int) (t2tb1 s) t))
  (apply b (set1 int) (infix_lspl b (set1 int) f g) (t2tb3 x))) ))))

;; apply_overriding_2
  (assert
  (forall ((b ty))
  (forall ((s (set Bool)) (t uni) (f uni) (g uni) (x Bool))
  (! (=>
     (and (mem (set1 (tuple21 bool b)) f (infix_plmngt b bool (t2tb2 s) t))
     (mem (set1 (tuple21 bool b)) g (infix_plmngt b bool (t2tb2 s) t)))
     (=> (not (mem2 x (tb2t2 (dom b bool g))))
     (=> (mem2 x (tb2t2 (dom b bool f)))
     (= (apply b bool (infix_lspl b bool f g) (t2tb12 x)) (apply b bool f
                                                          (t2tb12 x)))))) :pattern ((mem
  (set1 (tuple21 bool b)) f (infix_plmngt b bool (t2tb2 s) t))
  (apply b bool (infix_lspl b bool f g) (t2tb12 x))) :pattern ((mem
  (set1 (tuple21 bool b)) g (infix_plmngt b bool (t2tb2 s) t))
  (apply b bool (infix_lspl b bool f g) (t2tb12 x))) ))))

;; apply_overriding_2
  (assert
  (forall ((b ty))
  (forall ((s (set Int)) (t uni) (f uni) (g uni) (x Int))
  (! (=>
     (and (mem (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb3 s) t))
     (mem (set1 (tuple21 int b)) g (infix_plmngt b int (t2tb3 s) t)))
     (=> (not (mem1 x (tb2t3 (dom b int g))))
     (=> (mem1 x (tb2t3 (dom b int f)))
     (= (apply b int (infix_lspl b int f g) (t2tb13 x)) (apply b int f
                                                        (t2tb13 x)))))) :pattern ((mem
  (set1 (tuple21 int b)) f (infix_plmngt b int (t2tb3 s) t))
  (apply b int (infix_lspl b int f g) (t2tb13 x))) :pattern ((mem
  (set1 (tuple21 int b)) g (infix_plmngt b int (t2tb3 s) t))
  (apply b int (infix_lspl b int f g) (t2tb13 x))) ))))

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

(declare-fun t2tb200 ((set enum_aa)) uni)

;; t2tb_sort
  (assert (forall ((x (set enum_aa))) (sort (set1 enum_aa1) (t2tb200 x))))

(declare-fun tb2t200 (uni) (set enum_aa))

;; BridgeL
  (assert
  (forall ((i (set enum_aa)))
  (! (= (tb2t200 (t2tb200 i)) i) :pattern ((t2tb200 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 enum_aa1) j) (= (t2tb200 (tb2t200 j)) j)) :pattern (
  (t2tb200 (tb2t200 j))) )))

(declare-fun t2tb201 (enum_aa) uni)

;; t2tb_sort
  (assert (forall ((x enum_aa)) (sort enum_aa1 (t2tb201 x))))

(declare-fun tb2t201 (uni) enum_aa)

;; BridgeL
  (assert
  (forall ((i enum_aa))
  (! (= (tb2t201 (t2tb201 i)) i) :pattern ((t2tb201 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort enum_aa1 j) (= (t2tb201 (tb2t201 j)) j)) :pattern ((t2tb201
                                                                  (tb2t201 j))) )))

;; set_enum_aa_axiom
  (assert
  (forall ((x enum_aa)) (mem enum_aa1 (t2tb201 x) (t2tb200 set_enum_aa))))

(declare-fun f1 (Int Int Int Int Int Int Int Bool Bool Bool Bool Int Bool
  Bool Bool Bool (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))) Int Int Int) Bool)

;; f1_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss Bool) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Int)
  (v_nn Bool) (v_mm Bool) (v_ll Bool) (v_kk Bool)
  (v_jj (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (v_bbcc Int) (v_bbbb Int) (v_bbaa Int))
  (= (f1 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbcc v_bbbb v_bbaa)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (and (= v_tt 0) (= v_uu 1)) (mem1 v_vv integer)) (<= 0 v_vv))
  (<= v_vv 2147483647)) (mem1 v_ww integer)) (<= 0 v_ww))
  (<= v_ww 2147483647)) (mem1 v_xx integer)) (<= 0 v_xx))
  (<= v_xx 2147483647)) (mem1 v_yy integer)) (<= 0 v_yy))
  (<= v_yy 2147483647)) (<= 1 v_yy)) (<= v_yy 254)) (= v_yy v_ww)) (mem1 v_zz
  integer)) (<= 0 v_zz)) (<= v_zz 2147483647)) (<= 1 v_zz)) (<= v_zz 254))
  (= v_zz v_ww)) (mem1 v_bbaa integer)) (<= 0 v_bbaa))
  (<= v_bbaa 2147483647)) (<= 1 v_bbaa)) (<= (+ v_bbaa 1) 2147483647))
  (= v_bbaa v_xx)) (mem1 v_bbbb integer)) (<= 0 v_bbbb))
  (<= v_bbbb 2147483647)) (<= 2 v_bbbb)) (= v_bbbb v_vv))
  (<= (+ v_bbbb v_zz) 253)) (<= (+ (+ v_bbbb v_yy) v_zz) 251)) (mem1 v_bbcc
  integer)) (<= 0 v_bbcc)) (<= v_bbcc 2147483647)) (<= 1 v_bbcc))
  (<= (+ v_bbcc 1) 254)) (= v_bbcc v_vv)))))

(declare-fun f2 (Int Int Int Int Int Int Int Bool Bool Bool Bool Int Bool
  Bool Bool Bool (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))) Int Int Int) Bool)

;; f2_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss Bool) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Int)
  (v_nn Bool) (v_mm Bool) (v_ll Bool) (v_kk Bool)
  (v_jj (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (v_bbcc Int) (v_bbbb Int) (v_bbaa Int)) (f2 v_zz v_yy v_xx
  v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn v_mm v_ll v_kk v_jj
  v_bbcc v_bbbb v_bbaa)))

(declare-fun f6 (Int Int Int Int Int Int Int Bool Bool Bool Bool Int Bool
  Bool Bool Bool (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))) Int Int Int) Bool)

;; f6_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss Bool) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Int)
  (v_nn Bool) (v_mm Bool) (v_ll Bool) (v_kk Bool)
  (v_jj (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (v_bbcc Int) (v_bbbb Int) (v_bbaa Int))
  (= (f6 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbcc v_bbbb v_bbaa)
  (and
  (and (and (mem1 v_oo integer) (<= 0 v_oo)) (mem4 v_jj
  (infix_plmngt1 (times2 (times3 (times4 b_bool b_bool) b_bool) b_bool)
  (power1 natural)))) (infix_eqeq
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (dom (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb4 v_jj))
  (t2tb5 (times2 (times3 (times4 b_bool b_bool) b_bool) b_bool)))))))

(declare-fun f8 (Int Int Int Int Int Int Int Bool Bool Bool Bool Int Bool
  Bool Bool Bool (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))) Int Int Int) Bool)

;; f8_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss Bool) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Int)
  (v_nn Bool) (v_mm Bool) (v_ll Bool) (v_kk Bool)
  (v_jj (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (v_bbcc Int) (v_bbbb Int) (v_bbaa Int))
  (= (f8 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbcc v_bbbb v_bbaa) (mem1 (+ v_oo 1) integer))))

(declare-fun f9 (Int Int Int Int Int Int Int Bool Bool Bool Bool Int Bool
  Bool Bool Bool (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))) Int Int Int) Bool)

;; f9_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss Bool) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Int)
  (v_nn Bool) (v_mm Bool) (v_ll Bool) (v_kk Bool)
  (v_jj (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (v_bbcc Int) (v_bbbb Int) (v_bbaa Int))
  (= (f9 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbcc v_bbbb v_bbaa) (<= 0 (+ v_oo 1)))))

(declare-fun f11 (Int Int Int Int Int Int Int Bool Bool Bool Bool Int Bool
  Bool Bool Bool (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))) Int Int Int) Bool)

;; f11_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss Bool) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Int)
  (v_nn Bool) (v_mm Bool) (v_ll Bool) (v_kk Bool)
  (v_jj (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (v_bbcc Int) (v_bbbb Int) (v_bbaa Int))
  (= (f11 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbcc v_bbbb v_bbaa) (mem4
  (tb2t4
  (infix_lspl (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb4 v_jj)
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (Tuple2 (tuple21 (tuple21 bool bool) bool) bool
  (Tuple2 (tuple21 bool bool) bool
  (Tuple2 bool bool (t2tb12 v_kk) (t2tb12 v_ll)) (t2tb12 v_mm))
  (t2tb12 v_nn))
  (union int
  (apply (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb4 v_jj)
  (Tuple2 (tuple21 (tuple21 bool bool) bool) bool
  (Tuple2 (tuple21 bool bool) bool
  (Tuple2 bool bool (t2tb12 v_kk) (t2tb12 v_ll)) (t2tb12 v_mm))
  (t2tb12 v_nn))) (t2tb3 (add2 (+ v_oo 1) empty2)))) (t2tb4 empty4))))
  (infix_plmngt1 (times2 (times3 (times4 b_bool b_bool) b_bool) b_bool)
  (power1 natural))))))

(declare-fun f12 (Int Int Int Int Int Int Int Bool Bool Bool Bool Int Bool
  Bool Bool Bool (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))) Int Int Int) Bool)

;; f12_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss Bool) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Int)
  (v_nn Bool) (v_mm Bool) (v_ll Bool) (v_kk Bool)
  (v_jj (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (v_bbcc Int) (v_bbbb Int) (v_bbaa Int))
  (= (f12 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbcc v_bbbb v_bbaa) (infix_eqeq
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (dom (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (infix_lspl (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb4 v_jj)
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (Tuple2 (tuple21 (tuple21 bool bool) bool) bool
  (Tuple2 (tuple21 bool bool) bool
  (Tuple2 bool bool (t2tb12 v_kk) (t2tb12 v_ll)) (t2tb12 v_mm))
  (t2tb12 v_nn))
  (union int
  (apply (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb4 v_jj)
  (Tuple2 (tuple21 (tuple21 bool bool) bool) bool
  (Tuple2 (tuple21 bool bool) bool
  (Tuple2 bool bool (t2tb12 v_kk) (t2tb12 v_ll)) (t2tb12 v_mm))
  (t2tb12 v_nn))) (t2tb3 (add2 (+ v_oo 1) empty2)))) (t2tb4 empty4))))
  (t2tb5 (times2 (times3 (times4 b_bool b_bool) b_bool) b_bool))))))

(assert
;; bbdd_1
 ;; File "POwhy_bpo2why/p4/p4_34.why", line 177, characters 7-13
  (not
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss Bool) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Int)
  (v_nn Bool) (v_mm Bool) (v_ll Bool) (v_kk Bool)
  (v_jj (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (v_bbcc Int) (v_bbbb Int) (v_bbaa Int))
  (=>
  (and (f1 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbcc v_bbbb v_bbaa) (f2 v_zz v_yy v_xx v_ww v_vv v_uu
  v_tt v_ss v_rr v_qq v_pp v_oo v_nn v_mm v_ll v_kk v_jj v_bbcc v_bbbb
  v_bbaa)) (mem4
  (times1 (times2 (times3 (times4 b_bool b_bool) b_bool) b_bool)
  (add3 empty2 empty3))
  (infix_plmngt1 (times2 (times3 (times4 b_bool b_bool) b_bool) b_bool)
  (power1 natural)))))))
(check-sat)
