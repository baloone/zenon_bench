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

(declare-sort uninterpreted_type 0)

(declare-fun uninterpreted_type1 () ty)

(declare-sort tuple2 2)

(declare-fun tuple21 (ty ty) ty)

(declare-fun infix_eqeq (ty uni uni) Bool)

(declare-fun infix_eqeq1 ((set Bool) (set Bool)) Bool)

(declare-fun infix_eqeq2 ((set Int) (set Int)) Bool)

(declare-fun infix_eqeq3 ((set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))) Bool)

(declare-fun infix_eqeq4 ((set uninterpreted_type)
  (set uninterpreted_type)) Bool)

(declare-fun infix_eqeq5 ((set (set uninterpreted_type))
  (set (set uninterpreted_type))) Bool)

(declare-fun infix_eqeq6 ((set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)))
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))) Bool)

(declare-fun infix_eqeq7 ((set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool)) (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))) Bool)

(declare-fun infix_eqeq8 ((set (tuple2 (tuple2 Bool Bool) Bool))
  (set (tuple2 (tuple2 Bool Bool) Bool))) Bool)

(declare-fun infix_eqeq9 ((set (tuple2 Bool Bool)) (set (tuple2 Bool
  Bool))) Bool)

(declare-fun t2tb ((set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))))) (sort
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))) (t2tb x))))

(declare-fun tb2t (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))))
  (! (= (tb2t (t2tb i)) i) :pattern ((t2tb i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1))) j) (= (t2tb (tb2t j)) j)) :pattern (
  (t2tb (tb2t j))) )))

(declare-fun t2tb1 ((tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))) (sort
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb1 x))))

(declare-fun tb2t1 (uni) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))))
  (! (= (tb2t1 (t2tb1 i)) i) :pattern ((t2tb1 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1)) j) (= (t2tb1 (tb2t1 j)) j)) :pattern (
  (t2tb1 (tb2t1 j))) )))

;; infix ==_def
  (assert
  (forall ((s1 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))) (s2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type)))))
  (= (infix_eqeq6 s1 s2)
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))))
  (= (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb1 x) (t2tb s1)) (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb1 x) (t2tb s2)))))))

(declare-fun t2tb2 ((set (set uninterpreted_type))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set uninterpreted_type)))) (sort
  (set1 (set1 uninterpreted_type1)) (t2tb2 x))))

(declare-fun tb2t2 (uni) (set (set uninterpreted_type)))

;; BridgeL
  (assert
  (forall ((i (set (set uninterpreted_type))))
  (! (= (tb2t2 (t2tb2 i)) i) :pattern ((t2tb2 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (set1 uninterpreted_type1)) j) (= (t2tb2 (tb2t2 j)) j)) :pattern (
  (t2tb2 (tb2t2 j))) )))

(declare-fun t2tb3 ((set uninterpreted_type)) uni)

;; t2tb_sort
  (assert
  (forall ((x (set uninterpreted_type))) (sort (set1 uninterpreted_type1)
  (t2tb3 x))))

(declare-fun tb2t3 (uni) (set uninterpreted_type))

;; BridgeL
  (assert
  (forall ((i (set uninterpreted_type)))
  (! (= (tb2t3 (t2tb3 i)) i) :pattern ((t2tb3 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 uninterpreted_type1) j) (= (t2tb3 (tb2t3 j)) j)) :pattern (
  (t2tb3 (tb2t3 j))) )))

;; infix ==_def
  (assert
  (forall ((s1 (set (set uninterpreted_type)))
  (s2 (set (set uninterpreted_type))))
  (= (infix_eqeq5 s1 s2)
  (forall ((x (set uninterpreted_type)))
  (= (mem (set1 uninterpreted_type1) (t2tb3 x) (t2tb2 s1)) (mem
  (set1 uninterpreted_type1) (t2tb3 x) (t2tb2 s2)))))))

(declare-fun t2tb4 (uninterpreted_type) uni)

;; t2tb_sort
  (assert
  (forall ((x uninterpreted_type)) (sort uninterpreted_type1 (t2tb4 x))))

(declare-fun tb2t4 (uni) uninterpreted_type)

;; BridgeL
  (assert
  (forall ((i uninterpreted_type))
  (! (= (tb2t4 (t2tb4 i)) i) :pattern ((t2tb4 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort uninterpreted_type1 j) (= (t2tb4 (tb2t4 j)) j)) :pattern (
  (t2tb4 (tb2t4 j))) )))

;; infix ==_def
  (assert
  (forall ((s1 (set uninterpreted_type)) (s2 (set uninterpreted_type)))
  (= (infix_eqeq4 s1 s2)
  (forall ((x uninterpreted_type))
  (= (mem uninterpreted_type1 (t2tb4 x) (t2tb3 s1)) (mem uninterpreted_type1
  (t2tb4 x) (t2tb3 s2)))))))

(declare-fun t2tb5 ((set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (sort
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb5 x))))

(declare-fun tb2t5 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (! (= (tb2t5 (t2tb5 i)) i) :pattern ((t2tb5 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb5 (tb2t5 j)) j) :pattern ((t2tb5 (tb2t5 j))) )))

(declare-fun t2tb6 ((tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (sort
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb6 x))))

(declare-fun tb2t6 (uni) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (! (= (tb2t6 (t2tb6 i)) i) :pattern ((t2tb6 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb6 (tb2t6 j)) j) :pattern ((t2tb6 (tb2t6 j))) )))

;; infix ==_def
  (assert
  (forall ((s1 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))))
  (= (infix_eqeq3 s1 s2)
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))
  (= (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb6 x) (t2tb5 s1)) (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb6 x) (t2tb5 s2)))))))

(declare-fun t2tb7 ((set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))) (sort
  (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb7 x))))

(declare-fun tb2t7 (uni) (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (! (= (tb2t7 (t2tb7 i)) i) :pattern ((t2tb7 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) j)
     (= (t2tb7 (tb2t7 j)) j)) :pattern ((t2tb7 (tb2t7 j))) )))

(declare-fun t2tb8 ((tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))) (sort
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 x))))

(declare-fun tb2t8 (uni) (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (! (= (tb2t8 (t2tb8 i)) i) :pattern ((t2tb8 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (tuple21 (tuple21 (tuple21 bool bool) bool) bool) j)
     (= (t2tb8 (tb2t8 j)) j)) :pattern ((t2tb8 (tb2t8 j))) )))

;; infix ==_def
  (assert
  (forall ((s1 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (s2 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (= (infix_eqeq7 s1 s2)
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (= (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 x)
  (t2tb7 s1)) (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb8 x) (t2tb7 s2)))))))

(declare-fun t2tb9 ((set (tuple2 (tuple2 Bool Bool) Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Bool Bool) Bool)))) (sort
  (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb9 x))))

(declare-fun tb2t9 (uni) (set (tuple2 (tuple2 Bool Bool) Bool)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Bool Bool) Bool))))
  (! (= (tb2t9 (t2tb9 i)) i) :pattern ((t2tb9 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (tuple21 (tuple21 bool bool) bool)) j)
     (= (t2tb9 (tb2t9 j)) j)) :pattern ((t2tb9 (tb2t9 j))) )))

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

;; infix ==_def
  (assert
  (forall ((s1 (set (tuple2 (tuple2 Bool Bool) Bool)))
  (s2 (set (tuple2 (tuple2 Bool Bool) Bool))))
  (= (infix_eqeq8 s1 s2)
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)))
  (= (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb9 s1)) (mem
  (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb9 s2)))))))

(declare-fun t2tb11 ((set (tuple2 Bool Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Bool Bool)))) (sort (set1 (tuple21 bool bool))
  (t2tb11 x))))

(declare-fun tb2t11 (uni) (set (tuple2 Bool Bool)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Bool Bool))))
  (! (= (tb2t11 (t2tb11 i)) i) :pattern ((t2tb11 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (tuple21 bool bool)) j) (= (t2tb11 (tb2t11 j)) j)) :pattern (
  (t2tb11 (tb2t11 j))) )))

(declare-fun t2tb12 ((tuple2 Bool Bool)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Bool Bool))) (sort (tuple21 bool bool) (t2tb12 x))))

(declare-fun tb2t12 (uni) (tuple2 Bool Bool))

;; BridgeL
  (assert
  (forall ((i (tuple2 Bool Bool)))
  (! (= (tb2t12 (t2tb12 i)) i) :pattern ((t2tb12 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (tuple21 bool bool) j) (= (t2tb12 (tb2t12 j)) j)) :pattern (
  (t2tb12 (tb2t12 j))) )))

;; infix ==_def
  (assert
  (forall ((s1 (set (tuple2 Bool Bool))) (s2 (set (tuple2 Bool Bool))))
  (= (infix_eqeq9 s1 s2)
  (forall ((x (tuple2 Bool Bool)))
  (= (mem (tuple21 bool bool) (t2tb12 x) (t2tb11 s1)) (mem
  (tuple21 bool bool) (t2tb12 x) (t2tb11 s2)))))))

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

;; infix ==_def
  (assert
  (forall ((s1 (set Bool)) (s2 (set Bool)))
  (= (infix_eqeq1 s1 s2)
  (forall ((x Bool))
  (= (mem bool (t2tb13 x) (t2tb14 s1)) (mem bool (t2tb13 x) (t2tb14 s2)))))))

(declare-fun t2tb15 ((set Int)) uni)

;; t2tb_sort
  (assert (forall ((x (set Int))) (sort (set1 int) (t2tb15 x))))

(declare-fun tb2t15 (uni) (set Int))

;; BridgeL
  (assert
  (forall ((i (set Int)))
  (! (= (tb2t15 (t2tb15 i)) i) :pattern ((t2tb15 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb15 (tb2t15 j)) j) :pattern ((t2tb15 (tb2t15 j))) )))

(declare-fun t2tb16 (Int) uni)

;; t2tb_sort
  (assert (forall ((x Int)) (sort int (t2tb16 x))))

(declare-fun tb2t16 (uni) Int)

;; BridgeL
  (assert
  (forall ((i Int)) (! (= (tb2t16 (t2tb16 i)) i) :pattern ((t2tb16 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb16 (tb2t16 j)) j) :pattern ((t2tb16 (tb2t16 j))) )))

;; infix ==_def
  (assert
  (forall ((s1 (set Int)) (s2 (set Int)))
  (= (infix_eqeq2 s1 s2)
  (forall ((x Int))
  (= (mem int (t2tb16 x) (t2tb15 s1)) (mem int (t2tb16 x) (t2tb15 s2)))))))

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
  (forall ((s1 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))) (s2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type)))))
  (=> (infix_eqeq6 s1 s2) (= s1 s2))))

;; extensionality
  (assert
  (forall ((s1 (set (set uninterpreted_type)))
  (s2 (set (set uninterpreted_type)))) (=> (infix_eqeq5 s1 s2) (= s1 s2))))

;; extensionality
  (assert
  (forall ((s1 (set uninterpreted_type)) (s2 (set uninterpreted_type)))
  (=> (infix_eqeq4 s1 s2) (= s1 s2))))

;; extensionality
  (assert
  (forall ((s1 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (=> (infix_eqeq3 s1 s2) (= s1 s2))))

;; extensionality
  (assert
  (forall ((s1 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (s2 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (=> (infix_eqeq7 s1 s2) (= s1 s2))))

;; extensionality
  (assert
  (forall ((s1 (set (tuple2 (tuple2 Bool Bool) Bool)))
  (s2 (set (tuple2 (tuple2 Bool Bool) Bool))))
  (=> (infix_eqeq8 s1 s2) (= s1 s2))))

;; extensionality
  (assert
  (forall ((s1 (set (tuple2 Bool Bool))) (s2 (set (tuple2 Bool Bool))))
  (=> (infix_eqeq9 s1 s2) (= s1 s2))))

;; extensionality
  (assert
  (forall ((s1 (set Bool)) (s2 (set Bool)))
  (=> (infix_eqeq1 s1 s2) (= s1 s2))))

;; extensionality
  (assert
  (forall ((s1 (set Int)) (s2 (set Int))) (=> (infix_eqeq2 s1 s2) (= s1 s2))))

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

(declare-fun empty1 () (set Bool))

(declare-fun empty2 () (set Int))

(declare-fun empty3 () (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))

(declare-fun empty4 () (set uninterpreted_type))

(declare-fun empty5 () (set (set uninterpreted_type)))

(declare-fun empty6 () (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type))))

(declare-fun empty7 () (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))

(declare-fun empty8 () (set (tuple2 (tuple2 Bool Bool) Bool)))

(declare-fun empty9 () (set (tuple2 Bool Bool)))

(declare-fun is_empty (ty uni) Bool)

;; is_empty_def
  (assert
  (forall ((a ty))
  (forall ((s uni))
  (and (=> (is_empty a s) (forall ((x uni)) (not (mem a x s))))
  (=> (forall ((x uni)) (=> (sort a x) (not (mem a x s)))) (is_empty a s))))))

;; empty_def1
  (assert (is_empty
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb empty6)))

;; empty_def1
  (assert (is_empty (set1 uninterpreted_type1) (t2tb2 empty5)))

;; empty_def1
  (assert (is_empty uninterpreted_type1 (t2tb3 empty4)))

;; empty_def1
  (assert (is_empty
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb5 empty3)))

;; empty_def1
  (assert (is_empty (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb7 empty7)))

;; empty_def1
  (assert (is_empty (tuple21 (tuple21 bool bool) bool) (t2tb9 empty8)))

;; empty_def1
  (assert (is_empty (tuple21 bool bool) (t2tb11 empty9)))

;; empty_def1
  (assert (is_empty bool (t2tb14 empty1)))

;; empty_def1
  (assert (is_empty int (t2tb15 empty2)))

;; empty_def1
  (assert (forall ((a ty)) (is_empty a (empty a))))

;; mem_empty
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))))
  (not (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb1 x) (t2tb empty6)))))

;; mem_empty
  (assert
  (forall ((x (set uninterpreted_type)))
  (not (mem (set1 uninterpreted_type1) (t2tb3 x) (t2tb2 empty5)))))

;; mem_empty
  (assert
  (forall ((x uninterpreted_type))
  (not (mem uninterpreted_type1 (t2tb4 x) (t2tb3 empty4)))))

;; mem_empty
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))
  (not (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb6 x) (t2tb5 empty3)))))

;; mem_empty
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (not (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 x)
  (t2tb7 empty7)))))

;; mem_empty
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)))
  (not (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb9 empty8)))))

;; mem_empty
  (assert
  (forall ((x (tuple2 Bool Bool)))
  (not (mem (tuple21 bool bool) (t2tb12 x) (t2tb11 empty9)))))

;; mem_empty
  (assert (forall ((x Bool)) (not (mem bool (t2tb13 x) (t2tb14 empty1)))))

;; mem_empty
  (assert (forall ((x Int)) (not (mem int (t2tb16 x) (t2tb15 empty2)))))

;; mem_empty
  (assert (forall ((a ty)) (forall ((x uni)) (not (mem a x (empty a))))))

(declare-fun add (ty uni uni) uni)

;; add_sort
  (assert
  (forall ((a ty)) (forall ((x uni) (x1 uni)) (sort (set1 a) (add a x x1)))))

(declare-fun add1 (Bool (set Bool)) (set Bool))

(declare-fun add2 (Int (set Int)) (set Int))

(declare-fun add3 ((set uninterpreted_type)
  (set (set uninterpreted_type))) (set (set uninterpreted_type)))

(declare-fun add4 ((tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))) (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))

(declare-fun add5 ((tuple2 (tuple2 Bool Bool) Bool) (set (tuple2 (tuple2 Bool
  Bool) Bool))) (set (tuple2 (tuple2 Bool Bool) Bool)))

(declare-fun add6 ((tuple2 Bool Bool) (set (tuple2 Bool
  Bool))) (set (tuple2 Bool Bool)))

;; add_def1
  (assert
  (forall ((x (set uninterpreted_type)) (y (set uninterpreted_type)))
  (forall ((s (set (set uninterpreted_type))))
  (= (mem (set1 uninterpreted_type1) (t2tb3 x) (t2tb2 (add3 y s)))
  (or (= x y) (mem (set1 uninterpreted_type1) (t2tb3 x) (t2tb2 s)))))))

;; add_def1
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (y (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (forall ((s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (= (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 x)
  (t2tb7 (add4 y s)))
  (or (= x y) (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb8 x) (t2tb7 s)))))))

;; add_def1
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)) (y (tuple2 (tuple2 Bool Bool)
  Bool)))
  (forall ((s (set (tuple2 (tuple2 Bool Bool) Bool))))
  (= (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb9 (add5 y s)))
  (or (= x y) (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb9 s)))))))

;; add_def1
  (assert
  (forall ((x (tuple2 Bool Bool)) (y (tuple2 Bool Bool)))
  (forall ((s (set (tuple2 Bool Bool))))
  (= (mem (tuple21 bool bool) (t2tb12 x) (t2tb11 (add6 y s)))
  (or (= x y) (mem (tuple21 bool bool) (t2tb12 x) (t2tb11 s)))))))

;; add_def1
  (assert
  (forall ((x Bool) (y Bool))
  (forall ((s (set Bool)))
  (= (mem bool (t2tb13 x) (t2tb14 (add1 y s)))
  (or (= x y) (mem bool (t2tb13 x) (t2tb14 s)))))))

;; add_def1
  (assert
  (forall ((x Int) (y Int))
  (forall ((s (set Int)))
  (= (mem int (t2tb16 x) (t2tb15 (add2 y s)))
  (or (= x y) (mem int (t2tb16 x) (t2tb15 s)))))))

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
  (forall ((x (set uninterpreted_type)) (s (set (set uninterpreted_type))))
  (=> (mem (set1 uninterpreted_type1) (t2tb3 x) (t2tb2 s))
  (= (add3 x (tb2t2 (remove (set1 uninterpreted_type1) (t2tb3 x) (t2tb2 s)))) s))))

;; add_remove
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (=> (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 x)
  (t2tb7 s))
  (= (add4 x
     (tb2t7
     (remove (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 x)
     (t2tb7 s)))) s))))

;; add_remove
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)) (s (set (tuple2 (tuple2 Bool
  Bool) Bool))))
  (=> (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb9 s))
  (= (add5 x
     (tb2t9 (remove (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb9 s)))) s))))

;; add_remove
  (assert
  (forall ((x (tuple2 Bool Bool)) (s (set (tuple2 Bool Bool))))
  (=> (mem (tuple21 bool bool) (t2tb12 x) (t2tb11 s))
  (= (add6 x (tb2t11 (remove (tuple21 bool bool) (t2tb12 x) (t2tb11 s)))) s))))

;; add_remove
  (assert
  (forall ((x Bool) (s (set Bool)))
  (=> (mem bool (t2tb13 x) (t2tb14 s))
  (= (add1 x (tb2t14 (remove bool (t2tb13 x) (t2tb14 s)))) s))))

;; add_remove
  (assert
  (forall ((x Int) (s (set Int)))
  (=> (mem int (t2tb16 x) (t2tb15 s))
  (= (add2 x (tb2t15 (remove int (t2tb16 x) (t2tb15 s)))) s))))

;; add_remove
  (assert
  (forall ((a ty))
  (forall ((x uni) (s uni))
  (=> (sort (set1 a) s) (=> (mem a x s) (= (add a x (remove a x s)) s))))))

;; remove_add
  (assert
  (forall ((x (set uninterpreted_type)) (s (set (set uninterpreted_type))))
  (= (tb2t2 (remove (set1 uninterpreted_type1) (t2tb3 x) (t2tb2 (add3 x s)))) 
  (tb2t2 (remove (set1 uninterpreted_type1) (t2tb3 x) (t2tb2 s))))))

;; remove_add
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (= (tb2t7
     (remove (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 x)
     (t2tb7 (add4 x s)))) (tb2t7
                          (remove
                          (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
                          (t2tb8 x) (t2tb7 s))))))

;; remove_add
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)) (s (set (tuple2 (tuple2 Bool
  Bool) Bool))))
  (= (tb2t9
     (remove (tuple21 (tuple21 bool bool) bool) (t2tb10 x)
     (t2tb9 (add5 x s)))) (tb2t9
                          (remove (tuple21 (tuple21 bool bool) bool)
                          (t2tb10 x) (t2tb9 s))))))

;; remove_add
  (assert
  (forall ((x (tuple2 Bool Bool)) (s (set (tuple2 Bool Bool))))
  (= (tb2t11 (remove (tuple21 bool bool) (t2tb12 x) (t2tb11 (add6 x s)))) 
  (tb2t11 (remove (tuple21 bool bool) (t2tb12 x) (t2tb11 s))))))

;; remove_add
  (assert
  (forall ((x Bool) (s (set Bool)))
  (= (tb2t14 (remove bool (t2tb13 x) (t2tb14 (add1 x s)))) (tb2t14
                                                           (remove bool
                                                           (t2tb13 x)
                                                           (t2tb14 s))))))

;; remove_add
  (assert
  (forall ((x Int) (s (set Int)))
  (= (tb2t15 (remove int (t2tb16 x) (t2tb15 (add2 x s)))) (tb2t15
                                                          (remove int
                                                          (t2tb16 x)
                                                          (t2tb15 s))))))

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
  (assert (forall ((x Bool)) (mem bool (t2tb13 x) (t2tb14 b_bool))))

(declare-fun integer () (set Int))

;; mem_integer
  (assert (forall ((x Int)) (mem int (t2tb16 x) (t2tb15 integer))))

(declare-fun natural () (set Int))

;; mem_natural
  (assert
  (forall ((x Int)) (= (mem int (t2tb16 x) (t2tb15 natural)) (<= 0 x))))

(declare-fun natural1 () (set Int))

;; mem_natural1
  (assert
  (forall ((x Int)) (= (mem int (t2tb16 x) (t2tb15 natural1)) (< 0 x))))

(declare-fun nat () (set Int))

;; mem_nat
  (assert
  (forall ((x Int))
  (= (mem int (t2tb16 x) (t2tb15 nat)) (and (<= 0 x) (<= x 2147483647)))))

(declare-fun nat1 () (set Int))

;; mem_nat1
  (assert
  (forall ((x Int))
  (= (mem int (t2tb16 x) (t2tb15 nat1)) (and (< 0 x) (<= x 2147483647)))))

(declare-fun bounded_int () (set Int))

;; mem_bounded_int
  (assert
  (forall ((x Int))
  (= (mem int (t2tb16 x) (t2tb15 bounded_int))
  (and (<= (- 2147483647) x) (<= x 2147483647)))))

(declare-fun mk (Int Int) (set Int))

;; mem_interval
  (assert
  (forall ((x Int) (a Int) (b Int))
  (! (= (mem int (t2tb16 x) (t2tb15 (mk a b))) (and (<= a x) (<= x b))) :pattern ((mem
  int (t2tb16 x) (t2tb15 (mk a b)))) )))

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

(declare-fun t2tb17 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type)))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)))) (t2tb17 x))))

(declare-fun tb2t17 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type))))))
  (! (= (tb2t17 (t2tb17 i)) i) :pattern ((t2tb17 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1)))) j) (= (t2tb17 (tb2t17 j)) j)) :pattern (
  (t2tb17 (tb2t17 j))) )))

;; mem_non_empty_power
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))) (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type)))))
  (! (= (mem
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1))) (t2tb x)
     (non_empty_power
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1)) (t2tb y)))
     (and (subset
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1)) (t2tb x) (t2tb y)) (not (= x empty6)))) :pattern ((mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))) (t2tb x)
  (non_empty_power
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb y)))) )))

(declare-fun t2tb18 ((set (set (set uninterpreted_type)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (set uninterpreted_type))))) (sort
  (set1 (set1 (set1 uninterpreted_type1))) (t2tb18 x))))

(declare-fun tb2t18 (uni) (set (set (set uninterpreted_type))))

;; BridgeL
  (assert
  (forall ((i (set (set (set uninterpreted_type)))))
  (! (= (tb2t18 (t2tb18 i)) i) :pattern ((t2tb18 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (set1 (set1 uninterpreted_type1))) j)
     (= (t2tb18 (tb2t18 j)) j)) :pattern ((t2tb18 (tb2t18 j))) )))

;; mem_non_empty_power
  (assert
  (forall ((x (set (set uninterpreted_type)))
  (y (set (set uninterpreted_type))))
  (! (= (mem (set1 (set1 uninterpreted_type1)) (t2tb2 x)
     (non_empty_power (set1 uninterpreted_type1) (t2tb2 y)))
     (and (subset (set1 uninterpreted_type1) (t2tb2 x) (t2tb2 y))
     (not (= x empty5)))) :pattern ((mem
  (set1 (set1 uninterpreted_type1)) (t2tb2 x)
  (non_empty_power (set1 uninterpreted_type1) (t2tb2 y)))) )))

;; mem_non_empty_power
  (assert
  (forall ((x (set uninterpreted_type)) (y (set uninterpreted_type)))
  (! (= (mem (set1 uninterpreted_type1) (t2tb3 x)
     (non_empty_power uninterpreted_type1 (t2tb3 y)))
     (and (subset uninterpreted_type1 (t2tb3 x) (t2tb3 y))
     (not (= x empty4)))) :pattern ((mem
  (set1 uninterpreted_type1) (t2tb3 x)
  (non_empty_power uninterpreted_type1 (t2tb3 y)))) )))

(declare-fun t2tb19 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (t2tb19 x))))

(declare-fun tb2t19 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))))) (! (= (tb2t19 (t2tb19 i)) i) :pattern ((t2tb19 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb19 (tb2t19 j)) j) :pattern ((t2tb19 (tb2t19 j))) )))

;; mem_non_empty_power
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))
  (! (= (mem
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb5 x)
     (non_empty_power
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
     (t2tb5 y)))
     (and (subset
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
     (t2tb5 x) (t2tb5 y)) (not (= x empty3)))) :pattern ((mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb5 x)
  (non_empty_power
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb5 y)))) )))

(declare-fun t2tb20 ((set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))))
  (sort (set1 (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))
  (t2tb20 x))))

(declare-fun tb2t20 (uni) (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))))
  (! (= (tb2t20 (t2tb20 i)) i) :pattern ((t2tb20 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1 (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool))) j)
     (= (t2tb20 (tb2t20 j)) j)) :pattern ((t2tb20 (tb2t20 j))) )))

;; mem_non_empty_power
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (y (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (! (= (mem (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
     (t2tb7 x)
     (non_empty_power (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (t2tb7 y)))
     (and (subset (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb7 x)
     (t2tb7 y)) (not (= x empty7)))) :pattern ((mem
  (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb7 x)
  (non_empty_power (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb7 y)))) )))

(declare-fun t2tb21 ((set (set (tuple2 (tuple2 Bool Bool) Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 Bool Bool) Bool))))) (sort
  (set1 (set1 (tuple21 (tuple21 bool bool) bool))) (t2tb21 x))))

(declare-fun tb2t21 (uni) (set (set (tuple2 (tuple2 Bool Bool) Bool))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 Bool Bool) Bool)))))
  (! (= (tb2t21 (t2tb21 i)) i) :pattern ((t2tb21 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (set1 (tuple21 (tuple21 bool bool) bool))) j)
     (= (t2tb21 (tb2t21 j)) j)) :pattern ((t2tb21 (tb2t21 j))) )))

;; mem_non_empty_power
  (assert
  (forall ((x (set (tuple2 (tuple2 Bool Bool) Bool)))
  (y (set (tuple2 (tuple2 Bool Bool) Bool))))
  (! (= (mem (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb9 x)
     (non_empty_power (tuple21 (tuple21 bool bool) bool) (t2tb9 y)))
     (and (subset (tuple21 (tuple21 bool bool) bool) (t2tb9 x) (t2tb9 y))
     (not (= x empty8)))) :pattern ((mem
  (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb9 x)
  (non_empty_power (tuple21 (tuple21 bool bool) bool) (t2tb9 y)))) )))

(declare-fun t2tb22 ((set (set (tuple2 Bool Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Bool Bool))))) (sort
  (set1 (set1 (tuple21 bool bool))) (t2tb22 x))))

(declare-fun tb2t22 (uni) (set (set (tuple2 Bool Bool))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Bool Bool)))))
  (! (= (tb2t22 (t2tb22 i)) i) :pattern ((t2tb22 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (set1 (tuple21 bool bool))) j)
     (= (t2tb22 (tb2t22 j)) j)) :pattern ((t2tb22 (tb2t22 j))) )))

;; mem_non_empty_power
  (assert
  (forall ((x (set (tuple2 Bool Bool))) (y (set (tuple2 Bool Bool))))
  (! (= (mem (set1 (tuple21 bool bool)) (t2tb11 x)
     (non_empty_power (tuple21 bool bool) (t2tb11 y)))
     (and (subset (tuple21 bool bool) (t2tb11 x) (t2tb11 y))
     (not (= x empty9)))) :pattern ((mem
  (set1 (tuple21 bool bool)) (t2tb11 x)
  (non_empty_power (tuple21 bool bool) (t2tb11 y)))) )))

(declare-fun t2tb23 ((set (set Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set Bool)))) (sort (set1 (set1 bool)) (t2tb23 x))))

(declare-fun tb2t23 (uni) (set (set Bool)))

;; BridgeL
  (assert
  (forall ((i (set (set Bool))))
  (! (= (tb2t23 (t2tb23 i)) i) :pattern ((t2tb23 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (set1 bool)) j) (= (t2tb23 (tb2t23 j)) j)) :pattern (
  (t2tb23 (tb2t23 j))) )))

;; mem_non_empty_power
  (assert
  (forall ((x (set Bool)) (y (set Bool)))
  (! (= (mem (set1 bool) (t2tb14 x) (non_empty_power bool (t2tb14 y)))
     (and (subset bool (t2tb14 x) (t2tb14 y)) (not (= x empty1)))) :pattern ((mem
  (set1 bool) (t2tb14 x) (non_empty_power bool (t2tb14 y)))) )))

(declare-fun t2tb24 ((set (set Int))) uni)

;; t2tb_sort
  (assert (forall ((x (set (set Int)))) (sort (set1 (set1 int)) (t2tb24 x))))

(declare-fun tb2t24 (uni) (set (set Int)))

;; BridgeL
  (assert
  (forall ((i (set (set Int))))
  (! (= (tb2t24 (t2tb24 i)) i) :pattern ((t2tb24 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb24 (tb2t24 j)) j) :pattern ((t2tb24 (tb2t24 j))) )))

;; mem_non_empty_power
  (assert
  (forall ((x (set Int)) (y (set Int)))
  (! (= (mem (set1 int) (t2tb15 x) (non_empty_power int (t2tb15 y)))
     (and (subset int (t2tb15 x) (t2tb15 y)) (not (= x empty2)))) :pattern ((mem
  (set1 int) (t2tb15 x) (non_empty_power int (t2tb15 y)))) )))

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

(declare-fun Tuple21 (Bool Bool) (tuple2 Bool Bool))

(declare-fun Tuple22 ((tuple2 Bool Bool) Bool) (tuple2 (tuple2 Bool Bool)
  Bool))

(declare-fun Tuple23 ((tuple2 (tuple2 Bool Bool) Bool)
  Bool) (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))

(declare-fun Tuple2_proj_1 (ty ty uni) uni)

;; Tuple2_proj_1_sort
  (assert
  (forall ((a ty) (a1 ty))
  (forall ((x uni)) (sort a1 (Tuple2_proj_1 a1 a x)))))

;; Tuple2_proj_1_def
  (assert
  (forall ((u (tuple2 (tuple2 Bool Bool) Bool)) (u1 Bool))
  (= (tb2t10
     (Tuple2_proj_1 (tuple21 (tuple21 bool bool) bool) bool
     (t2tb8 (Tuple23 u u1)))) u)))

;; Tuple2_proj_1_def
  (assert
  (forall ((u (tuple2 Bool Bool)) (u1 Bool))
  (= (tb2t12
     (Tuple2_proj_1 (tuple21 bool bool) bool (t2tb10 (Tuple22 u u1)))) u)))

;; Tuple2_proj_1_def
  (assert
  (forall ((u Bool) (u1 Bool))
  (= (tb2t13 (Tuple2_proj_1 bool bool (t2tb12 (Tuple21 u u1)))) u)))

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
  (forall ((u (tuple2 (tuple2 Bool Bool) Bool)) (u1 Bool))
  (= (tb2t13
     (Tuple2_proj_2 (tuple21 (tuple21 bool bool) bool) bool
     (t2tb8 (Tuple23 u u1)))) u1)))

;; Tuple2_proj_2_def
  (assert
  (forall ((u (tuple2 Bool Bool)) (u1 Bool))
  (= (tb2t13
     (Tuple2_proj_2 (tuple21 bool bool) bool (t2tb10 (Tuple22 u u1)))) u1)))

;; Tuple2_proj_2_def
  (assert
  (forall ((u Bool) (u1 Bool))
  (= (tb2t13 (Tuple2_proj_2 bool bool (t2tb12 (Tuple21 u u1)))) u1)))

;; Tuple2_proj_2_def
  (assert
  (forall ((a ty) (a1 ty))
  (forall ((u uni) (u1 uni))
  (=> (sort a u1) (= (Tuple2_proj_2 a1 a (Tuple2 a1 a u u1)) u1)))))

;; tuple2_inversion
  (assert
  (forall ((u (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (= u (Tuple23
       (tb2t10
       (Tuple2_proj_1 (tuple21 (tuple21 bool bool) bool) bool (t2tb8 u)))
       (tb2t13
       (Tuple2_proj_2 (tuple21 (tuple21 bool bool) bool) bool (t2tb8 u)))))))

;; tuple2_inversion
  (assert
  (forall ((u (tuple2 (tuple2 Bool Bool) Bool)))
  (= u (Tuple22 (tb2t12 (Tuple2_proj_1 (tuple21 bool bool) bool (t2tb10 u)))
       (tb2t13 (Tuple2_proj_2 (tuple21 bool bool) bool (t2tb10 u)))))))

;; tuple2_inversion
  (assert
  (forall ((u (tuple2 Bool Bool)))
  (= u (Tuple21 (tb2t13 (Tuple2_proj_1 bool bool (t2tb12 u)))
       (tb2t13 (Tuple2_proj_2 bool bool (t2tb12 u)))))))

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
  (forall ((f (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (s (set (tuple2 (tuple2 Bool Bool) Bool))) (t (set Bool)))
  (= (mem (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb7 f)
  (relation bool (tuple21 (tuple21 bool bool) bool) (t2tb9 s) (t2tb14 t)))
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)) (y Bool))
  (=> (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb8 (Tuple23 x y)) (t2tb7 f))
  (and (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb9 s)) (mem
  bool (t2tb13 y) (t2tb14 t))))))))

;; mem_relation
  (assert
  (forall ((f (set (tuple2 (tuple2 Bool Bool) Bool))) (s (set (tuple2 Bool
  Bool))) (t (set Bool)))
  (= (mem (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb9 f)
  (relation bool (tuple21 bool bool) (t2tb11 s) (t2tb14 t)))
  (forall ((x (tuple2 Bool Bool)) (y Bool))
  (=> (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 x y))
  (t2tb9 f))
  (and (mem (tuple21 bool bool) (t2tb12 x) (t2tb11 s)) (mem bool (t2tb13 y)
  (t2tb14 t))))))))

;; mem_relation
  (assert
  (forall ((f (set (tuple2 Bool Bool))) (s (set Bool)) (t (set Bool)))
  (= (mem (set1 (tuple21 bool bool)) (t2tb11 f)
  (relation bool bool (t2tb14 s) (t2tb14 t)))
  (forall ((x Bool) (y Bool))
  (=> (mem (tuple21 bool bool) (t2tb12 (Tuple21 x y)) (t2tb11 f))
  (and (mem bool (t2tb13 x) (t2tb14 s)) (mem bool (t2tb13 y) (t2tb14 t))))))))

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
  (forall ((r (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (dom (set (tuple2 (tuple2 Bool Bool) Bool))) (y Bool))
  (! (= (mem bool (t2tb13 y)
     (image bool (tuple21 (tuple21 bool bool) bool) (t2tb7 r) (t2tb9 dom)))
     (exists ((x (tuple2 (tuple2 Bool Bool) Bool)))
     (and (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb9 dom))
     (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (t2tb8 (Tuple23 x y)) (t2tb7 r))))) :pattern ((mem
  bool (t2tb13 y)
  (image bool (tuple21 (tuple21 bool bool) bool) (t2tb7 r) (t2tb9 dom)))) )))

;; mem_image
  (assert
  (forall ((r (set (tuple2 (tuple2 Bool Bool) Bool))) (dom (set (tuple2 Bool
  Bool))) (y Bool))
  (! (= (mem bool (t2tb13 y)
     (image bool (tuple21 bool bool) (t2tb9 r) (t2tb11 dom)))
     (exists ((x (tuple2 Bool Bool)))
     (and (mem (tuple21 bool bool) (t2tb12 x) (t2tb11 dom)) (mem
     (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 x y)) (t2tb9 r))))) :pattern ((mem
  bool (t2tb13 y)
  (image bool (tuple21 bool bool) (t2tb9 r) (t2tb11 dom)))) )))

;; mem_image
  (assert
  (forall ((r (set (tuple2 Bool Bool))) (dom (set Bool)) (y Bool))
  (! (= (mem bool (t2tb13 y) (image bool bool (t2tb11 r) (t2tb14 dom)))
     (exists ((x Bool))
     (and (mem bool (t2tb13 x) (t2tb14 dom)) (mem (tuple21 bool bool)
     (t2tb12 (Tuple21 x y)) (t2tb11 r))))) :pattern ((mem
  bool (t2tb13 y) (image bool bool (t2tb11 r) (t2tb14 dom)))) )))

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
  (forall ((r uni) (dom (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type)))) (x (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type))))
  (= (image b
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1)) r
     (add
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1)) (t2tb1 x) (t2tb dom))) (union b
                                                        (image b
                                                        (tuple21
                                                        (tuple21
                                                        (tuple21
                                                        (tuple21 bool bool)
                                                        bool) bool)
                                                        (set1
                                                        uninterpreted_type1))
                                                        r
                                                        (add
                                                        (tuple21
                                                        (tuple21
                                                        (tuple21
                                                        (tuple21 bool bool)
                                                        bool) bool)
                                                        (set1
                                                        uninterpreted_type1))
                                                        (t2tb1 x)
                                                        (t2tb empty6)))
                                                        (image b
                                                        (tuple21
                                                        (tuple21
                                                        (tuple21
                                                        (tuple21 bool bool)
                                                        bool) bool)
                                                        (set1
                                                        uninterpreted_type1))
                                                        r (t2tb dom)))))))

;; image_add
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom (set (set uninterpreted_type)))
  (x (set uninterpreted_type)))
  (= (image b (set1 uninterpreted_type1) r (t2tb2 (add3 x dom))) (union b
                                                                 (image b
                                                                 (set1
                                                                 uninterpreted_type1)
                                                                 r
                                                                 (t2tb2
                                                                 (add3 x
                                                                 empty5)))
                                                                 (image b
                                                                 (set1
                                                                 uninterpreted_type1)
                                                                 r
                                                                 (t2tb2 dom)))))))

;; image_add
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom (set uninterpreted_type)) (x uninterpreted_type))
  (= (image b uninterpreted_type1 r
     (add uninterpreted_type1 (t2tb4 x) (t2tb3 dom))) (union b
                                                      (image b
                                                      uninterpreted_type1 r
                                                      (add
                                                      uninterpreted_type1
                                                      (t2tb4 x)
                                                      (t2tb3 empty4)))
                                                      (image b
                                                      uninterpreted_type1 r
                                                      (t2tb3 dom)))))))

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
     (t2tb6 x) (t2tb5 dom))) (union b
                             (image b
                             (tuple21
                             (tuple21 (tuple21 (tuple21 bool bool) bool)
                             bool) (set1 int)) r
                             (add
                             (tuple21
                             (tuple21 (tuple21 (tuple21 bool bool) bool)
                             bool) (set1 int)) (t2tb6 x) (t2tb5 empty3)))
                             (image b
                             (tuple21
                             (tuple21 (tuple21 (tuple21 bool bool) bool)
                             bool) (set1 int)) r (t2tb5 dom)))))))

;; image_add
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (= (image b (tuple21 (tuple21 (tuple21 bool bool) bool) bool) r
     (t2tb7 (add4 x dom))) (union b
                           (image b
                           (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
                           r (t2tb7 (add4 x empty7)))
                           (image b
                           (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
                           r (t2tb7 dom)))))))

;; image_add
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom (set (tuple2 (tuple2 Bool Bool) Bool)))
  (x (tuple2 (tuple2 Bool Bool) Bool)))
  (= (image b (tuple21 (tuple21 bool bool) bool) r (t2tb9 (add5 x dom))) 
  (union b
  (image b (tuple21 (tuple21 bool bool) bool) r (t2tb9 (add5 x empty8)))
  (image b (tuple21 (tuple21 bool bool) bool) r (t2tb9 dom)))))))

;; image_add
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom (set (tuple2 Bool Bool))) (x (tuple2 Bool Bool)))
  (= (image b (tuple21 bool bool) r (t2tb11 (add6 x dom))) (union b
                                                           (image b
                                                           (tuple21 bool
                                                           bool) r
                                                           (t2tb11
                                                           (add6 x empty9)))
                                                           (image b
                                                           (tuple21 bool
                                                           bool) r
                                                           (t2tb11 dom)))))))

;; image_add
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom (set Bool)) (x Bool))
  (= (image b bool r (t2tb14 (add1 x dom))) (union b
                                            (image b bool r
                                            (t2tb14 (add1 x empty1)))
                                            (image b bool r (t2tb14 dom)))))))

;; image_add
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom (set Int)) (x Int))
  (= (image b int r (t2tb15 (add2 x dom))) (union b
                                           (image b int r
                                           (t2tb15 (add2 x empty2)))
                                           (image b int r (t2tb15 dom)))))))

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
  (forall ((f (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (s (set (tuple2 (tuple2 Bool Bool) Bool))) (t (set Bool)))
  (= (mem (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb7 f)
  (infix_plmngt bool (tuple21 (tuple21 bool bool) bool) (t2tb9 s) (t2tb14 t)))
  (and
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)) (y Bool))
  (=> (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb8 (Tuple23 x y)) (t2tb7 f))
  (and (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb9 s)) (mem
  bool (t2tb13 y) (t2tb14 t)))))
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)) (y1 Bool) (y2 Bool))
  (=>
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb8 (Tuple23 x y1)) (t2tb7 f)) (mem
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 (Tuple23 x y2))
  (t2tb7 f))) (= y1 y2)))))))

;; mem_function
  (assert
  (forall ((f (set (tuple2 (tuple2 Bool Bool) Bool))) (s (set (tuple2 Bool
  Bool))) (t (set Bool)))
  (= (mem (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb9 f)
  (infix_plmngt bool (tuple21 bool bool) (t2tb11 s) (t2tb14 t)))
  (and
  (forall ((x (tuple2 Bool Bool)) (y Bool))
  (=> (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 x y))
  (t2tb9 f))
  (and (mem (tuple21 bool bool) (t2tb12 x) (t2tb11 s)) (mem bool (t2tb13 y)
  (t2tb14 t)))))
  (forall ((x (tuple2 Bool Bool)) (y1 Bool) (y2 Bool))
  (=>
  (and (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 x y1))
  (t2tb9 f)) (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 x y2))
  (t2tb9 f))) (= y1 y2)))))))

;; mem_function
  (assert
  (forall ((f (set (tuple2 Bool Bool))) (s (set Bool)) (t (set Bool)))
  (= (mem (set1 (tuple21 bool bool)) (t2tb11 f)
  (infix_plmngt bool bool (t2tb14 s) (t2tb14 t)))
  (and
  (forall ((x Bool) (y Bool))
  (=> (mem (tuple21 bool bool) (t2tb12 (Tuple21 x y)) (t2tb11 f))
  (and (mem bool (t2tb13 x) (t2tb14 s)) (mem bool (t2tb13 y) (t2tb14 t)))))
  (forall ((x Bool) (y1 Bool) (y2 Bool))
  (=>
  (and (mem (tuple21 bool bool) (t2tb12 (Tuple21 x y1)) (t2tb11 f)) (mem
  (tuple21 bool bool) (t2tb12 (Tuple21 x y2)) (t2tb11 f))) (= y1 y2)))))))

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
  (forall ((f (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (s (set (tuple2 (tuple2 Bool Bool) Bool))) (t (set Bool))
  (x (tuple2 (tuple2 Bool Bool) Bool)) (y Bool))
  (=> (mem (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb7 f)
  (infix_plmngt bool (tuple21 (tuple21 bool bool) bool) (t2tb9 s) (t2tb14 t)))
  (=> (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb8 (Tuple23 x y)) (t2tb7 f)) (mem (tuple21 (tuple21 bool bool) bool)
  (t2tb10 x) (t2tb9 s))))))

;; domain_function
  (assert
  (forall ((f (set (tuple2 (tuple2 Bool Bool) Bool))) (s (set (tuple2 Bool
  Bool))) (t (set Bool)) (x (tuple2 Bool Bool)) (y Bool))
  (=> (mem (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb9 f)
  (infix_plmngt bool (tuple21 bool bool) (t2tb11 s) (t2tb14 t)))
  (=> (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 x y))
  (t2tb9 f)) (mem (tuple21 bool bool) (t2tb12 x) (t2tb11 s))))))

;; domain_function
  (assert
  (forall ((f (set (tuple2 Bool Bool))) (s (set Bool)) (t (set Bool))
  (x Bool) (y Bool))
  (=> (mem (set1 (tuple21 bool bool)) (t2tb11 f)
  (infix_plmngt bool bool (t2tb14 s) (t2tb14 t)))
  (=> (mem (tuple21 bool bool) (t2tb12 (Tuple21 x y)) (t2tb11 f)) (mem 
  bool (t2tb13 x) (t2tb14 s))))))

;; domain_function
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni) (x uni) (y uni))
  (=> (mem (set1 (tuple21 a b)) f (infix_plmngt b a s t))
  (=> (mem (tuple21 a b) (Tuple2 a b x y) f) (mem a x s))))))

;; range_function
  (assert
  (forall ((f (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (s (set (tuple2 (tuple2 Bool Bool) Bool))) (t (set Bool))
  (x (tuple2 (tuple2 Bool Bool) Bool)) (y Bool))
  (=> (mem (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb7 f)
  (infix_plmngt bool (tuple21 (tuple21 bool bool) bool) (t2tb9 s) (t2tb14 t)))
  (=> (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb8 (Tuple23 x y)) (t2tb7 f)) (mem bool (t2tb13 y) (t2tb14 t))))))

;; range_function
  (assert
  (forall ((f (set (tuple2 (tuple2 Bool Bool) Bool))) (s (set (tuple2 Bool
  Bool))) (t (set Bool)) (x (tuple2 Bool Bool)) (y Bool))
  (=> (mem (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb9 f)
  (infix_plmngt bool (tuple21 bool bool) (t2tb11 s) (t2tb14 t)))
  (=> (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 x y))
  (t2tb9 f)) (mem bool (t2tb13 y) (t2tb14 t))))))

;; range_function
  (assert
  (forall ((f (set (tuple2 Bool Bool))) (s (set Bool)) (t (set Bool))
  (x Bool) (y Bool))
  (=> (mem (set1 (tuple21 bool bool)) (t2tb11 f)
  (infix_plmngt bool bool (t2tb14 s) (t2tb14 t)))
  (=> (mem (tuple21 bool bool) (t2tb12 (Tuple21 x y)) (t2tb11 f)) (mem 
  bool (t2tb13 y) (t2tb14 t))))))

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
  (forall ((f (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (s (set (tuple2 (tuple2 Bool Bool) Bool))) (t (set Bool)) (u (set Bool)))
  (=> (subset bool (t2tb14 u) (t2tb14 t))
  (=> (mem (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb7 f)
  (infix_plmngt bool (tuple21 (tuple21 bool bool) bool) (t2tb9 s) (t2tb14 t)))
  (=>
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)) (y Bool))
  (=> (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb8 (Tuple23 x y)) (t2tb7 f)) (mem bool (t2tb13 y) (t2tb14 u)))) (mem
  (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb7 f)
  (infix_plmngt bool (tuple21 (tuple21 bool bool) bool) (t2tb9 s) (t2tb14 u))))))))

;; function_reduce_range
  (assert
  (forall ((f (set (tuple2 (tuple2 Bool Bool) Bool))) (s (set (tuple2 Bool
  Bool))) (t (set Bool)) (u (set Bool)))
  (=> (subset bool (t2tb14 u) (t2tb14 t))
  (=> (mem (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb9 f)
  (infix_plmngt bool (tuple21 bool bool) (t2tb11 s) (t2tb14 t)))
  (=>
  (forall ((x (tuple2 Bool Bool)) (y Bool))
  (=> (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 x y))
  (t2tb9 f)) (mem bool (t2tb13 y) (t2tb14 u)))) (mem
  (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb9 f)
  (infix_plmngt bool (tuple21 bool bool) (t2tb11 s) (t2tb14 u))))))))

;; function_reduce_range
  (assert
  (forall ((f (set (tuple2 Bool Bool))) (s (set Bool)) (t (set Bool))
  (u (set Bool)))
  (=> (subset bool (t2tb14 u) (t2tb14 t))
  (=> (mem (set1 (tuple21 bool bool)) (t2tb11 f)
  (infix_plmngt bool bool (t2tb14 s) (t2tb14 t)))
  (=>
  (forall ((x Bool) (y Bool))
  (=> (mem (tuple21 bool bool) (t2tb12 (Tuple21 x y)) (t2tb11 f)) (mem 
  bool (t2tb13 y) (t2tb14 u)))) (mem (set1 (tuple21 bool bool)) (t2tb11 f)
  (infix_plmngt bool bool (t2tb14 s) (t2tb14 u))))))))

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

(declare-fun t2tb25 ((set (tuple2 Bool (tuple2 (tuple2 Bool Bool)
  Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Bool (tuple2 (tuple2 Bool Bool) Bool))))) (sort
  (set1 (tuple21 bool (tuple21 (tuple21 bool bool) bool))) (t2tb25 x))))

(declare-fun tb2t25 (uni) (set (tuple2 Bool (tuple2 (tuple2 Bool Bool)
  Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Bool (tuple2 (tuple2 Bool Bool) Bool)))))
  (! (= (tb2t25 (t2tb25 i)) i) :pattern ((t2tb25 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (tuple21 bool (tuple21 (tuple21 bool bool) bool))) j)
     (= (t2tb25 (tb2t25 j)) j)) :pattern ((t2tb25 (tb2t25 j))) )))

(declare-fun t2tb26 ((tuple2 Bool (tuple2 (tuple2 Bool Bool) Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Bool (tuple2 (tuple2 Bool Bool) Bool)))) (sort
  (tuple21 bool (tuple21 (tuple21 bool bool) bool)) (t2tb26 x))))

(declare-fun tb2t26 (uni) (tuple2 Bool (tuple2 (tuple2 Bool Bool) Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 Bool (tuple2 (tuple2 Bool Bool) Bool))))
  (! (= (tb2t26 (t2tb26 i)) i) :pattern ((t2tb26 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (tuple21 bool (tuple21 (tuple21 bool bool) bool)) j)
     (= (t2tb26 (tb2t26 j)) j)) :pattern ((t2tb26 (tb2t26 j))) )))

;; Inverse_def
  (assert
  (forall ((r (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)) (y Bool))
  (= (mem (tuple21 bool (tuple21 (tuple21 bool bool) bool))
  (Tuple2 bool (tuple21 (tuple21 bool bool) bool) (t2tb13 y) (t2tb10 x))
  (inverse bool (tuple21 (tuple21 bool bool) bool) (t2tb7 r))) (mem
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 (Tuple23 x y))
  (t2tb7 r))))))

(declare-fun t2tb27 ((set (tuple2 Bool (tuple2 Bool Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Bool (tuple2 Bool Bool))))) (sort
  (set1 (tuple21 bool (tuple21 bool bool))) (t2tb27 x))))

(declare-fun tb2t27 (uni) (set (tuple2 Bool (tuple2 Bool Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Bool (tuple2 Bool Bool)))))
  (! (= (tb2t27 (t2tb27 i)) i) :pattern ((t2tb27 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (tuple21 bool (tuple21 bool bool))) j)
     (= (t2tb27 (tb2t27 j)) j)) :pattern ((t2tb27 (tb2t27 j))) )))

(declare-fun t2tb28 ((tuple2 Bool (tuple2 Bool Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Bool (tuple2 Bool Bool)))) (sort
  (tuple21 bool (tuple21 bool bool)) (t2tb28 x))))

(declare-fun tb2t28 (uni) (tuple2 Bool (tuple2 Bool Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 Bool (tuple2 Bool Bool))))
  (! (= (tb2t28 (t2tb28 i)) i) :pattern ((t2tb28 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (tuple21 bool (tuple21 bool bool)) j)
     (= (t2tb28 (tb2t28 j)) j)) :pattern ((t2tb28 (tb2t28 j))) )))

;; Inverse_def
  (assert
  (forall ((r (set (tuple2 (tuple2 Bool Bool) Bool))))
  (forall ((x (tuple2 Bool Bool)) (y Bool))
  (= (mem (tuple21 bool (tuple21 bool bool))
  (Tuple2 bool (tuple21 bool bool) (t2tb13 y) (t2tb12 x))
  (inverse bool (tuple21 bool bool) (t2tb9 r))) (mem
  (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 x y)) (t2tb9 r))))))

;; Inverse_def
  (assert
  (forall ((r (set (tuple2 Bool (tuple2 (tuple2 Bool Bool) Bool)))))
  (forall ((x Bool) (y (tuple2 (tuple2 Bool Bool) Bool)))
  (= (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb8 (Tuple23 y x))
  (inverse (tuple21 (tuple21 bool bool) bool) bool (t2tb25 r))) (mem
  (tuple21 bool (tuple21 (tuple21 bool bool) bool))
  (Tuple2 bool (tuple21 (tuple21 bool bool) bool) (t2tb13 x) (t2tb10 y))
  (t2tb25 r))))))

;; Inverse_def
  (assert
  (forall ((r (set (tuple2 Bool (tuple2 Bool Bool)))))
  (forall ((x Bool) (y (tuple2 Bool Bool)))
  (= (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 y x))
  (inverse (tuple21 bool bool) bool (t2tb27 r))) (mem
  (tuple21 bool (tuple21 bool bool))
  (Tuple2 bool (tuple21 bool bool) (t2tb13 x) (t2tb12 y)) (t2tb27 r))))))

;; Inverse_def
  (assert
  (forall ((r (set (tuple2 Bool Bool))))
  (forall ((x Bool) (y Bool))
  (= (mem (tuple21 bool bool) (t2tb12 (Tuple21 y x))
  (inverse bool bool (t2tb11 r))) (mem (tuple21 bool bool)
  (t2tb12 (Tuple21 x y)) (t2tb11 r))))))

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
  (forall ((r (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)))
  (= (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x)
  (dom bool (tuple21 (tuple21 bool bool) bool) (t2tb7 r)))
  (exists ((y Bool)) (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb8 (Tuple23 x y)) (t2tb7 r)))))))

;; dom_def
  (assert
  (forall ((r (set (tuple2 (tuple2 Bool Bool) Bool))))
  (forall ((x (tuple2 Bool Bool)))
  (= (mem (tuple21 bool bool) (t2tb12 x)
  (dom bool (tuple21 bool bool) (t2tb9 r)))
  (exists ((y Bool)) (mem (tuple21 (tuple21 bool bool) bool)
  (t2tb10 (Tuple22 x y)) (t2tb9 r)))))))

;; dom_def
  (assert
  (forall ((r (set (tuple2 Bool Bool))))
  (forall ((x Bool))
  (= (mem bool (t2tb13 x) (dom bool bool (t2tb11 r)))
  (exists ((y Bool)) (mem (tuple21 bool bool) (t2tb12 (Tuple21 x y))
  (t2tb11 r)))))))

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
  (forall ((r (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (forall ((y Bool))
  (= (mem bool (t2tb13 y)
  (ran bool (tuple21 (tuple21 bool bool) bool) (t2tb7 r)))
  (exists ((x (tuple2 (tuple2 Bool Bool) Bool))) (mem
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 (Tuple23 x y))
  (t2tb7 r)))))))

;; ran_def
  (assert
  (forall ((r (set (tuple2 (tuple2 Bool Bool) Bool))))
  (forall ((y Bool))
  (= (mem bool (t2tb13 y) (ran bool (tuple21 bool bool) (t2tb9 r)))
  (exists ((x (tuple2 Bool Bool))) (mem (tuple21 (tuple21 bool bool) bool)
  (t2tb10 (Tuple22 x y)) (t2tb9 r)))))))

;; ran_def
  (assert
  (forall ((r (set (tuple2 Bool Bool))))
  (forall ((y Bool))
  (= (mem bool (t2tb13 y) (ran bool bool (t2tb11 r)))
  (exists ((x Bool)) (mem (tuple21 bool bool) (t2tb12 (Tuple21 x y))
  (t2tb11 r)))))))

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
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1))
     (empty
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1)) b)))) empty6)))

;; dom_empty
  (assert
  (forall ((b ty))
  (= (tb2t2
     (dom b (set1 uninterpreted_type1)
     (empty (tuple21 (set1 uninterpreted_type1) b)))) empty5)))

;; dom_empty
  (assert
  (forall ((b ty))
  (= (tb2t3
     (dom b uninterpreted_type1 (empty (tuple21 uninterpreted_type1 b)))) 
  empty4)))

;; dom_empty
  (assert
  (forall ((b ty))
  (= (tb2t5
     (dom b
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
     (empty
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
     b)))) empty3)))

;; dom_empty
  (assert
  (= (tb2t7
     (dom (set1 uninterpreted_type1)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb empty6))) 
  empty7))

;; dom_empty
  (assert
  (= (tb2t7
     (dom (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (t2tb5 empty3))) empty7))

;; dom_empty
  (assert
  (forall ((b ty))
  (= (tb2t7
     (dom b (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (empty (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) b)))) 
  empty7)))

;; dom_empty
  (assert
  (= (tb2t9 (dom bool (tuple21 (tuple21 bool bool) bool) (t2tb7 empty7))) 
  empty8))

;; dom_empty
  (assert
  (forall ((b ty))
  (= (tb2t9
     (dom b (tuple21 (tuple21 bool bool) bool)
     (empty (tuple21 (tuple21 (tuple21 bool bool) bool) b)))) empty8)))

;; dom_empty
  (assert (= (tb2t11 (dom bool (tuple21 bool bool) (t2tb9 empty8))) empty9))

;; dom_empty
  (assert
  (forall ((b ty))
  (= (tb2t11
     (dom b (tuple21 bool bool) (empty (tuple21 (tuple21 bool bool) b)))) 
  empty9)))

;; dom_empty
  (assert (= (tb2t14 (dom bool bool (t2tb11 empty9))) empty1))

;; dom_empty
  (assert
  (forall ((b ty)) (= (tb2t14 (dom b bool (empty (tuple21 bool b)))) empty1)))

;; dom_empty
  (assert
  (forall ((b ty)) (= (tb2t15 (dom b int (empty (tuple21 int b)))) empty2)))

;; dom_empty
  (assert
  (forall ((a ty) (b ty)) (= (dom b a (empty (tuple21 a b))) (empty a))))

;; dom_add
  (assert
  (forall ((b ty))
  (forall ((f uni) (x (set uninterpreted_type)) (y uni))
  (= (tb2t2
     (dom b (set1 uninterpreted_type1)
     (add (tuple21 (set1 uninterpreted_type1) b)
     (Tuple2 (set1 uninterpreted_type1) b (t2tb3 x) y) f))) (add3 x
                                                            (tb2t2
                                                            (dom b
                                                            (set1
                                                            uninterpreted_type1)
                                                            f)))))))

;; dom_add
  (assert
  (forall ((b ty))
  (forall ((f uni) (x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (y uni))
  (= (tb2t7
     (dom b (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) b)
     (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) b (t2tb8 x) y)
     f))) (add4 x
          (tb2t7 (dom b (tuple21 (tuple21 (tuple21 bool bool) bool) bool) f)))))))

;; dom_add
  (assert
  (forall ((f (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (x (tuple2 (tuple2 Bool Bool) Bool)) (y Bool))
  (= (tb2t9
     (dom bool (tuple21 (tuple21 bool bool) bool)
     (t2tb7 (add4 (Tuple23 x y) f)))) (add5 x
                                      (tb2t9
                                      (dom bool
                                      (tuple21 (tuple21 bool bool) bool)
                                      (t2tb7 f)))))))

;; dom_add
  (assert
  (forall ((b ty))
  (forall ((f uni) (x (tuple2 (tuple2 Bool Bool) Bool)) (y uni))
  (= (tb2t9
     (dom b (tuple21 (tuple21 bool bool) bool)
     (add (tuple21 (tuple21 (tuple21 bool bool) bool) b)
     (Tuple2 (tuple21 (tuple21 bool bool) bool) b (t2tb10 x) y) f))) 
  (add5 x (tb2t9 (dom b (tuple21 (tuple21 bool bool) bool) f)))))))

;; dom_add
  (assert
  (forall ((f (set (tuple2 (tuple2 Bool Bool) Bool))) (x (tuple2 Bool Bool))
  (y Bool))
  (= (tb2t11 (dom bool (tuple21 bool bool) (t2tb9 (add5 (Tuple22 x y) f)))) 
  (add6 x (tb2t11 (dom bool (tuple21 bool bool) (t2tb9 f)))))))

;; dom_add
  (assert
  (forall ((b ty))
  (forall ((f uni) (x (tuple2 Bool Bool)) (y uni))
  (= (tb2t11
     (dom b (tuple21 bool bool)
     (add (tuple21 (tuple21 bool bool) b)
     (Tuple2 (tuple21 bool bool) b (t2tb12 x) y) f))) (add6 x
                                                      (tb2t11
                                                      (dom b
                                                      (tuple21 bool bool) f)))))))

;; dom_add
  (assert
  (forall ((f (set (tuple2 Bool Bool))) (x Bool) (y Bool))
  (= (tb2t14 (dom bool bool (t2tb11 (add6 (Tuple21 x y) f)))) (add1 x
                                                              (tb2t14
                                                              (dom bool 
                                                              bool
                                                              (t2tb11 f)))))))

;; dom_add
  (assert
  (forall ((b ty))
  (forall ((f uni) (x Bool) (y uni))
  (= (tb2t14
     (dom b bool (add (tuple21 bool b) (Tuple2 bool b (t2tb13 x) y) f))) 
  (add1 x (tb2t14 (dom b bool f)))))))

;; dom_add
  (assert
  (forall ((b ty))
  (forall ((f uni) (x Int) (y uni))
  (= (tb2t15 (dom b int (add (tuple21 int b) (Tuple2 int b (t2tb16 x) y) f))) 
  (add2 x (tb2t15 (dom b int f)))))))

;; dom_add
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (x uni) (y uni))
  (= (dom b a (add (tuple21 a b) (Tuple2 a b x y) f)) (add a x (dom b a f))))))

;; dom_singleton
  (assert
  (forall ((b ty))
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))) (y uni))
  (= (tb2t
     (dom b
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1))
     (add
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1)) b)
     (Tuple2
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1)) b (t2tb1 x) y)
     (empty
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1)) b))))) (tb2t
                                        (add
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 uninterpreted_type1))
                                        (t2tb1 x) (t2tb empty6)))))))

;; dom_singleton
  (assert
  (forall ((b ty))
  (forall ((x (set uninterpreted_type)) (y uni))
  (= (tb2t2
     (dom b (set1 uninterpreted_type1)
     (add (tuple21 (set1 uninterpreted_type1) b)
     (Tuple2 (set1 uninterpreted_type1) b (t2tb3 x) y)
     (empty (tuple21 (set1 uninterpreted_type1) b))))) (add3 x empty5)))))

;; dom_singleton
  (assert
  (forall ((b ty))
  (forall ((x uninterpreted_type) (y uni))
  (= (tb2t3
     (dom b uninterpreted_type1
     (add (tuple21 uninterpreted_type1 b)
     (Tuple2 uninterpreted_type1 b (t2tb4 x) y)
     (empty (tuple21 uninterpreted_type1 b))))) (tb2t3
                                                (add uninterpreted_type1
                                                (t2tb4 x) (t2tb3 empty4)))))))

;; dom_singleton
  (assert
  (forall ((b ty))
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))) (y uni))
  (= (tb2t5
     (dom b
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
     (add
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
     b)
     (Tuple2
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)) b
     (t2tb6 x) y)
     (empty
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
     b))))) (tb2t5
            (add
            (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
            (set1 int)) (t2tb6 x) (t2tb5 empty3)))))))

;; dom_singleton
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (y (set uninterpreted_type)))
  (= (tb2t7
     (dom (set1 uninterpreted_type1)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (add
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1))
     (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1) (t2tb8 x) (t2tb3 y)) (t2tb empty6)))) 
  (add4 x empty7))))

;; dom_singleton
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)) (y (set Int)))
  (= (tb2t7
     (dom (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (add
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
     (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
     (t2tb8 x) (t2tb15 y)) (t2tb5 empty3)))) (add4 x empty7))))

;; dom_singleton
  (assert
  (forall ((b ty))
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)) (y uni))
  (= (tb2t7
     (dom b (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) b)
     (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) b (t2tb8 x) y)
     (empty (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) b))))) 
  (add4 x empty7)))))

;; dom_singleton
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)) (y Bool))
  (= (tb2t9
     (dom bool (tuple21 (tuple21 bool bool) bool)
     (t2tb7 (add4 (Tuple23 x y) empty7)))) (add5 x empty8))))

;; dom_singleton
  (assert
  (forall ((b ty))
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)) (y uni))
  (= (tb2t9
     (dom b (tuple21 (tuple21 bool bool) bool)
     (add (tuple21 (tuple21 (tuple21 bool bool) bool) b)
     (Tuple2 (tuple21 (tuple21 bool bool) bool) b (t2tb10 x) y)
     (empty (tuple21 (tuple21 (tuple21 bool bool) bool) b))))) (add5 x
                                                               empty8)))))

;; dom_singleton
  (assert
  (forall ((x (tuple2 Bool Bool)) (y Bool))
  (= (tb2t11
     (dom bool (tuple21 bool bool) (t2tb9 (add5 (Tuple22 x y) empty8)))) 
  (add6 x empty9))))

;; dom_singleton
  (assert
  (forall ((b ty))
  (forall ((x (tuple2 Bool Bool)) (y uni))
  (= (tb2t11
     (dom b (tuple21 bool bool)
     (add (tuple21 (tuple21 bool bool) b)
     (Tuple2 (tuple21 bool bool) b (t2tb12 x) y)
     (empty (tuple21 (tuple21 bool bool) b))))) (add6 x empty9)))))

;; dom_singleton
  (assert
  (forall ((x Bool) (y Bool))
  (= (tb2t14 (dom bool bool (t2tb11 (add6 (Tuple21 x y) empty9)))) (add1 x
                                                                   empty1))))

;; dom_singleton
  (assert
  (forall ((b ty))
  (forall ((x Bool) (y uni))
  (= (tb2t14
     (dom b bool
     (add (tuple21 bool b) (Tuple2 bool b (t2tb13 x) y)
     (empty (tuple21 bool b))))) (add1 x empty1)))))

;; dom_singleton
  (assert
  (forall ((b ty))
  (forall ((x Int) (y uni))
  (= (tb2t15
     (dom b int
     (add (tuple21 int b) (Tuple2 int b (t2tb16 x) y)
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
  (forall ((s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (t (set (set uninterpreted_type))) (x (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool)) (y (set uninterpreted_type)))
  (=>
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 x)
  (t2tb7 s)) (mem (set1 uninterpreted_type1) (t2tb3 y) (t2tb2 t))) (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1) (t2tb8 x) (t2tb3 y)) (t2tb empty6))
  (infix_plmngt (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb7 s) (t2tb2 t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (t (set (set Int))) (x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (y (set Int)))
  (=>
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 x)
  (t2tb7 s)) (mem (set1 int) (t2tb15 y) (t2tb24 t))) (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb8 x) (t2tb15 y)) (t2tb5 empty3))
  (infix_plmngt (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb7 s) (t2tb24 t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set (tuple2 (tuple2 Bool Bool) Bool))) (t (set Bool))
  (x (tuple2 (tuple2 Bool Bool) Bool)) (y Bool))
  (=>
  (and (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb9 s)) (mem
  bool (t2tb13 y) (t2tb14 t))) (mem
  (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (t2tb7 (add4 (Tuple23 x y) empty7))
  (infix_plmngt bool (tuple21 (tuple21 bool bool) bool) (t2tb9 s) (t2tb14 t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set (tuple2 Bool Bool))) (t (set Bool)) (x (tuple2 Bool Bool))
  (y Bool))
  (=>
  (and (mem (tuple21 bool bool) (t2tb12 x) (t2tb11 s)) (mem bool (t2tb13 y)
  (t2tb14 t))) (mem (set1 (tuple21 (tuple21 bool bool) bool))
  (t2tb9 (add5 (Tuple22 x y) empty8))
  (infix_plmngt bool (tuple21 bool bool) (t2tb11 s) (t2tb14 t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set Bool)) (t (set Bool)) (x Bool) (y Bool))
  (=> (and (mem bool (t2tb13 x) (t2tb14 s)) (mem bool (t2tb13 y) (t2tb14 t)))
  (mem (set1 (tuple21 bool bool)) (t2tb11 (add6 (Tuple21 x y) empty9))
  (infix_plmngt bool bool (t2tb14 s) (t2tb14 t))))))

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
  (forall ((x uni) (y (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))) (! (mem
  (set1
  (tuple21 a
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))))
  (add
  (tuple21 a
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)))
  (Tuple2 a
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) x (t2tb1 y))
  (empty
  (tuple21 a
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)))))
  (infix_mnmngt
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) a (add a x (empty a))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb1 y) (t2tb empty6)))) :pattern ((add
                                                                   (tuple21 a
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   bool 
                                                                   bool)
                                                                   bool)
                                                                   bool)
                                                                   (set1
                                                                   uninterpreted_type1)))
                                                                   (Tuple2 a
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   bool 
                                                                   bool)
                                                                   bool)
                                                                   bool)
                                                                   (set1
                                                                   uninterpreted_type1))
                                                                   x
                                                                   (t2tb1 y))
                                                                   (empty
                                                                   (tuple21 a
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   bool 
                                                                   bool)
                                                                   bool)
                                                                   bool)
                                                                   (set1
                                                                   uninterpreted_type1)))))) ))))

;; singleton_is_function
  (assert
  (forall ((a ty))
  (forall ((x uni) (y (set uninterpreted_type))) (! (mem
  (set1 (tuple21 a (set1 uninterpreted_type1)))
  (add (tuple21 a (set1 uninterpreted_type1))
  (Tuple2 a (set1 uninterpreted_type1) x (t2tb3 y))
  (empty (tuple21 a (set1 uninterpreted_type1))))
  (infix_mnmngt (set1 uninterpreted_type1) a (add a x (empty a))
  (t2tb2 (add3 y empty5)))) :pattern ((add
                                      (tuple21 a (set1 uninterpreted_type1))
                                      (Tuple2 a (set1 uninterpreted_type1) x
                                      (t2tb3 y))
                                      (empty
                                      (tuple21 a (set1 uninterpreted_type1))))) ))))

;; singleton_is_function
  (assert
  (forall ((a ty))
  (forall ((x uni) (y uninterpreted_type)) (! (mem
  (set1 (tuple21 a uninterpreted_type1))
  (add (tuple21 a uninterpreted_type1)
  (Tuple2 a uninterpreted_type1 x (t2tb4 y))
  (empty (tuple21 a uninterpreted_type1)))
  (infix_mnmngt uninterpreted_type1 a (add a x (empty a))
  (add uninterpreted_type1 (t2tb4 y) (t2tb3 empty4)))) :pattern ((add
                                                                 (tuple21 a
                                                                 uninterpreted_type1)
                                                                 (Tuple2 a
                                                                 uninterpreted_type1
                                                                 x (t2tb4 y))
                                                                 (empty
                                                                 (tuple21 a
                                                                 uninterpreted_type1)))) ))))

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
  (t2tb6 y))
  (empty
  (tuple21 a
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (infix_mnmngt
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)) a
  (add a x (empty a))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb6 y) (t2tb5 empty3)))) :pattern ((add
                                        (tuple21 a
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int)))
                                        (Tuple2 a
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int)) x (t2tb6 y))
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
  (Tuple2 a (tuple21 (tuple21 (tuple21 bool bool) bool) bool) x (t2tb8 y))
  (empty (tuple21 a (tuple21 (tuple21 (tuple21 bool bool) bool) bool))))
  (infix_mnmngt (tuple21 (tuple21 (tuple21 bool bool) bool) bool) a
  (add a x (empty a)) (t2tb7 (add4 y empty7)))) :pattern ((add
                                                          (tuple21 a
                                                          (tuple21
                                                          (tuple21
                                                          (tuple21 bool bool)
                                                          bool) bool))
                                                          (Tuple2 a
                                                          (tuple21
                                                          (tuple21
                                                          (tuple21 bool bool)
                                                          bool) bool) x
                                                          (t2tb8 y))
                                                          (empty
                                                          (tuple21 a
                                                          (tuple21
                                                          (tuple21
                                                          (tuple21 bool bool)
                                                          bool) bool))))) ))))

;; singleton_is_function
  (assert
  (forall ((a ty))
  (forall ((x uni) (y (tuple2 (tuple2 Bool Bool) Bool))) (! (mem
  (set1 (tuple21 a (tuple21 (tuple21 bool bool) bool)))
  (add (tuple21 a (tuple21 (tuple21 bool bool) bool))
  (Tuple2 a (tuple21 (tuple21 bool bool) bool) x (t2tb10 y))
  (empty (tuple21 a (tuple21 (tuple21 bool bool) bool))))
  (infix_mnmngt (tuple21 (tuple21 bool bool) bool) a (add a x (empty a))
  (t2tb9 (add5 y empty8)))) :pattern ((add
                                      (tuple21 a
                                      (tuple21 (tuple21 bool bool) bool))
                                      (Tuple2 a
                                      (tuple21 (tuple21 bool bool) bool) x
                                      (t2tb10 y))
                                      (empty
                                      (tuple21 a
                                      (tuple21 (tuple21 bool bool) bool))))) ))))

;; singleton_is_function
  (assert
  (forall ((a ty))
  (forall ((x uni) (y (tuple2 Bool Bool))) (! (mem
  (set1 (tuple21 a (tuple21 bool bool)))
  (add (tuple21 a (tuple21 bool bool))
  (Tuple2 a (tuple21 bool bool) x (t2tb12 y))
  (empty (tuple21 a (tuple21 bool bool))))
  (infix_mnmngt (tuple21 bool bool) a (add a x (empty a))
  (t2tb11 (add6 y empty9)))) :pattern ((add (tuple21 a (tuple21 bool bool))
                                       (Tuple2 a (tuple21 bool bool) x
                                       (t2tb12 y))
                                       (empty
                                       (tuple21 a (tuple21 bool bool))))) ))))

;; singleton_is_function
  (assert
  (forall ((a ty))
  (forall ((x uni) (y Bool)) (! (mem (set1 (tuple21 a bool))
  (add (tuple21 a bool) (Tuple2 a bool x (t2tb13 y))
  (empty (tuple21 a bool)))
  (infix_mnmngt bool a (add a x (empty a)) (t2tb14 (add1 y empty1)))) :pattern (
  (add (tuple21 a bool) (Tuple2 a bool x (t2tb13 y))
  (empty (tuple21 a bool)))) ))))

;; singleton_is_function
  (assert
  (forall ((a ty))
  (forall ((x uni) (y Int)) (! (mem (set1 (tuple21 a int))
  (add (tuple21 a int) (Tuple2 a int x (t2tb16 y)) (empty (tuple21 a int)))
  (infix_mnmngt int a (add a x (empty a)) (t2tb15 (add2 y empty2)))) :pattern (
  (add (tuple21 a int) (Tuple2 a int x (t2tb16 y)) (empty (tuple21 a int)))) ))))

(declare-fun t2tb29 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type))
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)) (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type))))))) (sort
  (set1
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))))) (t2tb29 x))))

(declare-fun tb2t29 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type))
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)) (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type)))))))
  (! (= (tb2t29 (t2tb29 i)) i) :pattern ((t2tb29 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1))
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1))))) j) (= (t2tb29 (tb2t29 j)) j)) :pattern (
  (t2tb29 (tb2t29 j))) )))

(declare-fun t2tb30 ((set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)) (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)))))) (sort
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)))) (t2tb30 x))))

(declare-fun tb2t30 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type))
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type))))))
  (! (= (tb2t30 (t2tb30 i)) i) :pattern ((t2tb30 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1))
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1)))) j) (= (t2tb30 (tb2t30 j)) j)) :pattern (
  (t2tb30 (tb2t30 j))) )))

(declare-fun t2tb31 ((tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type))))) (sort
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))) (t2tb31 x))))

(declare-fun tb2t31 (uni) (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)) (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type))))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type)))))
  (! (= (tb2t31 (t2tb31 i)) i) :pattern ((t2tb31 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1))
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1))) j) (= (t2tb31 (tb2t31 j)) j)) :pattern (
  (t2tb31 (tb2t31 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))) (y (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)))) (! (mem
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))))
  (add
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)))
  (Tuple2
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb1 x) (t2tb1 y))
  (empty
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)))))
  (infix_mnmngt
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb1 x) (t2tb empty6))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb1 y) (t2tb empty6)))) :pattern ((tb2t30
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
                                                                   (set1
                                                                   uninterpreted_type1))
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   bool 
                                                                   bool)
                                                                   bool)
                                                                   bool)
                                                                   (set1
                                                                   uninterpreted_type1)))
                                                                   (Tuple2
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   bool 
                                                                   bool)
                                                                   bool)
                                                                   bool)
                                                                   (set1
                                                                   uninterpreted_type1))
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   bool 
                                                                   bool)
                                                                   bool)
                                                                   bool)
                                                                   (set1
                                                                   uninterpreted_type1))
                                                                   (t2tb1 x)
                                                                   (t2tb1 y))
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
                                                                   (set1
                                                                   uninterpreted_type1))
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   bool 
                                                                   bool)
                                                                   bool)
                                                                   bool)
                                                                   (set1
                                                                   uninterpreted_type1))))))) )))

(declare-fun t2tb32 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type))
  (set uninterpreted_type))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)) (set uninterpreted_type)))))) (sort
  (set1
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (set1 uninterpreted_type1)))) (t2tb32 x))))

(declare-fun tb2t32 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type)) (set uninterpreted_type)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)) (set uninterpreted_type))))))
  (! (= (tb2t32 (t2tb32 i)) i) :pattern ((t2tb32 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1)) (set1 uninterpreted_type1)))) j)
     (= (t2tb32 (tb2t32 j)) j)) :pattern ((t2tb32 (tb2t32 j))) )))

(declare-fun t2tb33 ((set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)) (set uninterpreted_type)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type)) (set uninterpreted_type))))) (sort
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (set1 uninterpreted_type1))) (t2tb33 x))))

(declare-fun tb2t33 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type)) (set uninterpreted_type))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type)) (set uninterpreted_type)))))
  (! (= (tb2t33 (t2tb33 i)) i) :pattern ((t2tb33 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1)) (set1 uninterpreted_type1))) j)
     (= (t2tb33 (tb2t33 j)) j)) :pattern ((t2tb33 (tb2t33 j))) )))

(declare-fun t2tb34 ((tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type)) (set uninterpreted_type))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)) (set uninterpreted_type)))) (sort
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (set1 uninterpreted_type1)) (t2tb34 x))))

(declare-fun tb2t34 (uni) (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)) (set uninterpreted_type)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)) (set uninterpreted_type))))
  (! (= (tb2t34 (t2tb34 i)) i) :pattern ((t2tb34 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1)) (set1 uninterpreted_type1)) j)
     (= (t2tb34 (tb2t34 j)) j)) :pattern ((t2tb34 (tb2t34 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))) (y (set uninterpreted_type))) (! (mem
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (set1 uninterpreted_type1)))
  (add
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (set1 uninterpreted_type1))
  (Tuple2
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (set1 uninterpreted_type1) (t2tb1 x) (t2tb3 y))
  (empty
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (set1 uninterpreted_type1))))
  (infix_mnmngt (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb1 x) (t2tb empty6))
  (t2tb2 (add3 y empty5)))) :pattern ((tb2t33
                                      (add
                                      (tuple21
                                      (tuple21
                                      (tuple21
                                      (tuple21 (tuple21 bool bool) bool)
                                      bool) (set1 uninterpreted_type1))
                                      (set1 uninterpreted_type1))
                                      (Tuple2
                                      (tuple21
                                      (tuple21
                                      (tuple21 (tuple21 bool bool) bool)
                                      bool) (set1 uninterpreted_type1))
                                      (set1 uninterpreted_type1) (t2tb1 x)
                                      (t2tb3 y))
                                      (empty
                                      (tuple21
                                      (tuple21
                                      (tuple21
                                      (tuple21 (tuple21 bool bool) bool)
                                      bool) (set1 uninterpreted_type1))
                                      (set1 uninterpreted_type1)))))) )))

(declare-fun t2tb35 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type)) uninterpreted_type)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)) uninterpreted_type))))) (sort
  (set1
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) uninterpreted_type1))) (t2tb35 x))))

(declare-fun tb2t35 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type)) uninterpreted_type))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)) uninterpreted_type)))))
  (! (= (tb2t35 (t2tb35 i)) i) :pattern ((t2tb35 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1)) uninterpreted_type1))) j)
     (= (t2tb35 (tb2t35 j)) j)) :pattern ((t2tb35 (tb2t35 j))) )))

(declare-fun t2tb36 ((set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)) uninterpreted_type))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type)) uninterpreted_type)))) (sort
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) uninterpreted_type1)) (t2tb36 x))))

(declare-fun tb2t36 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type)) uninterpreted_type)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type)) uninterpreted_type))))
  (! (= (tb2t36 (t2tb36 i)) i) :pattern ((t2tb36 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1)) uninterpreted_type1)) j)
     (= (t2tb36 (tb2t36 j)) j)) :pattern ((t2tb36 (tb2t36 j))) )))

(declare-fun t2tb37 ((tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type)) uninterpreted_type)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)) uninterpreted_type))) (sort
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) uninterpreted_type1) (t2tb37 x))))

(declare-fun tb2t37 (uni) (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)) uninterpreted_type))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)) uninterpreted_type)))
  (! (= (tb2t37 (t2tb37 i)) i) :pattern ((t2tb37 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1)) uninterpreted_type1) j)
     (= (t2tb37 (tb2t37 j)) j)) :pattern ((t2tb37 (tb2t37 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))) (y uninterpreted_type)) (! (mem
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) uninterpreted_type1))
  (add
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) uninterpreted_type1)
  (Tuple2
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) uninterpreted_type1 (t2tb1 x) (t2tb4 y))
  (empty
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) uninterpreted_type1)))
  (infix_mnmngt uninterpreted_type1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb1 x) (t2tb empty6))
  (add uninterpreted_type1 (t2tb4 y) (t2tb3 empty4)))) :pattern ((tb2t36
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
                                                                 (set1
                                                                 uninterpreted_type1))
                                                                 uninterpreted_type1)
                                                                 (Tuple2
                                                                 (tuple21
                                                                 (tuple21
                                                                 (tuple21
                                                                 (tuple21
                                                                 bool 
                                                                 bool) 
                                                                 bool) 
                                                                 bool)
                                                                 (set1
                                                                 uninterpreted_type1))
                                                                 uninterpreted_type1
                                                                 (t2tb1 x)
                                                                 (t2tb4 y))
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
                                                                 (set1
                                                                 uninterpreted_type1))
                                                                 uninterpreted_type1))))) )))

(declare-fun t2tb38 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type))
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)) (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))))) (sort
  (set1
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (t2tb38 x))))

(declare-fun tb2t38 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type))
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)) (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))))))
  (! (= (tb2t38 (t2tb38 i)) i) :pattern ((t2tb38 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb38 (tb2t38 j)) j) :pattern ((t2tb38 (tb2t38 j))) )))

(declare-fun t2tb39 ((set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)) (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))))) (sort
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (t2tb39 x))))

(declare-fun tb2t39 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type))
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))))
  (! (= (tb2t39 (t2tb39 i)) i) :pattern ((t2tb39 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb39 (tb2t39 j)) j) :pattern ((t2tb39 (tb2t39 j))) )))

(declare-fun t2tb40 ((tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (sort
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb40 x))))

(declare-fun tb2t40 (uni) (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)) (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (! (= (tb2t40 (t2tb40 i)) i) :pattern ((t2tb40 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb40 (tb2t40 j)) j) :pattern ((t2tb40 (tb2t40 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))) (y (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))) (! (mem
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (add
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (Tuple2
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb1 x) (t2tb6 y))
  (empty
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (infix_mnmngt
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb1 x) (t2tb empty6))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb6 y) (t2tb5 empty3)))) :pattern ((tb2t39
                                        (add
                                        (tuple21
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 uninterpreted_type1))
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int)))
                                        (Tuple2
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 uninterpreted_type1))
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int)) (t2tb1 x)
                                        (t2tb6 y))
                                        (empty
                                        (tuple21
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 uninterpreted_type1))
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int))))))) )))

(declare-fun t2tb41 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type)) (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)) (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool)))))) (sort
  (set1
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))) (t2tb41 x))))

(declare-fun tb2t41 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type)) (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)) (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool)))))) (! (= (tb2t41 (t2tb41 i)) i) :pattern ((t2tb41 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1))
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))) j)
     (= (t2tb41 (tb2t41 j)) j)) :pattern ((t2tb41 (tb2t41 j))) )))

(declare-fun t2tb42 ((set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)) (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type)) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))))) (sort
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))) (t2tb42 x))))

(declare-fun tb2t42 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type)) (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type)) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))))) (! (= (tb2t42 (t2tb42 i)) i) :pattern ((t2tb42 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1))
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool))) j)
     (= (t2tb42 (tb2t42 j)) j)) :pattern ((t2tb42 (tb2t42 j))) )))

(declare-fun t2tb43 ((tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type)) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)) (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (sort
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb43 x))))

(declare-fun tb2t43 (uni) (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)) (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)) (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (! (= (tb2t43 (t2tb43 i)) i) :pattern ((t2tb43 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1))
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) j)
     (= (t2tb43 (tb2t43 j)) j)) :pattern ((t2tb43 (tb2t43 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))) (y (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))) (! (mem
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))
  (add
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (Tuple2
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb1 x) (t2tb8 y))
  (empty
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))))
  (infix_mnmngt (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb1 x) (t2tb empty6))
  (t2tb7 (add4 y empty7)))) :pattern ((tb2t42
                                      (add
                                      (tuple21
                                      (tuple21
                                      (tuple21
                                      (tuple21 (tuple21 bool bool) bool)
                                      bool) (set1 uninterpreted_type1))
                                      (tuple21
                                      (tuple21 (tuple21 bool bool) bool)
                                      bool))
                                      (Tuple2
                                      (tuple21
                                      (tuple21
                                      (tuple21 (tuple21 bool bool) bool)
                                      bool) (set1 uninterpreted_type1))
                                      (tuple21
                                      (tuple21 (tuple21 bool bool) bool)
                                      bool) (t2tb1 x) (t2tb8 y))
                                      (empty
                                      (tuple21
                                      (tuple21
                                      (tuple21
                                      (tuple21 (tuple21 bool bool) bool)
                                      bool) (set1 uninterpreted_type1))
                                      (tuple21
                                      (tuple21 (tuple21 bool bool) bool)
                                      bool)))))) )))

(declare-fun t2tb44 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type)) (tuple2 (tuple2 Bool Bool)
  Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)) (tuple2 (tuple2 Bool Bool) Bool))))))
  (sort
  (set1
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (tuple21 (tuple21 bool bool) bool))))
  (t2tb44 x))))

(declare-fun tb2t44 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type)) (tuple2 (tuple2 Bool Bool)
  Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)) (tuple2 (tuple2 Bool Bool) Bool))))))
  (! (= (tb2t44 (t2tb44 i)) i) :pattern ((t2tb44 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1)) (tuple21 (tuple21 bool bool) bool)))) j)
     (= (t2tb44 (tb2t44 j)) j)) :pattern ((t2tb44 (tb2t44 j))) )))

(declare-fun t2tb45 ((set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)) (tuple2 (tuple2 Bool Bool)
  Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type)) (tuple2 (tuple2 Bool Bool) Bool))))) (sort
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (tuple21 (tuple21 bool bool) bool)))
  (t2tb45 x))))

(declare-fun tb2t45 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type)) (tuple2 (tuple2 Bool Bool)
  Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type)) (tuple2 (tuple2 Bool Bool) Bool)))))
  (! (= (tb2t45 (t2tb45 i)) i) :pattern ((t2tb45 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1)) (tuple21 (tuple21 bool bool) bool))) j)
     (= (t2tb45 (tb2t45 j)) j)) :pattern ((t2tb45 (tb2t45 j))) )))

(declare-fun t2tb46 ((tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type)) (tuple2 (tuple2 Bool Bool) Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)) (tuple2 (tuple2 Bool Bool) Bool)))) (sort
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (tuple21 (tuple21 bool bool) bool))
  (t2tb46 x))))

(declare-fun tb2t46 (uni) (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)) (tuple2 (tuple2 Bool Bool) Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)) (tuple2 (tuple2 Bool Bool) Bool))))
  (! (= (tb2t46 (t2tb46 i)) i) :pattern ((t2tb46 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1)) (tuple21 (tuple21 bool bool) bool)) j)
     (= (t2tb46 (tb2t46 j)) j)) :pattern ((t2tb46 (tb2t46 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))) (y (tuple2 (tuple2 Bool Bool) Bool))) (! (mem
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (tuple21 (tuple21 bool bool) bool)))
  (add
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (tuple21 (tuple21 bool bool) bool))
  (Tuple2
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (tuple21 (tuple21 bool bool) bool) (t2tb1 x)
  (t2tb10 y))
  (empty
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (tuple21 (tuple21 bool bool) bool))))
  (infix_mnmngt (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb1 x) (t2tb empty6))
  (t2tb9 (add5 y empty8)))) :pattern ((tb2t45
                                      (add
                                      (tuple21
                                      (tuple21
                                      (tuple21
                                      (tuple21 (tuple21 bool bool) bool)
                                      bool) (set1 uninterpreted_type1))
                                      (tuple21 (tuple21 bool bool) bool))
                                      (Tuple2
                                      (tuple21
                                      (tuple21
                                      (tuple21 (tuple21 bool bool) bool)
                                      bool) (set1 uninterpreted_type1))
                                      (tuple21 (tuple21 bool bool) bool)
                                      (t2tb1 x) (t2tb10 y))
                                      (empty
                                      (tuple21
                                      (tuple21
                                      (tuple21
                                      (tuple21 (tuple21 bool bool) bool)
                                      bool) (set1 uninterpreted_type1))
                                      (tuple21 (tuple21 bool bool) bool)))))) )))

(declare-fun t2tb47 ((set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)) (tuple2 Bool Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type)) (tuple2 Bool Bool))))) (sort
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (tuple21 bool bool))) (t2tb47 x))))

(declare-fun tb2t47 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type)) (tuple2 Bool Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type)) (tuple2 Bool Bool)))))
  (! (= (tb2t47 (t2tb47 i)) i) :pattern ((t2tb47 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1)) (tuple21 bool bool))) j)
     (= (t2tb47 (tb2t47 j)) j)) :pattern ((t2tb47 (tb2t47 j))) )))

(declare-fun t2tb48 ((tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type)) (tuple2 Bool Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)) (tuple2 Bool Bool)))) (sort
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (tuple21 bool bool)) (t2tb48 x))))

(declare-fun tb2t48 (uni) (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)) (tuple2 Bool Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)) (tuple2 Bool Bool))))
  (! (= (tb2t48 (t2tb48 i)) i) :pattern ((t2tb48 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1)) (tuple21 bool bool)) j)
     (= (t2tb48 (tb2t48 j)) j)) :pattern ((t2tb48 (tb2t48 j))) )))

(declare-fun t2tb49 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type)) (tuple2 Bool Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)) (tuple2 Bool Bool)))))) (sort
  (set1
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (tuple21 bool bool)))) (t2tb49 x))))

(declare-fun tb2t49 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type)) (tuple2 Bool Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)) (tuple2 Bool Bool))))))
  (! (= (tb2t49 (t2tb49 i)) i) :pattern ((t2tb49 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1)) (tuple21 bool bool)))) j)
     (= (t2tb49 (tb2t49 j)) j)) :pattern ((t2tb49 (tb2t49 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))) (y (tuple2 Bool Bool))) (! (mem
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (tuple21 bool bool)))
  (add
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (tuple21 bool bool))
  (Tuple2
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (tuple21 bool bool) (t2tb1 x) (t2tb12 y))
  (empty
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (tuple21 bool bool))))
  (infix_mnmngt (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb1 x) (t2tb empty6))
  (t2tb11 (add6 y empty9)))) :pattern ((tb2t47
                                       (add
                                       (tuple21
                                       (tuple21
                                       (tuple21
                                       (tuple21 (tuple21 bool bool) bool)
                                       bool) (set1 uninterpreted_type1))
                                       (tuple21 bool bool))
                                       (Tuple2
                                       (tuple21
                                       (tuple21
                                       (tuple21 (tuple21 bool bool) bool)
                                       bool) (set1 uninterpreted_type1))
                                       (tuple21 bool bool) (t2tb1 x)
                                       (t2tb12 y))
                                       (empty
                                       (tuple21
                                       (tuple21
                                       (tuple21
                                       (tuple21 (tuple21 bool bool) bool)
                                       bool) (set1 uninterpreted_type1))
                                       (tuple21 bool bool)))))) )))

(declare-fun t2tb50 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type)) Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)) Bool))))) (sort
  (set1
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) bool))) (t2tb50 x))))

(declare-fun tb2t50 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type)) Bool))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)) Bool)))))
  (! (= (tb2t50 (t2tb50 i)) i) :pattern ((t2tb50 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1)) bool))) j) (= (t2tb50 (tb2t50 j)) j)) :pattern (
  (t2tb50 (tb2t50 j))) )))

(declare-fun t2tb51 ((set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)) Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type)) Bool)))) (sort
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) bool)) (t2tb51 x))))

(declare-fun tb2t51 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type)) Bool)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type)) Bool))))
  (! (= (tb2t51 (t2tb51 i)) i) :pattern ((t2tb51 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1)) bool)) j) (= (t2tb51 (tb2t51 j)) j)) :pattern (
  (t2tb51 (tb2t51 j))) )))

(declare-fun t2tb52 ((tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type)) Bool)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)) Bool))) (sort
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) bool) (t2tb52 x))))

(declare-fun tb2t52 (uni) (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)) Bool))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)) Bool)))
  (! (= (tb2t52 (t2tb52 i)) i) :pattern ((t2tb52 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1)) bool) j) (= (t2tb52 (tb2t52 j)) j)) :pattern (
  (t2tb52 (tb2t52 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))) (y Bool)) (! (mem
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) bool))
  (add
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) bool)
  (Tuple2
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) bool (t2tb1 x) (t2tb13 y))
  (empty
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) bool)))
  (infix_mnmngt bool
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb1 x) (t2tb empty6))
  (t2tb14 (add1 y empty1)))) :pattern ((tb2t51
                                       (add
                                       (tuple21
                                       (tuple21
                                       (tuple21
                                       (tuple21 (tuple21 bool bool) bool)
                                       bool) (set1 uninterpreted_type1))
                                       bool)
                                       (Tuple2
                                       (tuple21
                                       (tuple21
                                       (tuple21 (tuple21 bool bool) bool)
                                       bool) (set1 uninterpreted_type1)) 
                                       bool (t2tb1 x) (t2tb13 y))
                                       (empty
                                       (tuple21
                                       (tuple21
                                       (tuple21
                                       (tuple21 (tuple21 bool bool) bool)
                                       bool) (set1 uninterpreted_type1))
                                       bool))))) )))

(declare-fun t2tb53 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type)) Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)) Int))))) (sort
  (set1
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) int))) (t2tb53 x))))

(declare-fun tb2t53 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type)) Int))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)) Int)))))
  (! (= (tb2t53 (t2tb53 i)) i) :pattern ((t2tb53 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb53 (tb2t53 j)) j) :pattern ((t2tb53 (tb2t53 j))) )))

(declare-fun t2tb54 ((set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)) Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type)) Int)))) (sort
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) int)) (t2tb54 x))))

(declare-fun tb2t54 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type)) Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type)) Int))))
  (! (= (tb2t54 (t2tb54 i)) i) :pattern ((t2tb54 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb54 (tb2t54 j)) j) :pattern ((t2tb54 (tb2t54 j))) )))

(declare-fun t2tb55 ((tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type)) Int)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)) Int))) (sort
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) int) (t2tb55 x))))

(declare-fun tb2t55 (uni) (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)) Int))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)) Int)))
  (! (= (tb2t55 (t2tb55 i)) i) :pattern ((t2tb55 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb55 (tb2t55 j)) j) :pattern ((t2tb55 (tb2t55 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))) (y Int)) (! (mem
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) int))
  (add
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) int)
  (Tuple2
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) int (t2tb1 x) (t2tb16 y))
  (empty
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) int)))
  (infix_mnmngt int
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb1 x) (t2tb empty6))
  (t2tb15 (add2 y empty2)))) :pattern ((tb2t54
                                       (add
                                       (tuple21
                                       (tuple21
                                       (tuple21
                                       (tuple21 (tuple21 bool bool) bool)
                                       bool) (set1 uninterpreted_type1)) 
                                       int)
                                       (Tuple2
                                       (tuple21
                                       (tuple21
                                       (tuple21 (tuple21 bool bool) bool)
                                       bool) (set1 uninterpreted_type1)) 
                                       int (t2tb1 x) (t2tb16 y))
                                       (empty
                                       (tuple21
                                       (tuple21
                                       (tuple21
                                       (tuple21 (tuple21 bool bool) bool)
                                       bool) (set1 uninterpreted_type1)) 
                                       int))))) )))

;; singleton_is_function
  (assert
  (forall ((b ty))
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))) (y uni)) (! (mem
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) b))
  (add
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) b)
  (Tuple2
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) b (t2tb1 x) y)
  (empty
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) b)))
  (infix_mnmngt b
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb1 x) (t2tb empty6)) (add b y (empty b)))) :pattern (
  (add
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) b)
  (Tuple2
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) b (t2tb1 x) y)
  (empty
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) b)))) ))))

(declare-fun t2tb56 ((set (set (tuple2 (set uninterpreted_type)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (set uninterpreted_type)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))))))) (sort
  (set1
  (set1
  (tuple21 (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))))) (t2tb56 x))))

(declare-fun tb2t56 (uni) (set (set (tuple2 (set uninterpreted_type)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (set uninterpreted_type)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))))))
  (! (= (tb2t56 (t2tb56 i)) i) :pattern ((t2tb56 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21 (set1 uninterpreted_type1)
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1))))) j) (= (t2tb56 (tb2t56 j)) j)) :pattern (
  (t2tb56 (tb2t56 j))) )))

(declare-fun t2tb57 ((set (tuple2 (set uninterpreted_type)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (set uninterpreted_type)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))))) (sort
  (set1
  (tuple21 (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)))) (t2tb57 x))))

(declare-fun tb2t57 (uni) (set (tuple2 (set uninterpreted_type)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (set uninterpreted_type)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))))))
  (! (= (tb2t57 (t2tb57 i)) i) :pattern ((t2tb57 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21 (set1 uninterpreted_type1)
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1)))) j) (= (t2tb57 (tb2t57 j)) j)) :pattern (
  (t2tb57 (tb2t57 j))) )))

(declare-fun t2tb58 ((tuple2 (set uninterpreted_type)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (set uninterpreted_type)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))))) (sort
  (tuple21 (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))) (t2tb58 x))))

(declare-fun tb2t58 (uni) (tuple2 (set uninterpreted_type)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))))

;; BridgeL
  (assert
  (forall ((i (tuple2 (set uninterpreted_type)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))))
  (! (= (tb2t58 (t2tb58 i)) i) :pattern ((t2tb58 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 (set1 uninterpreted_type1)
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1))) j) (= (t2tb58 (tb2t58 j)) j)) :pattern (
  (t2tb58 (tb2t58 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (set uninterpreted_type))
  (y (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))) (! (mem
  (set1
  (tuple21 (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))))
  (add
  (tuple21 (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)))
  (Tuple2 (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb3 x) (t2tb1 y))
  (empty
  (tuple21 (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)))))
  (infix_mnmngt
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (set1 uninterpreted_type1)
  (t2tb2 (add3 x empty5))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb1 y) (t2tb empty6)))) :pattern ((tb2t57
                                                                   (add
                                                                   (tuple21
                                                                   (set1
                                                                   uninterpreted_type1)
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   bool 
                                                                   bool)
                                                                   bool)
                                                                   bool)
                                                                   (set1
                                                                   uninterpreted_type1)))
                                                                   (Tuple2
                                                                   (set1
                                                                   uninterpreted_type1)
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   bool 
                                                                   bool)
                                                                   bool)
                                                                   bool)
                                                                   (set1
                                                                   uninterpreted_type1))
                                                                   (t2tb3 x)
                                                                   (t2tb1 y))
                                                                   (empty
                                                                   (tuple21
                                                                   (set1
                                                                   uninterpreted_type1)
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   bool 
                                                                   bool)
                                                                   bool)
                                                                   bool)
                                                                   (set1
                                                                   uninterpreted_type1))))))) )))

(declare-fun t2tb59 ((set (set (tuple2 (set uninterpreted_type)
  (set uninterpreted_type))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (set uninterpreted_type)
  (set uninterpreted_type)))))) (sort
  (set1
  (set1 (tuple21 (set1 uninterpreted_type1) (set1 uninterpreted_type1))))
  (t2tb59 x))))

(declare-fun tb2t59 (uni) (set (set (tuple2 (set uninterpreted_type)
  (set uninterpreted_type)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (set uninterpreted_type)
  (set uninterpreted_type))))))
  (! (= (tb2t59 (t2tb59 i)) i) :pattern ((t2tb59 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1 (tuple21 (set1 uninterpreted_type1) (set1 uninterpreted_type1))))
     j) (= (t2tb59 (tb2t59 j)) j)) :pattern ((t2tb59 (tb2t59 j))) )))

(declare-fun t2tb60 ((set (tuple2 (set uninterpreted_type)
  (set uninterpreted_type)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (set uninterpreted_type)
  (set uninterpreted_type))))) (sort
  (set1 (tuple21 (set1 uninterpreted_type1) (set1 uninterpreted_type1)))
  (t2tb60 x))))

(declare-fun tb2t60 (uni) (set (tuple2 (set uninterpreted_type)
  (set uninterpreted_type))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (set uninterpreted_type)
  (set uninterpreted_type)))))
  (! (= (tb2t60 (t2tb60 i)) i) :pattern ((t2tb60 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1 (tuple21 (set1 uninterpreted_type1) (set1 uninterpreted_type1)))
     j) (= (t2tb60 (tb2t60 j)) j)) :pattern ((t2tb60 (tb2t60 j))) )))

(declare-fun t2tb61 ((tuple2 (set uninterpreted_type)
  (set uninterpreted_type))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (set uninterpreted_type) (set uninterpreted_type))))
  (sort (tuple21 (set1 uninterpreted_type1) (set1 uninterpreted_type1))
  (t2tb61 x))))

(declare-fun tb2t61 (uni) (tuple2 (set uninterpreted_type)
  (set uninterpreted_type)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (set uninterpreted_type) (set uninterpreted_type))))
  (! (= (tb2t61 (t2tb61 i)) i) :pattern ((t2tb61 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 (set1 uninterpreted_type1) (set1 uninterpreted_type1)) j)
     (= (t2tb61 (tb2t61 j)) j)) :pattern ((t2tb61 (tb2t61 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (set uninterpreted_type)) (y (set uninterpreted_type))) (! (mem
  (set1 (tuple21 (set1 uninterpreted_type1) (set1 uninterpreted_type1)))
  (add (tuple21 (set1 uninterpreted_type1) (set1 uninterpreted_type1))
  (Tuple2 (set1 uninterpreted_type1) (set1 uninterpreted_type1) (t2tb3 x)
  (t2tb3 y))
  (empty (tuple21 (set1 uninterpreted_type1) (set1 uninterpreted_type1))))
  (infix_mnmngt (set1 uninterpreted_type1) (set1 uninterpreted_type1)
  (t2tb2 (add3 x empty5)) (t2tb2 (add3 y empty5)))) :pattern ((tb2t60
                                                              (add
                                                              (tuple21
                                                              (set1
                                                              uninterpreted_type1)
                                                              (set1
                                                              uninterpreted_type1))
                                                              (Tuple2
                                                              (set1
                                                              uninterpreted_type1)
                                                              (set1
                                                              uninterpreted_type1)
                                                              (t2tb3 x)
                                                              (t2tb3 y))
                                                              (empty
                                                              (tuple21
                                                              (set1
                                                              uninterpreted_type1)
                                                              (set1
                                                              uninterpreted_type1)))))) )))

(declare-fun t2tb62 ((set (tuple2 (set uninterpreted_type)
  uninterpreted_type))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (set uninterpreted_type) uninterpreted_type))))
  (sort (set1 (tuple21 (set1 uninterpreted_type1) uninterpreted_type1))
  (t2tb62 x))))

(declare-fun tb2t62 (uni) (set (tuple2 (set uninterpreted_type)
  uninterpreted_type)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (set uninterpreted_type) uninterpreted_type))))
  (! (= (tb2t62 (t2tb62 i)) i) :pattern ((t2tb62 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1 (tuple21 (set1 uninterpreted_type1) uninterpreted_type1)) j)
     (= (t2tb62 (tb2t62 j)) j)) :pattern ((t2tb62 (tb2t62 j))) )))

(declare-fun t2tb63 ((tuple2 (set uninterpreted_type)
  uninterpreted_type)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (set uninterpreted_type) uninterpreted_type))) (sort
  (tuple21 (set1 uninterpreted_type1) uninterpreted_type1) (t2tb63 x))))

(declare-fun tb2t63 (uni) (tuple2 (set uninterpreted_type)
  uninterpreted_type))

;; BridgeL
  (assert
  (forall ((i (tuple2 (set uninterpreted_type) uninterpreted_type)))
  (! (= (tb2t63 (t2tb63 i)) i) :pattern ((t2tb63 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (tuple21 (set1 uninterpreted_type1) uninterpreted_type1) j)
     (= (t2tb63 (tb2t63 j)) j)) :pattern ((t2tb63 (tb2t63 j))) )))

(declare-fun t2tb64 ((set (set (tuple2 (set uninterpreted_type)
  uninterpreted_type)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (set uninterpreted_type)
  uninterpreted_type))))) (sort
  (set1 (set1 (tuple21 (set1 uninterpreted_type1) uninterpreted_type1)))
  (t2tb64 x))))

(declare-fun tb2t64 (uni) (set (set (tuple2 (set uninterpreted_type)
  uninterpreted_type))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (set uninterpreted_type)
  uninterpreted_type)))))
  (! (= (tb2t64 (t2tb64 i)) i) :pattern ((t2tb64 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1 (set1 (tuple21 (set1 uninterpreted_type1) uninterpreted_type1)))
     j) (= (t2tb64 (tb2t64 j)) j)) :pattern ((t2tb64 (tb2t64 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (set uninterpreted_type)) (y uninterpreted_type)) (! (mem
  (set1 (tuple21 (set1 uninterpreted_type1) uninterpreted_type1))
  (add (tuple21 (set1 uninterpreted_type1) uninterpreted_type1)
  (Tuple2 (set1 uninterpreted_type1) uninterpreted_type1 (t2tb3 x) (t2tb4 y))
  (empty (tuple21 (set1 uninterpreted_type1) uninterpreted_type1)))
  (infix_mnmngt uninterpreted_type1 (set1 uninterpreted_type1)
  (t2tb2 (add3 x empty5)) (add uninterpreted_type1 (t2tb4 y) (t2tb3 empty4)))) :pattern (
  (tb2t62
  (add (tuple21 (set1 uninterpreted_type1) uninterpreted_type1)
  (Tuple2 (set1 uninterpreted_type1) uninterpreted_type1 (t2tb3 x) (t2tb4 y))
  (empty (tuple21 (set1 uninterpreted_type1) uninterpreted_type1))))) )))

(declare-fun t2tb65 ((set (set (tuple2 (set uninterpreted_type)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (set uninterpreted_type)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))))
  (sort
  (set1
  (set1
  (tuple21 (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (t2tb65 x))))

(declare-fun tb2t65 (uni) (set (set (tuple2 (set uninterpreted_type)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (set uninterpreted_type)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))))
  (! (= (tb2t65 (t2tb65 i)) i) :pattern ((t2tb65 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb65 (tb2t65 j)) j) :pattern ((t2tb65 (tb2t65 j))) )))

(declare-fun t2tb66 ((set (tuple2 (set uninterpreted_type)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (set uninterpreted_type)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))) (sort
  (set1
  (tuple21 (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (t2tb66 x))))

(declare-fun tb2t66 (uni) (set (tuple2 (set uninterpreted_type)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (set uninterpreted_type)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))))
  (! (= (tb2t66 (t2tb66 i)) i) :pattern ((t2tb66 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb66 (tb2t66 j)) j) :pattern ((t2tb66 (tb2t66 j))) )))

(declare-fun t2tb67 ((tuple2 (set uninterpreted_type)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (set uninterpreted_type)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))) (sort
  (tuple21 (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb67 x))))

(declare-fun tb2t67 (uni) (tuple2 (set uninterpreted_type)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))

;; BridgeL
  (assert
  (forall ((i (tuple2 (set uninterpreted_type)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))
  (! (= (tb2t67 (t2tb67 i)) i) :pattern ((t2tb67 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb67 (tb2t67 j)) j) :pattern ((t2tb67 (tb2t67 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (set uninterpreted_type))
  (y (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))
  (! (mem
  (set1
  (tuple21 (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (add
  (tuple21 (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (Tuple2 (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb3 x) (t2tb6 y))
  (empty
  (tuple21 (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (infix_mnmngt
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (set1 uninterpreted_type1) (t2tb2 (add3 x empty5))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb6 y) (t2tb5 empty3)))) :pattern ((tb2t66
                                        (add
                                        (tuple21 (set1 uninterpreted_type1)
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int)))
                                        (Tuple2 (set1 uninterpreted_type1)
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int)) (t2tb3 x)
                                        (t2tb6 y))
                                        (empty
                                        (tuple21 (set1 uninterpreted_type1)
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int))))))) )))

(declare-fun t2tb68 ((set (set (tuple2 (set uninterpreted_type)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (set uninterpreted_type)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))))) (sort
  (set1
  (set1
  (tuple21 (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))) (t2tb68 x))))

(declare-fun tb2t68 (uni) (set (set (tuple2 (set uninterpreted_type)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (set uninterpreted_type)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))))
  (! (= (tb2t68 (t2tb68 i)) i) :pattern ((t2tb68 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21 (set1 uninterpreted_type1)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))) j)
     (= (t2tb68 (tb2t68 j)) j)) :pattern ((t2tb68 (tb2t68 j))) )))

(declare-fun t2tb69 ((set (tuple2 (set uninterpreted_type)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (set uninterpreted_type)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))) (sort
  (set1
  (tuple21 (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))) (t2tb69 x))))

(declare-fun tb2t69 (uni) (set (tuple2 (set uninterpreted_type)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (set uninterpreted_type)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))))
  (! (= (tb2t69 (t2tb69 i)) i) :pattern ((t2tb69 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21 (set1 uninterpreted_type1)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool))) j)
     (= (t2tb69 (tb2t69 j)) j)) :pattern ((t2tb69 (tb2t69 j))) )))

(declare-fun t2tb70 ((tuple2 (set uninterpreted_type)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (set uninterpreted_type) (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool)))) (sort
  (tuple21 (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb70 x))))

(declare-fun tb2t70 (uni) (tuple2 (set uninterpreted_type)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (set uninterpreted_type) (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool)))) (! (= (tb2t70 (t2tb70 i)) i) :pattern ((t2tb70 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 (set1 uninterpreted_type1)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) j)
     (= (t2tb70 (tb2t70 j)) j)) :pattern ((t2tb70 (tb2t70 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (set uninterpreted_type)) (y (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool))) (! (mem
  (set1
  (tuple21 (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))
  (add
  (tuple21 (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (Tuple2 (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb3 x) (t2tb8 y))
  (empty
  (tuple21 (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))))
  (infix_mnmngt (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1) (t2tb2 (add3 x empty5)) (t2tb7 (add4 y empty7)))) :pattern (
  (tb2t69
  (add
  (tuple21 (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (Tuple2 (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb3 x) (t2tb8 y))
  (empty
  (tuple21 (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))))) )))

(declare-fun t2tb71 ((set (set (tuple2 (set uninterpreted_type)
  (tuple2 (tuple2 Bool Bool) Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (set uninterpreted_type) (tuple2 (tuple2 Bool
  Bool) Bool)))))) (sort
  (set1
  (set1
  (tuple21 (set1 uninterpreted_type1) (tuple21 (tuple21 bool bool) bool))))
  (t2tb71 x))))

(declare-fun tb2t71 (uni) (set (set (tuple2 (set uninterpreted_type)
  (tuple2 (tuple2 Bool Bool) Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (set uninterpreted_type) (tuple2 (tuple2 Bool
  Bool) Bool)))))) (! (= (tb2t71 (t2tb71 i)) i) :pattern ((t2tb71 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21 (set1 uninterpreted_type1) (tuple21 (tuple21 bool bool) bool))))
     j) (= (t2tb71 (tb2t71 j)) j)) :pattern ((t2tb71 (tb2t71 j))) )))

(declare-fun t2tb72 ((set (tuple2 (set uninterpreted_type)
  (tuple2 (tuple2 Bool Bool) Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (set uninterpreted_type) (tuple2 (tuple2 Bool
  Bool) Bool))))) (sort
  (set1
  (tuple21 (set1 uninterpreted_type1) (tuple21 (tuple21 bool bool) bool)))
  (t2tb72 x))))

(declare-fun tb2t72 (uni) (set (tuple2 (set uninterpreted_type)
  (tuple2 (tuple2 Bool Bool) Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (set uninterpreted_type) (tuple2 (tuple2 Bool
  Bool) Bool))))) (! (= (tb2t72 (t2tb72 i)) i) :pattern ((t2tb72 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21 (set1 uninterpreted_type1) (tuple21 (tuple21 bool bool) bool)))
     j) (= (t2tb72 (tb2t72 j)) j)) :pattern ((t2tb72 (tb2t72 j))) )))

(declare-fun t2tb73 ((tuple2 (set uninterpreted_type) (tuple2 (tuple2 Bool
  Bool) Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (set uninterpreted_type) (tuple2 (tuple2 Bool Bool)
  Bool)))) (sort
  (tuple21 (set1 uninterpreted_type1) (tuple21 (tuple21 bool bool) bool))
  (t2tb73 x))))

(declare-fun tb2t73 (uni) (tuple2 (set uninterpreted_type)
  (tuple2 (tuple2 Bool Bool) Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (set uninterpreted_type) (tuple2 (tuple2 Bool Bool)
  Bool)))) (! (= (tb2t73 (t2tb73 i)) i) :pattern ((t2tb73 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 (set1 uninterpreted_type1) (tuple21 (tuple21 bool bool) bool))
     j) (= (t2tb73 (tb2t73 j)) j)) :pattern ((t2tb73 (tb2t73 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (set uninterpreted_type)) (y (tuple2 (tuple2 Bool Bool) Bool)))
  (! (mem
  (set1
  (tuple21 (set1 uninterpreted_type1) (tuple21 (tuple21 bool bool) bool)))
  (add
  (tuple21 (set1 uninterpreted_type1) (tuple21 (tuple21 bool bool) bool))
  (Tuple2 (set1 uninterpreted_type1) (tuple21 (tuple21 bool bool) bool)
  (t2tb3 x) (t2tb10 y))
  (empty
  (tuple21 (set1 uninterpreted_type1) (tuple21 (tuple21 bool bool) bool))))
  (infix_mnmngt (tuple21 (tuple21 bool bool) bool) (set1 uninterpreted_type1)
  (t2tb2 (add3 x empty5)) (t2tb9 (add5 y empty8)))) :pattern ((tb2t72
                                                              (add
                                                              (tuple21
                                                              (set1
                                                              uninterpreted_type1)
                                                              (tuple21
                                                              (tuple21 
                                                              bool bool)
                                                              bool))
                                                              (Tuple2
                                                              (set1
                                                              uninterpreted_type1)
                                                              (tuple21
                                                              (tuple21 
                                                              bool bool)
                                                              bool) (t2tb3 x)
                                                              (t2tb10 y))
                                                              (empty
                                                              (tuple21
                                                              (set1
                                                              uninterpreted_type1)
                                                              (tuple21
                                                              (tuple21 
                                                              bool bool)
                                                              bool)))))) )))

(declare-fun t2tb74 ((set (set (tuple2 (set uninterpreted_type) (tuple2 Bool
  Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (set uninterpreted_type) (tuple2 Bool
  Bool)))))) (sort
  (set1 (set1 (tuple21 (set1 uninterpreted_type1) (tuple21 bool bool))))
  (t2tb74 x))))

(declare-fun tb2t74 (uni) (set (set (tuple2 (set uninterpreted_type)
  (tuple2 Bool Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (set uninterpreted_type) (tuple2 Bool
  Bool)))))) (! (= (tb2t74 (t2tb74 i)) i) :pattern ((t2tb74 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1 (set1 (tuple21 (set1 uninterpreted_type1) (tuple21 bool bool))))
     j) (= (t2tb74 (tb2t74 j)) j)) :pattern ((t2tb74 (tb2t74 j))) )))

(declare-fun t2tb75 ((set (tuple2 (set uninterpreted_type) (tuple2 Bool
  Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (set uninterpreted_type) (tuple2 Bool Bool)))))
  (sort (set1 (tuple21 (set1 uninterpreted_type1) (tuple21 bool bool)))
  (t2tb75 x))))

(declare-fun tb2t75 (uni) (set (tuple2 (set uninterpreted_type) (tuple2 Bool
  Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (set uninterpreted_type) (tuple2 Bool Bool)))))
  (! (= (tb2t75 (t2tb75 i)) i) :pattern ((t2tb75 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1 (tuple21 (set1 uninterpreted_type1) (tuple21 bool bool))) j)
     (= (t2tb75 (tb2t75 j)) j)) :pattern ((t2tb75 (tb2t75 j))) )))

(declare-fun t2tb76 ((tuple2 (set uninterpreted_type) (tuple2 Bool
  Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (set uninterpreted_type) (tuple2 Bool Bool)))) (sort
  (tuple21 (set1 uninterpreted_type1) (tuple21 bool bool)) (t2tb76 x))))

(declare-fun tb2t76 (uni) (tuple2 (set uninterpreted_type) (tuple2 Bool
  Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (set uninterpreted_type) (tuple2 Bool Bool))))
  (! (= (tb2t76 (t2tb76 i)) i) :pattern ((t2tb76 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (tuple21 (set1 uninterpreted_type1) (tuple21 bool bool)) j)
     (= (t2tb76 (tb2t76 j)) j)) :pattern ((t2tb76 (tb2t76 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (set uninterpreted_type)) (y (tuple2 Bool Bool))) (! (mem
  (set1 (tuple21 (set1 uninterpreted_type1) (tuple21 bool bool)))
  (add (tuple21 (set1 uninterpreted_type1) (tuple21 bool bool))
  (Tuple2 (set1 uninterpreted_type1) (tuple21 bool bool) (t2tb3 x)
  (t2tb12 y))
  (empty (tuple21 (set1 uninterpreted_type1) (tuple21 bool bool))))
  (infix_mnmngt (tuple21 bool bool) (set1 uninterpreted_type1)
  (t2tb2 (add3 x empty5)) (t2tb11 (add6 y empty9)))) :pattern ((tb2t75
                                                               (add
                                                               (tuple21
                                                               (set1
                                                               uninterpreted_type1)
                                                               (tuple21 
                                                               bool bool))
                                                               (Tuple2
                                                               (set1
                                                               uninterpreted_type1)
                                                               (tuple21 
                                                               bool bool)
                                                               (t2tb3 x)
                                                               (t2tb12 y))
                                                               (empty
                                                               (tuple21
                                                               (set1
                                                               uninterpreted_type1)
                                                               (tuple21 
                                                               bool bool)))))) )))

(declare-fun t2tb77 ((tuple2 (set uninterpreted_type) Bool)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (set uninterpreted_type) Bool))) (sort
  (tuple21 (set1 uninterpreted_type1) bool) (t2tb77 x))))

(declare-fun tb2t77 (uni) (tuple2 (set uninterpreted_type) Bool))

;; BridgeL
  (assert
  (forall ((i (tuple2 (set uninterpreted_type) Bool)))
  (! (= (tb2t77 (t2tb77 i)) i) :pattern ((t2tb77 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (tuple21 (set1 uninterpreted_type1) bool) j)
     (= (t2tb77 (tb2t77 j)) j)) :pattern ((t2tb77 (tb2t77 j))) )))

(declare-fun t2tb78 ((set (set (tuple2 (set uninterpreted_type) Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (set uninterpreted_type) Bool))))) (sort
  (set1 (set1 (tuple21 (set1 uninterpreted_type1) bool))) (t2tb78 x))))

(declare-fun tb2t78 (uni) (set (set (tuple2 (set uninterpreted_type) Bool))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (set uninterpreted_type) Bool)))))
  (! (= (tb2t78 (t2tb78 i)) i) :pattern ((t2tb78 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (set1 (tuple21 (set1 uninterpreted_type1) bool))) j)
     (= (t2tb78 (tb2t78 j)) j)) :pattern ((t2tb78 (tb2t78 j))) )))

(declare-fun t2tb79 ((set (tuple2 (set uninterpreted_type) Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (set uninterpreted_type) Bool)))) (sort
  (set1 (tuple21 (set1 uninterpreted_type1) bool)) (t2tb79 x))))

(declare-fun tb2t79 (uni) (set (tuple2 (set uninterpreted_type) Bool)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (set uninterpreted_type) Bool))))
  (! (= (tb2t79 (t2tb79 i)) i) :pattern ((t2tb79 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (tuple21 (set1 uninterpreted_type1) bool)) j)
     (= (t2tb79 (tb2t79 j)) j)) :pattern ((t2tb79 (tb2t79 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (set uninterpreted_type)) (y Bool)) (! (mem
  (set1 (tuple21 (set1 uninterpreted_type1) bool))
  (add (tuple21 (set1 uninterpreted_type1) bool)
  (Tuple2 (set1 uninterpreted_type1) bool (t2tb3 x) (t2tb13 y))
  (empty (tuple21 (set1 uninterpreted_type1) bool)))
  (infix_mnmngt bool (set1 uninterpreted_type1) (t2tb2 (add3 x empty5))
  (t2tb14 (add1 y empty1)))) :pattern ((tb2t79
                                       (add
                                       (tuple21 (set1 uninterpreted_type1)
                                       bool)
                                       (Tuple2 (set1 uninterpreted_type1)
                                       bool (t2tb3 x) (t2tb13 y))
                                       (empty
                                       (tuple21 (set1 uninterpreted_type1)
                                       bool))))) )))

(declare-fun t2tb80 ((set (set (tuple2 (set uninterpreted_type) Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (set uninterpreted_type) Int))))) (sort
  (set1 (set1 (tuple21 (set1 uninterpreted_type1) int))) (t2tb80 x))))

(declare-fun tb2t80 (uni) (set (set (tuple2 (set uninterpreted_type) Int))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (set uninterpreted_type) Int)))))
  (! (= (tb2t80 (t2tb80 i)) i) :pattern ((t2tb80 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb80 (tb2t80 j)) j) :pattern ((t2tb80 (tb2t80 j))) )))

(declare-fun t2tb81 ((set (tuple2 (set uninterpreted_type) Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (set uninterpreted_type) Int)))) (sort
  (set1 (tuple21 (set1 uninterpreted_type1) int)) (t2tb81 x))))

(declare-fun tb2t81 (uni) (set (tuple2 (set uninterpreted_type) Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (set uninterpreted_type) Int))))
  (! (= (tb2t81 (t2tb81 i)) i) :pattern ((t2tb81 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb81 (tb2t81 j)) j) :pattern ((t2tb81 (tb2t81 j))) )))

(declare-fun t2tb82 ((tuple2 (set uninterpreted_type) Int)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (set uninterpreted_type) Int))) (sort
  (tuple21 (set1 uninterpreted_type1) int) (t2tb82 x))))

(declare-fun tb2t82 (uni) (tuple2 (set uninterpreted_type) Int))

;; BridgeL
  (assert
  (forall ((i (tuple2 (set uninterpreted_type) Int)))
  (! (= (tb2t82 (t2tb82 i)) i) :pattern ((t2tb82 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb82 (tb2t82 j)) j) :pattern ((t2tb82 (tb2t82 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (set uninterpreted_type)) (y Int)) (! (mem
  (set1 (tuple21 (set1 uninterpreted_type1) int))
  (add (tuple21 (set1 uninterpreted_type1) int)
  (Tuple2 (set1 uninterpreted_type1) int (t2tb3 x) (t2tb16 y))
  (empty (tuple21 (set1 uninterpreted_type1) int)))
  (infix_mnmngt int (set1 uninterpreted_type1) (t2tb2 (add3 x empty5))
  (t2tb15 (add2 y empty2)))) :pattern ((tb2t81
                                       (add
                                       (tuple21 (set1 uninterpreted_type1)
                                       int)
                                       (Tuple2 (set1 uninterpreted_type1) 
                                       int (t2tb3 x) (t2tb16 y))
                                       (empty
                                       (tuple21 (set1 uninterpreted_type1)
                                       int))))) )))

;; singleton_is_function
  (assert
  (forall ((b ty))
  (forall ((x (set uninterpreted_type)) (y uni)) (! (mem
  (set1 (tuple21 (set1 uninterpreted_type1) b))
  (add (tuple21 (set1 uninterpreted_type1) b)
  (Tuple2 (set1 uninterpreted_type1) b (t2tb3 x) y)
  (empty (tuple21 (set1 uninterpreted_type1) b)))
  (infix_mnmngt b (set1 uninterpreted_type1) (t2tb2 (add3 x empty5))
  (add b y (empty b)))) :pattern ((add (tuple21 (set1 uninterpreted_type1) b)
                                  (Tuple2 (set1 uninterpreted_type1) b
                                  (t2tb3 x) y)
                                  (empty
                                  (tuple21 (set1 uninterpreted_type1) b)))) ))))

(declare-fun t2tb83 ((set (set (tuple2 uninterpreted_type
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 uninterpreted_type
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))))))) (sort
  (set1
  (set1
  (tuple21 uninterpreted_type1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))))) (t2tb83 x))))

(declare-fun tb2t83 (uni) (set (set (tuple2 uninterpreted_type
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 uninterpreted_type
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))))))
  (! (= (tb2t83 (t2tb83 i)) i) :pattern ((t2tb83 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21 uninterpreted_type1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1))))) j) (= (t2tb83 (tb2t83 j)) j)) :pattern (
  (t2tb83 (tb2t83 j))) )))

(declare-fun t2tb84 ((set (tuple2 uninterpreted_type
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 uninterpreted_type
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))))) (sort
  (set1
  (tuple21 uninterpreted_type1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)))) (t2tb84 x))))

(declare-fun tb2t84 (uni) (set (tuple2 uninterpreted_type
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 uninterpreted_type
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))))))
  (! (= (tb2t84 (t2tb84 i)) i) :pattern ((t2tb84 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21 uninterpreted_type1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1)))) j) (= (t2tb84 (tb2t84 j)) j)) :pattern (
  (t2tb84 (tb2t84 j))) )))

(declare-fun t2tb85 ((tuple2 uninterpreted_type
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 uninterpreted_type (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type))))) (sort
  (tuple21 uninterpreted_type1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))) (t2tb85 x))))

(declare-fun tb2t85 (uni) (tuple2 uninterpreted_type
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))))

;; BridgeL
  (assert
  (forall ((i (tuple2 uninterpreted_type (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type)))))
  (! (= (tb2t85 (t2tb85 i)) i) :pattern ((t2tb85 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 uninterpreted_type1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1))) j) (= (t2tb85 (tb2t85 j)) j)) :pattern (
  (t2tb85 (tb2t85 j))) )))

;; singleton_is_function
  (assert
  (forall ((x uninterpreted_type) (y (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type)))) (! (mem
  (set1
  (tuple21 uninterpreted_type1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))))
  (add
  (tuple21 uninterpreted_type1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)))
  (Tuple2 uninterpreted_type1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb4 x) (t2tb1 y))
  (empty
  (tuple21 uninterpreted_type1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)))))
  (infix_mnmngt
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) uninterpreted_type1
  (add uninterpreted_type1 (t2tb4 x) (t2tb3 empty4))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb1 y) (t2tb empty6)))) :pattern ((tb2t84
                                                                   (add
                                                                   (tuple21
                                                                   uninterpreted_type1
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   bool 
                                                                   bool)
                                                                   bool)
                                                                   bool)
                                                                   (set1
                                                                   uninterpreted_type1)))
                                                                   (Tuple2
                                                                   uninterpreted_type1
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   bool 
                                                                   bool)
                                                                   bool)
                                                                   bool)
                                                                   (set1
                                                                   uninterpreted_type1))
                                                                   (t2tb4 x)
                                                                   (t2tb1 y))
                                                                   (empty
                                                                   (tuple21
                                                                   uninterpreted_type1
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   bool 
                                                                   bool)
                                                                   bool)
                                                                   bool)
                                                                   (set1
                                                                   uninterpreted_type1))))))) )))

(declare-fun t2tb86 ((set (set (tuple2 uninterpreted_type
  (set uninterpreted_type))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 uninterpreted_type
  (set uninterpreted_type)))))) (sort
  (set1 (set1 (tuple21 uninterpreted_type1 (set1 uninterpreted_type1))))
  (t2tb86 x))))

(declare-fun tb2t86 (uni) (set (set (tuple2 uninterpreted_type
  (set uninterpreted_type)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 uninterpreted_type
  (set uninterpreted_type))))))
  (! (= (tb2t86 (t2tb86 i)) i) :pattern ((t2tb86 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1 (set1 (tuple21 uninterpreted_type1 (set1 uninterpreted_type1))))
     j) (= (t2tb86 (tb2t86 j)) j)) :pattern ((t2tb86 (tb2t86 j))) )))

(declare-fun t2tb87 ((set (tuple2 uninterpreted_type
  (set uninterpreted_type)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 uninterpreted_type (set uninterpreted_type)))))
  (sort (set1 (tuple21 uninterpreted_type1 (set1 uninterpreted_type1)))
  (t2tb87 x))))

(declare-fun tb2t87 (uni) (set (tuple2 uninterpreted_type
  (set uninterpreted_type))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 uninterpreted_type (set uninterpreted_type)))))
  (! (= (tb2t87 (t2tb87 i)) i) :pattern ((t2tb87 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1 (tuple21 uninterpreted_type1 (set1 uninterpreted_type1))) j)
     (= (t2tb87 (tb2t87 j)) j)) :pattern ((t2tb87 (tb2t87 j))) )))

(declare-fun t2tb88 ((tuple2 uninterpreted_type
  (set uninterpreted_type))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 uninterpreted_type (set uninterpreted_type)))) (sort
  (tuple21 uninterpreted_type1 (set1 uninterpreted_type1)) (t2tb88 x))))

(declare-fun tb2t88 (uni) (tuple2 uninterpreted_type
  (set uninterpreted_type)))

;; BridgeL
  (assert
  (forall ((i (tuple2 uninterpreted_type (set uninterpreted_type))))
  (! (= (tb2t88 (t2tb88 i)) i) :pattern ((t2tb88 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (tuple21 uninterpreted_type1 (set1 uninterpreted_type1)) j)
     (= (t2tb88 (tb2t88 j)) j)) :pattern ((t2tb88 (tb2t88 j))) )))

;; singleton_is_function
  (assert
  (forall ((x uninterpreted_type) (y (set uninterpreted_type))) (! (mem
  (set1 (tuple21 uninterpreted_type1 (set1 uninterpreted_type1)))
  (add (tuple21 uninterpreted_type1 (set1 uninterpreted_type1))
  (Tuple2 uninterpreted_type1 (set1 uninterpreted_type1) (t2tb4 x) (t2tb3 y))
  (empty (tuple21 uninterpreted_type1 (set1 uninterpreted_type1))))
  (infix_mnmngt (set1 uninterpreted_type1) uninterpreted_type1
  (add uninterpreted_type1 (t2tb4 x) (t2tb3 empty4)) (t2tb2 (add3 y empty5)))) :pattern (
  (tb2t87
  (add (tuple21 uninterpreted_type1 (set1 uninterpreted_type1))
  (Tuple2 uninterpreted_type1 (set1 uninterpreted_type1) (t2tb4 x) (t2tb3 y))
  (empty (tuple21 uninterpreted_type1 (set1 uninterpreted_type1)))))) )))

(declare-fun t2tb89 ((set (set (tuple2 uninterpreted_type
  uninterpreted_type)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 uninterpreted_type uninterpreted_type)))))
  (sort (set1 (set1 (tuple21 uninterpreted_type1 uninterpreted_type1)))
  (t2tb89 x))))

(declare-fun tb2t89 (uni) (set (set (tuple2 uninterpreted_type
  uninterpreted_type))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 uninterpreted_type uninterpreted_type)))))
  (! (= (tb2t89 (t2tb89 i)) i) :pattern ((t2tb89 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1 (set1 (tuple21 uninterpreted_type1 uninterpreted_type1))) j)
     (= (t2tb89 (tb2t89 j)) j)) :pattern ((t2tb89 (tb2t89 j))) )))

(declare-fun t2tb90 ((set (tuple2 uninterpreted_type
  uninterpreted_type))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 uninterpreted_type uninterpreted_type)))) (sort
  (set1 (tuple21 uninterpreted_type1 uninterpreted_type1)) (t2tb90 x))))

(declare-fun tb2t90 (uni) (set (tuple2 uninterpreted_type
  uninterpreted_type)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 uninterpreted_type uninterpreted_type))))
  (! (= (tb2t90 (t2tb90 i)) i) :pattern ((t2tb90 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (tuple21 uninterpreted_type1 uninterpreted_type1)) j)
     (= (t2tb90 (tb2t90 j)) j)) :pattern ((t2tb90 (tb2t90 j))) )))

(declare-fun t2tb91 ((tuple2 uninterpreted_type uninterpreted_type)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 uninterpreted_type uninterpreted_type))) (sort
  (tuple21 uninterpreted_type1 uninterpreted_type1) (t2tb91 x))))

(declare-fun tb2t91 (uni) (tuple2 uninterpreted_type uninterpreted_type))

;; BridgeL
  (assert
  (forall ((i (tuple2 uninterpreted_type uninterpreted_type)))
  (! (= (tb2t91 (t2tb91 i)) i) :pattern ((t2tb91 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (tuple21 uninterpreted_type1 uninterpreted_type1) j)
     (= (t2tb91 (tb2t91 j)) j)) :pattern ((t2tb91 (tb2t91 j))) )))

;; singleton_is_function
  (assert
  (forall ((x uninterpreted_type) (y uninterpreted_type)) (! (mem
  (set1 (tuple21 uninterpreted_type1 uninterpreted_type1))
  (add (tuple21 uninterpreted_type1 uninterpreted_type1)
  (Tuple2 uninterpreted_type1 uninterpreted_type1 (t2tb4 x) (t2tb4 y))
  (empty (tuple21 uninterpreted_type1 uninterpreted_type1)))
  (infix_mnmngt uninterpreted_type1 uninterpreted_type1
  (add uninterpreted_type1 (t2tb4 x) (t2tb3 empty4))
  (add uninterpreted_type1 (t2tb4 y) (t2tb3 empty4)))) :pattern ((tb2t90
                                                                 (add
                                                                 (tuple21
                                                                 uninterpreted_type1
                                                                 uninterpreted_type1)
                                                                 (Tuple2
                                                                 uninterpreted_type1
                                                                 uninterpreted_type1
                                                                 (t2tb4 x)
                                                                 (t2tb4 y))
                                                                 (empty
                                                                 (tuple21
                                                                 uninterpreted_type1
                                                                 uninterpreted_type1))))) )))

(declare-fun t2tb92 ((tuple2 uninterpreted_type
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 uninterpreted_type (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))) (sort
  (tuple21 uninterpreted_type1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb92 x))))

(declare-fun tb2t92 (uni) (tuple2 uninterpreted_type
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))

;; BridgeL
  (assert
  (forall ((i (tuple2 uninterpreted_type (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))))
  (! (= (tb2t92 (t2tb92 i)) i) :pattern ((t2tb92 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb92 (tb2t92 j)) j) :pattern ((t2tb92 (tb2t92 j))) )))

(declare-fun t2tb93 ((set (set (tuple2 uninterpreted_type
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 uninterpreted_type
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))))
  (sort
  (set1
  (set1
  (tuple21 uninterpreted_type1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (t2tb93 x))))

(declare-fun tb2t93 (uni) (set (set (tuple2 uninterpreted_type
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 uninterpreted_type
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))))
  (! (= (tb2t93 (t2tb93 i)) i) :pattern ((t2tb93 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb93 (tb2t93 j)) j) :pattern ((t2tb93 (tb2t93 j))) )))

(declare-fun t2tb94 ((set (tuple2 uninterpreted_type
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 uninterpreted_type
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))) (sort
  (set1
  (tuple21 uninterpreted_type1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (t2tb94 x))))

(declare-fun tb2t94 (uni) (set (tuple2 uninterpreted_type
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 uninterpreted_type
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))))
  (! (= (tb2t94 (t2tb94 i)) i) :pattern ((t2tb94 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb94 (tb2t94 j)) j) :pattern ((t2tb94 (tb2t94 j))) )))

;; singleton_is_function
  (assert
  (forall ((x uninterpreted_type) (y (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))) (! (mem
  (set1
  (tuple21 uninterpreted_type1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (add
  (tuple21 uninterpreted_type1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (Tuple2 uninterpreted_type1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb4 x) (t2tb6 y))
  (empty
  (tuple21 uninterpreted_type1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (infix_mnmngt
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  uninterpreted_type1 (add uninterpreted_type1 (t2tb4 x) (t2tb3 empty4))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb6 y) (t2tb5 empty3)))) :pattern ((tb2t94
                                        (add
                                        (tuple21 uninterpreted_type1
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int)))
                                        (Tuple2 uninterpreted_type1
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int)) (t2tb4 x)
                                        (t2tb6 y))
                                        (empty
                                        (tuple21 uninterpreted_type1
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int))))))) )))

(declare-fun t2tb95 ((set (set (tuple2 uninterpreted_type
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 uninterpreted_type
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))))) (sort
  (set1
  (set1
  (tuple21 uninterpreted_type1
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))) (t2tb95 x))))

(declare-fun tb2t95 (uni) (set (set (tuple2 uninterpreted_type
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 uninterpreted_type
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))))
  (! (= (tb2t95 (t2tb95 i)) i) :pattern ((t2tb95 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21 uninterpreted_type1
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))) j)
     (= (t2tb95 (tb2t95 j)) j)) :pattern ((t2tb95 (tb2t95 j))) )))

(declare-fun t2tb96 ((set (tuple2 uninterpreted_type
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 uninterpreted_type (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool))))) (sort
  (set1
  (tuple21 uninterpreted_type1
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))) (t2tb96 x))))

(declare-fun tb2t96 (uni) (set (tuple2 uninterpreted_type
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 uninterpreted_type (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool))))) (! (= (tb2t96 (t2tb96 i)) i) :pattern ((t2tb96 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21 uninterpreted_type1
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool))) j)
     (= (t2tb96 (tb2t96 j)) j)) :pattern ((t2tb96 (tb2t96 j))) )))

(declare-fun t2tb97 ((tuple2 uninterpreted_type (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 uninterpreted_type (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool)))) (sort
  (tuple21 uninterpreted_type1
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb97 x))))

(declare-fun tb2t97 (uni) (tuple2 uninterpreted_type
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 uninterpreted_type (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool)))) (! (= (tb2t97 (t2tb97 i)) i) :pattern ((t2tb97 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 uninterpreted_type1
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) j)
     (= (t2tb97 (tb2t97 j)) j)) :pattern ((t2tb97 (tb2t97 j))) )))

;; singleton_is_function
  (assert
  (forall ((x uninterpreted_type) (y (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))) (! (mem
  (set1
  (tuple21 uninterpreted_type1
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))
  (add
  (tuple21 uninterpreted_type1
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (Tuple2 uninterpreted_type1
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb4 x) (t2tb8 y))
  (empty
  (tuple21 uninterpreted_type1
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))))
  (infix_mnmngt (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  uninterpreted_type1 (add uninterpreted_type1 (t2tb4 x) (t2tb3 empty4))
  (t2tb7 (add4 y empty7)))) :pattern ((tb2t96
                                      (add
                                      (tuple21 uninterpreted_type1
                                      (tuple21
                                      (tuple21 (tuple21 bool bool) bool)
                                      bool))
                                      (Tuple2 uninterpreted_type1
                                      (tuple21
                                      (tuple21 (tuple21 bool bool) bool)
                                      bool) (t2tb4 x) (t2tb8 y))
                                      (empty
                                      (tuple21 uninterpreted_type1
                                      (tuple21
                                      (tuple21 (tuple21 bool bool) bool)
                                      bool)))))) )))

(declare-fun t2tb98 ((set (set (tuple2 uninterpreted_type
  (tuple2 (tuple2 Bool Bool) Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 uninterpreted_type (tuple2 (tuple2 Bool Bool)
  Bool)))))) (sort
  (set1
  (set1 (tuple21 uninterpreted_type1 (tuple21 (tuple21 bool bool) bool))))
  (t2tb98 x))))

(declare-fun tb2t98 (uni) (set (set (tuple2 uninterpreted_type
  (tuple2 (tuple2 Bool Bool) Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 uninterpreted_type (tuple2 (tuple2 Bool Bool)
  Bool)))))) (! (= (tb2t98 (t2tb98 i)) i) :pattern ((t2tb98 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1 (tuple21 uninterpreted_type1 (tuple21 (tuple21 bool bool) bool))))
     j) (= (t2tb98 (tb2t98 j)) j)) :pattern ((t2tb98 (tb2t98 j))) )))

(declare-fun t2tb99 ((set (tuple2 uninterpreted_type (tuple2 (tuple2 Bool
  Bool) Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 uninterpreted_type (tuple2 (tuple2 Bool Bool)
  Bool))))) (sort
  (set1 (tuple21 uninterpreted_type1 (tuple21 (tuple21 bool bool) bool)))
  (t2tb99 x))))

(declare-fun tb2t99 (uni) (set (tuple2 uninterpreted_type
  (tuple2 (tuple2 Bool Bool) Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 uninterpreted_type (tuple2 (tuple2 Bool Bool)
  Bool))))) (! (= (tb2t99 (t2tb99 i)) i) :pattern ((t2tb99 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1 (tuple21 uninterpreted_type1 (tuple21 (tuple21 bool bool) bool)))
     j) (= (t2tb99 (tb2t99 j)) j)) :pattern ((t2tb99 (tb2t99 j))) )))

(declare-fun t2tb100 ((tuple2 uninterpreted_type (tuple2 (tuple2 Bool Bool)
  Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 uninterpreted_type (tuple2 (tuple2 Bool Bool) Bool))))
  (sort (tuple21 uninterpreted_type1 (tuple21 (tuple21 bool bool) bool))
  (t2tb100 x))))

(declare-fun tb2t100 (uni) (tuple2 uninterpreted_type (tuple2 (tuple2 Bool
  Bool) Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 uninterpreted_type (tuple2 (tuple2 Bool Bool) Bool))))
  (! (= (tb2t100 (t2tb100 i)) i) :pattern ((t2tb100 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 uninterpreted_type1 (tuple21 (tuple21 bool bool) bool)) j)
     (= (t2tb100 (tb2t100 j)) j)) :pattern ((t2tb100 (tb2t100 j))) )))

;; singleton_is_function
  (assert
  (forall ((x uninterpreted_type) (y (tuple2 (tuple2 Bool Bool) Bool)))
  (! (mem
  (set1 (tuple21 uninterpreted_type1 (tuple21 (tuple21 bool bool) bool)))
  (add (tuple21 uninterpreted_type1 (tuple21 (tuple21 bool bool) bool))
  (Tuple2 uninterpreted_type1 (tuple21 (tuple21 bool bool) bool) (t2tb4 x)
  (t2tb10 y))
  (empty (tuple21 uninterpreted_type1 (tuple21 (tuple21 bool bool) bool))))
  (infix_mnmngt (tuple21 (tuple21 bool bool) bool) uninterpreted_type1
  (add uninterpreted_type1 (t2tb4 x) (t2tb3 empty4)) (t2tb9 (add5 y empty8)))) :pattern (
  (tb2t99
  (add (tuple21 uninterpreted_type1 (tuple21 (tuple21 bool bool) bool))
  (Tuple2 uninterpreted_type1 (tuple21 (tuple21 bool bool) bool) (t2tb4 x)
  (t2tb10 y))
  (empty (tuple21 uninterpreted_type1 (tuple21 (tuple21 bool bool) bool)))))) )))

(declare-fun t2tb101 ((set (set (tuple2 uninterpreted_type (tuple2 Bool
  Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 uninterpreted_type (tuple2 Bool Bool))))))
  (sort (set1 (set1 (tuple21 uninterpreted_type1 (tuple21 bool bool))))
  (t2tb101 x))))

(declare-fun tb2t101 (uni) (set (set (tuple2 uninterpreted_type (tuple2 Bool
  Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 uninterpreted_type (tuple2 Bool Bool))))))
  (! (= (tb2t101 (t2tb101 i)) i) :pattern ((t2tb101 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1 (set1 (tuple21 uninterpreted_type1 (tuple21 bool bool)))) j)
     (= (t2tb101 (tb2t101 j)) j)) :pattern ((t2tb101 (tb2t101 j))) )))

(declare-fun t2tb102 ((set (tuple2 uninterpreted_type (tuple2 Bool
  Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 uninterpreted_type (tuple2 Bool Bool))))) (sort
  (set1 (tuple21 uninterpreted_type1 (tuple21 bool bool))) (t2tb102 x))))

(declare-fun tb2t102 (uni) (set (tuple2 uninterpreted_type (tuple2 Bool
  Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 uninterpreted_type (tuple2 Bool Bool)))))
  (! (= (tb2t102 (t2tb102 i)) i) :pattern ((t2tb102 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (tuple21 uninterpreted_type1 (tuple21 bool bool))) j)
     (= (t2tb102 (tb2t102 j)) j)) :pattern ((t2tb102 (tb2t102 j))) )))

(declare-fun t2tb103 ((tuple2 uninterpreted_type (tuple2 Bool Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 uninterpreted_type (tuple2 Bool Bool)))) (sort
  (tuple21 uninterpreted_type1 (tuple21 bool bool)) (t2tb103 x))))

(declare-fun tb2t103 (uni) (tuple2 uninterpreted_type (tuple2 Bool Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 uninterpreted_type (tuple2 Bool Bool))))
  (! (= (tb2t103 (t2tb103 i)) i) :pattern ((t2tb103 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (tuple21 uninterpreted_type1 (tuple21 bool bool)) j)
     (= (t2tb103 (tb2t103 j)) j)) :pattern ((t2tb103 (tb2t103 j))) )))

;; singleton_is_function
  (assert
  (forall ((x uninterpreted_type) (y (tuple2 Bool Bool))) (! (mem
  (set1 (tuple21 uninterpreted_type1 (tuple21 bool bool)))
  (add (tuple21 uninterpreted_type1 (tuple21 bool bool))
  (Tuple2 uninterpreted_type1 (tuple21 bool bool) (t2tb4 x) (t2tb12 y))
  (empty (tuple21 uninterpreted_type1 (tuple21 bool bool))))
  (infix_mnmngt (tuple21 bool bool) uninterpreted_type1
  (add uninterpreted_type1 (t2tb4 x) (t2tb3 empty4))
  (t2tb11 (add6 y empty9)))) :pattern ((tb2t102
                                       (add
                                       (tuple21 uninterpreted_type1
                                       (tuple21 bool bool))
                                       (Tuple2 uninterpreted_type1
                                       (tuple21 bool bool) (t2tb4 x)
                                       (t2tb12 y))
                                       (empty
                                       (tuple21 uninterpreted_type1
                                       (tuple21 bool bool)))))) )))

(declare-fun t2tb104 ((set (set (tuple2 uninterpreted_type Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 uninterpreted_type Bool))))) (sort
  (set1 (set1 (tuple21 uninterpreted_type1 bool))) (t2tb104 x))))

(declare-fun tb2t104 (uni) (set (set (tuple2 uninterpreted_type Bool))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 uninterpreted_type Bool)))))
  (! (= (tb2t104 (t2tb104 i)) i) :pattern ((t2tb104 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (set1 (tuple21 uninterpreted_type1 bool))) j)
     (= (t2tb104 (tb2t104 j)) j)) :pattern ((t2tb104 (tb2t104 j))) )))

(declare-fun t2tb105 ((set (tuple2 uninterpreted_type Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 uninterpreted_type Bool)))) (sort
  (set1 (tuple21 uninterpreted_type1 bool)) (t2tb105 x))))

(declare-fun tb2t105 (uni) (set (tuple2 uninterpreted_type Bool)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 uninterpreted_type Bool))))
  (! (= (tb2t105 (t2tb105 i)) i) :pattern ((t2tb105 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (tuple21 uninterpreted_type1 bool)) j)
     (= (t2tb105 (tb2t105 j)) j)) :pattern ((t2tb105 (tb2t105 j))) )))

(declare-fun t2tb106 ((tuple2 uninterpreted_type Bool)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 uninterpreted_type Bool))) (sort
  (tuple21 uninterpreted_type1 bool) (t2tb106 x))))

(declare-fun tb2t106 (uni) (tuple2 uninterpreted_type Bool))

;; BridgeL
  (assert
  (forall ((i (tuple2 uninterpreted_type Bool)))
  (! (= (tb2t106 (t2tb106 i)) i) :pattern ((t2tb106 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (tuple21 uninterpreted_type1 bool) j)
     (= (t2tb106 (tb2t106 j)) j)) :pattern ((t2tb106 (tb2t106 j))) )))

;; singleton_is_function
  (assert
  (forall ((x uninterpreted_type) (y Bool)) (! (mem
  (set1 (tuple21 uninterpreted_type1 bool))
  (add (tuple21 uninterpreted_type1 bool)
  (Tuple2 uninterpreted_type1 bool (t2tb4 x) (t2tb13 y))
  (empty (tuple21 uninterpreted_type1 bool)))
  (infix_mnmngt bool uninterpreted_type1
  (add uninterpreted_type1 (t2tb4 x) (t2tb3 empty4))
  (t2tb14 (add1 y empty1)))) :pattern ((tb2t105
                                       (add
                                       (tuple21 uninterpreted_type1 bool)
                                       (Tuple2 uninterpreted_type1 bool
                                       (t2tb4 x) (t2tb13 y))
                                       (empty
                                       (tuple21 uninterpreted_type1 bool))))) )))

(declare-fun t2tb107 ((set (set (tuple2 uninterpreted_type Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 uninterpreted_type Int))))) (sort
  (set1 (set1 (tuple21 uninterpreted_type1 int))) (t2tb107 x))))

(declare-fun tb2t107 (uni) (set (set (tuple2 uninterpreted_type Int))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 uninterpreted_type Int)))))
  (! (= (tb2t107 (t2tb107 i)) i) :pattern ((t2tb107 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb107 (tb2t107 j)) j) :pattern ((t2tb107 (tb2t107 j))) )))

(declare-fun t2tb108 ((set (tuple2 uninterpreted_type Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 uninterpreted_type Int)))) (sort
  (set1 (tuple21 uninterpreted_type1 int)) (t2tb108 x))))

(declare-fun tb2t108 (uni) (set (tuple2 uninterpreted_type Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 uninterpreted_type Int))))
  (! (= (tb2t108 (t2tb108 i)) i) :pattern ((t2tb108 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb108 (tb2t108 j)) j) :pattern ((t2tb108 (tb2t108 j))) )))

(declare-fun t2tb109 ((tuple2 uninterpreted_type Int)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 uninterpreted_type Int))) (sort
  (tuple21 uninterpreted_type1 int) (t2tb109 x))))

(declare-fun tb2t109 (uni) (tuple2 uninterpreted_type Int))

;; BridgeL
  (assert
  (forall ((i (tuple2 uninterpreted_type Int)))
  (! (= (tb2t109 (t2tb109 i)) i) :pattern ((t2tb109 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb109 (tb2t109 j)) j) :pattern ((t2tb109 (tb2t109 j))) )))

;; singleton_is_function
  (assert
  (forall ((x uninterpreted_type) (y Int)) (! (mem
  (set1 (tuple21 uninterpreted_type1 int))
  (add (tuple21 uninterpreted_type1 int)
  (Tuple2 uninterpreted_type1 int (t2tb4 x) (t2tb16 y))
  (empty (tuple21 uninterpreted_type1 int)))
  (infix_mnmngt int uninterpreted_type1
  (add uninterpreted_type1 (t2tb4 x) (t2tb3 empty4))
  (t2tb15 (add2 y empty2)))) :pattern ((tb2t108
                                       (add (tuple21 uninterpreted_type1 int)
                                       (Tuple2 uninterpreted_type1 int
                                       (t2tb4 x) (t2tb16 y))
                                       (empty
                                       (tuple21 uninterpreted_type1 int))))) )))

;; singleton_is_function
  (assert
  (forall ((b ty))
  (forall ((x uninterpreted_type) (y uni)) (! (mem
  (set1 (tuple21 uninterpreted_type1 b))
  (add (tuple21 uninterpreted_type1 b)
  (Tuple2 uninterpreted_type1 b (t2tb4 x) y)
  (empty (tuple21 uninterpreted_type1 b)))
  (infix_mnmngt b uninterpreted_type1
  (add uninterpreted_type1 (t2tb4 x) (t2tb3 empty4)) (add b y (empty b)))) :pattern (
  (add (tuple21 uninterpreted_type1 b)
  (Tuple2 uninterpreted_type1 b (t2tb4 x) y)
  (empty (tuple21 uninterpreted_type1 b)))) ))))

(declare-fun t2tb110 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type))))))) (sort
  (set1
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))))) (t2tb110 x))))

(declare-fun tb2t110 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type)))))))
  (! (= (tb2t110 (t2tb110 i)) i) :pattern ((t2tb110 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb110 (tb2t110 j)) j) :pattern ((t2tb110 (tb2t110 j))) )))

(declare-fun t2tb111 ((set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))))) (sort
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)))) (t2tb111 x))))

(declare-fun tb2t111 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))))))
  (! (= (tb2t111 (t2tb111 i)) i) :pattern ((t2tb111 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb111 (tb2t111 j)) j) :pattern ((t2tb111 (tb2t111 j))) )))

(declare-fun t2tb112 ((tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))))) (sort
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))) (t2tb112 x))))

(declare-fun tb2t112 (uni) (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type))))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))))
  (! (= (tb2t112 (t2tb112 i)) i) :pattern ((t2tb112 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb112 (tb2t112 j)) j) :pattern ((t2tb112 (tb2t112 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))) (y (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))) (! (mem
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))))
  (add
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)))
  (Tuple2
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb6 x) (t2tb1 y))
  (empty
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)))))
  (infix_mnmngt
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb6 x) (t2tb5 empty3))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb1 y) (t2tb empty6)))) :pattern ((tb2t111
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
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   bool 
                                                                   bool)
                                                                   bool)
                                                                   bool)
                                                                   (set1
                                                                   uninterpreted_type1)))
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
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   bool 
                                                                   bool)
                                                                   bool)
                                                                   bool)
                                                                   (set1
                                                                   uninterpreted_type1))
                                                                   (t2tb6 x)
                                                                   (t2tb1 y))
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
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   bool 
                                                                   bool)
                                                                   bool)
                                                                   bool)
                                                                   (set1
                                                                   uninterpreted_type1))))))) )))

(declare-fun t2tb113 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) (set uninterpreted_type))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (set uninterpreted_type)))))) (sort
  (set1
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (set1 uninterpreted_type1)))) (t2tb113 x))))

(declare-fun tb2t113 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) (set uninterpreted_type)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (set uninterpreted_type))))))
  (! (= (tb2t113 (t2tb113 i)) i) :pattern ((t2tb113 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb113 (tb2t113 j)) j) :pattern ((t2tb113 (tb2t113 j))) )))

(declare-fun t2tb114 ((set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (set uninterpreted_type)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)) (set uninterpreted_type))))) (sort
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (set1 uninterpreted_type1))) (t2tb114 x))))

(declare-fun tb2t114 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) (set uninterpreted_type))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)) (set uninterpreted_type)))))
  (! (= (tb2t114 (t2tb114 i)) i) :pattern ((t2tb114 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb114 (tb2t114 j)) j) :pattern ((t2tb114 (tb2t114 j))) )))

(declare-fun t2tb115 ((tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (set uninterpreted_type))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)) (set uninterpreted_type)))) (sort
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (set1 uninterpreted_type1)) (t2tb115 x))))

(declare-fun tb2t115 (uni) (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (set uninterpreted_type)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)) (set uninterpreted_type))))
  (! (= (tb2t115 (t2tb115 i)) i) :pattern ((t2tb115 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb115 (tb2t115 j)) j) :pattern ((t2tb115 (tb2t115 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))) (y (set uninterpreted_type))) (! (mem
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (set1 uninterpreted_type1)))
  (add
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (set1 uninterpreted_type1))
  (Tuple2
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (set1 uninterpreted_type1) (t2tb6 x) (t2tb3 y))
  (empty
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (set1 uninterpreted_type1))))
  (infix_mnmngt (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb6 x) (t2tb5 empty3)) (t2tb2 (add3 y empty5)))) :pattern ((tb2t114
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
                                                                (set1
                                                                uninterpreted_type1))
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
                                                                (set1
                                                                uninterpreted_type1)
                                                                (t2tb6 x)
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
                                                                (set1
                                                                uninterpreted_type1)))))) )))

(declare-fun t2tb116 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) uninterpreted_type)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) uninterpreted_type))))) (sort
  (set1
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  uninterpreted_type1))) (t2tb116 x))))

(declare-fun tb2t116 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) uninterpreted_type))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) uninterpreted_type)))))
  (! (= (tb2t116 (t2tb116 i)) i) :pattern ((t2tb116 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb116 (tb2t116 j)) j) :pattern ((t2tb116 (tb2t116 j))) )))

(declare-fun t2tb117 ((set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) uninterpreted_type))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)) uninterpreted_type)))) (sort
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  uninterpreted_type1)) (t2tb117 x))))

(declare-fun tb2t117 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) uninterpreted_type)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)) uninterpreted_type))))
  (! (= (tb2t117 (t2tb117 i)) i) :pattern ((t2tb117 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb117 (tb2t117 j)) j) :pattern ((t2tb117 (tb2t117 j))) )))

(declare-fun t2tb118 ((tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) uninterpreted_type)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)) uninterpreted_type))) (sort
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  uninterpreted_type1) (t2tb118 x))))

(declare-fun tb2t118 (uni) (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) uninterpreted_type))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)) uninterpreted_type)))
  (! (= (tb2t118 (t2tb118 i)) i) :pattern ((t2tb118 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb118 (tb2t118 j)) j) :pattern ((t2tb118 (tb2t118 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))) (y uninterpreted_type)) (! (mem
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  uninterpreted_type1))
  (add
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  uninterpreted_type1)
  (Tuple2
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  uninterpreted_type1 (t2tb6 x) (t2tb4 y))
  (empty
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  uninterpreted_type1)))
  (infix_mnmngt uninterpreted_type1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb6 x) (t2tb5 empty3))
  (add uninterpreted_type1 (t2tb4 y) (t2tb3 empty4)))) :pattern ((tb2t117
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
                                                                 uninterpreted_type1)
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
                                                                 uninterpreted_type1
                                                                 (t2tb6 x)
                                                                 (t2tb4 y))
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
                                                                 uninterpreted_type1))))) )))

(declare-fun t2tb119 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
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
  (t2tb119 x))))

(declare-fun tb2t119 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))))))
  (! (= (tb2t119 (t2tb119 i)) i) :pattern ((t2tb119 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb119 (tb2t119 j)) j) :pattern ((t2tb119 (tb2t119 j))) )))

(declare-fun t2tb120 ((set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
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
  (t2tb120 x))))

(declare-fun tb2t120 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))) (! (= (tb2t120 (t2tb120 i)) i) :pattern ((t2tb120 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb120 (tb2t120 j)) j) :pattern ((t2tb120 (tb2t120 j))) )))

(declare-fun t2tb121 ((tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (sort
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb121 x))))

(declare-fun tb2t121 (uni) (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (! (= (tb2t121 (t2tb121 i)) i) :pattern ((t2tb121 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb121 (tb2t121 j)) j) :pattern ((t2tb121 (tb2t121 j))) )))

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
  (t2tb6 x) (t2tb6 y))
  (empty
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (infix_mnmngt
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb6 x) (t2tb5 empty3))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb6 y) (t2tb5 empty3)))) :pattern ((tb2t120
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
                                        bool) (set1 int)) (t2tb6 x)
                                        (t2tb6 y))
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

(declare-fun t2tb122 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
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
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))) (t2tb122 x))))

(declare-fun tb2t122 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))))
  (! (= (tb2t122 (t2tb122 i)) i) :pattern ((t2tb122 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb122 (tb2t122 j)) j) :pattern ((t2tb122 (tb2t122 j))) )))

(declare-fun t2tb123 ((set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)) (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))) (sort
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))) (t2tb123 x))))

(declare-fun tb2t123 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)) (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))))
  (! (= (tb2t123 (t2tb123 i)) i) :pattern ((t2tb123 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb123 (tb2t123 j)) j) :pattern ((t2tb123 (tb2t123 j))) )))

(declare-fun t2tb124 ((tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)) (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))) (sort
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb124 x))))

(declare-fun tb2t124 (uni) (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)) (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (! (= (tb2t124 (t2tb124 i)) i) :pattern ((t2tb124 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb124 (tb2t124 j)) j) :pattern ((t2tb124 (tb2t124 j))) )))

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
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb6 x) (t2tb8 y))
  (empty
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))))
  (infix_mnmngt (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb6 x) (t2tb5 empty3)) (t2tb7 (add4 y empty7)))) :pattern ((tb2t123
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
                                                                (tuple21
                                                                (tuple21 
                                                                bool 
                                                                bool) 
                                                                bool) 
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
                                                                (tuple21
                                                                (tuple21 
                                                                bool 
                                                                bool) 
                                                                bool) 
                                                                bool)
                                                                (t2tb6 x)
                                                                (t2tb8 y))
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
                                                                (tuple21
                                                                (tuple21 
                                                                bool 
                                                                bool) 
                                                                bool) 
                                                                bool)))))) )))

(declare-fun t2tb125 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) (tuple2 (tuple2 Bool Bool) Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (tuple2 (tuple2 Bool Bool) Bool)))))) (sort
  (set1
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 bool bool) bool)))) (t2tb125 x))))

(declare-fun tb2t125 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) (tuple2 (tuple2 Bool Bool) Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (tuple2 (tuple2 Bool Bool) Bool))))))
  (! (= (tb2t125 (t2tb125 i)) i) :pattern ((t2tb125 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb125 (tb2t125 j)) j) :pattern ((t2tb125 (tb2t125 j))) )))

(declare-fun t2tb126 ((set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (tuple2 (tuple2 Bool Bool) Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)) (tuple2 (tuple2 Bool Bool) Bool))))) (sort
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 bool bool) bool))) (t2tb126 x))))

(declare-fun tb2t126 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) (tuple2 (tuple2 Bool Bool) Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)) (tuple2 (tuple2 Bool Bool) Bool)))))
  (! (= (tb2t126 (t2tb126 i)) i) :pattern ((t2tb126 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb126 (tb2t126 j)) j) :pattern ((t2tb126 (tb2t126 j))) )))

(declare-fun t2tb127 ((tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (tuple2 (tuple2 Bool Bool) Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)) (tuple2 (tuple2 Bool Bool) Bool)))) (sort
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 bool bool) bool)) (t2tb127 x))))

(declare-fun tb2t127 (uni) (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (tuple2 (tuple2 Bool Bool) Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)) (tuple2 (tuple2 Bool Bool) Bool))))
  (! (= (tb2t127 (t2tb127 i)) i) :pattern ((t2tb127 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb127 (tb2t127 j)) j) :pattern ((t2tb127 (tb2t127 j))) )))

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
  (tuple21 (tuple21 bool bool) bool) (t2tb6 x) (t2tb10 y))
  (empty
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 bool bool) bool))))
  (infix_mnmngt (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb6 x) (t2tb5 empty3)) (t2tb9 (add5 y empty8)))) :pattern ((tb2t126
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
                                                                (tuple21 
                                                                bool 
                                                                bool) 
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
                                                                (tuple21 
                                                                bool 
                                                                bool) 
                                                                bool)
                                                                (t2tb6 x)
                                                                (t2tb10 y))
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
                                                                (tuple21 
                                                                bool 
                                                                bool) 
                                                                bool)))))) )))

(declare-fun t2tb128 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) (tuple2 Bool Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (tuple2 Bool Bool)))))) (sort
  (set1
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 bool bool)))) (t2tb128 x))))

(declare-fun tb2t128 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) (tuple2 Bool Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (tuple2 Bool Bool))))))
  (! (= (tb2t128 (t2tb128 i)) i) :pattern ((t2tb128 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb128 (tb2t128 j)) j) :pattern ((t2tb128 (tb2t128 j))) )))

(declare-fun t2tb129 ((set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (tuple2 Bool Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)) (tuple2 Bool Bool))))) (sort
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 bool bool))) (t2tb129 x))))

(declare-fun tb2t129 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) (tuple2 Bool Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)) (tuple2 Bool Bool)))))
  (! (= (tb2t129 (t2tb129 i)) i) :pattern ((t2tb129 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb129 (tb2t129 j)) j) :pattern ((t2tb129 (tb2t129 j))) )))

(declare-fun t2tb130 ((tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (tuple2 Bool Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)) (tuple2 Bool Bool)))) (sort
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 bool bool)) (t2tb130 x))))

(declare-fun tb2t130 (uni) (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (tuple2 Bool Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)) (tuple2 Bool Bool))))
  (! (= (tb2t130 (t2tb130 i)) i) :pattern ((t2tb130 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb130 (tb2t130 j)) j) :pattern ((t2tb130 (tb2t130 j))) )))

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
  (tuple21 bool bool) (t2tb6 x) (t2tb12 y))
  (empty
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 bool bool))))
  (infix_mnmngt (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb6 x) (t2tb5 empty3)) (t2tb11 (add6 y empty9)))) :pattern ((tb2t129
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
                                                                 (t2tb6 x)
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
                                                                 (tuple21
                                                                 bool 
                                                                 bool)))))) )))

(declare-fun t2tb131 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) Bool))))) (sort
  (set1
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  bool))) (t2tb131 x))))

(declare-fun tb2t131 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) Bool))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) Bool)))))
  (! (= (tb2t131 (t2tb131 i)) i) :pattern ((t2tb131 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb131 (tb2t131 j)) j) :pattern ((t2tb131 (tb2t131 j))) )))

(declare-fun t2tb132 ((set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)) Bool)))) (sort
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  bool)) (t2tb132 x))))

(declare-fun tb2t132 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) Bool)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)) Bool))))
  (! (= (tb2t132 (t2tb132 i)) i) :pattern ((t2tb132 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb132 (tb2t132 j)) j) :pattern ((t2tb132 (tb2t132 j))) )))

(declare-fun t2tb133 ((tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) Bool)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)) Bool))) (sort
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  bool) (t2tb133 x))))

(declare-fun tb2t133 (uni) (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) Bool))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)) Bool))) (! (= (tb2t133 (t2tb133 i)) i) :pattern ((t2tb133 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb133 (tb2t133 j)) j) :pattern ((t2tb133 (tb2t133 j))) )))

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
  bool (t2tb6 x) (t2tb13 y))
  (empty
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  bool)))
  (infix_mnmngt bool
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb6 x) (t2tb5 empty3)) (t2tb14 (add1 y empty1)))) :pattern ((tb2t132
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
                                                                 (t2tb6 x)
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
                                                                 bool))))) )))

(declare-fun t2tb134 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) Int))))) (sort
  (set1
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)) 
  int))) (t2tb134 x))))

(declare-fun tb2t134 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) Int))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) Int)))))
  (! (= (tb2t134 (t2tb134 i)) i) :pattern ((t2tb134 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb134 (tb2t134 j)) j) :pattern ((t2tb134 (tb2t134 j))) )))

(declare-fun t2tb135 ((set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)) Int)))) (sort
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)) 
  int)) (t2tb135 x))))

(declare-fun tb2t135 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)) Int))))
  (! (= (tb2t135 (t2tb135 i)) i) :pattern ((t2tb135 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb135 (tb2t135 j)) j) :pattern ((t2tb135 (tb2t135 j))) )))

(declare-fun t2tb136 ((tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) Int)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)) Int))) (sort
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)) 
  int) (t2tb136 x))))

(declare-fun tb2t136 (uni) (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) Int))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)) Int))) (! (= (tb2t136 (t2tb136 i)) i) :pattern ((t2tb136 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb136 (tb2t136 j)) j) :pattern ((t2tb136 (tb2t136 j))) )))

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
  int (t2tb6 x) (t2tb16 y))
  (empty
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)) 
  int)))
  (infix_mnmngt int
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb6 x) (t2tb5 empty3)) (t2tb15 (add2 y empty2)))) :pattern ((tb2t135
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
                                                                 int
                                                                 (t2tb6 x)
                                                                 (t2tb16 y))
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
  (t2tb6 x) y)
  (empty
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)) b)))
  (infix_mnmngt b
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb6 x) (t2tb5 empty3)) (add b y (empty b)))) :pattern ((add
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
                                                            (t2tb6 x) y)
                                                            (empty
                                                            (tuple21
                                                            (tuple21
                                                            (tuple21
                                                            (tuple21
                                                            (tuple21 
                                                            bool bool) 
                                                            bool) bool)
                                                            (set1 int)) b)))) ))))

(declare-fun t2tb137 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))))) (t2tb137 x))))

(declare-fun tb2t137 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))))))
  (! (= (tb2t137 (t2tb137 i)) i) :pattern ((t2tb137 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1))))) j) (= (t2tb137 (tb2t137 j)) j)) :pattern (
  (t2tb137 (tb2t137 j))) )))

(declare-fun t2tb138 ((set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))))) (sort
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)))) (t2tb138 x))))

(declare-fun tb2t138 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))))))
  (! (= (tb2t138 (t2tb138 i)) i) :pattern ((t2tb138 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1)))) j) (= (t2tb138 (tb2t138 j)) j)) :pattern (
  (t2tb138 (tb2t138 j))) )))

(declare-fun t2tb139 ((tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))))) (sort
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))) (t2tb139 x))))

(declare-fun tb2t139 (uni) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))))
  (! (= (tb2t139 (t2tb139 i)) i) :pattern ((t2tb139 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1))) j) (= (t2tb139 (tb2t139 j)) j)) :pattern (
  (t2tb139 (tb2t139 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (y (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))) (! (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb8 x) (t2tb1 y))
  (empty
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)))))
  (infix_mnmngt
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb7 (add4 x empty7))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb1 y) (t2tb empty6)))) :pattern ((tb2t138
                                                                   (add
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   bool 
                                                                   bool)
                                                                   bool)
                                                                   bool)
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   bool 
                                                                   bool)
                                                                   bool)
                                                                   bool)
                                                                   (set1
                                                                   uninterpreted_type1)))
                                                                   (Tuple2
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   bool 
                                                                   bool)
                                                                   bool)
                                                                   bool)
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   bool 
                                                                   bool)
                                                                   bool)
                                                                   bool)
                                                                   (set1
                                                                   uninterpreted_type1))
                                                                   (t2tb8 x)
                                                                   (t2tb1 y))
                                                                   (empty
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   bool 
                                                                   bool)
                                                                   bool)
                                                                   bool)
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   bool 
                                                                   bool)
                                                                   bool)
                                                                   bool)
                                                                   (set1
                                                                   uninterpreted_type1))))))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (y (set uninterpreted_type))) (! (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1) (t2tb8 x) (t2tb3 y)) (t2tb empty6))
  (infix_mnmngt (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb7 (add4 x empty7))
  (t2tb2 (add3 y empty5)))) :pattern ((tb2t
                                      (add
                                      (tuple21
                                      (tuple21
                                      (tuple21 (tuple21 bool bool) bool)
                                      bool) (set1 uninterpreted_type1))
                                      (Tuple2
                                      (tuple21
                                      (tuple21 (tuple21 bool bool) bool)
                                      bool) (set1 uninterpreted_type1)
                                      (t2tb8 x) (t2tb3 y)) (t2tb empty6)))) )))

(declare-fun t2tb140 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) uninterpreted_type)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) uninterpreted_type))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  uninterpreted_type1))) (t2tb140 x))))

(declare-fun tb2t140 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) uninterpreted_type))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) uninterpreted_type)))))
  (! (= (tb2t140 (t2tb140 i)) i) :pattern ((t2tb140 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     uninterpreted_type1))) j) (= (t2tb140 (tb2t140 j)) j)) :pattern (
  (t2tb140 (tb2t140 j))) )))

(declare-fun t2tb141 ((set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) uninterpreted_type))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  uninterpreted_type)))) (sort
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  uninterpreted_type1)) (t2tb141 x))))

(declare-fun tb2t141 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) uninterpreted_type)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  uninterpreted_type))))
  (! (= (tb2t141 (t2tb141 i)) i) :pattern ((t2tb141 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     uninterpreted_type1)) j) (= (t2tb141 (tb2t141 j)) j)) :pattern (
  (t2tb141 (tb2t141 j))) )))

(declare-fun t2tb142 ((tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  uninterpreted_type)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  uninterpreted_type))) (sort
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  uninterpreted_type1) (t2tb142 x))))

(declare-fun tb2t142 (uni) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) uninterpreted_type))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  uninterpreted_type)))
  (! (= (tb2t142 (t2tb142 i)) i) :pattern ((t2tb142 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     uninterpreted_type1) j) (= (t2tb142 (tb2t142 j)) j)) :pattern ((t2tb142
                                                                    (tb2t142
                                                                    j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (y uninterpreted_type)) (! (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  uninterpreted_type1))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  uninterpreted_type1)
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  uninterpreted_type1 (t2tb8 x) (t2tb4 y))
  (empty
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  uninterpreted_type1)))
  (infix_mnmngt uninterpreted_type1
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb7 (add4 x empty7))
  (add uninterpreted_type1 (t2tb4 y) (t2tb3 empty4)))) :pattern ((tb2t141
                                                                 (add
                                                                 (tuple21
                                                                 (tuple21
                                                                 (tuple21
                                                                 (tuple21
                                                                 bool 
                                                                 bool) 
                                                                 bool) 
                                                                 bool)
                                                                 uninterpreted_type1)
                                                                 (Tuple2
                                                                 (tuple21
                                                                 (tuple21
                                                                 (tuple21
                                                                 bool 
                                                                 bool) 
                                                                 bool) 
                                                                 bool)
                                                                 uninterpreted_type1
                                                                 (t2tb8 x)
                                                                 (t2tb4 y))
                                                                 (empty
                                                                 (tuple21
                                                                 (tuple21
                                                                 (tuple21
                                                                 (tuple21
                                                                 bool 
                                                                 bool) 
                                                                 bool) 
                                                                 bool)
                                                                 uninterpreted_type1))))) )))

(declare-fun t2tb143 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
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
  (t2tb143 x))))

(declare-fun tb2t143 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))))) (! (= (tb2t143 (t2tb143 i)) i) :pattern ((t2tb143 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb143 (tb2t143 j)) j) :pattern ((t2tb143 (tb2t143 j))) )))

(declare-fun t2tb144 ((set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))) (sort
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (t2tb144 x))))

(declare-fun tb2t144 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))))
  (! (= (tb2t144 (t2tb144 i)) i) :pattern ((t2tb144 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb144 (tb2t144 j)) j) :pattern ((t2tb144 (tb2t144 j))) )))

(declare-fun t2tb145 ((tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))) (sort
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb145 x))))

(declare-fun tb2t145 (uni) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))
  (! (= (tb2t145 (t2tb145 i)) i) :pattern ((t2tb145 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb145 (tb2t145 j)) j) :pattern ((t2tb145 (tb2t145 j))) )))

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
  (t2tb8 x) (t2tb6 y))
  (empty
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (infix_mnmngt
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb7 (add4 x empty7))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb6 y) (t2tb5 empty3)))) :pattern ((tb2t144
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
                                        bool) (set1 int)) (t2tb8 x)
                                        (t2tb6 y))
                                        (empty
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool)
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int))))))) )))

(declare-fun t2tb146 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))) (t2tb146 x))))

(declare-fun tb2t146 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))))
  (! (= (tb2t146 (t2tb146 i)) i) :pattern ((t2tb146 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))) j)
     (= (t2tb146 (tb2t146 j)) j)) :pattern ((t2tb146 (tb2t146 j))) )))

(declare-fun t2tb147 ((set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))) (sort
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))) (t2tb147 x))))

(declare-fun tb2t147 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))))
  (! (= (tb2t147 (t2tb147 i)) i) :pattern ((t2tb147 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool))) j)
     (= (t2tb147 (tb2t147 j)) j)) :pattern ((t2tb147 (tb2t147 j))) )))

(declare-fun t2tb148 ((tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))) (sort
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb148 x))))

(declare-fun tb2t148 (uni) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (! (= (tb2t148 (t2tb148 i)) i) :pattern ((t2tb148 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) j)
     (= (t2tb148 (tb2t148 j)) j)) :pattern ((t2tb148 (tb2t148 j))) )))

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
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 x) (t2tb8 y))
  (empty
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))))
  (infix_mnmngt (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb7 (add4 x empty7))
  (t2tb7 (add4 y empty7)))) :pattern ((tb2t147
                                      (add
                                      (tuple21
                                      (tuple21
                                      (tuple21 (tuple21 bool bool) bool)
                                      bool)
                                      (tuple21
                                      (tuple21 (tuple21 bool bool) bool)
                                      bool))
                                      (Tuple2
                                      (tuple21
                                      (tuple21 (tuple21 bool bool) bool)
                                      bool)
                                      (tuple21
                                      (tuple21 (tuple21 bool bool) bool)
                                      bool) (t2tb8 x) (t2tb8 y))
                                      (empty
                                      (tuple21
                                      (tuple21
                                      (tuple21 (tuple21 bool bool) bool)
                                      bool)
                                      (tuple21
                                      (tuple21 (tuple21 bool bool) bool)
                                      bool)))))) )))

(declare-fun t2tb149 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (tuple2 (tuple2 Bool Bool) Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (tuple2 (tuple2 Bool Bool) Bool)))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 bool bool) bool)))) (t2tb149 x))))

(declare-fun tb2t149 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (tuple2 (tuple2 Bool Bool) Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (tuple2 (tuple2 Bool Bool) Bool))))))
  (! (= (tb2t149 (t2tb149 i)) i) :pattern ((t2tb149 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (tuple21 (tuple21 bool bool) bool)))) j) (= (t2tb149 (tb2t149 j)) j)) :pattern (
  (t2tb149 (tb2t149 j))) )))

(declare-fun t2tb150 ((set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (tuple2 (tuple2 Bool Bool) Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 (tuple2 Bool Bool) Bool))))) (sort
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 bool bool) bool))) (t2tb150 x))))

(declare-fun tb2t150 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (tuple2 (tuple2 Bool Bool) Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 (tuple2 Bool Bool) Bool)))))
  (! (= (tb2t150 (t2tb150 i)) i) :pattern ((t2tb150 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (tuple21 (tuple21 bool bool) bool))) j) (= (t2tb150 (tb2t150 j)) j)) :pattern (
  (t2tb150 (tb2t150 j))) )))

(declare-fun t2tb151 ((tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 (tuple2 Bool Bool) Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 (tuple2 Bool Bool) Bool)))) (sort
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 bool bool) bool)) (t2tb151 x))))

(declare-fun tb2t151 (uni) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (tuple2 (tuple2 Bool Bool) Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 (tuple2 Bool Bool) Bool))))
  (! (= (tb2t151 (t2tb151 i)) i) :pattern ((t2tb151 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (tuple21 (tuple21 bool bool) bool)) j) (= (t2tb151 (tb2t151 j)) j)) :pattern (
  (t2tb151 (tb2t151 j))) )))

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
  (tuple21 (tuple21 bool bool) bool) (t2tb8 x) (t2tb10 y))
  (empty
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 bool bool) bool))))
  (infix_mnmngt (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb7 (add4 x empty7))
  (t2tb9 (add5 y empty8)))) :pattern ((tb2t150
                                      (add
                                      (tuple21
                                      (tuple21
                                      (tuple21 (tuple21 bool bool) bool)
                                      bool)
                                      (tuple21 (tuple21 bool bool) bool))
                                      (Tuple2
                                      (tuple21
                                      (tuple21 (tuple21 bool bool) bool)
                                      bool)
                                      (tuple21 (tuple21 bool bool) bool)
                                      (t2tb8 x) (t2tb10 y))
                                      (empty
                                      (tuple21
                                      (tuple21
                                      (tuple21 (tuple21 bool bool) bool)
                                      bool)
                                      (tuple21 (tuple21 bool bool) bool)))))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)) (y (set Int)))
  (! (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb8 x) (t2tb15 y)) (t2tb5 empty3))
  (infix_mnmngt (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb7 (add4 x empty7)) (add (set1 int) (t2tb15 y) (empty (set1 int))))) :pattern (
  (tb2t5
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb8 x) (t2tb15 y)) (t2tb5 empty3)))) )))

(declare-fun t2tb152 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (tuple2 Bool Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (tuple2 Bool Bool)))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 bool bool)))) (t2tb152 x))))

(declare-fun tb2t152 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (tuple2 Bool Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (tuple2 Bool Bool))))))
  (! (= (tb2t152 (t2tb152 i)) i) :pattern ((t2tb152 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (tuple21 bool bool)))) j) (= (t2tb152 (tb2t152 j)) j)) :pattern (
  (t2tb152 (tb2t152 j))) )))

(declare-fun t2tb153 ((set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (tuple2 Bool Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 Bool Bool))))) (sort
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 bool bool))) (t2tb153 x))))

(declare-fun tb2t153 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (tuple2 Bool Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 Bool Bool)))))
  (! (= (tb2t153 (t2tb153 i)) i) :pattern ((t2tb153 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (tuple21 bool bool))) j) (= (t2tb153 (tb2t153 j)) j)) :pattern (
  (t2tb153 (tb2t153 j))) )))

(declare-fun t2tb154 ((tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 Bool Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 Bool Bool)))) (sort
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 bool bool)) (t2tb154 x))))

(declare-fun tb2t154 (uni) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (tuple2 Bool Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 Bool Bool))))
  (! (= (tb2t154 (t2tb154 i)) i) :pattern ((t2tb154 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (tuple21 bool bool)) j) (= (t2tb154 (tb2t154 j)) j)) :pattern ((t2tb154
                                                                    (tb2t154
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
  (tuple21 bool bool) (t2tb8 x) (t2tb12 y))
  (empty
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 bool bool))))
  (infix_mnmngt (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb7 (add4 x empty7))
  (t2tb11 (add6 y empty9)))) :pattern ((tb2t153
                                       (add
                                       (tuple21
                                       (tuple21
                                       (tuple21 (tuple21 bool bool) bool)
                                       bool) (tuple21 bool bool))
                                       (Tuple2
                                       (tuple21
                                       (tuple21 (tuple21 bool bool) bool)
                                       bool) (tuple21 bool bool) (t2tb8 x)
                                       (t2tb12 y))
                                       (empty
                                       (tuple21
                                       (tuple21
                                       (tuple21 (tuple21 bool bool) bool)
                                       bool) (tuple21 bool bool)))))) )))

(declare-fun t2tb155 ((set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  Bool)))) (sort
  (set1 (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) bool))
  (t2tb155 x))))

(declare-fun tb2t155 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) Bool)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  Bool)))) (! (= (tb2t155 (t2tb155 i)) i) :pattern ((t2tb155 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1 (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) bool))
     j) (= (t2tb155 (tb2t155 j)) j)) :pattern ((t2tb155 (tb2t155 j))) )))

(declare-fun t2tb156 ((tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  Bool)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) Bool)))
  (sort (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) bool)
  (t2tb156 x))))

(declare-fun tb2t156 (uni) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) Bool))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) Bool)))
  (! (= (tb2t156 (t2tb156 i)) i) :pattern ((t2tb156 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) bool) j)
     (= (t2tb156 (tb2t156 j)) j)) :pattern ((t2tb156 (tb2t156 j))) )))

(declare-fun t2tb157 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) Bool))))) (sort
  (set1
  (set1 (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) bool)))
  (t2tb157 x))))

(declare-fun tb2t157 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) Bool))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) Bool))))) (! (= (tb2t157 (t2tb157 i)) i) :pattern ((t2tb157 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1 (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) bool)))
     j) (= (t2tb157 (tb2t157 j)) j)) :pattern ((t2tb157 (tb2t157 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)) (y Bool))
  (! (mem
  (set1 (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) bool))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) bool)
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) bool (t2tb8 x)
  (t2tb13 y))
  (empty (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) bool)))
  (infix_mnmngt bool (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb7 (add4 x empty7)) (t2tb14 (add1 y empty1)))) :pattern ((tb2t155
                                                               (add
                                                               (tuple21
                                                               (tuple21
                                                               (tuple21
                                                               (tuple21 
                                                               bool bool)
                                                               bool) 
                                                               bool) 
                                                               bool)
                                                               (Tuple2
                                                               (tuple21
                                                               (tuple21
                                                               (tuple21 
                                                               bool bool)
                                                               bool) 
                                                               bool) 
                                                               bool (t2tb8 x)
                                                               (t2tb13 y))
                                                               (empty
                                                               (tuple21
                                                               (tuple21
                                                               (tuple21
                                                               (tuple21 
                                                               bool bool)
                                                               bool) 
                                                               bool) 
                                                               bool))))) )))

(declare-fun t2tb158 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) Int))))) (sort
  (set1
  (set1 (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) int)))
  (t2tb158 x))))

(declare-fun tb2t158 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) Int))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) Int))))) (! (= (tb2t158 (t2tb158 i)) i) :pattern ((t2tb158 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb158 (tb2t158 j)) j) :pattern ((t2tb158 (tb2t158 j))) )))

(declare-fun t2tb159 ((set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  Int)))) (sort
  (set1 (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) int))
  (t2tb159 x))))

(declare-fun tb2t159 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  Int)))) (! (= (tb2t159 (t2tb159 i)) i) :pattern ((t2tb159 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb159 (tb2t159 j)) j) :pattern ((t2tb159 (tb2t159 j))) )))

(declare-fun t2tb160 ((tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  Int)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) Int)))
  (sort (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) int)
  (t2tb160 x))))

(declare-fun tb2t160 (uni) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) Int))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) Int)))
  (! (= (tb2t160 (t2tb160 i)) i) :pattern ((t2tb160 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb160 (tb2t160 j)) j) :pattern ((t2tb160 (tb2t160 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)) (y Int))
  (! (mem
  (set1 (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) int))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) int)
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) int (t2tb8 x)
  (t2tb16 y))
  (empty (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) int)))
  (infix_mnmngt int (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb7 (add4 x empty7)) (t2tb15 (add2 y empty2)))) :pattern ((tb2t159
                                                               (add
                                                               (tuple21
                                                               (tuple21
                                                               (tuple21
                                                               (tuple21 
                                                               bool bool)
                                                               bool) 
                                                               bool) 
                                                               int)
                                                               (Tuple2
                                                               (tuple21
                                                               (tuple21
                                                               (tuple21 
                                                               bool bool)
                                                               bool) 
                                                               bool) 
                                                               int (t2tb8 x)
                                                               (t2tb16 y))
                                                               (empty
                                                               (tuple21
                                                               (tuple21
                                                               (tuple21
                                                               (tuple21 
                                                               bool bool)
                                                               bool) 
                                                               bool) 
                                                               int))))) )))

;; singleton_is_function
  (assert
  (forall ((b ty))
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)) (y uni))
  (! (mem
  (set1 (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) b))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) b)
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) b (t2tb8 x) y)
  (empty (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) b)))
  (infix_mnmngt b (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb7 (add4 x empty7)) (add b y (empty b)))) :pattern ((add
                                                          (tuple21
                                                          (tuple21
                                                          (tuple21
                                                          (tuple21 bool bool)
                                                          bool) bool) b)
                                                          (Tuple2
                                                          (tuple21
                                                          (tuple21
                                                          (tuple21 bool bool)
                                                          bool) bool) b
                                                          (t2tb8 x) y)
                                                          (empty
                                                          (tuple21
                                                          (tuple21
                                                          (tuple21
                                                          (tuple21 bool bool)
                                                          bool) bool) b)))) ))))

(declare-fun t2tb161 ((set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))))) (t2tb161 x))))

(declare-fun tb2t161 (uni) (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))))))
  (! (= (tb2t161 (t2tb161 i)) i) :pattern ((t2tb161 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21 (tuple21 (tuple21 bool bool) bool)
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1))))) j) (= (t2tb161 (tb2t161 j)) j)) :pattern (
  (t2tb161 (tb2t161 j))) )))

(declare-fun t2tb162 ((set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))))) (sort
  (set1
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)))) (t2tb162 x))))

(declare-fun tb2t162 (uni) (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))))))
  (! (= (tb2t162 (t2tb162 i)) i) :pattern ((t2tb162 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21 (tuple21 (tuple21 bool bool) bool)
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1)))) j) (= (t2tb162 (tb2t162 j)) j)) :pattern (
  (t2tb162 (tb2t162 j))) )))

(declare-fun t2tb163 ((tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))))) (sort
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))) (t2tb163 x))))

(declare-fun tb2t163 (uni) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))))
  (! (= (tb2t163 (t2tb163 i)) i) :pattern ((t2tb163 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 (tuple21 (tuple21 bool bool) bool)
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1))) j) (= (t2tb163 (tb2t163 j)) j)) :pattern (
  (t2tb163 (tb2t163 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool))
  (y (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))) (! (mem
  (set1
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))))
  (add
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)))
  (Tuple2 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb10 x) (t2tb1 y))
  (empty
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)))))
  (infix_mnmngt
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (tuple21 (tuple21 bool bool) bool)
  (t2tb9 (add5 x empty8))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb1 y) (t2tb empty6)))) :pattern ((tb2t162
                                                                   (add
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   bool 
                                                                   bool)
                                                                   bool)
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   bool 
                                                                   bool)
                                                                   bool)
                                                                   bool)
                                                                   (set1
                                                                   uninterpreted_type1)))
                                                                   (Tuple2
                                                                   (tuple21
                                                                   (tuple21
                                                                   bool 
                                                                   bool)
                                                                   bool)
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   bool 
                                                                   bool)
                                                                   bool)
                                                                   bool)
                                                                   (set1
                                                                   uninterpreted_type1))
                                                                   (t2tb10 x)
                                                                   (t2tb1 y))
                                                                   (empty
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   bool 
                                                                   bool)
                                                                   bool)
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   bool 
                                                                   bool)
                                                                   bool)
                                                                   bool)
                                                                   (set1
                                                                   uninterpreted_type1))))))) )))

(declare-fun t2tb164 ((set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (set uninterpreted_type))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (set uninterpreted_type)))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 bool bool) bool) (set1 uninterpreted_type1))))
  (t2tb164 x))))

(declare-fun tb2t164 (uni) (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (set uninterpreted_type)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (set uninterpreted_type))))))
  (! (= (tb2t164 (t2tb164 i)) i) :pattern ((t2tb164 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21 (tuple21 (tuple21 bool bool) bool) (set1 uninterpreted_type1))))
     j) (= (t2tb164 (tb2t164 j)) j)) :pattern ((t2tb164 (tb2t164 j))) )))

(declare-fun t2tb165 ((set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (set uninterpreted_type)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (set uninterpreted_type))))) (sort
  (set1
  (tuple21 (tuple21 (tuple21 bool bool) bool) (set1 uninterpreted_type1)))
  (t2tb165 x))))

(declare-fun tb2t165 (uni) (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (set uninterpreted_type))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (set uninterpreted_type)))))
  (! (= (tb2t165 (t2tb165 i)) i) :pattern ((t2tb165 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21 (tuple21 (tuple21 bool bool) bool) (set1 uninterpreted_type1)))
     j) (= (t2tb165 (tb2t165 j)) j)) :pattern ((t2tb165 (tb2t165 j))) )))

(declare-fun t2tb166 ((tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (set uninterpreted_type))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (set uninterpreted_type)))) (sort
  (tuple21 (tuple21 (tuple21 bool bool) bool) (set1 uninterpreted_type1))
  (t2tb166 x))))

(declare-fun tb2t166 (uni) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (set uninterpreted_type)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (set uninterpreted_type))))
  (! (= (tb2t166 (t2tb166 i)) i) :pattern ((t2tb166 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 (tuple21 (tuple21 bool bool) bool) (set1 uninterpreted_type1))
     j) (= (t2tb166 (tb2t166 j)) j)) :pattern ((t2tb166 (tb2t166 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)) (y (set uninterpreted_type)))
  (! (mem
  (set1
  (tuple21 (tuple21 (tuple21 bool bool) bool) (set1 uninterpreted_type1)))
  (add
  (tuple21 (tuple21 (tuple21 bool bool) bool) (set1 uninterpreted_type1))
  (Tuple2 (tuple21 (tuple21 bool bool) bool) (set1 uninterpreted_type1)
  (t2tb10 x) (t2tb3 y))
  (empty
  (tuple21 (tuple21 (tuple21 bool bool) bool) (set1 uninterpreted_type1))))
  (infix_mnmngt (set1 uninterpreted_type1) (tuple21 (tuple21 bool bool) bool)
  (t2tb9 (add5 x empty8)) (t2tb2 (add3 y empty5)))) :pattern ((tb2t165
                                                              (add
                                                              (tuple21
                                                              (tuple21
                                                              (tuple21 
                                                              bool bool)
                                                              bool)
                                                              (set1
                                                              uninterpreted_type1))
                                                              (Tuple2
                                                              (tuple21
                                                              (tuple21 
                                                              bool bool)
                                                              bool)
                                                              (set1
                                                              uninterpreted_type1)
                                                              (t2tb10 x)
                                                              (t2tb3 y))
                                                              (empty
                                                              (tuple21
                                                              (tuple21
                                                              (tuple21 
                                                              bool bool)
                                                              bool)
                                                              (set1
                                                              uninterpreted_type1)))))) )))

(declare-fun t2tb167 ((set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  uninterpreted_type)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  uninterpreted_type))))) (sort
  (set1
  (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) uninterpreted_type1)))
  (t2tb167 x))))

(declare-fun tb2t167 (uni) (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  uninterpreted_type))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  uninterpreted_type)))))
  (! (= (tb2t167 (t2tb167 i)) i) :pattern ((t2tb167 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) uninterpreted_type1)))
     j) (= (t2tb167 (tb2t167 j)) j)) :pattern ((t2tb167 (tb2t167 j))) )))

(declare-fun t2tb168 ((set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  uninterpreted_type))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  uninterpreted_type)))) (sort
  (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) uninterpreted_type1))
  (t2tb168 x))))

(declare-fun tb2t168 (uni) (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  uninterpreted_type)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  uninterpreted_type))))
  (! (= (tb2t168 (t2tb168 i)) i) :pattern ((t2tb168 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) uninterpreted_type1))
     j) (= (t2tb168 (tb2t168 j)) j)) :pattern ((t2tb168 (tb2t168 j))) )))

(declare-fun t2tb169 ((tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  uninterpreted_type)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) uninterpreted_type)))
  (sort (tuple21 (tuple21 (tuple21 bool bool) bool) uninterpreted_type1)
  (t2tb169 x))))

(declare-fun tb2t169 (uni) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  uninterpreted_type))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 Bool Bool) Bool) uninterpreted_type)))
  (! (= (tb2t169 (t2tb169 i)) i) :pattern ((t2tb169 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 (tuple21 (tuple21 bool bool) bool) uninterpreted_type1) j)
     (= (t2tb169 (tb2t169 j)) j)) :pattern ((t2tb169 (tb2t169 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)) (y uninterpreted_type))
  (! (mem
  (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) uninterpreted_type1))
  (add (tuple21 (tuple21 (tuple21 bool bool) bool) uninterpreted_type1)
  (Tuple2 (tuple21 (tuple21 bool bool) bool) uninterpreted_type1 (t2tb10 x)
  (t2tb4 y))
  (empty (tuple21 (tuple21 (tuple21 bool bool) bool) uninterpreted_type1)))
  (infix_mnmngt uninterpreted_type1 (tuple21 (tuple21 bool bool) bool)
  (t2tb9 (add5 x empty8)) (add uninterpreted_type1 (t2tb4 y) (t2tb3 empty4)))) :pattern (
  (tb2t168
  (add (tuple21 (tuple21 (tuple21 bool bool) bool) uninterpreted_type1)
  (Tuple2 (tuple21 (tuple21 bool bool) bool) uninterpreted_type1 (t2tb10 x)
  (t2tb4 y))
  (empty (tuple21 (tuple21 (tuple21 bool bool) bool) uninterpreted_type1))))) )))

(declare-fun t2tb170 ((set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))) (sort
  (set1
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (t2tb170 x))))

(declare-fun tb2t170 (uni) (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))))
  (! (= (tb2t170 (t2tb170 i)) i) :pattern ((t2tb170 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb170 (tb2t170 j)) j) :pattern ((t2tb170 (tb2t170 j))) )))

(declare-fun t2tb171 ((tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))) (sort
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb171 x))))

(declare-fun tb2t171 (uni) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))
  (! (= (tb2t171 (t2tb171 i)) i) :pattern ((t2tb171 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb171 (tb2t171 j)) j) :pattern ((t2tb171 (tb2t171 j))) )))

(declare-fun t2tb172 ((set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
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
  (t2tb172 x))))

(declare-fun tb2t172 (uni) (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))))
  (! (= (tb2t172 (t2tb172 i)) i) :pattern ((t2tb172 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb172 (tb2t172 j)) j) :pattern ((t2tb172 (tb2t172 j))) )))

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
  (t2tb10 x) (t2tb6 y))
  (empty
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (infix_mnmngt
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 bool bool) bool) (t2tb9 (add5 x empty8))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb6 y) (t2tb5 empty3)))) :pattern ((tb2t170
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
                                        (t2tb6 y))
                                        (empty
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int))))))) )))

(declare-fun t2tb173 ((set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))) (t2tb173 x))))

(declare-fun tb2t173 (uni) (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))))
  (! (= (tb2t173 (t2tb173 i)) i) :pattern ((t2tb173 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21 (tuple21 (tuple21 bool bool) bool)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))) j)
     (= (t2tb173 (tb2t173 j)) j)) :pattern ((t2tb173 (tb2t173 j))) )))

(declare-fun t2tb174 ((set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))) (sort
  (set1
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))) (t2tb174 x))))

(declare-fun tb2t174 (uni) (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))))
  (! (= (tb2t174 (t2tb174 i)) i) :pattern ((t2tb174 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21 (tuple21 (tuple21 bool bool) bool)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool))) j)
     (= (t2tb174 (tb2t174 j)) j)) :pattern ((t2tb174 (tb2t174 j))) )))

(declare-fun t2tb175 ((tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))) (sort
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb175 x))))

(declare-fun tb2t175 (uni) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (! (= (tb2t175 (t2tb175 i)) i) :pattern ((t2tb175 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 (tuple21 (tuple21 bool bool) bool)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) j)
     (= (t2tb175 (tb2t175 j)) j)) :pattern ((t2tb175 (tb2t175 j))) )))

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
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb10 x) (t2tb8 y))
  (empty
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))))
  (infix_mnmngt (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 bool bool) bool) (t2tb9 (add5 x empty8))
  (t2tb7 (add4 y empty7)))) :pattern ((tb2t174
                                      (add
                                      (tuple21
                                      (tuple21 (tuple21 bool bool) bool)
                                      (tuple21
                                      (tuple21 (tuple21 bool bool) bool)
                                      bool))
                                      (Tuple2
                                      (tuple21 (tuple21 bool bool) bool)
                                      (tuple21
                                      (tuple21 (tuple21 bool bool) bool)
                                      bool) (t2tb10 x) (t2tb8 y))
                                      (empty
                                      (tuple21
                                      (tuple21 (tuple21 bool bool) bool)
                                      (tuple21
                                      (tuple21 (tuple21 bool bool) bool)
                                      bool)))))) )))

(declare-fun t2tb176 ((set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 Bool Bool) Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 Bool Bool) Bool)))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 bool bool) bool)))) (t2tb176 x))))

(declare-fun tb2t176 (uni) (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 Bool Bool) Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 Bool Bool) Bool))))))
  (! (= (tb2t176 (t2tb176 i)) i) :pattern ((t2tb176 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21 (tuple21 (tuple21 bool bool) bool)
     (tuple21 (tuple21 bool bool) bool)))) j) (= (t2tb176 (tb2t176 j)) j)) :pattern (
  (t2tb176 (tb2t176 j))) )))

(declare-fun t2tb177 ((set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 Bool Bool) Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 Bool Bool) Bool))))) (sort
  (set1
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 bool bool) bool))) (t2tb177 x))))

(declare-fun tb2t177 (uni) (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 Bool Bool) Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 Bool Bool) Bool)))))
  (! (= (tb2t177 (t2tb177 i)) i) :pattern ((t2tb177 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21 (tuple21 (tuple21 bool bool) bool)
     (tuple21 (tuple21 bool bool) bool))) j) (= (t2tb177 (tb2t177 j)) j)) :pattern (
  (t2tb177 (tb2t177 j))) )))

(declare-fun t2tb178 ((tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 Bool Bool) Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) (tuple2 (tuple2 Bool
  Bool) Bool)))) (sort
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 bool bool) bool)) (t2tb178 x))))

(declare-fun tb2t178 (uni) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 Bool Bool) Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 Bool Bool) Bool) (tuple2 (tuple2 Bool
  Bool) Bool)))) (! (= (tb2t178 (t2tb178 i)) i) :pattern ((t2tb178 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 (tuple21 (tuple21 bool bool) bool)
     (tuple21 (tuple21 bool bool) bool)) j) (= (t2tb178 (tb2t178 j)) j)) :pattern (
  (t2tb178 (tb2t178 j))) )))

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
  (tuple21 (tuple21 bool bool) bool) (t2tb9 (add5 x empty8))
  (t2tb9 (add5 y empty8)))) :pattern ((tb2t177
                                      (add
                                      (tuple21
                                      (tuple21 (tuple21 bool bool) bool)
                                      (tuple21 (tuple21 bool bool) bool))
                                      (Tuple2
                                      (tuple21 (tuple21 bool bool) bool)
                                      (tuple21 (tuple21 bool bool) bool)
                                      (t2tb10 x) (t2tb10 y))
                                      (empty
                                      (tuple21
                                      (tuple21 (tuple21 bool bool) bool)
                                      (tuple21 (tuple21 bool bool) bool)))))) )))

(declare-fun t2tb179 ((set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 Bool Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) (tuple2 Bool
  Bool)))))) (sort
  (set1
  (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool))))
  (t2tb179 x))))

(declare-fun tb2t179 (uni) (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 Bool Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) (tuple2 Bool
  Bool)))))) (! (= (tb2t179 (t2tb179 i)) i) :pattern ((t2tb179 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool))))
     j) (= (t2tb179 (tb2t179 j)) j)) :pattern ((t2tb179 (tb2t179 j))) )))

(declare-fun t2tb180 ((set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 Bool Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) (tuple2 Bool
  Bool))))) (sort
  (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool)))
  (t2tb180 x))))

(declare-fun tb2t180 (uni) (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 Bool Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) (tuple2 Bool
  Bool))))) (! (= (tb2t180 (t2tb180 i)) i) :pattern ((t2tb180 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool)))
     j) (= (t2tb180 (tb2t180 j)) j)) :pattern ((t2tb180 (tb2t180 j))) )))

(declare-fun t2tb181 ((tuple2 (tuple2 (tuple2 Bool Bool) Bool) (tuple2 Bool
  Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) (tuple2 Bool Bool))))
  (sort (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool))
  (t2tb181 x))))

(declare-fun tb2t181 (uni) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 Bool Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 Bool Bool) Bool) (tuple2 Bool Bool))))
  (! (= (tb2t181 (t2tb181 i)) i) :pattern ((t2tb181 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool)) j)
     (= (t2tb181 (tb2t181 j)) j)) :pattern ((t2tb181 (tb2t181 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)) (y (tuple2 Bool Bool)))
  (! (mem
  (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool)))
  (add (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool))
  (Tuple2 (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool) (t2tb10 x)
  (t2tb12 y))
  (empty (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool))))
  (infix_mnmngt (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool)
  (t2tb9 (add5 x empty8)) (t2tb11 (add6 y empty9)))) :pattern ((tb2t180
                                                               (add
                                                               (tuple21
                                                               (tuple21
                                                               (tuple21 
                                                               bool bool)
                                                               bool)
                                                               (tuple21 
                                                               bool bool))
                                                               (Tuple2
                                                               (tuple21
                                                               (tuple21 
                                                               bool bool)
                                                               bool)
                                                               (tuple21 
                                                               bool bool)
                                                               (t2tb10 x)
                                                               (t2tb12 y))
                                                               (empty
                                                               (tuple21
                                                               (tuple21
                                                               (tuple21 
                                                               bool bool)
                                                               bool)
                                                               (tuple21 
                                                               bool bool)))))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)) (y Bool)) (! (mem
  (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (t2tb7 (add4 (Tuple23 x y) empty7))
  (infix_mnmngt bool (tuple21 (tuple21 bool bool) bool)
  (t2tb9 (add5 x empty8)) (t2tb14 (add1 y empty1)))) :pattern ((add4
                                                               (Tuple23 x y)
                                                               empty7)) )))

(declare-fun t2tb182 ((set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Int)))))
  (sort (set1 (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) int)))
  (t2tb182 x))))

(declare-fun tb2t182 (uni) (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Int))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Int)))))
  (! (= (tb2t182 (t2tb182 i)) i) :pattern ((t2tb182 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb182 (tb2t182 j)) j) :pattern ((t2tb182 (tb2t182 j))) )))

(declare-fun t2tb183 ((set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Int)))) (sort
  (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) int)) (t2tb183 x))))

(declare-fun tb2t183 (uni) (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Int))))
  (! (= (tb2t183 (t2tb183 i)) i) :pattern ((t2tb183 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb183 (tb2t183 j)) j) :pattern ((t2tb183 (tb2t183 j))) )))

(declare-fun t2tb184 ((tuple2 (tuple2 (tuple2 Bool Bool) Bool) Int)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Int))) (sort
  (tuple21 (tuple21 (tuple21 bool bool) bool) int) (t2tb184 x))))

(declare-fun tb2t184 (uni) (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Int))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Int)))
  (! (= (tb2t184 (t2tb184 i)) i) :pattern ((t2tb184 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb184 (tb2t184 j)) j) :pattern ((t2tb184 (tb2t184 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)) (y Int)) (! (mem
  (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) int))
  (add (tuple21 (tuple21 (tuple21 bool bool) bool) int)
  (Tuple2 (tuple21 (tuple21 bool bool) bool) int (t2tb10 x) (t2tb16 y))
  (empty (tuple21 (tuple21 (tuple21 bool bool) bool) int)))
  (infix_mnmngt int (tuple21 (tuple21 bool bool) bool)
  (t2tb9 (add5 x empty8)) (t2tb15 (add2 y empty2)))) :pattern ((tb2t183
                                                               (add
                                                               (tuple21
                                                               (tuple21
                                                               (tuple21 
                                                               bool bool)
                                                               bool) 
                                                               int)
                                                               (Tuple2
                                                               (tuple21
                                                               (tuple21 
                                                               bool bool)
                                                               bool) 
                                                               int (t2tb10 x)
                                                               (t2tb16 y))
                                                               (empty
                                                               (tuple21
                                                               (tuple21
                                                               (tuple21 
                                                               bool bool)
                                                               bool) 
                                                               int))))) )))

;; singleton_is_function
  (assert
  (forall ((b ty))
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)) (y uni)) (! (mem
  (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) b))
  (add (tuple21 (tuple21 (tuple21 bool bool) bool) b)
  (Tuple2 (tuple21 (tuple21 bool bool) bool) b (t2tb10 x) y)
  (empty (tuple21 (tuple21 (tuple21 bool bool) bool) b)))
  (infix_mnmngt b (tuple21 (tuple21 bool bool) bool) (t2tb9 (add5 x empty8))
  (add b y (empty b)))) :pattern ((add
                                  (tuple21 (tuple21 (tuple21 bool bool) bool)
                                  b)
                                  (Tuple2 (tuple21 (tuple21 bool bool) bool)
                                  b (t2tb10 x) y)
                                  (empty
                                  (tuple21 (tuple21 (tuple21 bool bool) bool)
                                  b)))) ))))

(declare-fun t2tb185 ((set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))))) (sort
  (set1
  (tuple21 (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)))) (t2tb185 x))))

(declare-fun tb2t185 (uni) (set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))))))
  (! (= (tb2t185 (t2tb185 i)) i) :pattern ((t2tb185 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21 (tuple21 bool bool)
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1)))) j) (= (t2tb185 (tb2t185 j)) j)) :pattern (
  (t2tb185 (tb2t185 j))) )))

(declare-fun t2tb186 ((tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type))))) (sort
  (tuple21 (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))) (t2tb186 x))))

(declare-fun tb2t186 (uni) (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type)))))
  (! (= (tb2t186 (t2tb186 i)) i) :pattern ((t2tb186 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 (tuple21 bool bool)
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1))) j) (= (t2tb186 (tb2t186 j)) j)) :pattern (
  (t2tb186 (tb2t186 j))) )))

(declare-fun t2tb187 ((set (set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))))) (t2tb187 x))))

(declare-fun tb2t187 (uni) (set (set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))))))
  (! (= (tb2t187 (t2tb187 i)) i) :pattern ((t2tb187 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21 (tuple21 bool bool)
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1))))) j) (= (t2tb187 (tb2t187 j)) j)) :pattern (
  (t2tb187 (tb2t187 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 Bool Bool)) (y (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type)))) (! (mem
  (set1
  (tuple21 (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))))
  (add
  (tuple21 (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)))
  (Tuple2 (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb12 x) (t2tb1 y))
  (empty
  (tuple21 (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)))))
  (infix_mnmngt
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (tuple21 bool bool) (t2tb11 (add6 x empty9))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb1 y) (t2tb empty6)))) :pattern ((tb2t185
                                                                   (add
                                                                   (tuple21
                                                                   (tuple21
                                                                   bool 
                                                                   bool)
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   bool 
                                                                   bool)
                                                                   bool)
                                                                   bool)
                                                                   (set1
                                                                   uninterpreted_type1)))
                                                                   (Tuple2
                                                                   (tuple21
                                                                   bool 
                                                                   bool)
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   bool 
                                                                   bool)
                                                                   bool)
                                                                   bool)
                                                                   (set1
                                                                   uninterpreted_type1))
                                                                   (t2tb12 x)
                                                                   (t2tb1 y))
                                                                   (empty
                                                                   (tuple21
                                                                   (tuple21
                                                                   bool 
                                                                   bool)
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   bool 
                                                                   bool)
                                                                   bool)
                                                                   bool)
                                                                   (set1
                                                                   uninterpreted_type1))))))) )))

(declare-fun t2tb188 ((set (set (tuple2 (tuple2 Bool Bool)
  (set uninterpreted_type))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 Bool Bool)
  (set uninterpreted_type)))))) (sort
  (set1 (set1 (tuple21 (tuple21 bool bool) (set1 uninterpreted_type1))))
  (t2tb188 x))))

(declare-fun tb2t188 (uni) (set (set (tuple2 (tuple2 Bool Bool)
  (set uninterpreted_type)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 Bool Bool)
  (set uninterpreted_type))))))
  (! (= (tb2t188 (t2tb188 i)) i) :pattern ((t2tb188 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1 (set1 (tuple21 (tuple21 bool bool) (set1 uninterpreted_type1))))
     j) (= (t2tb188 (tb2t188 j)) j)) :pattern ((t2tb188 (tb2t188 j))) )))

(declare-fun t2tb189 ((set (tuple2 (tuple2 Bool Bool)
  (set uninterpreted_type)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Bool Bool) (set uninterpreted_type)))))
  (sort (set1 (tuple21 (tuple21 bool bool) (set1 uninterpreted_type1)))
  (t2tb189 x))))

(declare-fun tb2t189 (uni) (set (tuple2 (tuple2 Bool Bool)
  (set uninterpreted_type))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Bool Bool) (set uninterpreted_type)))))
  (! (= (tb2t189 (t2tb189 i)) i) :pattern ((t2tb189 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1 (tuple21 (tuple21 bool bool) (set1 uninterpreted_type1))) j)
     (= (t2tb189 (tb2t189 j)) j)) :pattern ((t2tb189 (tb2t189 j))) )))

(declare-fun t2tb190 ((tuple2 (tuple2 Bool Bool)
  (set uninterpreted_type))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) (set uninterpreted_type)))) (sort
  (tuple21 (tuple21 bool bool) (set1 uninterpreted_type1)) (t2tb190 x))))

(declare-fun tb2t190 (uni) (tuple2 (tuple2 Bool Bool)
  (set uninterpreted_type)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 Bool Bool) (set uninterpreted_type))))
  (! (= (tb2t190 (t2tb190 i)) i) :pattern ((t2tb190 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (tuple21 (tuple21 bool bool) (set1 uninterpreted_type1)) j)
     (= (t2tb190 (tb2t190 j)) j)) :pattern ((t2tb190 (tb2t190 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 Bool Bool)) (y (set uninterpreted_type))) (! (mem
  (set1 (tuple21 (tuple21 bool bool) (set1 uninterpreted_type1)))
  (add (tuple21 (tuple21 bool bool) (set1 uninterpreted_type1))
  (Tuple2 (tuple21 bool bool) (set1 uninterpreted_type1) (t2tb12 x)
  (t2tb3 y))
  (empty (tuple21 (tuple21 bool bool) (set1 uninterpreted_type1))))
  (infix_mnmngt (set1 uninterpreted_type1) (tuple21 bool bool)
  (t2tb11 (add6 x empty9)) (t2tb2 (add3 y empty5)))) :pattern ((tb2t189
                                                               (add
                                                               (tuple21
                                                               (tuple21 
                                                               bool bool)
                                                               (set1
                                                               uninterpreted_type1))
                                                               (Tuple2
                                                               (tuple21 
                                                               bool bool)
                                                               (set1
                                                               uninterpreted_type1)
                                                               (t2tb12 x)
                                                               (t2tb3 y))
                                                               (empty
                                                               (tuple21
                                                               (tuple21 
                                                               bool bool)
                                                               (set1
                                                               uninterpreted_type1)))))) )))

(declare-fun t2tb191 ((set (set (tuple2 (tuple2 Bool Bool)
  uninterpreted_type)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 Bool Bool) uninterpreted_type)))))
  (sort (set1 (set1 (tuple21 (tuple21 bool bool) uninterpreted_type1)))
  (t2tb191 x))))

(declare-fun tb2t191 (uni) (set (set (tuple2 (tuple2 Bool Bool)
  uninterpreted_type))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 Bool Bool) uninterpreted_type)))))
  (! (= (tb2t191 (t2tb191 i)) i) :pattern ((t2tb191 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1 (set1 (tuple21 (tuple21 bool bool) uninterpreted_type1))) j)
     (= (t2tb191 (tb2t191 j)) j)) :pattern ((t2tb191 (tb2t191 j))) )))

(declare-fun t2tb192 ((set (tuple2 (tuple2 Bool Bool)
  uninterpreted_type))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Bool Bool) uninterpreted_type)))) (sort
  (set1 (tuple21 (tuple21 bool bool) uninterpreted_type1)) (t2tb192 x))))

(declare-fun tb2t192 (uni) (set (tuple2 (tuple2 Bool Bool)
  uninterpreted_type)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Bool Bool) uninterpreted_type))))
  (! (= (tb2t192 (t2tb192 i)) i) :pattern ((t2tb192 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (tuple21 (tuple21 bool bool) uninterpreted_type1)) j)
     (= (t2tb192 (tb2t192 j)) j)) :pattern ((t2tb192 (tb2t192 j))) )))

(declare-fun t2tb193 ((tuple2 (tuple2 Bool Bool) uninterpreted_type)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) uninterpreted_type))) (sort
  (tuple21 (tuple21 bool bool) uninterpreted_type1) (t2tb193 x))))

(declare-fun tb2t193 (uni) (tuple2 (tuple2 Bool Bool) uninterpreted_type))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 Bool Bool) uninterpreted_type)))
  (! (= (tb2t193 (t2tb193 i)) i) :pattern ((t2tb193 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (tuple21 (tuple21 bool bool) uninterpreted_type1) j)
     (= (t2tb193 (tb2t193 j)) j)) :pattern ((t2tb193 (tb2t193 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 Bool Bool)) (y uninterpreted_type)) (! (mem
  (set1 (tuple21 (tuple21 bool bool) uninterpreted_type1))
  (add (tuple21 (tuple21 bool bool) uninterpreted_type1)
  (Tuple2 (tuple21 bool bool) uninterpreted_type1 (t2tb12 x) (t2tb4 y))
  (empty (tuple21 (tuple21 bool bool) uninterpreted_type1)))
  (infix_mnmngt uninterpreted_type1 (tuple21 bool bool)
  (t2tb11 (add6 x empty9))
  (add uninterpreted_type1 (t2tb4 y) (t2tb3 empty4)))) :pattern ((tb2t192
                                                                 (add
                                                                 (tuple21
                                                                 (tuple21
                                                                 bool 
                                                                 bool)
                                                                 uninterpreted_type1)
                                                                 (Tuple2
                                                                 (tuple21
                                                                 bool 
                                                                 bool)
                                                                 uninterpreted_type1
                                                                 (t2tb12 x)
                                                                 (t2tb4 y))
                                                                 (empty
                                                                 (tuple21
                                                                 (tuple21
                                                                 bool 
                                                                 bool)
                                                                 uninterpreted_type1))))) )))

(declare-fun t2tb194 ((set (set (tuple2 (tuple2 Bool Bool)
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
  (t2tb194 x))))

(declare-fun tb2t194 (uni) (set (set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))))
  (! (= (tb2t194 (t2tb194 i)) i) :pattern ((t2tb194 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb194 (tb2t194 j)) j) :pattern ((t2tb194 (tb2t194 j))) )))

(declare-fun t2tb195 ((set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))) (sort
  (set1
  (tuple21 (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (t2tb195 x))))

(declare-fun tb2t195 (uni) (set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))))
  (! (= (tb2t195 (t2tb195 i)) i) :pattern ((t2tb195 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb195 (tb2t195 j)) j) :pattern ((t2tb195 (tb2t195 j))) )))

(declare-fun t2tb196 ((tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))) (sort
  (tuple21 (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb196 x))))

(declare-fun tb2t196 (uni) (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))))
  (! (= (tb2t196 (t2tb196 i)) i) :pattern ((t2tb196 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb196 (tb2t196 j)) j) :pattern ((t2tb196 (tb2t196 j))) )))

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
  (t2tb12 x) (t2tb6 y))
  (empty
  (tuple21 (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (infix_mnmngt
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 bool bool) (t2tb11 (add6 x empty9))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb6 y) (t2tb5 empty3)))) :pattern ((tb2t195
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
                                        bool) (set1 int)) (t2tb12 x)
                                        (t2tb6 y))
                                        (empty
                                        (tuple21 (tuple21 bool bool)
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int))))))) )))

(declare-fun t2tb197 ((set (set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))) (t2tb197 x))))

(declare-fun tb2t197 (uni) (set (set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))))
  (! (= (tb2t197 (t2tb197 i)) i) :pattern ((t2tb197 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21 (tuple21 bool bool)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))) j)
     (= (t2tb197 (tb2t197 j)) j)) :pattern ((t2tb197 (tb2t197 j))) )))

(declare-fun t2tb198 ((set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool))))) (sort
  (set1
  (tuple21 (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))) (t2tb198 x))))

(declare-fun tb2t198 (uni) (set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool)))))
  (! (= (tb2t198 (t2tb198 i)) i) :pattern ((t2tb198 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21 (tuple21 bool bool)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool))) j)
     (= (t2tb198 (tb2t198 j)) j)) :pattern ((t2tb198 (tb2t198 j))) )))

(declare-fun t2tb199 ((tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool)))) (sort
  (tuple21 (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb199 x))))

(declare-fun tb2t199 (uni) (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool)))) (! (= (tb2t199 (t2tb199 i)) i) :pattern ((t2tb199 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 (tuple21 bool bool)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) j)
     (= (t2tb199 (tb2t199 j)) j)) :pattern ((t2tb199 (tb2t199 j))) )))

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
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb12 x) (t2tb8 y))
  (empty
  (tuple21 (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))))
  (infix_mnmngt (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 bool bool) (t2tb11 (add6 x empty9)) (t2tb7 (add4 y empty7)))) :pattern (
  (tb2t198
  (add
  (tuple21 (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (Tuple2 (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb12 x) (t2tb8 y))
  (empty
  (tuple21 (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))))) )))

(declare-fun t2tb200 ((tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 Bool Bool)
  Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 Bool Bool) Bool))))
  (sort (tuple21 (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool))
  (t2tb200 x))))

(declare-fun tb2t200 (uni) (tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 Bool
  Bool) Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 Bool Bool) Bool))))
  (! (= (tb2t200 (t2tb200 i)) i) :pattern ((t2tb200 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool)) j)
     (= (t2tb200 (tb2t200 j)) j)) :pattern ((t2tb200 (tb2t200 j))) )))

(declare-fun t2tb201 ((set (set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 Bool Bool) Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 Bool Bool)
  Bool)))))) (sort
  (set1
  (set1 (tuple21 (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool))))
  (t2tb201 x))))

(declare-fun tb2t201 (uni) (set (set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 Bool Bool) Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 Bool Bool)
  Bool)))))) (! (= (tb2t201 (t2tb201 i)) i) :pattern ((t2tb201 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1 (tuple21 (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool))))
     j) (= (t2tb201 (tb2t201 j)) j)) :pattern ((t2tb201 (tb2t201 j))) )))

(declare-fun t2tb202 ((set (tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 Bool
  Bool) Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 Bool Bool)
  Bool))))) (sort
  (set1 (tuple21 (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool)))
  (t2tb202 x))))

(declare-fun tb2t202 (uni) (set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 Bool Bool) Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 Bool Bool)
  Bool))))) (! (= (tb2t202 (t2tb202 i)) i) :pattern ((t2tb202 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1 (tuple21 (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool)))
     j) (= (t2tb202 (tb2t202 j)) j)) :pattern ((t2tb202 (tb2t202 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 Bool Bool)) (y (tuple2 (tuple2 Bool Bool) Bool)))
  (! (mem
  (set1 (tuple21 (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool)))
  (add (tuple21 (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool))
  (Tuple2 (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool) (t2tb12 x)
  (t2tb10 y))
  (empty (tuple21 (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool))))
  (infix_mnmngt (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool)
  (t2tb11 (add6 x empty9)) (t2tb9 (add5 y empty8)))) :pattern ((tb2t202
                                                               (add
                                                               (tuple21
                                                               (tuple21 
                                                               bool bool)
                                                               (tuple21
                                                               (tuple21 
                                                               bool bool)
                                                               bool))
                                                               (Tuple2
                                                               (tuple21 
                                                               bool bool)
                                                               (tuple21
                                                               (tuple21 
                                                               bool bool)
                                                               bool)
                                                               (t2tb12 x)
                                                               (t2tb10 y))
                                                               (empty
                                                               (tuple21
                                                               (tuple21 
                                                               bool bool)
                                                               (tuple21
                                                               (tuple21 
                                                               bool bool)
                                                               bool)))))) )))

(declare-fun t2tb203 ((set (set (tuple2 (tuple2 Bool Bool) (tuple2 Bool
  Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 Bool Bool) (tuple2 Bool Bool))))))
  (sort (set1 (set1 (tuple21 (tuple21 bool bool) (tuple21 bool bool))))
  (t2tb203 x))))

(declare-fun tb2t203 (uni) (set (set (tuple2 (tuple2 Bool Bool) (tuple2 Bool
  Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 Bool Bool) (tuple2 Bool Bool))))))
  (! (= (tb2t203 (t2tb203 i)) i) :pattern ((t2tb203 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1 (set1 (tuple21 (tuple21 bool bool) (tuple21 bool bool)))) j)
     (= (t2tb203 (tb2t203 j)) j)) :pattern ((t2tb203 (tb2t203 j))) )))

(declare-fun t2tb204 ((set (tuple2 (tuple2 Bool Bool) (tuple2 Bool
  Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Bool Bool) (tuple2 Bool Bool))))) (sort
  (set1 (tuple21 (tuple21 bool bool) (tuple21 bool bool))) (t2tb204 x))))

(declare-fun tb2t204 (uni) (set (tuple2 (tuple2 Bool Bool) (tuple2 Bool
  Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Bool Bool) (tuple2 Bool Bool)))))
  (! (= (tb2t204 (t2tb204 i)) i) :pattern ((t2tb204 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (tuple21 (tuple21 bool bool) (tuple21 bool bool))) j)
     (= (t2tb204 (tb2t204 j)) j)) :pattern ((t2tb204 (tb2t204 j))) )))

(declare-fun t2tb205 ((tuple2 (tuple2 Bool Bool) (tuple2 Bool Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) (tuple2 Bool Bool)))) (sort
  (tuple21 (tuple21 bool bool) (tuple21 bool bool)) (t2tb205 x))))

(declare-fun tb2t205 (uni) (tuple2 (tuple2 Bool Bool) (tuple2 Bool Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 Bool Bool) (tuple2 Bool Bool))))
  (! (= (tb2t205 (t2tb205 i)) i) :pattern ((t2tb205 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (tuple21 (tuple21 bool bool) (tuple21 bool bool)) j)
     (= (t2tb205 (tb2t205 j)) j)) :pattern ((t2tb205 (tb2t205 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 Bool Bool)) (y (tuple2 Bool Bool))) (! (mem
  (set1 (tuple21 (tuple21 bool bool) (tuple21 bool bool)))
  (add (tuple21 (tuple21 bool bool) (tuple21 bool bool))
  (Tuple2 (tuple21 bool bool) (tuple21 bool bool) (t2tb12 x) (t2tb12 y))
  (empty (tuple21 (tuple21 bool bool) (tuple21 bool bool))))
  (infix_mnmngt (tuple21 bool bool) (tuple21 bool bool)
  (t2tb11 (add6 x empty9)) (t2tb11 (add6 y empty9)))) :pattern ((tb2t204
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
                                                                (t2tb12 x)
                                                                (t2tb12 y))
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
  (t2tb9 (add5 (Tuple22 x y) empty8))
  (infix_mnmngt bool (tuple21 bool bool) (t2tb11 (add6 x empty9))
  (t2tb14 (add1 y empty1)))) :pattern ((add5 (Tuple22 x y) empty8)) )))

(declare-fun t2tb206 ((set (set (tuple2 (tuple2 Bool Bool) Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 Bool Bool) Int))))) (sort
  (set1 (set1 (tuple21 (tuple21 bool bool) int))) (t2tb206 x))))

(declare-fun tb2t206 (uni) (set (set (tuple2 (tuple2 Bool Bool) Int))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 Bool Bool) Int)))))
  (! (= (tb2t206 (t2tb206 i)) i) :pattern ((t2tb206 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb206 (tb2t206 j)) j) :pattern ((t2tb206 (tb2t206 j))) )))

(declare-fun t2tb207 ((set (tuple2 (tuple2 Bool Bool) Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Bool Bool) Int)))) (sort
  (set1 (tuple21 (tuple21 bool bool) int)) (t2tb207 x))))

(declare-fun tb2t207 (uni) (set (tuple2 (tuple2 Bool Bool) Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Bool Bool) Int))))
  (! (= (tb2t207 (t2tb207 i)) i) :pattern ((t2tb207 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb207 (tb2t207 j)) j) :pattern ((t2tb207 (tb2t207 j))) )))

(declare-fun t2tb208 ((tuple2 (tuple2 Bool Bool) Int)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) Int))) (sort
  (tuple21 (tuple21 bool bool) int) (t2tb208 x))))

(declare-fun tb2t208 (uni) (tuple2 (tuple2 Bool Bool) Int))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 Bool Bool) Int)))
  (! (= (tb2t208 (t2tb208 i)) i) :pattern ((t2tb208 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb208 (tb2t208 j)) j) :pattern ((t2tb208 (tb2t208 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 Bool Bool)) (y Int)) (! (mem
  (set1 (tuple21 (tuple21 bool bool) int))
  (add (tuple21 (tuple21 bool bool) int)
  (Tuple2 (tuple21 bool bool) int (t2tb12 x) (t2tb16 y))
  (empty (tuple21 (tuple21 bool bool) int)))
  (infix_mnmngt int (tuple21 bool bool) (t2tb11 (add6 x empty9))
  (t2tb15 (add2 y empty2)))) :pattern ((tb2t207
                                       (add (tuple21 (tuple21 bool bool) int)
                                       (Tuple2 (tuple21 bool bool) int
                                       (t2tb12 x) (t2tb16 y))
                                       (empty
                                       (tuple21 (tuple21 bool bool) int))))) )))

;; singleton_is_function
  (assert
  (forall ((b ty))
  (forall ((x (tuple2 Bool Bool)) (y uni)) (! (mem
  (set1 (tuple21 (tuple21 bool bool) b))
  (add (tuple21 (tuple21 bool bool) b)
  (Tuple2 (tuple21 bool bool) b (t2tb12 x) y)
  (empty (tuple21 (tuple21 bool bool) b)))
  (infix_mnmngt b (tuple21 bool bool) (t2tb11 (add6 x empty9))
  (add b y (empty b)))) :pattern ((add (tuple21 (tuple21 bool bool) b)
                                  (Tuple2 (tuple21 bool bool) b (t2tb12 x) y)
                                  (empty (tuple21 (tuple21 bool bool) b)))) ))))

(declare-fun t2tb209 ((set (set (tuple2 Bool
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Bool (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type))))))) (sort
  (set1
  (set1
  (tuple21 bool
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))))) (t2tb209 x))))

(declare-fun tb2t209 (uni) (set (set (tuple2 Bool
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Bool (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type)))))))
  (! (= (tb2t209 (t2tb209 i)) i) :pattern ((t2tb209 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21 bool
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1))))) j) (= (t2tb209 (tb2t209 j)) j)) :pattern (
  (t2tb209 (tb2t209 j))) )))

(declare-fun t2tb210 ((set (tuple2 Bool (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Bool (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)))))) (sort
  (set1
  (tuple21 bool
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)))) (t2tb210 x))))

(declare-fun tb2t210 (uni) (set (tuple2 Bool
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Bool (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type))))))
  (! (= (tb2t210 (t2tb210 i)) i) :pattern ((t2tb210 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21 bool
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1)))) j) (= (t2tb210 (tb2t210 j)) j)) :pattern (
  (t2tb210 (tb2t210 j))) )))

(declare-fun t2tb211 ((tuple2 Bool (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Bool (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type))))) (sort
  (tuple21 bool
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))) (t2tb211 x))))

(declare-fun tb2t211 (uni) (tuple2 Bool (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type))))

;; BridgeL
  (assert
  (forall ((i (tuple2 Bool (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type)))))
  (! (= (tb2t211 (t2tb211 i)) i) :pattern ((t2tb211 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 bool
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1))) j) (= (t2tb211 (tb2t211 j)) j)) :pattern (
  (t2tb211 (tb2t211 j))) )))

;; singleton_is_function
  (assert
  (forall ((x Bool) (y (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))) (! (mem
  (set1
  (tuple21 bool
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))))
  (add
  (tuple21 bool
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)))
  (Tuple2 bool
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb13 x) (t2tb1 y))
  (empty
  (tuple21 bool
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)))))
  (infix_mnmngt
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) bool (t2tb14 (add1 x empty1))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb1 y) (t2tb empty6)))) :pattern ((tb2t210
                                                                   (add
                                                                   (tuple21
                                                                   bool
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   bool 
                                                                   bool)
                                                                   bool)
                                                                   bool)
                                                                   (set1
                                                                   uninterpreted_type1)))
                                                                   (Tuple2
                                                                   bool
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   bool 
                                                                   bool)
                                                                   bool)
                                                                   bool)
                                                                   (set1
                                                                   uninterpreted_type1))
                                                                   (t2tb13 x)
                                                                   (t2tb1 y))
                                                                   (empty
                                                                   (tuple21
                                                                   bool
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   bool 
                                                                   bool)
                                                                   bool)
                                                                   bool)
                                                                   (set1
                                                                   uninterpreted_type1))))))) )))

(declare-fun t2tb212 ((set (set (tuple2 Bool
  (set uninterpreted_type))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Bool (set uninterpreted_type)))))) (sort
  (set1 (set1 (tuple21 bool (set1 uninterpreted_type1)))) (t2tb212 x))))

(declare-fun tb2t212 (uni) (set (set (tuple2 Bool
  (set uninterpreted_type)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Bool (set uninterpreted_type))))))
  (! (= (tb2t212 (t2tb212 i)) i) :pattern ((t2tb212 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (set1 (tuple21 bool (set1 uninterpreted_type1)))) j)
     (= (t2tb212 (tb2t212 j)) j)) :pattern ((t2tb212 (tb2t212 j))) )))

(declare-fun t2tb213 ((set (tuple2 Bool (set uninterpreted_type)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Bool (set uninterpreted_type))))) (sort
  (set1 (tuple21 bool (set1 uninterpreted_type1))) (t2tb213 x))))

(declare-fun tb2t213 (uni) (set (tuple2 Bool (set uninterpreted_type))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Bool (set uninterpreted_type)))))
  (! (= (tb2t213 (t2tb213 i)) i) :pattern ((t2tb213 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (tuple21 bool (set1 uninterpreted_type1))) j)
     (= (t2tb213 (tb2t213 j)) j)) :pattern ((t2tb213 (tb2t213 j))) )))

(declare-fun t2tb214 ((tuple2 Bool (set uninterpreted_type))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Bool (set uninterpreted_type)))) (sort
  (tuple21 bool (set1 uninterpreted_type1)) (t2tb214 x))))

(declare-fun tb2t214 (uni) (tuple2 Bool (set uninterpreted_type)))

;; BridgeL
  (assert
  (forall ((i (tuple2 Bool (set uninterpreted_type))))
  (! (= (tb2t214 (t2tb214 i)) i) :pattern ((t2tb214 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (tuple21 bool (set1 uninterpreted_type1)) j)
     (= (t2tb214 (tb2t214 j)) j)) :pattern ((t2tb214 (tb2t214 j))) )))

;; singleton_is_function
  (assert
  (forall ((x Bool) (y (set uninterpreted_type))) (! (mem
  (set1 (tuple21 bool (set1 uninterpreted_type1)))
  (add (tuple21 bool (set1 uninterpreted_type1))
  (Tuple2 bool (set1 uninterpreted_type1) (t2tb13 x) (t2tb3 y))
  (empty (tuple21 bool (set1 uninterpreted_type1))))
  (infix_mnmngt (set1 uninterpreted_type1) bool (t2tb14 (add1 x empty1))
  (t2tb2 (add3 y empty5)))) :pattern ((tb2t213
                                      (add
                                      (tuple21 bool
                                      (set1 uninterpreted_type1))
                                      (Tuple2 bool (set1 uninterpreted_type1)
                                      (t2tb13 x) (t2tb3 y))
                                      (empty
                                      (tuple21 bool
                                      (set1 uninterpreted_type1)))))) )))

(declare-fun t2tb215 ((tuple2 Bool uninterpreted_type)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Bool uninterpreted_type))) (sort
  (tuple21 bool uninterpreted_type1) (t2tb215 x))))

(declare-fun tb2t215 (uni) (tuple2 Bool uninterpreted_type))

;; BridgeL
  (assert
  (forall ((i (tuple2 Bool uninterpreted_type)))
  (! (= (tb2t215 (t2tb215 i)) i) :pattern ((t2tb215 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (tuple21 bool uninterpreted_type1) j)
     (= (t2tb215 (tb2t215 j)) j)) :pattern ((t2tb215 (tb2t215 j))) )))

(declare-fun t2tb216 ((set (set (tuple2 Bool uninterpreted_type)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Bool uninterpreted_type))))) (sort
  (set1 (set1 (tuple21 bool uninterpreted_type1))) (t2tb216 x))))

(declare-fun tb2t216 (uni) (set (set (tuple2 Bool uninterpreted_type))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Bool uninterpreted_type)))))
  (! (= (tb2t216 (t2tb216 i)) i) :pattern ((t2tb216 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (set1 (tuple21 bool uninterpreted_type1))) j)
     (= (t2tb216 (tb2t216 j)) j)) :pattern ((t2tb216 (tb2t216 j))) )))

(declare-fun t2tb217 ((set (tuple2 Bool uninterpreted_type))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Bool uninterpreted_type)))) (sort
  (set1 (tuple21 bool uninterpreted_type1)) (t2tb217 x))))

(declare-fun tb2t217 (uni) (set (tuple2 Bool uninterpreted_type)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Bool uninterpreted_type))))
  (! (= (tb2t217 (t2tb217 i)) i) :pattern ((t2tb217 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (tuple21 bool uninterpreted_type1)) j)
     (= (t2tb217 (tb2t217 j)) j)) :pattern ((t2tb217 (tb2t217 j))) )))

;; singleton_is_function
  (assert
  (forall ((x Bool) (y uninterpreted_type)) (! (mem
  (set1 (tuple21 bool uninterpreted_type1))
  (add (tuple21 bool uninterpreted_type1)
  (Tuple2 bool uninterpreted_type1 (t2tb13 x) (t2tb4 y))
  (empty (tuple21 bool uninterpreted_type1)))
  (infix_mnmngt uninterpreted_type1 bool (t2tb14 (add1 x empty1))
  (add uninterpreted_type1 (t2tb4 y) (t2tb3 empty4)))) :pattern ((tb2t217
                                                                 (add
                                                                 (tuple21
                                                                 bool
                                                                 uninterpreted_type1)
                                                                 (Tuple2 
                                                                 bool
                                                                 uninterpreted_type1
                                                                 (t2tb13 x)
                                                                 (t2tb4 y))
                                                                 (empty
                                                                 (tuple21
                                                                 bool
                                                                 uninterpreted_type1))))) )))

(declare-fun t2tb218 ((set (set (tuple2 Bool
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Bool (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))))) (sort
  (set1
  (set1
  (tuple21 bool
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (t2tb218 x))))

(declare-fun tb2t218 (uni) (set (set (tuple2 Bool
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Bool (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))))))
  (! (= (tb2t218 (t2tb218 i)) i) :pattern ((t2tb218 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb218 (tb2t218 j)) j) :pattern ((t2tb218 (tb2t218 j))) )))

(declare-fun t2tb219 ((set (tuple2 Bool (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Bool (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))))) (sort
  (set1
  (tuple21 bool
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (t2tb219 x))))

(declare-fun tb2t219 (uni) (set (tuple2 Bool
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Bool (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))))
  (! (= (tb2t219 (t2tb219 i)) i) :pattern ((t2tb219 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb219 (tb2t219 j)) j) :pattern ((t2tb219 (tb2t219 j))) )))

(declare-fun t2tb220 ((tuple2 Bool (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Bool (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (sort
  (tuple21 bool
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb220 x))))

(declare-fun tb2t220 (uni) (tuple2 Bool (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))

;; BridgeL
  (assert
  (forall ((i (tuple2 Bool (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))))
  (! (= (tb2t220 (t2tb220 i)) i) :pattern ((t2tb220 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb220 (tb2t220 j)) j) :pattern ((t2tb220 (tb2t220 j))) )))

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
  (t2tb13 x) (t2tb6 y))
  (empty
  (tuple21 bool
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (infix_mnmngt
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)) 
  bool (t2tb14 (add1 x empty1))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb6 y) (t2tb5 empty3)))) :pattern ((tb2t219
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
                                        bool) (set1 int)) (t2tb13 x)
                                        (t2tb6 y))
                                        (empty
                                        (tuple21 bool
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int))))))) )))

(declare-fun t2tb221 ((set (set (tuple2 Bool (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Bool (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool)))))) (sort
  (set1
  (set1 (tuple21 bool (tuple21 (tuple21 (tuple21 bool bool) bool) bool))))
  (t2tb221 x))))

(declare-fun tb2t221 (uni) (set (set (tuple2 Bool
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Bool (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool)))))) (! (= (tb2t221 (t2tb221 i)) i) :pattern ((t2tb221 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1 (tuple21 bool (tuple21 (tuple21 (tuple21 bool bool) bool) bool))))
     j) (= (t2tb221 (tb2t221 j)) j)) :pattern ((t2tb221 (tb2t221 j))) )))

(declare-fun t2tb222 ((set (tuple2 Bool (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Bool (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))))) (sort
  (set1 (tuple21 bool (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))
  (t2tb222 x))))

(declare-fun tb2t222 (uni) (set (tuple2 Bool (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Bool (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))))) (! (= (tb2t222 (t2tb222 i)) i) :pattern ((t2tb222 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1 (tuple21 bool (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))
     j) (= (t2tb222 (tb2t222 j)) j)) :pattern ((t2tb222 (tb2t222 j))) )))

(declare-fun t2tb223 ((tuple2 Bool (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Bool (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (sort (tuple21 bool (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (t2tb223 x))))

(declare-fun tb2t223 (uni) (tuple2 Bool (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 Bool (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (! (= (tb2t223 (t2tb223 i)) i) :pattern ((t2tb223 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 bool (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) j)
     (= (t2tb223 (tb2t223 j)) j)) :pattern ((t2tb223 (tb2t223 j))) )))

;; singleton_is_function
  (assert
  (forall ((x Bool) (y (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (! (mem
  (set1 (tuple21 bool (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))
  (add (tuple21 bool (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (Tuple2 bool (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb13 x)
  (t2tb8 y))
  (empty (tuple21 bool (tuple21 (tuple21 (tuple21 bool bool) bool) bool))))
  (infix_mnmngt (tuple21 (tuple21 (tuple21 bool bool) bool) bool) bool
  (t2tb14 (add1 x empty1)) (t2tb7 (add4 y empty7)))) :pattern ((tb2t222
                                                               (add
                                                               (tuple21 
                                                               bool
                                                               (tuple21
                                                               (tuple21
                                                               (tuple21 
                                                               bool bool)
                                                               bool) 
                                                               bool))
                                                               (Tuple2 
                                                               bool
                                                               (tuple21
                                                               (tuple21
                                                               (tuple21 
                                                               bool bool)
                                                               bool) 
                                                               bool)
                                                               (t2tb13 x)
                                                               (t2tb8 y))
                                                               (empty
                                                               (tuple21 
                                                               bool
                                                               (tuple21
                                                               (tuple21
                                                               (tuple21 
                                                               bool bool)
                                                               bool) 
                                                               bool)))))) )))

(declare-fun t2tb224 ((set (set (tuple2 Bool (tuple2 (tuple2 Bool Bool)
  Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Bool (tuple2 (tuple2 Bool Bool) Bool))))))
  (sort (set1 (set1 (tuple21 bool (tuple21 (tuple21 bool bool) bool))))
  (t2tb224 x))))

(declare-fun tb2t224 (uni) (set (set (tuple2 Bool (tuple2 (tuple2 Bool Bool)
  Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Bool (tuple2 (tuple2 Bool Bool) Bool))))))
  (! (= (tb2t224 (t2tb224 i)) i) :pattern ((t2tb224 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1 (set1 (tuple21 bool (tuple21 (tuple21 bool bool) bool)))) j)
     (= (t2tb224 (tb2t224 j)) j)) :pattern ((t2tb224 (tb2t224 j))) )))

;; singleton_is_function
  (assert
  (forall ((x Bool) (y (tuple2 (tuple2 Bool Bool) Bool))) (! (mem
  (set1 (tuple21 bool (tuple21 (tuple21 bool bool) bool)))
  (add (tuple21 bool (tuple21 (tuple21 bool bool) bool))
  (Tuple2 bool (tuple21 (tuple21 bool bool) bool) (t2tb13 x) (t2tb10 y))
  (empty (tuple21 bool (tuple21 (tuple21 bool bool) bool))))
  (infix_mnmngt (tuple21 (tuple21 bool bool) bool) bool
  (t2tb14 (add1 x empty1)) (t2tb9 (add5 y empty8)))) :pattern ((tb2t25
                                                               (add
                                                               (tuple21 
                                                               bool
                                                               (tuple21
                                                               (tuple21 
                                                               bool bool)
                                                               bool))
                                                               (Tuple2 
                                                               bool
                                                               (tuple21
                                                               (tuple21 
                                                               bool bool)
                                                               bool)
                                                               (t2tb13 x)
                                                               (t2tb10 y))
                                                               (empty
                                                               (tuple21 
                                                               bool
                                                               (tuple21
                                                               (tuple21 
                                                               bool bool)
                                                               bool)))))) )))

(declare-fun t2tb225 ((set (set (tuple2 Bool (tuple2 Bool Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Bool (tuple2 Bool Bool)))))) (sort
  (set1 (set1 (tuple21 bool (tuple21 bool bool)))) (t2tb225 x))))

(declare-fun tb2t225 (uni) (set (set (tuple2 Bool (tuple2 Bool Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Bool (tuple2 Bool Bool))))))
  (! (= (tb2t225 (t2tb225 i)) i) :pattern ((t2tb225 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (set1 (tuple21 bool (tuple21 bool bool)))) j)
     (= (t2tb225 (tb2t225 j)) j)) :pattern ((t2tb225 (tb2t225 j))) )))

;; singleton_is_function
  (assert
  (forall ((x Bool) (y (tuple2 Bool Bool))) (! (mem
  (set1 (tuple21 bool (tuple21 bool bool)))
  (add (tuple21 bool (tuple21 bool bool))
  (Tuple2 bool (tuple21 bool bool) (t2tb13 x) (t2tb12 y))
  (empty (tuple21 bool (tuple21 bool bool))))
  (infix_mnmngt (tuple21 bool bool) bool (t2tb14 (add1 x empty1))
  (t2tb11 (add6 y empty9)))) :pattern ((tb2t27
                                       (add
                                       (tuple21 bool (tuple21 bool bool))
                                       (Tuple2 bool (tuple21 bool bool)
                                       (t2tb13 x) (t2tb12 y))
                                       (empty
                                       (tuple21 bool (tuple21 bool bool)))))) )))

;; singleton_is_function
  (assert
  (forall ((x Bool) (y Bool)) (! (mem (set1 (tuple21 bool bool))
  (t2tb11 (add6 (Tuple21 x y) empty9))
  (infix_mnmngt bool bool (t2tb14 (add1 x empty1)) (t2tb14 (add1 y empty1)))) :pattern (
  (add6 (Tuple21 x y) empty9)) )))

(declare-fun t2tb226 ((set (set (tuple2 Bool Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Bool Int))))) (sort
  (set1 (set1 (tuple21 bool int))) (t2tb226 x))))

(declare-fun tb2t226 (uni) (set (set (tuple2 Bool Int))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Bool Int)))))
  (! (= (tb2t226 (t2tb226 i)) i) :pattern ((t2tb226 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb226 (tb2t226 j)) j) :pattern ((t2tb226 (tb2t226 j))) )))

(declare-fun t2tb227 ((set (tuple2 Bool Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Bool Int)))) (sort (set1 (tuple21 bool int))
  (t2tb227 x))))

(declare-fun tb2t227 (uni) (set (tuple2 Bool Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Bool Int))))
  (! (= (tb2t227 (t2tb227 i)) i) :pattern ((t2tb227 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb227 (tb2t227 j)) j) :pattern ((t2tb227 (tb2t227 j))) )))

(declare-fun t2tb228 ((tuple2 Bool Int)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Bool Int))) (sort (tuple21 bool int) (t2tb228 x))))

(declare-fun tb2t228 (uni) (tuple2 Bool Int))

;; BridgeL
  (assert
  (forall ((i (tuple2 Bool Int)))
  (! (= (tb2t228 (t2tb228 i)) i) :pattern ((t2tb228 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb228 (tb2t228 j)) j) :pattern ((t2tb228 (tb2t228 j))) )))

;; singleton_is_function
  (assert
  (forall ((x Bool) (y Int)) (! (mem (set1 (tuple21 bool int))
  (add (tuple21 bool int) (Tuple2 bool int (t2tb13 x) (t2tb16 y))
  (empty (tuple21 bool int)))
  (infix_mnmngt int bool (t2tb14 (add1 x empty1)) (t2tb15 (add2 y empty2)))) :pattern (
  (tb2t227
  (add (tuple21 bool int) (Tuple2 bool int (t2tb13 x) (t2tb16 y))
  (empty (tuple21 bool int))))) )))

;; singleton_is_function
  (assert
  (forall ((b ty))
  (forall ((x Bool) (y uni)) (! (mem (set1 (tuple21 bool b))
  (add (tuple21 bool b) (Tuple2 bool b (t2tb13 x) y)
  (empty (tuple21 bool b)))
  (infix_mnmngt b bool (t2tb14 (add1 x empty1)) (add b y (empty b)))) :pattern (
  (add (tuple21 bool b) (Tuple2 bool b (t2tb13 x) y)
  (empty (tuple21 bool b)))) ))))

(declare-fun t2tb229 ((set (set (tuple2 Int
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Int (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type))))))) (sort
  (set1
  (set1
  (tuple21 int
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))))) (t2tb229 x))))

(declare-fun tb2t229 (uni) (set (set (tuple2 Int
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Int (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type)))))))
  (! (= (tb2t229 (t2tb229 i)) i) :pattern ((t2tb229 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb229 (tb2t229 j)) j) :pattern ((t2tb229 (tb2t229 j))) )))

(declare-fun t2tb230 ((set (tuple2 Int (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)))))) (sort
  (set1
  (tuple21 int
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)))) (t2tb230 x))))

(declare-fun tb2t230 (uni) (set (tuple2 Int
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type))))))
  (! (= (tb2t230 (t2tb230 i)) i) :pattern ((t2tb230 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb230 (tb2t230 j)) j) :pattern ((t2tb230 (tb2t230 j))) )))

(declare-fun t2tb231 ((tuple2 Int (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Int (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type))))) (sort
  (tuple21 int
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))) (t2tb231 x))))

(declare-fun tb2t231 (uni) (tuple2 Int (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type))))

;; BridgeL
  (assert
  (forall ((i (tuple2 Int (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type)))))
  (! (= (tb2t231 (t2tb231 i)) i) :pattern ((t2tb231 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb231 (tb2t231 j)) j) :pattern ((t2tb231 (tb2t231 j))) )))

;; singleton_is_function
  (assert
  (forall ((x Int) (y (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))) (! (mem
  (set1
  (tuple21 int
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))))
  (add
  (tuple21 int
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)))
  (Tuple2 int
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb16 x) (t2tb1 y))
  (empty
  (tuple21 int
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)))))
  (infix_mnmngt
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) int (t2tb15 (add2 x empty2))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb1 y) (t2tb empty6)))) :pattern ((tb2t230
                                                                   (add
                                                                   (tuple21
                                                                   int
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   bool 
                                                                   bool)
                                                                   bool)
                                                                   bool)
                                                                   (set1
                                                                   uninterpreted_type1)))
                                                                   (Tuple2
                                                                   int
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   bool 
                                                                   bool)
                                                                   bool)
                                                                   bool)
                                                                   (set1
                                                                   uninterpreted_type1))
                                                                   (t2tb16 x)
                                                                   (t2tb1 y))
                                                                   (empty
                                                                   (tuple21
                                                                   int
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   (tuple21
                                                                   bool 
                                                                   bool)
                                                                   bool)
                                                                   bool)
                                                                   (set1
                                                                   uninterpreted_type1))))))) )))

(declare-fun t2tb232 ((set (set (tuple2 Int (set uninterpreted_type))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Int (set uninterpreted_type)))))) (sort
  (set1 (set1 (tuple21 int (set1 uninterpreted_type1)))) (t2tb232 x))))

(declare-fun tb2t232 (uni) (set (set (tuple2 Int (set uninterpreted_type)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Int (set uninterpreted_type))))))
  (! (= (tb2t232 (t2tb232 i)) i) :pattern ((t2tb232 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb232 (tb2t232 j)) j) :pattern ((t2tb232 (tb2t232 j))) )))

(declare-fun t2tb233 ((set (tuple2 Int (set uninterpreted_type)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int (set uninterpreted_type))))) (sort
  (set1 (tuple21 int (set1 uninterpreted_type1))) (t2tb233 x))))

(declare-fun tb2t233 (uni) (set (tuple2 Int (set uninterpreted_type))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int (set uninterpreted_type)))))
  (! (= (tb2t233 (t2tb233 i)) i) :pattern ((t2tb233 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb233 (tb2t233 j)) j) :pattern ((t2tb233 (tb2t233 j))) )))

(declare-fun t2tb234 ((tuple2 Int (set uninterpreted_type))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Int (set uninterpreted_type)))) (sort
  (tuple21 int (set1 uninterpreted_type1)) (t2tb234 x))))

(declare-fun tb2t234 (uni) (tuple2 Int (set uninterpreted_type)))

;; BridgeL
  (assert
  (forall ((i (tuple2 Int (set uninterpreted_type))))
  (! (= (tb2t234 (t2tb234 i)) i) :pattern ((t2tb234 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb234 (tb2t234 j)) j) :pattern ((t2tb234 (tb2t234 j))) )))

;; singleton_is_function
  (assert
  (forall ((x Int) (y (set uninterpreted_type))) (! (mem
  (set1 (tuple21 int (set1 uninterpreted_type1)))
  (add (tuple21 int (set1 uninterpreted_type1))
  (Tuple2 int (set1 uninterpreted_type1) (t2tb16 x) (t2tb3 y))
  (empty (tuple21 int (set1 uninterpreted_type1))))
  (infix_mnmngt (set1 uninterpreted_type1) int (t2tb15 (add2 x empty2))
  (t2tb2 (add3 y empty5)))) :pattern ((tb2t233
                                      (add
                                      (tuple21 int
                                      (set1 uninterpreted_type1))
                                      (Tuple2 int (set1 uninterpreted_type1)
                                      (t2tb16 x) (t2tb3 y))
                                      (empty
                                      (tuple21 int
                                      (set1 uninterpreted_type1)))))) )))

(declare-fun t2tb235 ((set (set (tuple2 Int uninterpreted_type)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Int uninterpreted_type))))) (sort
  (set1 (set1 (tuple21 int uninterpreted_type1))) (t2tb235 x))))

(declare-fun tb2t235 (uni) (set (set (tuple2 Int uninterpreted_type))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Int uninterpreted_type)))))
  (! (= (tb2t235 (t2tb235 i)) i) :pattern ((t2tb235 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb235 (tb2t235 j)) j) :pattern ((t2tb235 (tb2t235 j))) )))

(declare-fun t2tb236 ((set (tuple2 Int uninterpreted_type))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int uninterpreted_type)))) (sort
  (set1 (tuple21 int uninterpreted_type1)) (t2tb236 x))))

(declare-fun tb2t236 (uni) (set (tuple2 Int uninterpreted_type)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int uninterpreted_type))))
  (! (= (tb2t236 (t2tb236 i)) i) :pattern ((t2tb236 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb236 (tb2t236 j)) j) :pattern ((t2tb236 (tb2t236 j))) )))

(declare-fun t2tb237 ((tuple2 Int uninterpreted_type)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Int uninterpreted_type))) (sort
  (tuple21 int uninterpreted_type1) (t2tb237 x))))

(declare-fun tb2t237 (uni) (tuple2 Int uninterpreted_type))

;; BridgeL
  (assert
  (forall ((i (tuple2 Int uninterpreted_type)))
  (! (= (tb2t237 (t2tb237 i)) i) :pattern ((t2tb237 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb237 (tb2t237 j)) j) :pattern ((t2tb237 (tb2t237 j))) )))

;; singleton_is_function
  (assert
  (forall ((x Int) (y uninterpreted_type)) (! (mem
  (set1 (tuple21 int uninterpreted_type1))
  (add (tuple21 int uninterpreted_type1)
  (Tuple2 int uninterpreted_type1 (t2tb16 x) (t2tb4 y))
  (empty (tuple21 int uninterpreted_type1)))
  (infix_mnmngt uninterpreted_type1 int (t2tb15 (add2 x empty2))
  (add uninterpreted_type1 (t2tb4 y) (t2tb3 empty4)))) :pattern ((tb2t236
                                                                 (add
                                                                 (tuple21 
                                                                 int
                                                                 uninterpreted_type1)
                                                                 (Tuple2 
                                                                 int
                                                                 uninterpreted_type1
                                                                 (t2tb16 x)
                                                                 (t2tb4 y))
                                                                 (empty
                                                                 (tuple21 
                                                                 int
                                                                 uninterpreted_type1))))) )))

(declare-fun t2tb238 ((set (set (tuple2 Int
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Int (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))))) (sort
  (set1
  (set1
  (tuple21 int
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (t2tb238 x))))

(declare-fun tb2t238 (uni) (set (set (tuple2 Int
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Int (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))))))
  (! (= (tb2t238 (t2tb238 i)) i) :pattern ((t2tb238 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb238 (tb2t238 j)) j) :pattern ((t2tb238 (tb2t238 j))) )))

(declare-fun t2tb239 ((set (tuple2 Int (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))))) (sort
  (set1
  (tuple21 int
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (t2tb239 x))))

(declare-fun tb2t239 (uni) (set (tuple2 Int
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))))
  (! (= (tb2t239 (t2tb239 i)) i) :pattern ((t2tb239 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb239 (tb2t239 j)) j) :pattern ((t2tb239 (tb2t239 j))) )))

(declare-fun t2tb240 ((tuple2 Int (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Int (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (sort
  (tuple21 int
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb240 x))))

(declare-fun tb2t240 (uni) (tuple2 Int (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))

;; BridgeL
  (assert
  (forall ((i (tuple2 Int (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))))
  (! (= (tb2t240 (t2tb240 i)) i) :pattern ((t2tb240 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb240 (tb2t240 j)) j) :pattern ((t2tb240 (tb2t240 j))) )))

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
  (t2tb16 x) (t2tb6 y))
  (empty
  (tuple21 int
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (infix_mnmngt
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)) 
  int (t2tb15 (add2 x empty2))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb6 y) (t2tb5 empty3)))) :pattern ((tb2t239
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
                                        bool) (set1 int)) (t2tb16 x)
                                        (t2tb6 y))
                                        (empty
                                        (tuple21 int
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int))))))) )))

(declare-fun t2tb241 ((set (set (tuple2 Int (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Int (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool)))))) (sort
  (set1
  (set1 (tuple21 int (tuple21 (tuple21 (tuple21 bool bool) bool) bool))))
  (t2tb241 x))))

(declare-fun tb2t241 (uni) (set (set (tuple2 Int (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Int (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool)))))) (! (= (tb2t241 (t2tb241 i)) i) :pattern ((t2tb241 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb241 (tb2t241 j)) j) :pattern ((t2tb241 (tb2t241 j))) )))

(declare-fun t2tb242 ((set (tuple2 Int (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))))) (sort
  (set1 (tuple21 int (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))
  (t2tb242 x))))

(declare-fun tb2t242 (uni) (set (tuple2 Int (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))))) (! (= (tb2t242 (t2tb242 i)) i) :pattern ((t2tb242 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb242 (tb2t242 j)) j) :pattern ((t2tb242 (tb2t242 j))) )))

(declare-fun t2tb243 ((tuple2 Int (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Int (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (sort (tuple21 int (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (t2tb243 x))))

(declare-fun tb2t243 (uni) (tuple2 Int (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 Int (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (! (= (tb2t243 (t2tb243 i)) i) :pattern ((t2tb243 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb243 (tb2t243 j)) j) :pattern ((t2tb243 (tb2t243 j))) )))

;; singleton_is_function
  (assert
  (forall ((x Int) (y (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (! (mem
  (set1 (tuple21 int (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))
  (add (tuple21 int (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (Tuple2 int (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb16 x)
  (t2tb8 y))
  (empty (tuple21 int (tuple21 (tuple21 (tuple21 bool bool) bool) bool))))
  (infix_mnmngt (tuple21 (tuple21 (tuple21 bool bool) bool) bool) int
  (t2tb15 (add2 x empty2)) (t2tb7 (add4 y empty7)))) :pattern ((tb2t242
                                                               (add
                                                               (tuple21 
                                                               int
                                                               (tuple21
                                                               (tuple21
                                                               (tuple21 
                                                               bool bool)
                                                               bool) 
                                                               bool))
                                                               (Tuple2 
                                                               int
                                                               (tuple21
                                                               (tuple21
                                                               (tuple21 
                                                               bool bool)
                                                               bool) 
                                                               bool)
                                                               (t2tb16 x)
                                                               (t2tb8 y))
                                                               (empty
                                                               (tuple21 
                                                               int
                                                               (tuple21
                                                               (tuple21
                                                               (tuple21 
                                                               bool bool)
                                                               bool) 
                                                               bool)))))) )))

(declare-fun t2tb244 ((set (set (tuple2 Int (tuple2 (tuple2 Bool Bool)
  Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Int (tuple2 (tuple2 Bool Bool) Bool))))))
  (sort (set1 (set1 (tuple21 int (tuple21 (tuple21 bool bool) bool))))
  (t2tb244 x))))

(declare-fun tb2t244 (uni) (set (set (tuple2 Int (tuple2 (tuple2 Bool Bool)
  Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Int (tuple2 (tuple2 Bool Bool) Bool))))))
  (! (= (tb2t244 (t2tb244 i)) i) :pattern ((t2tb244 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb244 (tb2t244 j)) j) :pattern ((t2tb244 (tb2t244 j))) )))

(declare-fun t2tb245 ((set (tuple2 Int (tuple2 (tuple2 Bool Bool)
  Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int (tuple2 (tuple2 Bool Bool) Bool))))) (sort
  (set1 (tuple21 int (tuple21 (tuple21 bool bool) bool))) (t2tb245 x))))

(declare-fun tb2t245 (uni) (set (tuple2 Int (tuple2 (tuple2 Bool Bool)
  Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int (tuple2 (tuple2 Bool Bool) Bool)))))
  (! (= (tb2t245 (t2tb245 i)) i) :pattern ((t2tb245 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb245 (tb2t245 j)) j) :pattern ((t2tb245 (tb2t245 j))) )))

(declare-fun t2tb246 ((tuple2 Int (tuple2 (tuple2 Bool Bool) Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Int (tuple2 (tuple2 Bool Bool) Bool)))) (sort
  (tuple21 int (tuple21 (tuple21 bool bool) bool)) (t2tb246 x))))

(declare-fun tb2t246 (uni) (tuple2 Int (tuple2 (tuple2 Bool Bool) Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 Int (tuple2 (tuple2 Bool Bool) Bool))))
  (! (= (tb2t246 (t2tb246 i)) i) :pattern ((t2tb246 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb246 (tb2t246 j)) j) :pattern ((t2tb246 (tb2t246 j))) )))

;; singleton_is_function
  (assert
  (forall ((x Int) (y (tuple2 (tuple2 Bool Bool) Bool))) (! (mem
  (set1 (tuple21 int (tuple21 (tuple21 bool bool) bool)))
  (add (tuple21 int (tuple21 (tuple21 bool bool) bool))
  (Tuple2 int (tuple21 (tuple21 bool bool) bool) (t2tb16 x) (t2tb10 y))
  (empty (tuple21 int (tuple21 (tuple21 bool bool) bool))))
  (infix_mnmngt (tuple21 (tuple21 bool bool) bool) int
  (t2tb15 (add2 x empty2)) (t2tb9 (add5 y empty8)))) :pattern ((tb2t245
                                                               (add
                                                               (tuple21 
                                                               int
                                                               (tuple21
                                                               (tuple21 
                                                               bool bool)
                                                               bool))
                                                               (Tuple2 
                                                               int
                                                               (tuple21
                                                               (tuple21 
                                                               bool bool)
                                                               bool)
                                                               (t2tb16 x)
                                                               (t2tb10 y))
                                                               (empty
                                                               (tuple21 
                                                               int
                                                               (tuple21
                                                               (tuple21 
                                                               bool bool)
                                                               bool)))))) )))

(declare-fun t2tb247 ((set (tuple2 Int (tuple2 Bool Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int (tuple2 Bool Bool))))) (sort
  (set1 (tuple21 int (tuple21 bool bool))) (t2tb247 x))))

(declare-fun tb2t247 (uni) (set (tuple2 Int (tuple2 Bool Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int (tuple2 Bool Bool)))))
  (! (= (tb2t247 (t2tb247 i)) i) :pattern ((t2tb247 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb247 (tb2t247 j)) j) :pattern ((t2tb247 (tb2t247 j))) )))

(declare-fun t2tb248 ((tuple2 Int (tuple2 Bool Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Int (tuple2 Bool Bool)))) (sort
  (tuple21 int (tuple21 bool bool)) (t2tb248 x))))

(declare-fun tb2t248 (uni) (tuple2 Int (tuple2 Bool Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 Int (tuple2 Bool Bool))))
  (! (= (tb2t248 (t2tb248 i)) i) :pattern ((t2tb248 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb248 (tb2t248 j)) j) :pattern ((t2tb248 (tb2t248 j))) )))

(declare-fun t2tb249 ((set (set (tuple2 Int (tuple2 Bool Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Int (tuple2 Bool Bool)))))) (sort
  (set1 (set1 (tuple21 int (tuple21 bool bool)))) (t2tb249 x))))

(declare-fun tb2t249 (uni) (set (set (tuple2 Int (tuple2 Bool Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Int (tuple2 Bool Bool))))))
  (! (= (tb2t249 (t2tb249 i)) i) :pattern ((t2tb249 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb249 (tb2t249 j)) j) :pattern ((t2tb249 (tb2t249 j))) )))

;; singleton_is_function
  (assert
  (forall ((x Int) (y (tuple2 Bool Bool))) (! (mem
  (set1 (tuple21 int (tuple21 bool bool)))
  (add (tuple21 int (tuple21 bool bool))
  (Tuple2 int (tuple21 bool bool) (t2tb16 x) (t2tb12 y))
  (empty (tuple21 int (tuple21 bool bool))))
  (infix_mnmngt (tuple21 bool bool) int (t2tb15 (add2 x empty2))
  (t2tb11 (add6 y empty9)))) :pattern ((tb2t247
                                       (add (tuple21 int (tuple21 bool bool))
                                       (Tuple2 int (tuple21 bool bool)
                                       (t2tb16 x) (t2tb12 y))
                                       (empty
                                       (tuple21 int (tuple21 bool bool)))))) )))

(declare-fun t2tb250 ((set (set (tuple2 Int Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Int Bool))))) (sort
  (set1 (set1 (tuple21 int bool))) (t2tb250 x))))

(declare-fun tb2t250 (uni) (set (set (tuple2 Int Bool))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Int Bool)))))
  (! (= (tb2t250 (t2tb250 i)) i) :pattern ((t2tb250 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb250 (tb2t250 j)) j) :pattern ((t2tb250 (tb2t250 j))) )))

(declare-fun t2tb251 ((set (tuple2 Int Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int Bool)))) (sort (set1 (tuple21 int bool))
  (t2tb251 x))))

(declare-fun tb2t251 (uni) (set (tuple2 Int Bool)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int Bool))))
  (! (= (tb2t251 (t2tb251 i)) i) :pattern ((t2tb251 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb251 (tb2t251 j)) j) :pattern ((t2tb251 (tb2t251 j))) )))

(declare-fun t2tb252 ((tuple2 Int Bool)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Int Bool))) (sort (tuple21 int bool) (t2tb252 x))))

(declare-fun tb2t252 (uni) (tuple2 Int Bool))

;; BridgeL
  (assert
  (forall ((i (tuple2 Int Bool)))
  (! (= (tb2t252 (t2tb252 i)) i) :pattern ((t2tb252 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb252 (tb2t252 j)) j) :pattern ((t2tb252 (tb2t252 j))) )))

;; singleton_is_function
  (assert
  (forall ((x Int) (y Bool)) (! (mem (set1 (tuple21 int bool))
  (add (tuple21 int bool) (Tuple2 int bool (t2tb16 x) (t2tb13 y))
  (empty (tuple21 int bool)))
  (infix_mnmngt bool int (t2tb15 (add2 x empty2)) (t2tb14 (add1 y empty1)))) :pattern (
  (tb2t251
  (add (tuple21 int bool) (Tuple2 int bool (t2tb16 x) (t2tb13 y))
  (empty (tuple21 int bool))))) )))

(declare-fun t2tb253 ((set (set (tuple2 Int Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Int Int))))) (sort
  (set1 (set1 (tuple21 int int))) (t2tb253 x))))

(declare-fun tb2t253 (uni) (set (set (tuple2 Int Int))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Int Int)))))
  (! (= (tb2t253 (t2tb253 i)) i) :pattern ((t2tb253 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb253 (tb2t253 j)) j) :pattern ((t2tb253 (tb2t253 j))) )))

(declare-fun t2tb254 ((set (tuple2 Int Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int Int)))) (sort (set1 (tuple21 int int))
  (t2tb254 x))))

(declare-fun tb2t254 (uni) (set (tuple2 Int Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int Int))))
  (! (= (tb2t254 (t2tb254 i)) i) :pattern ((t2tb254 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb254 (tb2t254 j)) j) :pattern ((t2tb254 (tb2t254 j))) )))

(declare-fun t2tb255 ((tuple2 Int Int)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Int Int))) (sort (tuple21 int int) (t2tb255 x))))

(declare-fun tb2t255 (uni) (tuple2 Int Int))

;; BridgeL
  (assert
  (forall ((i (tuple2 Int Int)))
  (! (= (tb2t255 (t2tb255 i)) i) :pattern ((t2tb255 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb255 (tb2t255 j)) j) :pattern ((t2tb255 (tb2t255 j))) )))

;; singleton_is_function
  (assert
  (forall ((x Int) (y Int)) (! (mem (set1 (tuple21 int int))
  (add (tuple21 int int) (Tuple2 int int (t2tb16 x) (t2tb16 y))
  (empty (tuple21 int int)))
  (infix_mnmngt int int (t2tb15 (add2 x empty2)) (t2tb15 (add2 y empty2)))) :pattern (
  (tb2t254
  (add (tuple21 int int) (Tuple2 int int (t2tb16 x) (t2tb16 y))
  (empty (tuple21 int int))))) )))

;; singleton_is_function
  (assert
  (forall ((b ty))
  (forall ((x Int) (y uni)) (! (mem (set1 (tuple21 int b))
  (add (tuple21 int b) (Tuple2 int b (t2tb16 x) y) (empty (tuple21 int b)))
  (infix_mnmngt b int (t2tb15 (add2 x empty2)) (add b y (empty b)))) :pattern (
  (add (tuple21 int b) (Tuple2 int b (t2tb16 x) y) (empty (tuple21 int b)))) ))))

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

(declare-fun apply1 ((set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (tuple2 (tuple2 Bool Bool) Bool)) Bool)

(declare-fun apply2 ((set (tuple2 (tuple2 Bool Bool) Bool)) (tuple2 Bool
  Bool)) Bool)

(declare-fun apply3 ((set (tuple2 Bool Bool)) Bool) Bool)

(declare-fun apply4 ((set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool)) (set Int))

(declare-fun apply5 ((set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type))) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool)) (set uninterpreted_type))

;; apply_def0
  (assert
  (forall ((f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))) (s (set (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool))) (t (set (set uninterpreted_type)))
  (a (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (=>
  (and (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))) (t2tb f)
  (infix_plmngt (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb7 s) (t2tb2 t)))
  (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 a)
  (dom (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb f)))) (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1) (t2tb8 a) (t2tb3 (apply5 f a))) (t2tb f)))))

;; apply_def0
  (assert
  (forall ((f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (t (set (set Int))) (a (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (=>
  (and (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb5 f)
  (infix_plmngt (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb7 s) (t2tb24 t))) (mem
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 a)
  (dom (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 f)))) (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb8 a) (t2tb15 (apply4 f a))) (t2tb5 f)))))

;; apply_def0
  (assert
  (forall ((f (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (s (set (tuple2 (tuple2 Bool Bool) Bool))) (t (set Bool))
  (a (tuple2 (tuple2 Bool Bool) Bool)))
  (=>
  (and (mem (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (t2tb7 f)
  (infix_plmngt bool (tuple21 (tuple21 bool bool) bool) (t2tb9 s) (t2tb14 t)))
  (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 a)
  (dom bool (tuple21 (tuple21 bool bool) bool) (t2tb7 f)))) (mem
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb8 (Tuple23 a (apply1 f a))) (t2tb7 f)))))

;; apply_def0
  (assert
  (forall ((f (set (tuple2 (tuple2 Bool Bool) Bool))) (s (set (tuple2 Bool
  Bool))) (t (set Bool)) (a (tuple2 Bool Bool)))
  (=>
  (and (mem (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb9 f)
  (infix_plmngt bool (tuple21 bool bool) (t2tb11 s) (t2tb14 t))) (mem
  (tuple21 bool bool) (t2tb12 a) (dom bool (tuple21 bool bool) (t2tb9 f))))
  (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 a (apply2 f a)))
  (t2tb9 f)))))

;; apply_def0
  (assert
  (forall ((f (set (tuple2 Bool Bool))) (s (set Bool)) (t (set Bool))
  (a Bool))
  (=>
  (and (mem (set1 (tuple21 bool bool)) (t2tb11 f)
  (infix_plmngt bool bool (t2tb14 s) (t2tb14 t))) (mem bool (t2tb13 a)
  (dom bool bool (t2tb11 f)))) (mem (tuple21 bool bool)
  (t2tb12 (Tuple21 a (apply3 f a))) (t2tb11 f)))))

;; apply_def0
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni) (a1 uni))
  (=>
  (and (mem (set1 (tuple21 a b)) f (infix_plmngt b a s t)) (mem a a1
  (dom b a f))) (mem (tuple21 a b) (Tuple2 a b a1 (apply b a f a1)) f)))))

;; apply_def1
  (assert
  (forall ((f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))) (s (set (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool))) (t (set (set uninterpreted_type)))
  (a (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (=>
  (and (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))) (t2tb f)
  (infix_mnmngt (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb7 s) (t2tb2 t)))
  (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 a)
  (t2tb7 s))) (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1) (t2tb8 a) (t2tb3 (apply5 f a))) (t2tb f)))))

;; apply_def1
  (assert
  (forall ((f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (t (set (set Int))) (a (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (=>
  (and (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb5 f)
  (infix_mnmngt (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb7 s) (t2tb24 t))) (mem
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 a) (t2tb7 s)))
  (mem (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb8 a) (t2tb15 (apply4 f a))) (t2tb5 f)))))

;; apply_def1
  (assert
  (forall ((f (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (s (set (tuple2 (tuple2 Bool Bool) Bool))) (t (set Bool))
  (a (tuple2 (tuple2 Bool Bool) Bool)))
  (=>
  (and (mem (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (t2tb7 f)
  (infix_mnmngt bool (tuple21 (tuple21 bool bool) bool) (t2tb9 s) (t2tb14 t)))
  (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 a) (t2tb9 s))) (mem
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb8 (Tuple23 a (apply1 f a))) (t2tb7 f)))))

;; apply_def1
  (assert
  (forall ((f (set (tuple2 (tuple2 Bool Bool) Bool))) (s (set (tuple2 Bool
  Bool))) (t (set Bool)) (a (tuple2 Bool Bool)))
  (=>
  (and (mem (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb9 f)
  (infix_mnmngt bool (tuple21 bool bool) (t2tb11 s) (t2tb14 t))) (mem
  (tuple21 bool bool) (t2tb12 a) (t2tb11 s))) (mem
  (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 a (apply2 f a)))
  (t2tb9 f)))))

;; apply_def1
  (assert
  (forall ((f (set (tuple2 Bool Bool))) (s (set Bool)) (t (set Bool))
  (a Bool))
  (=>
  (and (mem (set1 (tuple21 bool bool)) (t2tb11 f)
  (infix_mnmngt bool bool (t2tb14 s) (t2tb14 t))) (mem bool (t2tb13 a)
  (t2tb14 s))) (mem (tuple21 bool bool) (t2tb12 (Tuple21 a (apply3 f a)))
  (t2tb11 f)))))

;; apply_def1
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni) (a1 uni))
  (=> (and (mem (set1 (tuple21 a b)) f (infix_mnmngt b a s t)) (mem a a1 s))
  (mem (tuple21 a b) (Tuple2 a b a1 (apply b a f a1)) f)))))

;; apply_def2
  (assert
  (forall ((f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))) (s (set (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool))) (t (set (set uninterpreted_type)))
  (a (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (b (set uninterpreted_type)))
  (=>
  (and (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))) (t2tb f)
  (infix_plmngt (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb7 s) (t2tb2 t)))
  (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1) (t2tb8 a) (t2tb3 b)) (t2tb f)))
  (= (apply5 f a) b))))

;; apply_def2
  (assert
  (forall ((f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (t (set (set Int))) (a (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (b (set Int)))
  (=>
  (and (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb5 f)
  (infix_plmngt (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb7 s) (t2tb24 t))) (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb8 a) (t2tb15 b)) (t2tb5 f))) (= (apply4 f a) b))))

;; apply_def2
  (assert
  (forall ((f (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (s (set (tuple2 (tuple2 Bool Bool) Bool))) (t (set Bool))
  (a (tuple2 (tuple2 Bool Bool) Bool)) (b Bool))
  (=>
  (and (mem (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (t2tb7 f)
  (infix_plmngt bool (tuple21 (tuple21 bool bool) bool) (t2tb9 s) (t2tb14 t)))
  (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb8 (Tuple23 a b)) (t2tb7 f))) (= (apply1 f a) b))))

;; apply_def2
  (assert
  (forall ((f (set (tuple2 (tuple2 Bool Bool) Bool))) (s (set (tuple2 Bool
  Bool))) (t (set Bool)) (a (tuple2 Bool Bool)) (b Bool))
  (=>
  (and (mem (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb9 f)
  (infix_plmngt bool (tuple21 bool bool) (t2tb11 s) (t2tb14 t))) (mem
  (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 a b)) (t2tb9 f)))
  (= (apply2 f a) b))))

;; apply_def2
  (assert
  (forall ((f (set (tuple2 Bool Bool))) (s (set Bool)) (t (set Bool))
  (a Bool) (b Bool))
  (=>
  (and (mem (set1 (tuple21 bool bool)) (t2tb11 f)
  (infix_plmngt bool bool (t2tb14 s) (t2tb14 t))) (mem (tuple21 bool bool)
  (t2tb12 (Tuple21 a b)) (t2tb11 f))) (= (apply3 f a) b))))

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
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (y (set uninterpreted_type)))
  (= (apply5
     (tb2t
     (add
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1))
     (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1) (t2tb8 x) (t2tb3 y)) (t2tb empty6))) x) y)))

;; apply_singleton
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)) (y (set Int)))
  (= (apply4
     (tb2t5
     (add
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
     (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
     (t2tb8 x) (t2tb15 y)) (t2tb5 empty3))) x) y)))

;; apply_singleton
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)) (y Bool))
  (= (apply1 (add4 (Tuple23 x y) empty7) x) y)))

;; apply_singleton
  (assert
  (forall ((x (tuple2 Bool Bool)) (y Bool))
  (= (apply2 (add5 (Tuple22 x y) empty8) x) y)))

;; apply_singleton
  (assert
  (forall ((x Bool) (y Bool)) (= (apply3 (add6 (Tuple21 x y) empty9) x) y)))

;; apply_singleton
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (y uni))
  (=> (sort b y)
  (= (apply b a (add (tuple21 a b) (Tuple2 a b x y) (empty (tuple21 a b))) x) y)))))

;; apply_range
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))) (s (set (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool))) (t (set (set uninterpreted_type))))
  (! (=>
     (and (mem
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1))) (t2tb f)
     (infix_plmngt (set1 uninterpreted_type1)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb7 s) (t2tb2 t)))
     (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 x)
     (dom (set1 uninterpreted_type1)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb f)))) (mem
     (set1 uninterpreted_type1) (t2tb3 (apply5 f x)) (t2tb2 t))) :pattern ((mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))) (t2tb f)
  (infix_plmngt (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb7 s) (t2tb2 t)))
  (apply5 f x)) )))

;; apply_range
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))
  (s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (t (set (set Int))))
  (! (=>
     (and (mem
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb5 f)
     (infix_plmngt (set1 int)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb7 s) (t2tb24 t)))
     (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 x)
     (dom (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (t2tb5 f)))) (mem (set1 int) (t2tb15 (apply4 f x)) (t2tb24 t))) :pattern ((mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb5 f)
  (infix_plmngt (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb7 s) (t2tb24 t))) (apply4 f x)) )))

;; apply_range
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool))
  (f (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (s (set (tuple2 (tuple2 Bool Bool) Bool))) (t (set Bool)))
  (! (=>
     (and (mem (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
     (t2tb7 f)
     (infix_plmngt bool (tuple21 (tuple21 bool bool) bool) (t2tb9 s)
     (t2tb14 t))) (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x)
     (dom bool (tuple21 (tuple21 bool bool) bool) (t2tb7 f)))) (mem bool
     (t2tb13 (apply1 f x)) (t2tb14 t))) :pattern ((mem
  (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb7 f)
  (infix_plmngt bool (tuple21 (tuple21 bool bool) bool) (t2tb9 s) (t2tb14 t)))
  (apply1 f x)) )))

;; apply_range
  (assert
  (forall ((x (tuple2 Bool Bool)) (f (set (tuple2 (tuple2 Bool Bool) Bool)))
  (s (set (tuple2 Bool Bool))) (t (set Bool)))
  (! (=>
     (and (mem (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb9 f)
     (infix_plmngt bool (tuple21 bool bool) (t2tb11 s) (t2tb14 t))) (mem
     (tuple21 bool bool) (t2tb12 x)
     (dom bool (tuple21 bool bool) (t2tb9 f)))) (mem bool
     (t2tb13 (apply2 f x)) (t2tb14 t))) :pattern ((mem
  (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb9 f)
  (infix_plmngt bool (tuple21 bool bool) (t2tb11 s) (t2tb14 t)))
  (apply2 f x)) )))

;; apply_range
  (assert
  (forall ((x Bool) (f (set (tuple2 Bool Bool))) (s (set Bool))
  (t (set Bool)))
  (! (=>
     (and (mem (set1 (tuple21 bool bool)) (t2tb11 f)
     (infix_plmngt bool bool (t2tb14 s) (t2tb14 t))) (mem bool (t2tb13 x)
     (dom bool bool (t2tb11 f)))) (mem bool (t2tb13 (apply3 f x))
     (t2tb14 t))) :pattern ((mem
  (set1 (tuple21 bool bool)) (t2tb11 f)
  (infix_plmngt bool bool (t2tb14 s) (t2tb14 t))) (apply3 f x)) )))

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
  (forall ((x uni) (z Bool) (p uni) (q (set (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool))))
  (= (mem (tuple21 a bool) (Tuple2 a bool x (t2tb13 z))
  (semicolon bool (tuple21 (tuple21 bool bool) bool) a p (t2tb7 q)))
  (exists ((y (tuple2 (tuple2 Bool Bool) Bool)))
  (and (mem (tuple21 a (tuple21 (tuple21 bool bool) bool))
  (Tuple2 a (tuple21 (tuple21 bool bool) bool) x (t2tb10 y)) p) (mem
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 (Tuple23 y z))
  (t2tb7 q))))))))

;; semicolon_def
  (assert
  (forall ((a ty))
  (forall ((x uni) (z Bool) (p uni) (q (set (tuple2 (tuple2 Bool Bool)
  Bool))))
  (= (mem (tuple21 a bool) (Tuple2 a bool x (t2tb13 z))
  (semicolon bool (tuple21 bool bool) a p (t2tb9 q)))
  (exists ((y (tuple2 Bool Bool)))
  (and (mem (tuple21 a (tuple21 bool bool))
  (Tuple2 a (tuple21 bool bool) x (t2tb12 y)) p) (mem
  (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 y z)) (t2tb9 q))))))))

;; semicolon_def
  (assert
  (forall ((a ty))
  (forall ((x uni) (z Bool) (p uni) (q (set (tuple2 Bool Bool))))
  (= (mem (tuple21 a bool) (Tuple2 a bool x (t2tb13 z))
  (semicolon bool bool a p (t2tb11 q)))
  (exists ((y Bool))
  (and (mem (tuple21 a bool) (Tuple2 a bool x (t2tb13 y)) p) (mem
  (tuple21 bool bool) (t2tb12 (Tuple21 y z)) (t2tb11 q))))))))

;; semicolon_def
  (assert
  (forall ((b ty))
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)) (z Bool) (p uni) (q uni))
  (and
  (=> (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb8 (Tuple23 x z))
  (semicolon bool b (tuple21 (tuple21 bool bool) bool) p q))
  (exists ((y uni))
  (and (sort b y)
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) b)
  (Tuple2 (tuple21 (tuple21 bool bool) bool) b (t2tb10 x) y) p) (mem
  (tuple21 b bool) (Tuple2 b bool y (t2tb13 z)) q)))))
  (=>
  (exists ((y uni))
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) b)
  (Tuple2 (tuple21 (tuple21 bool bool) bool) b (t2tb10 x) y) p) (mem
  (tuple21 b bool) (Tuple2 b bool y (t2tb13 z)) q))) (mem
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 (Tuple23 x z))
  (semicolon bool b (tuple21 (tuple21 bool bool) bool) p q)))))))

;; semicolon_def
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)) (z Bool)
  (p (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) (tuple2 (tuple2 Bool Bool)
  Bool)))) (q (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (= (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb8 (Tuple23 x z))
  (semicolon bool (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 bool bool) bool) (t2tb177 p) (t2tb7 q)))
  (exists ((y (tuple2 (tuple2 Bool Bool) Bool)))
  (and (mem
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 bool bool) bool))
  (Tuple2 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb10 y)) (t2tb177 p)) (mem
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 (Tuple23 y z))
  (t2tb7 q)))))))

;; semicolon_def
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)) (z Bool)
  (p (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) (tuple2 Bool Bool))))
  (q (set (tuple2 (tuple2 Bool Bool) Bool))))
  (= (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb8 (Tuple23 x z))
  (semicolon bool (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool)
  (t2tb180 p) (t2tb9 q)))
  (exists ((y (tuple2 Bool Bool)))
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool))
  (Tuple2 (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool) (t2tb10 x)
  (t2tb12 y)) (t2tb180 p)) (mem (tuple21 (tuple21 bool bool) bool)
  (t2tb10 (Tuple22 y z)) (t2tb9 q)))))))

;; semicolon_def
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)) (z Bool)
  (p (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (q (set (tuple2 Bool Bool))))
  (= (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb8 (Tuple23 x z))
  (semicolon bool bool (tuple21 (tuple21 bool bool) bool) (t2tb7 p)
  (t2tb11 q)))
  (exists ((y Bool))
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb8 (Tuple23 x y)) (t2tb7 p)) (mem (tuple21 bool bool)
  (t2tb12 (Tuple21 y z)) (t2tb11 q)))))))

;; semicolon_def
  (assert
  (forall ((c ty))
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)) (z uni)
  (p (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))) (q uni))
  (= (mem (tuple21 (tuple21 (tuple21 bool bool) bool) c)
  (Tuple2 (tuple21 (tuple21 bool bool) bool) c (t2tb10 x) z)
  (semicolon c bool (tuple21 (tuple21 bool bool) bool) (t2tb7 p) q))
  (exists ((y Bool))
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb8 (Tuple23 x y)) (t2tb7 p)) (mem (tuple21 bool c)
  (Tuple2 bool c (t2tb13 y) z) q)))))))

;; semicolon_def
  (assert
  (forall ((b ty))
  (forall ((x (tuple2 Bool Bool)) (z Bool) (p uni) (q uni))
  (and
  (=> (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 x z))
  (semicolon bool b (tuple21 bool bool) p q))
  (exists ((y uni))
  (and (sort b y)
  (and (mem (tuple21 (tuple21 bool bool) b)
  (Tuple2 (tuple21 bool bool) b (t2tb12 x) y) p) (mem (tuple21 b bool)
  (Tuple2 b bool y (t2tb13 z)) q)))))
  (=>
  (exists ((y uni))
  (and (mem (tuple21 (tuple21 bool bool) b)
  (Tuple2 (tuple21 bool bool) b (t2tb12 x) y) p) (mem (tuple21 b bool)
  (Tuple2 b bool y (t2tb13 z)) q))) (mem (tuple21 (tuple21 bool bool) bool)
  (t2tb10 (Tuple22 x z)) (semicolon bool b (tuple21 bool bool) p q)))))))

;; semicolon_def
  (assert
  (forall ((x (tuple2 Bool Bool)) (z Bool) (p (set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 Bool Bool) Bool)))) (q (set (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool))))
  (= (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 x z))
  (semicolon bool (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool)
  (t2tb202 p) (t2tb7 q)))
  (exists ((y (tuple2 (tuple2 Bool Bool) Bool)))
  (and (mem (tuple21 (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool))
  (Tuple2 (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool) (t2tb12 x)
  (t2tb10 y)) (t2tb202 p)) (mem
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 (Tuple23 y z))
  (t2tb7 q)))))))

;; semicolon_def
  (assert
  (forall ((x (tuple2 Bool Bool)) (z Bool) (p (set (tuple2 (tuple2 Bool Bool)
  (tuple2 Bool Bool)))) (q (set (tuple2 (tuple2 Bool Bool) Bool))))
  (= (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 x z))
  (semicolon bool (tuple21 bool bool) (tuple21 bool bool) (t2tb204 p)
  (t2tb9 q)))
  (exists ((y (tuple2 Bool Bool)))
  (and (mem (tuple21 (tuple21 bool bool) (tuple21 bool bool))
  (Tuple2 (tuple21 bool bool) (tuple21 bool bool) (t2tb12 x) (t2tb12 y))
  (t2tb204 p)) (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 y z))
  (t2tb9 q)))))))

;; semicolon_def
  (assert
  (forall ((x (tuple2 Bool Bool)) (z Bool) (p (set (tuple2 (tuple2 Bool Bool)
  Bool))) (q (set (tuple2 Bool Bool))))
  (= (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 x z))
  (semicolon bool bool (tuple21 bool bool) (t2tb9 p) (t2tb11 q)))
  (exists ((y Bool))
  (and (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 x y))
  (t2tb9 p)) (mem (tuple21 bool bool) (t2tb12 (Tuple21 y z)) (t2tb11 q)))))))

;; semicolon_def
  (assert
  (forall ((c ty))
  (forall ((x (tuple2 Bool Bool)) (z uni) (p (set (tuple2 (tuple2 Bool Bool)
  Bool))) (q uni))
  (= (mem (tuple21 (tuple21 bool bool) c)
  (Tuple2 (tuple21 bool bool) c (t2tb12 x) z)
  (semicolon c bool (tuple21 bool bool) (t2tb9 p) q))
  (exists ((y Bool))
  (and (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 x y))
  (t2tb9 p)) (mem (tuple21 bool c) (Tuple2 bool c (t2tb13 y) z) q)))))))

;; semicolon_def
  (assert
  (forall ((b ty))
  (forall ((x Bool) (z Bool) (p uni) (q uni))
  (and
  (=> (mem (tuple21 bool bool) (t2tb12 (Tuple21 x z))
  (semicolon bool b bool p q))
  (exists ((y uni))
  (and (sort b y)
  (and (mem (tuple21 bool b) (Tuple2 bool b (t2tb13 x) y) p) (mem
  (tuple21 b bool) (Tuple2 b bool y (t2tb13 z)) q)))))
  (=>
  (exists ((y uni))
  (and (mem (tuple21 bool b) (Tuple2 bool b (t2tb13 x) y) p) (mem
  (tuple21 b bool) (Tuple2 b bool y (t2tb13 z)) q))) (mem (tuple21 bool bool)
  (t2tb12 (Tuple21 x z)) (semicolon bool b bool p q)))))))

;; semicolon_def
  (assert
  (forall ((x Bool) (z Bool) (p (set (tuple2 Bool (tuple2 (tuple2 Bool Bool)
  Bool)))) (q (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (= (mem (tuple21 bool bool) (t2tb12 (Tuple21 x z))
  (semicolon bool (tuple21 (tuple21 bool bool) bool) bool (t2tb25 p)
  (t2tb7 q)))
  (exists ((y (tuple2 (tuple2 Bool Bool) Bool)))
  (and (mem (tuple21 bool (tuple21 (tuple21 bool bool) bool))
  (Tuple2 bool (tuple21 (tuple21 bool bool) bool) (t2tb13 x) (t2tb10 y))
  (t2tb25 p)) (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb8 (Tuple23 y z)) (t2tb7 q)))))))

;; semicolon_def
  (assert
  (forall ((x Bool) (z Bool) (p (set (tuple2 Bool (tuple2 Bool Bool))))
  (q (set (tuple2 (tuple2 Bool Bool) Bool))))
  (= (mem (tuple21 bool bool) (t2tb12 (Tuple21 x z))
  (semicolon bool (tuple21 bool bool) bool (t2tb27 p) (t2tb9 q)))
  (exists ((y (tuple2 Bool Bool)))
  (and (mem (tuple21 bool (tuple21 bool bool))
  (Tuple2 bool (tuple21 bool bool) (t2tb13 x) (t2tb12 y)) (t2tb27 p)) (mem
  (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 y z)) (t2tb9 q)))))))

;; semicolon_def
  (assert
  (forall ((x Bool) (z Bool) (p (set (tuple2 Bool Bool)))
  (q (set (tuple2 Bool Bool))))
  (= (mem (tuple21 bool bool) (t2tb12 (Tuple21 x z))
  (semicolon bool bool bool (t2tb11 p) (t2tb11 q)))
  (exists ((y Bool))
  (and (mem (tuple21 bool bool) (t2tb12 (Tuple21 x y)) (t2tb11 p)) (mem
  (tuple21 bool bool) (t2tb12 (Tuple21 y z)) (t2tb11 q)))))))

;; semicolon_def
  (assert
  (forall ((c ty))
  (forall ((x Bool) (z uni) (p (set (tuple2 Bool Bool))) (q uni))
  (= (mem (tuple21 bool c) (Tuple2 bool c (t2tb13 x) z)
  (semicolon c bool bool (t2tb11 p) q))
  (exists ((y Bool))
  (and (mem (tuple21 bool bool) (t2tb12 (Tuple21 x y)) (t2tb11 p)) (mem
  (tuple21 bool c) (Tuple2 bool c (t2tb13 y) z) q)))))))

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
  (! (=> (sort (tuple21 t (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
     e)
     (and
     (=> (mem (tuple21 t (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) e
     (direct_product bool (tuple21 (tuple21 bool bool) bool) t r1 r2))
     (exists ((x uni) (y (tuple2 (tuple2 Bool Bool) Bool)) (z Bool))
     (and (sort t x)
     (and
     (= (Tuple2 t (tuple21 (tuple21 (tuple21 bool bool) bool) bool) x
        (t2tb8 (Tuple23 y z))) e)
     (and (mem (tuple21 t (tuple21 (tuple21 bool bool) bool))
     (Tuple2 t (tuple21 (tuple21 bool bool) bool) x (t2tb10 y)) r1) (mem
     (tuple21 t bool) (Tuple2 t bool x (t2tb13 z)) r2))))))
     (=>
     (exists ((x uni) (y (tuple2 (tuple2 Bool Bool) Bool)) (z Bool))
     (and
     (= (Tuple2 t (tuple21 (tuple21 (tuple21 bool bool) bool) bool) x
        (t2tb8 (Tuple23 y z))) e)
     (and (mem (tuple21 t (tuple21 (tuple21 bool bool) bool))
     (Tuple2 t (tuple21 (tuple21 bool bool) bool) x (t2tb10 y)) r1) (mem
     (tuple21 t bool) (Tuple2 t bool x (t2tb13 z)) r2)))) (mem
     (tuple21 t (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) e
     (direct_product bool (tuple21 (tuple21 bool bool) bool) t r1 r2))))) :pattern ((mem
  (tuple21 t (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) e
  (direct_product bool (tuple21 (tuple21 bool bool) bool) t r1 r2))) ))))

;; direct_product_def
  (assert
  (forall ((t ty))
  (forall ((e uni) (r1 uni) (r2 uni))
  (! (=> (sort (tuple21 t (tuple21 (tuple21 bool bool) bool)) e)
     (and
     (=> (mem (tuple21 t (tuple21 (tuple21 bool bool) bool)) e
     (direct_product bool (tuple21 bool bool) t r1 r2))
     (exists ((x uni) (y (tuple2 Bool Bool)) (z Bool))
     (and (sort t x)
     (and
     (= (Tuple2 t (tuple21 (tuple21 bool bool) bool) x
        (t2tb10 (Tuple22 y z))) e)
     (and (mem (tuple21 t (tuple21 bool bool))
     (Tuple2 t (tuple21 bool bool) x (t2tb12 y)) r1) (mem (tuple21 t bool)
     (Tuple2 t bool x (t2tb13 z)) r2))))))
     (=>
     (exists ((x uni) (y (tuple2 Bool Bool)) (z Bool))
     (and
     (= (Tuple2 t (tuple21 (tuple21 bool bool) bool) x
        (t2tb10 (Tuple22 y z))) e)
     (and (mem (tuple21 t (tuple21 bool bool))
     (Tuple2 t (tuple21 bool bool) x (t2tb12 y)) r1) (mem (tuple21 t bool)
     (Tuple2 t bool x (t2tb13 z)) r2)))) (mem
     (tuple21 t (tuple21 (tuple21 bool bool) bool)) e
     (direct_product bool (tuple21 bool bool) t r1 r2))))) :pattern ((mem
  (tuple21 t (tuple21 (tuple21 bool bool) bool)) e
  (direct_product bool (tuple21 bool bool) t r1 r2))) ))))

;; direct_product_def
  (assert
  (forall ((t ty))
  (forall ((e uni) (r1 uni) (r2 uni))
  (! (=> (sort (tuple21 t (tuple21 bool bool)) e)
     (and
     (=> (mem (tuple21 t (tuple21 bool bool)) e
     (direct_product bool bool t r1 r2))
     (exists ((x uni) (y Bool) (z Bool))
     (and (sort t x)
     (and (= (Tuple2 t (tuple21 bool bool) x (t2tb12 (Tuple21 y z))) e)
     (and (mem (tuple21 t bool) (Tuple2 t bool x (t2tb13 y)) r1) (mem
     (tuple21 t bool) (Tuple2 t bool x (t2tb13 z)) r2))))))
     (=>
     (exists ((x uni) (y Bool) (z Bool))
     (and (= (Tuple2 t (tuple21 bool bool) x (t2tb12 (Tuple21 y z))) e)
     (and (mem (tuple21 t bool) (Tuple2 t bool x (t2tb13 y)) r1) (mem
     (tuple21 t bool) (Tuple2 t bool x (t2tb13 z)) r2)))) (mem
     (tuple21 t (tuple21 bool bool)) e (direct_product bool bool t r1 r2))))) :pattern ((mem
  (tuple21 t (tuple21 bool bool)) e (direct_product bool bool t r1 r2))) ))))

;; direct_product_def
  (assert
  (forall ((u ty))
  (forall ((e uni) (r1 uni) (r2 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))))
  (! (=> (sort (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 u bool))
     e)
     (and
     (=> (mem (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 u bool)) e
     (direct_product bool u (tuple21 (tuple21 bool bool) bool) r1 (t2tb7 r2)))
     (exists ((x (tuple2 (tuple2 Bool Bool) Bool)) (y uni) (z Bool))
     (and (sort u y)
     (and
     (= (Tuple2 (tuple21 (tuple21 bool bool) bool) (tuple21 u bool)
        (t2tb10 x) (Tuple2 u bool y (t2tb13 z))) e)
     (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) u)
     (Tuple2 (tuple21 (tuple21 bool bool) bool) u (t2tb10 x) y) r1) (mem
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 (Tuple23 x z))
     (t2tb7 r2)))))))
     (=>
     (exists ((x (tuple2 (tuple2 Bool Bool) Bool)) (y uni) (z Bool))
     (and
     (= (Tuple2 (tuple21 (tuple21 bool bool) bool) (tuple21 u bool)
        (t2tb10 x) (Tuple2 u bool y (t2tb13 z))) e)
     (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) u)
     (Tuple2 (tuple21 (tuple21 bool bool) bool) u (t2tb10 x) y) r1) (mem
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 (Tuple23 x z))
     (t2tb7 r2))))) (mem
     (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 u bool)) e
     (direct_product bool u (tuple21 (tuple21 bool bool) bool) r1 (t2tb7 r2)))))) :pattern ((mem
  (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 u bool)) e
  (direct_product bool u (tuple21 (tuple21 bool bool) bool) r1 (t2tb7 r2)))) ))))

;; direct_product_def
  (assert
  (forall ((e (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (r1 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) (tuple2 (tuple2 Bool
  Bool) Bool)))) (r2 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (! (= (mem
     (tuple21 (tuple21 (tuple21 bool bool) bool)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb175 e)
     (direct_product bool (tuple21 (tuple21 bool bool) bool)
     (tuple21 (tuple21 bool bool) bool) (t2tb177 r1) (t2tb7 r2)))
     (exists ((x (tuple2 (tuple2 Bool Bool) Bool)) (y (tuple2 (tuple2 Bool
     Bool) Bool)) (z Bool))
     (and
     (= (tb2t175
        (Tuple2 (tuple21 (tuple21 bool bool) bool)
        (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb10 x)
        (t2tb8 (Tuple23 y z)))) e)
     (and (mem
     (tuple21 (tuple21 (tuple21 bool bool) bool)
     (tuple21 (tuple21 bool bool) bool))
     (Tuple2 (tuple21 (tuple21 bool bool) bool)
     (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb10 y)) (t2tb177 r1))
     (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (t2tb8 (Tuple23 x z)) (t2tb7 r2)))))) :pattern ((mem
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb175 e)
  (direct_product bool (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 bool bool) bool) (t2tb177 r1) (t2tb7 r2)))) )))

;; direct_product_def
  (assert
  (forall ((e (tuple2 (tuple2 (tuple2 Bool Bool) Bool) (tuple2 (tuple2 Bool
  Bool) Bool))) (r1 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 Bool Bool)))) (r2 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))))
  (! (= (mem
     (tuple21 (tuple21 (tuple21 bool bool) bool)
     (tuple21 (tuple21 bool bool) bool)) (t2tb178 e)
     (direct_product bool (tuple21 bool bool)
     (tuple21 (tuple21 bool bool) bool) (t2tb180 r1) (t2tb7 r2)))
     (exists ((x (tuple2 (tuple2 Bool Bool) Bool)) (y (tuple2 Bool Bool))
     (z Bool))
     (and
     (= (tb2t178
        (Tuple2 (tuple21 (tuple21 bool bool) bool)
        (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb10 (Tuple22 y z)))) e)
     (and (mem
     (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool))
     (Tuple2 (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool)
     (t2tb10 x) (t2tb12 y)) (t2tb180 r1)) (mem
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 (Tuple23 x z))
     (t2tb7 r2)))))) :pattern ((mem
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 bool bool) bool)) (t2tb178 e)
  (direct_product bool (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool)
  (t2tb180 r1) (t2tb7 r2)))) )))

;; direct_product_def
  (assert
  (forall ((e (tuple2 (tuple2 (tuple2 Bool Bool) Bool) (tuple2 Bool Bool)))
  (r1 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (r2 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (! (= (mem (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool))
     (t2tb181 e)
     (direct_product bool bool (tuple21 (tuple21 bool bool) bool) (t2tb7 r1)
     (t2tb7 r2)))
     (exists ((x (tuple2 (tuple2 Bool Bool) Bool)) (y Bool) (z Bool))
     (and
     (= (tb2t181
        (Tuple2 (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool)
        (t2tb10 x) (t2tb12 (Tuple21 y z)))) e)
     (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (t2tb8 (Tuple23 x y)) (t2tb7 r1)) (mem
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 (Tuple23 x z))
     (t2tb7 r2)))))) :pattern ((mem
  (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool))
  (t2tb181 e)
  (direct_product bool bool (tuple21 (tuple21 bool bool) bool) (t2tb7 r1)
  (t2tb7 r2)))) )))

;; direct_product_def
  (assert
  (forall ((v ty))
  (forall ((e uni) (r1 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (r2 uni))
  (! (=> (sort (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 bool v))
     e)
     (and
     (=> (mem (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 bool v)) e
     (direct_product v bool (tuple21 (tuple21 bool bool) bool) (t2tb7 r1) r2))
     (exists ((x (tuple2 (tuple2 Bool Bool) Bool)) (y Bool) (z uni))
     (and (sort v z)
     (and
     (= (Tuple2 (tuple21 (tuple21 bool bool) bool) (tuple21 bool v)
        (t2tb10 x) (Tuple2 bool v (t2tb13 y) z)) e)
     (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (t2tb8 (Tuple23 x y)) (t2tb7 r1)) (mem
     (tuple21 (tuple21 (tuple21 bool bool) bool) v)
     (Tuple2 (tuple21 (tuple21 bool bool) bool) v (t2tb10 x) z) r2))))))
     (=>
     (exists ((x (tuple2 (tuple2 Bool Bool) Bool)) (y Bool) (z uni))
     (and
     (= (Tuple2 (tuple21 (tuple21 bool bool) bool) (tuple21 bool v)
        (t2tb10 x) (Tuple2 bool v (t2tb13 y) z)) e)
     (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (t2tb8 (Tuple23 x y)) (t2tb7 r1)) (mem
     (tuple21 (tuple21 (tuple21 bool bool) bool) v)
     (Tuple2 (tuple21 (tuple21 bool bool) bool) v (t2tb10 x) z) r2)))) (mem
     (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 bool v)) e
     (direct_product v bool (tuple21 (tuple21 bool bool) bool) (t2tb7 r1) r2))))) :pattern ((mem
  (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 bool v)) e
  (direct_product v bool (tuple21 (tuple21 bool bool) bool) (t2tb7 r1) r2))) ))))

;; direct_product_def
  (assert
  (forall ((u ty))
  (forall ((e uni) (r1 uni) (r2 (set (tuple2 (tuple2 Bool Bool) Bool))))
  (! (=> (sort (tuple21 (tuple21 bool bool) (tuple21 u bool)) e)
     (and
     (=> (mem (tuple21 (tuple21 bool bool) (tuple21 u bool)) e
     (direct_product bool u (tuple21 bool bool) r1 (t2tb9 r2)))
     (exists ((x (tuple2 Bool Bool)) (y uni) (z Bool))
     (and (sort u y)
     (and
     (= (Tuple2 (tuple21 bool bool) (tuple21 u bool) (t2tb12 x)
        (Tuple2 u bool y (t2tb13 z))) e)
     (and (mem (tuple21 (tuple21 bool bool) u)
     (Tuple2 (tuple21 bool bool) u (t2tb12 x) y) r1) (mem
     (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 x z)) (t2tb9 r2)))))))
     (=>
     (exists ((x (tuple2 Bool Bool)) (y uni) (z Bool))
     (and
     (= (Tuple2 (tuple21 bool bool) (tuple21 u bool) (t2tb12 x)
        (Tuple2 u bool y (t2tb13 z))) e)
     (and (mem (tuple21 (tuple21 bool bool) u)
     (Tuple2 (tuple21 bool bool) u (t2tb12 x) y) r1) (mem
     (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 x z)) (t2tb9 r2)))))
     (mem (tuple21 (tuple21 bool bool) (tuple21 u bool)) e
     (direct_product bool u (tuple21 bool bool) r1 (t2tb9 r2)))))) :pattern ((mem
  (tuple21 (tuple21 bool bool) (tuple21 u bool)) e
  (direct_product bool u (tuple21 bool bool) r1 (t2tb9 r2)))) ))))

;; direct_product_def
  (assert
  (forall ((e (tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool))) (r1 (set (tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 Bool
  Bool) Bool)))) (r2 (set (tuple2 (tuple2 Bool Bool) Bool))))
  (! (= (mem
     (tuple21 (tuple21 bool bool)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb199 e)
     (direct_product bool (tuple21 (tuple21 bool bool) bool)
     (tuple21 bool bool) (t2tb202 r1) (t2tb9 r2)))
     (exists ((x (tuple2 Bool Bool)) (y (tuple2 (tuple2 Bool Bool) Bool))
     (z Bool))
     (and
     (= (tb2t199
        (Tuple2 (tuple21 bool bool)
        (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb12 x)
        (t2tb8 (Tuple23 y z)))) e)
     (and (mem
     (tuple21 (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool))
     (Tuple2 (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool)
     (t2tb12 x) (t2tb10 y)) (t2tb202 r1)) (mem
     (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 x z)) (t2tb9 r2)))))) :pattern ((mem
  (tuple21 (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb199 e)
  (direct_product bool (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool)
  (t2tb202 r1) (t2tb9 r2)))) )))

;; direct_product_def
  (assert
  (forall ((e (tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 Bool Bool) Bool)))
  (r1 (set (tuple2 (tuple2 Bool Bool) (tuple2 Bool Bool))))
  (r2 (set (tuple2 (tuple2 Bool Bool) Bool))))
  (! (= (mem (tuple21 (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool))
     (t2tb200 e)
     (direct_product bool (tuple21 bool bool) (tuple21 bool bool)
     (t2tb204 r1) (t2tb9 r2)))
     (exists ((x (tuple2 Bool Bool)) (y (tuple2 Bool Bool)) (z Bool))
     (and
     (= (tb2t200
        (Tuple2 (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool)
        (t2tb12 x) (t2tb10 (Tuple22 y z)))) e)
     (and (mem (tuple21 (tuple21 bool bool) (tuple21 bool bool))
     (Tuple2 (tuple21 bool bool) (tuple21 bool bool) (t2tb12 x) (t2tb12 y))
     (t2tb204 r1)) (mem (tuple21 (tuple21 bool bool) bool)
     (t2tb10 (Tuple22 x z)) (t2tb9 r2)))))) :pattern ((mem
  (tuple21 (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool))
  (t2tb200 e)
  (direct_product bool (tuple21 bool bool) (tuple21 bool bool) (t2tb204 r1)
  (t2tb9 r2)))) )))

;; direct_product_def
  (assert
  (forall ((e (tuple2 (tuple2 Bool Bool) (tuple2 Bool Bool)))
  (r1 (set (tuple2 (tuple2 Bool Bool) Bool))) (r2 (set (tuple2 (tuple2 Bool
  Bool) Bool))))
  (! (= (mem (tuple21 (tuple21 bool bool) (tuple21 bool bool)) (t2tb205 e)
     (direct_product bool bool (tuple21 bool bool) (t2tb9 r1) (t2tb9 r2)))
     (exists ((x (tuple2 Bool Bool)) (y Bool) (z Bool))
     (and
     (= (tb2t205
        (Tuple2 (tuple21 bool bool) (tuple21 bool bool) (t2tb12 x)
        (t2tb12 (Tuple21 y z)))) e)
     (and (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 x y))
     (t2tb9 r1)) (mem (tuple21 (tuple21 bool bool) bool)
     (t2tb10 (Tuple22 x z)) (t2tb9 r2)))))) :pattern ((mem
  (tuple21 (tuple21 bool bool) (tuple21 bool bool)) (t2tb205 e)
  (direct_product bool bool (tuple21 bool bool) (t2tb9 r1) (t2tb9 r2)))) )))

;; direct_product_def
  (assert
  (forall ((v ty))
  (forall ((e uni) (r1 (set (tuple2 (tuple2 Bool Bool) Bool))) (r2 uni))
  (! (=> (sort (tuple21 (tuple21 bool bool) (tuple21 bool v)) e)
     (and
     (=> (mem (tuple21 (tuple21 bool bool) (tuple21 bool v)) e
     (direct_product v bool (tuple21 bool bool) (t2tb9 r1) r2))
     (exists ((x (tuple2 Bool Bool)) (y Bool) (z uni))
     (and (sort v z)
     (and
     (= (Tuple2 (tuple21 bool bool) (tuple21 bool v) (t2tb12 x)
        (Tuple2 bool v (t2tb13 y) z)) e)
     (and (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 x y))
     (t2tb9 r1)) (mem (tuple21 (tuple21 bool bool) v)
     (Tuple2 (tuple21 bool bool) v (t2tb12 x) z) r2))))))
     (=>
     (exists ((x (tuple2 Bool Bool)) (y Bool) (z uni))
     (and
     (= (Tuple2 (tuple21 bool bool) (tuple21 bool v) (t2tb12 x)
        (Tuple2 bool v (t2tb13 y) z)) e)
     (and (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 x y))
     (t2tb9 r1)) (mem (tuple21 (tuple21 bool bool) v)
     (Tuple2 (tuple21 bool bool) v (t2tb12 x) z) r2)))) (mem
     (tuple21 (tuple21 bool bool) (tuple21 bool v)) e
     (direct_product v bool (tuple21 bool bool) (t2tb9 r1) r2))))) :pattern ((mem
  (tuple21 (tuple21 bool bool) (tuple21 bool v)) e
  (direct_product v bool (tuple21 bool bool) (t2tb9 r1) r2))) ))))

;; direct_product_def
  (assert
  (forall ((u ty))
  (forall ((e uni) (r1 uni) (r2 (set (tuple2 Bool Bool))))
  (! (=> (sort (tuple21 bool (tuple21 u bool)) e)
     (and
     (=> (mem (tuple21 bool (tuple21 u bool)) e
     (direct_product bool u bool r1 (t2tb11 r2)))
     (exists ((x Bool) (y uni) (z Bool))
     (and (sort u y)
     (and
     (= (Tuple2 bool (tuple21 u bool) (t2tb13 x)
        (Tuple2 u bool y (t2tb13 z))) e)
     (and (mem (tuple21 bool u) (Tuple2 bool u (t2tb13 x) y) r1) (mem
     (tuple21 bool bool) (t2tb12 (Tuple21 x z)) (t2tb11 r2)))))))
     (=>
     (exists ((x Bool) (y uni) (z Bool))
     (and
     (= (Tuple2 bool (tuple21 u bool) (t2tb13 x)
        (Tuple2 u bool y (t2tb13 z))) e)
     (and (mem (tuple21 bool u) (Tuple2 bool u (t2tb13 x) y) r1) (mem
     (tuple21 bool bool) (t2tb12 (Tuple21 x z)) (t2tb11 r2))))) (mem
     (tuple21 bool (tuple21 u bool)) e
     (direct_product bool u bool r1 (t2tb11 r2)))))) :pattern ((mem
  (tuple21 bool (tuple21 u bool)) e
  (direct_product bool u bool r1 (t2tb11 r2)))) ))))

;; direct_product_def
  (assert
  (forall ((e (tuple2 Bool (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (r1 (set (tuple2 Bool (tuple2 (tuple2 Bool Bool) Bool))))
  (r2 (set (tuple2 Bool Bool))))
  (! (= (mem (tuple21 bool (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
     (t2tb223 e)
     (direct_product bool (tuple21 (tuple21 bool bool) bool) bool (t2tb25 r1)
     (t2tb11 r2)))
     (exists ((x Bool) (y (tuple2 (tuple2 Bool Bool) Bool)) (z Bool))
     (and
     (= (tb2t223
        (Tuple2 bool (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (t2tb13 x) (t2tb8 (Tuple23 y z)))) e)
     (and (mem (tuple21 bool (tuple21 (tuple21 bool bool) bool))
     (Tuple2 bool (tuple21 (tuple21 bool bool) bool) (t2tb13 x) (t2tb10 y))
     (t2tb25 r1)) (mem (tuple21 bool bool) (t2tb12 (Tuple21 x z))
     (t2tb11 r2)))))) :pattern ((mem
  (tuple21 bool (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (t2tb223 e)
  (direct_product bool (tuple21 (tuple21 bool bool) bool) bool (t2tb25 r1)
  (t2tb11 r2)))) )))

;; direct_product_def
  (assert
  (forall ((e (tuple2 Bool (tuple2 (tuple2 Bool Bool) Bool)))
  (r1 (set (tuple2 Bool (tuple2 Bool Bool)))) (r2 (set (tuple2 Bool Bool))))
  (! (= (mem (tuple21 bool (tuple21 (tuple21 bool bool) bool)) (t2tb26 e)
     (direct_product bool (tuple21 bool bool) bool (t2tb27 r1) (t2tb11 r2)))
     (exists ((x Bool) (y (tuple2 Bool Bool)) (z Bool))
     (and
     (= (tb2t26
        (Tuple2 bool (tuple21 (tuple21 bool bool) bool) (t2tb13 x)
        (t2tb10 (Tuple22 y z)))) e)
     (and (mem (tuple21 bool (tuple21 bool bool))
     (Tuple2 bool (tuple21 bool bool) (t2tb13 x) (t2tb12 y)) (t2tb27 r1))
     (mem (tuple21 bool bool) (t2tb12 (Tuple21 x z)) (t2tb11 r2)))))) :pattern ((mem
  (tuple21 bool (tuple21 (tuple21 bool bool) bool)) (t2tb26 e)
  (direct_product bool (tuple21 bool bool) bool (t2tb27 r1) (t2tb11 r2)))) )))

;; direct_product_def
  (assert
  (forall ((e (tuple2 Bool (tuple2 Bool Bool))) (r1 (set (tuple2 Bool Bool)))
  (r2 (set (tuple2 Bool Bool))))
  (! (= (mem (tuple21 bool (tuple21 bool bool)) (t2tb28 e)
     (direct_product bool bool bool (t2tb11 r1) (t2tb11 r2)))
     (exists ((x Bool) (y Bool) (z Bool))
     (and
     (= (tb2t28
        (Tuple2 bool (tuple21 bool bool) (t2tb13 x) (t2tb12 (Tuple21 y z)))) e)
     (and (mem (tuple21 bool bool) (t2tb12 (Tuple21 x y)) (t2tb11 r1)) (mem
     (tuple21 bool bool) (t2tb12 (Tuple21 x z)) (t2tb11 r2)))))) :pattern ((mem
  (tuple21 bool (tuple21 bool bool)) (t2tb28 e)
  (direct_product bool bool bool (t2tb11 r1) (t2tb11 r2)))) )))

;; direct_product_def
  (assert
  (forall ((v ty))
  (forall ((e uni) (r1 (set (tuple2 Bool Bool))) (r2 uni))
  (! (=> (sort (tuple21 bool (tuple21 bool v)) e)
     (and
     (=> (mem (tuple21 bool (tuple21 bool v)) e
     (direct_product v bool bool (t2tb11 r1) r2))
     (exists ((x Bool) (y Bool) (z uni))
     (and (sort v z)
     (and
     (= (Tuple2 bool (tuple21 bool v) (t2tb13 x)
        (Tuple2 bool v (t2tb13 y) z)) e)
     (and (mem (tuple21 bool bool) (t2tb12 (Tuple21 x y)) (t2tb11 r1)) (mem
     (tuple21 bool v) (Tuple2 bool v (t2tb13 x) z) r2))))))
     (=>
     (exists ((x Bool) (y Bool) (z uni))
     (and
     (= (Tuple2 bool (tuple21 bool v) (t2tb13 x)
        (Tuple2 bool v (t2tb13 y) z)) e)
     (and (mem (tuple21 bool bool) (t2tb12 (Tuple21 x y)) (t2tb11 r1)) (mem
     (tuple21 bool v) (Tuple2 bool v (t2tb13 x) z) r2)))) (mem
     (tuple21 bool (tuple21 bool v)) e
     (direct_product v bool bool (t2tb11 r1) r2))))) :pattern ((mem
  (tuple21 bool (tuple21 bool v)) e
  (direct_product v bool bool (t2tb11 r1) r2))) ))))

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
  (forall ((e uni) (r1 uni) (r2 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))))
  (=> (sort
  (tuple21 (tuple21 t (tuple21 (tuple21 bool bool) bool)) (tuple21 u bool))
  e)
  (and
  (=> (mem
  (tuple21 (tuple21 t (tuple21 (tuple21 bool bool) bool)) (tuple21 u bool)) e
  (parallel_product bool (tuple21 (tuple21 bool bool) bool) u t r1
  (t2tb7 r2)))
  (exists ((x uni) (y (tuple2 (tuple2 Bool Bool) Bool)) (z uni) (a Bool))
  (and (sort t x)
  (and (sort u z)
  (and
  (= (Tuple2 (tuple21 t (tuple21 (tuple21 bool bool) bool)) (tuple21 u bool)
     (Tuple2 t (tuple21 (tuple21 bool bool) bool) x (t2tb10 y))
     (Tuple2 u bool z (t2tb13 a))) e)
  (and (mem (tuple21 t u) (Tuple2 t u x z) r1) (mem
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 (Tuple23 y a))
  (t2tb7 r2))))))))
  (=>
  (exists ((x uni) (y (tuple2 (tuple2 Bool Bool) Bool)) (z uni) (a Bool))
  (and
  (= (Tuple2 (tuple21 t (tuple21 (tuple21 bool bool) bool)) (tuple21 u bool)
     (Tuple2 t (tuple21 (tuple21 bool bool) bool) x (t2tb10 y))
     (Tuple2 u bool z (t2tb13 a))) e)
  (and (mem (tuple21 t u) (Tuple2 t u x z) r1) (mem
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 (Tuple23 y a))
  (t2tb7 r2))))) (mem
  (tuple21 (tuple21 t (tuple21 (tuple21 bool bool) bool)) (tuple21 u bool)) e
  (parallel_product bool (tuple21 (tuple21 bool bool) bool) u t r1
  (t2tb7 r2)))))))))

;; parallel_product_def
  (assert
  (forall ((t ty) (u ty))
  (forall ((e uni) (r1 uni) (r2 (set (tuple2 (tuple2 Bool Bool) Bool))))
  (=> (sort (tuple21 (tuple21 t (tuple21 bool bool)) (tuple21 u bool)) e)
  (and
  (=> (mem (tuple21 (tuple21 t (tuple21 bool bool)) (tuple21 u bool)) e
  (parallel_product bool (tuple21 bool bool) u t r1 (t2tb9 r2)))
  (exists ((x uni) (y (tuple2 Bool Bool)) (z uni) (a Bool))
  (and (sort t x)
  (and (sort u z)
  (and
  (= (Tuple2 (tuple21 t (tuple21 bool bool)) (tuple21 u bool)
     (Tuple2 t (tuple21 bool bool) x (t2tb12 y))
     (Tuple2 u bool z (t2tb13 a))) e)
  (and (mem (tuple21 t u) (Tuple2 t u x z) r1) (mem
  (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 y a)) (t2tb9 r2))))))))
  (=>
  (exists ((x uni) (y (tuple2 Bool Bool)) (z uni) (a Bool))
  (and
  (= (Tuple2 (tuple21 t (tuple21 bool bool)) (tuple21 u bool)
     (Tuple2 t (tuple21 bool bool) x (t2tb12 y))
     (Tuple2 u bool z (t2tb13 a))) e)
  (and (mem (tuple21 t u) (Tuple2 t u x z) r1) (mem
  (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 y a)) (t2tb9 r2)))))
  (mem (tuple21 (tuple21 t (tuple21 bool bool)) (tuple21 u bool)) e
  (parallel_product bool (tuple21 bool bool) u t r1 (t2tb9 r2)))))))))

;; parallel_product_def
  (assert
  (forall ((t ty) (u ty))
  (forall ((e uni) (r1 uni) (r2 (set (tuple2 Bool Bool))))
  (=> (sort (tuple21 (tuple21 t bool) (tuple21 u bool)) e)
  (and
  (=> (mem (tuple21 (tuple21 t bool) (tuple21 u bool)) e
  (parallel_product bool bool u t r1 (t2tb11 r2)))
  (exists ((x uni) (y Bool) (z uni) (a Bool))
  (and (sort t x)
  (and (sort u z)
  (and
  (= (Tuple2 (tuple21 t bool) (tuple21 u bool) (Tuple2 t bool x (t2tb13 y))
     (Tuple2 u bool z (t2tb13 a))) e)
  (and (mem (tuple21 t u) (Tuple2 t u x z) r1) (mem (tuple21 bool bool)
  (t2tb12 (Tuple21 y a)) (t2tb11 r2))))))))
  (=>
  (exists ((x uni) (y Bool) (z uni) (a Bool))
  (and
  (= (Tuple2 (tuple21 t bool) (tuple21 u bool) (Tuple2 t bool x (t2tb13 y))
     (Tuple2 u bool z (t2tb13 a))) e)
  (and (mem (tuple21 t u) (Tuple2 t u x z) r1) (mem (tuple21 bool bool)
  (t2tb12 (Tuple21 y a)) (t2tb11 r2))))) (mem
  (tuple21 (tuple21 t bool) (tuple21 u bool)) e
  (parallel_product bool bool u t r1 (t2tb11 r2)))))))))

;; parallel_product_def
  (assert
  (forall ((t ty) (v ty))
  (forall ((e uni) (r1 uni) (r2 uni))
  (=> (sort
  (tuple21 (tuple21 t v) (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  e)
  (and
  (=> (mem
  (tuple21 (tuple21 t v) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) e
  (parallel_product bool v (tuple21 (tuple21 bool bool) bool) t r1 r2))
  (exists ((x uni) (y uni) (z (tuple2 (tuple2 Bool Bool) Bool)) (a Bool))
  (and (sort t x)
  (and (sort v y)
  (and
  (= (Tuple2 (tuple21 t v) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (Tuple2 t v x y) (t2tb8 (Tuple23 z a))) e)
  (and (mem (tuple21 t (tuple21 (tuple21 bool bool) bool))
  (Tuple2 t (tuple21 (tuple21 bool bool) bool) x (t2tb10 z)) r1) (mem
  (tuple21 v bool) (Tuple2 v bool y (t2tb13 a)) r2)))))))
  (=>
  (exists ((x uni) (y uni) (z (tuple2 (tuple2 Bool Bool) Bool)) (a Bool))
  (and
  (= (Tuple2 (tuple21 t v) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (Tuple2 t v x y) (t2tb8 (Tuple23 z a))) e)
  (and (mem (tuple21 t (tuple21 (tuple21 bool bool) bool))
  (Tuple2 t (tuple21 (tuple21 bool bool) bool) x (t2tb10 z)) r1) (mem
  (tuple21 v bool) (Tuple2 v bool y (t2tb13 a)) r2)))) (mem
  (tuple21 (tuple21 t v) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) e
  (parallel_product bool v (tuple21 (tuple21 bool bool) bool) t r1 r2))))))))

;; parallel_product_def
  (assert
  (forall ((t ty))
  (forall ((e uni) (r1 uni) (r2 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))))
  (=> (sort
  (tuple21 (tuple21 t (tuple21 (tuple21 bool bool) bool))
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) e)
  (and
  (=> (mem
  (tuple21 (tuple21 t (tuple21 (tuple21 bool bool) bool))
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) e
  (parallel_product bool (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 bool bool) bool) t r1 (t2tb7 r2)))
  (exists ((x uni) (y (tuple2 (tuple2 Bool Bool) Bool))
  (z (tuple2 (tuple2 Bool Bool) Bool)) (a Bool))
  (and (sort t x)
  (and
  (= (Tuple2 (tuple21 t (tuple21 (tuple21 bool bool) bool))
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (Tuple2 t (tuple21 (tuple21 bool bool) bool) x (t2tb10 y))
     (t2tb8 (Tuple23 z a))) e)
  (and (mem (tuple21 t (tuple21 (tuple21 bool bool) bool))
  (Tuple2 t (tuple21 (tuple21 bool bool) bool) x (t2tb10 z)) r1) (mem
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 (Tuple23 y a))
  (t2tb7 r2)))))))
  (=>
  (exists ((x uni) (y (tuple2 (tuple2 Bool Bool) Bool))
  (z (tuple2 (tuple2 Bool Bool) Bool)) (a Bool))
  (and
  (= (Tuple2 (tuple21 t (tuple21 (tuple21 bool bool) bool))
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (Tuple2 t (tuple21 (tuple21 bool bool) bool) x (t2tb10 y))
     (t2tb8 (Tuple23 z a))) e)
  (and (mem (tuple21 t (tuple21 (tuple21 bool bool) bool))
  (Tuple2 t (tuple21 (tuple21 bool bool) bool) x (t2tb10 z)) r1) (mem
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 (Tuple23 y a))
  (t2tb7 r2))))) (mem
  (tuple21 (tuple21 t (tuple21 (tuple21 bool bool) bool))
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) e
  (parallel_product bool (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 bool bool) bool) t r1 (t2tb7 r2)))))))))

;; parallel_product_def
  (assert
  (forall ((t ty))
  (forall ((e uni) (r1 uni) (r2 (set (tuple2 (tuple2 Bool Bool) Bool))))
  (=> (sort
  (tuple21 (tuple21 t (tuple21 bool bool))
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) e)
  (and
  (=> (mem
  (tuple21 (tuple21 t (tuple21 bool bool))
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) e
  (parallel_product bool (tuple21 bool bool)
  (tuple21 (tuple21 bool bool) bool) t r1 (t2tb9 r2)))
  (exists ((x uni) (y (tuple2 Bool Bool)) (z (tuple2 (tuple2 Bool Bool)
  Bool)) (a Bool))
  (and (sort t x)
  (and
  (= (Tuple2 (tuple21 t (tuple21 bool bool))
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (Tuple2 t (tuple21 bool bool) x (t2tb12 y)) (t2tb8 (Tuple23 z a))) e)
  (and (mem (tuple21 t (tuple21 (tuple21 bool bool) bool))
  (Tuple2 t (tuple21 (tuple21 bool bool) bool) x (t2tb10 z)) r1) (mem
  (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 y a)) (t2tb9 r2)))))))
  (=>
  (exists ((x uni) (y (tuple2 Bool Bool)) (z (tuple2 (tuple2 Bool Bool)
  Bool)) (a Bool))
  (and
  (= (Tuple2 (tuple21 t (tuple21 bool bool))
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (Tuple2 t (tuple21 bool bool) x (t2tb12 y)) (t2tb8 (Tuple23 z a))) e)
  (and (mem (tuple21 t (tuple21 (tuple21 bool bool) bool))
  (Tuple2 t (tuple21 (tuple21 bool bool) bool) x (t2tb10 z)) r1) (mem
  (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 y a)) (t2tb9 r2)))))
  (mem
  (tuple21 (tuple21 t (tuple21 bool bool))
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) e
  (parallel_product bool (tuple21 bool bool)
  (tuple21 (tuple21 bool bool) bool) t r1 (t2tb9 r2)))))))))

;; parallel_product_def
  (assert
  (forall ((t ty))
  (forall ((e uni) (r1 uni) (r2 (set (tuple2 Bool Bool))))
  (=> (sort
  (tuple21 (tuple21 t bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) e)
  (and
  (=> (mem
  (tuple21 (tuple21 t bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) e
  (parallel_product bool bool (tuple21 (tuple21 bool bool) bool) t r1
  (t2tb11 r2)))
  (exists ((x uni) (y Bool) (z (tuple2 (tuple2 Bool Bool) Bool)) (a Bool))
  (and (sort t x)
  (and
  (= (Tuple2 (tuple21 t bool)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (Tuple2 t bool x (t2tb13 y)) (t2tb8 (Tuple23 z a))) e)
  (and (mem (tuple21 t (tuple21 (tuple21 bool bool) bool))
  (Tuple2 t (tuple21 (tuple21 bool bool) bool) x (t2tb10 z)) r1) (mem
  (tuple21 bool bool) (t2tb12 (Tuple21 y a)) (t2tb11 r2)))))))
  (=>
  (exists ((x uni) (y Bool) (z (tuple2 (tuple2 Bool Bool) Bool)) (a Bool))
  (and
  (= (Tuple2 (tuple21 t bool)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (Tuple2 t bool x (t2tb13 y)) (t2tb8 (Tuple23 z a))) e)
  (and (mem (tuple21 t (tuple21 (tuple21 bool bool) bool))
  (Tuple2 t (tuple21 (tuple21 bool bool) bool) x (t2tb10 z)) r1) (mem
  (tuple21 bool bool) (t2tb12 (Tuple21 y a)) (t2tb11 r2))))) (mem
  (tuple21 (tuple21 t bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) e
  (parallel_product bool bool (tuple21 (tuple21 bool bool) bool) t r1
  (t2tb11 r2)))))))))

;; parallel_product_def
  (assert
  (forall ((t ty) (v ty))
  (forall ((e uni) (r1 uni) (r2 uni))
  (=> (sort (tuple21 (tuple21 t v) (tuple21 (tuple21 bool bool) bool)) e)
  (and
  (=> (mem (tuple21 (tuple21 t v) (tuple21 (tuple21 bool bool) bool)) e
  (parallel_product bool v (tuple21 bool bool) t r1 r2))
  (exists ((x uni) (y uni) (z (tuple2 Bool Bool)) (a Bool))
  (and (sort t x)
  (and (sort v y)
  (and
  (= (Tuple2 (tuple21 t v) (tuple21 (tuple21 bool bool) bool)
     (Tuple2 t v x y) (t2tb10 (Tuple22 z a))) e)
  (and (mem (tuple21 t (tuple21 bool bool))
  (Tuple2 t (tuple21 bool bool) x (t2tb12 z)) r1) (mem (tuple21 v bool)
  (Tuple2 v bool y (t2tb13 a)) r2)))))))
  (=>
  (exists ((x uni) (y uni) (z (tuple2 Bool Bool)) (a Bool))
  (and
  (= (Tuple2 (tuple21 t v) (tuple21 (tuple21 bool bool) bool)
     (Tuple2 t v x y) (t2tb10 (Tuple22 z a))) e)
  (and (mem (tuple21 t (tuple21 bool bool))
  (Tuple2 t (tuple21 bool bool) x (t2tb12 z)) r1) (mem (tuple21 v bool)
  (Tuple2 v bool y (t2tb13 a)) r2)))) (mem
  (tuple21 (tuple21 t v) (tuple21 (tuple21 bool bool) bool)) e
  (parallel_product bool v (tuple21 bool bool) t r1 r2))))))))

;; parallel_product_def
  (assert
  (forall ((t ty))
  (forall ((e uni) (r1 uni) (r2 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))))
  (=> (sort
  (tuple21 (tuple21 t (tuple21 (tuple21 bool bool) bool))
  (tuple21 (tuple21 bool bool) bool)) e)
  (and
  (=> (mem
  (tuple21 (tuple21 t (tuple21 (tuple21 bool bool) bool))
  (tuple21 (tuple21 bool bool) bool)) e
  (parallel_product bool (tuple21 (tuple21 bool bool) bool)
  (tuple21 bool bool) t r1 (t2tb7 r2)))
  (exists ((x uni) (y (tuple2 (tuple2 Bool Bool) Bool)) (z (tuple2 Bool
  Bool)) (a Bool))
  (and (sort t x)
  (and
  (= (Tuple2 (tuple21 t (tuple21 (tuple21 bool bool) bool))
     (tuple21 (tuple21 bool bool) bool)
     (Tuple2 t (tuple21 (tuple21 bool bool) bool) x (t2tb10 y))
     (t2tb10 (Tuple22 z a))) e)
  (and (mem (tuple21 t (tuple21 bool bool))
  (Tuple2 t (tuple21 bool bool) x (t2tb12 z)) r1) (mem
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 (Tuple23 y a))
  (t2tb7 r2)))))))
  (=>
  (exists ((x uni) (y (tuple2 (tuple2 Bool Bool) Bool)) (z (tuple2 Bool
  Bool)) (a Bool))
  (and
  (= (Tuple2 (tuple21 t (tuple21 (tuple21 bool bool) bool))
     (tuple21 (tuple21 bool bool) bool)
     (Tuple2 t (tuple21 (tuple21 bool bool) bool) x (t2tb10 y))
     (t2tb10 (Tuple22 z a))) e)
  (and (mem (tuple21 t (tuple21 bool bool))
  (Tuple2 t (tuple21 bool bool) x (t2tb12 z)) r1) (mem
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 (Tuple23 y a))
  (t2tb7 r2))))) (mem
  (tuple21 (tuple21 t (tuple21 (tuple21 bool bool) bool))
  (tuple21 (tuple21 bool bool) bool)) e
  (parallel_product bool (tuple21 (tuple21 bool bool) bool)
  (tuple21 bool bool) t r1 (t2tb7 r2)))))))))

;; parallel_product_def
  (assert
  (forall ((t ty))
  (forall ((e uni) (r1 uni) (r2 (set (tuple2 (tuple2 Bool Bool) Bool))))
  (=> (sort
  (tuple21 (tuple21 t (tuple21 bool bool))
  (tuple21 (tuple21 bool bool) bool)) e)
  (and
  (=> (mem
  (tuple21 (tuple21 t (tuple21 bool bool))
  (tuple21 (tuple21 bool bool) bool)) e
  (parallel_product bool (tuple21 bool bool) (tuple21 bool bool) t r1
  (t2tb9 r2)))
  (exists ((x uni) (y (tuple2 Bool Bool)) (z (tuple2 Bool Bool)) (a Bool))
  (and (sort t x)
  (and
  (= (Tuple2 (tuple21 t (tuple21 bool bool))
     (tuple21 (tuple21 bool bool) bool)
     (Tuple2 t (tuple21 bool bool) x (t2tb12 y)) (t2tb10 (Tuple22 z a))) e)
  (and (mem (tuple21 t (tuple21 bool bool))
  (Tuple2 t (tuple21 bool bool) x (t2tb12 z)) r1) (mem
  (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 y a)) (t2tb9 r2)))))))
  (=>
  (exists ((x uni) (y (tuple2 Bool Bool)) (z (tuple2 Bool Bool)) (a Bool))
  (and
  (= (Tuple2 (tuple21 t (tuple21 bool bool))
     (tuple21 (tuple21 bool bool) bool)
     (Tuple2 t (tuple21 bool bool) x (t2tb12 y)) (t2tb10 (Tuple22 z a))) e)
  (and (mem (tuple21 t (tuple21 bool bool))
  (Tuple2 t (tuple21 bool bool) x (t2tb12 z)) r1) (mem
  (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 y a)) (t2tb9 r2)))))
  (mem
  (tuple21 (tuple21 t (tuple21 bool bool))
  (tuple21 (tuple21 bool bool) bool)) e
  (parallel_product bool (tuple21 bool bool) (tuple21 bool bool) t r1
  (t2tb9 r2)))))))))

;; parallel_product_def
  (assert
  (forall ((t ty))
  (forall ((e uni) (r1 uni) (r2 (set (tuple2 Bool Bool))))
  (=> (sort (tuple21 (tuple21 t bool) (tuple21 (tuple21 bool bool) bool)) e)
  (and
  (=> (mem (tuple21 (tuple21 t bool) (tuple21 (tuple21 bool bool) bool)) e
  (parallel_product bool bool (tuple21 bool bool) t r1 (t2tb11 r2)))
  (exists ((x uni) (y Bool) (z (tuple2 Bool Bool)) (a Bool))
  (and (sort t x)
  (and
  (= (Tuple2 (tuple21 t bool) (tuple21 (tuple21 bool bool) bool)
     (Tuple2 t bool x (t2tb13 y)) (t2tb10 (Tuple22 z a))) e)
  (and (mem (tuple21 t (tuple21 bool bool))
  (Tuple2 t (tuple21 bool bool) x (t2tb12 z)) r1) (mem (tuple21 bool bool)
  (t2tb12 (Tuple21 y a)) (t2tb11 r2)))))))
  (=>
  (exists ((x uni) (y Bool) (z (tuple2 Bool Bool)) (a Bool))
  (and
  (= (Tuple2 (tuple21 t bool) (tuple21 (tuple21 bool bool) bool)
     (Tuple2 t bool x (t2tb13 y)) (t2tb10 (Tuple22 z a))) e)
  (and (mem (tuple21 t (tuple21 bool bool))
  (Tuple2 t (tuple21 bool bool) x (t2tb12 z)) r1) (mem (tuple21 bool bool)
  (t2tb12 (Tuple21 y a)) (t2tb11 r2))))) (mem
  (tuple21 (tuple21 t bool) (tuple21 (tuple21 bool bool) bool)) e
  (parallel_product bool bool (tuple21 bool bool) t r1 (t2tb11 r2)))))))))

;; parallel_product_def
  (assert
  (forall ((t ty) (v ty))
  (forall ((e uni) (r1 uni) (r2 uni))
  (=> (sort (tuple21 (tuple21 t v) (tuple21 bool bool)) e)
  (and
  (=> (mem (tuple21 (tuple21 t v) (tuple21 bool bool)) e
  (parallel_product bool v bool t r1 r2))
  (exists ((x uni) (y uni) (z Bool) (a Bool))
  (and (sort t x)
  (and (sort v y)
  (and
  (= (Tuple2 (tuple21 t v) (tuple21 bool bool) (Tuple2 t v x y)
     (t2tb12 (Tuple21 z a))) e)
  (and (mem (tuple21 t bool) (Tuple2 t bool x (t2tb13 z)) r1) (mem
  (tuple21 v bool) (Tuple2 v bool y (t2tb13 a)) r2)))))))
  (=>
  (exists ((x uni) (y uni) (z Bool) (a Bool))
  (and
  (= (Tuple2 (tuple21 t v) (tuple21 bool bool) (Tuple2 t v x y)
     (t2tb12 (Tuple21 z a))) e)
  (and (mem (tuple21 t bool) (Tuple2 t bool x (t2tb13 z)) r1) (mem
  (tuple21 v bool) (Tuple2 v bool y (t2tb13 a)) r2)))) (mem
  (tuple21 (tuple21 t v) (tuple21 bool bool)) e
  (parallel_product bool v bool t r1 r2))))))))

;; parallel_product_def
  (assert
  (forall ((t ty))
  (forall ((e uni) (r1 uni) (r2 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))))
  (=> (sort
  (tuple21 (tuple21 t (tuple21 (tuple21 bool bool) bool))
  (tuple21 bool bool)) e)
  (and
  (=> (mem
  (tuple21 (tuple21 t (tuple21 (tuple21 bool bool) bool))
  (tuple21 bool bool)) e
  (parallel_product bool (tuple21 (tuple21 bool bool) bool) bool t r1
  (t2tb7 r2)))
  (exists ((x uni) (y (tuple2 (tuple2 Bool Bool) Bool)) (z Bool) (a Bool))
  (and (sort t x)
  (and
  (= (Tuple2 (tuple21 t (tuple21 (tuple21 bool bool) bool))
     (tuple21 bool bool)
     (Tuple2 t (tuple21 (tuple21 bool bool) bool) x (t2tb10 y))
     (t2tb12 (Tuple21 z a))) e)
  (and (mem (tuple21 t bool) (Tuple2 t bool x (t2tb13 z)) r1) (mem
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 (Tuple23 y a))
  (t2tb7 r2)))))))
  (=>
  (exists ((x uni) (y (tuple2 (tuple2 Bool Bool) Bool)) (z Bool) (a Bool))
  (and
  (= (Tuple2 (tuple21 t (tuple21 (tuple21 bool bool) bool))
     (tuple21 bool bool)
     (Tuple2 t (tuple21 (tuple21 bool bool) bool) x (t2tb10 y))
     (t2tb12 (Tuple21 z a))) e)
  (and (mem (tuple21 t bool) (Tuple2 t bool x (t2tb13 z)) r1) (mem
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 (Tuple23 y a))
  (t2tb7 r2))))) (mem
  (tuple21 (tuple21 t (tuple21 (tuple21 bool bool) bool))
  (tuple21 bool bool)) e
  (parallel_product bool (tuple21 (tuple21 bool bool) bool) bool t r1
  (t2tb7 r2)))))))))

;; parallel_product_def
  (assert
  (forall ((t ty))
  (forall ((e uni) (r1 uni) (r2 (set (tuple2 (tuple2 Bool Bool) Bool))))
  (=> (sort (tuple21 (tuple21 t (tuple21 bool bool)) (tuple21 bool bool)) e)
  (and
  (=> (mem (tuple21 (tuple21 t (tuple21 bool bool)) (tuple21 bool bool)) e
  (parallel_product bool (tuple21 bool bool) bool t r1 (t2tb9 r2)))
  (exists ((x uni) (y (tuple2 Bool Bool)) (z Bool) (a Bool))
  (and (sort t x)
  (and
  (= (Tuple2 (tuple21 t (tuple21 bool bool)) (tuple21 bool bool)
     (Tuple2 t (tuple21 bool bool) x (t2tb12 y)) (t2tb12 (Tuple21 z a))) e)
  (and (mem (tuple21 t bool) (Tuple2 t bool x (t2tb13 z)) r1) (mem
  (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 y a)) (t2tb9 r2)))))))
  (=>
  (exists ((x uni) (y (tuple2 Bool Bool)) (z Bool) (a Bool))
  (and
  (= (Tuple2 (tuple21 t (tuple21 bool bool)) (tuple21 bool bool)
     (Tuple2 t (tuple21 bool bool) x (t2tb12 y)) (t2tb12 (Tuple21 z a))) e)
  (and (mem (tuple21 t bool) (Tuple2 t bool x (t2tb13 z)) r1) (mem
  (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 y a)) (t2tb9 r2)))))
  (mem (tuple21 (tuple21 t (tuple21 bool bool)) (tuple21 bool bool)) e
  (parallel_product bool (tuple21 bool bool) bool t r1 (t2tb9 r2)))))))))

;; parallel_product_def
  (assert
  (forall ((t ty))
  (forall ((e uni) (r1 uni) (r2 (set (tuple2 Bool Bool))))
  (=> (sort (tuple21 (tuple21 t bool) (tuple21 bool bool)) e)
  (and
  (=> (mem (tuple21 (tuple21 t bool) (tuple21 bool bool)) e
  (parallel_product bool bool bool t r1 (t2tb11 r2)))
  (exists ((x uni) (y Bool) (z Bool) (a Bool))
  (and (sort t x)
  (and
  (= (Tuple2 (tuple21 t bool) (tuple21 bool bool)
     (Tuple2 t bool x (t2tb13 y)) (t2tb12 (Tuple21 z a))) e)
  (and (mem (tuple21 t bool) (Tuple2 t bool x (t2tb13 z)) r1) (mem
  (tuple21 bool bool) (t2tb12 (Tuple21 y a)) (t2tb11 r2)))))))
  (=>
  (exists ((x uni) (y Bool) (z Bool) (a Bool))
  (and
  (= (Tuple2 (tuple21 t bool) (tuple21 bool bool)
     (Tuple2 t bool x (t2tb13 y)) (t2tb12 (Tuple21 z a))) e)
  (and (mem (tuple21 t bool) (Tuple2 t bool x (t2tb13 z)) r1) (mem
  (tuple21 bool bool) (t2tb12 (Tuple21 y a)) (t2tb11 r2))))) (mem
  (tuple21 (tuple21 t bool) (tuple21 bool bool)) e
  (parallel_product bool bool bool t r1 (t2tb11 r2)))))))))

;; parallel_product_def
  (assert
  (forall ((u ty))
  (forall ((e uni) (r1 uni) (r2 (set (tuple2 Bool Bool))))
  (=> (sort
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 u bool)) e)
  (and
  (=> (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 u bool)) e
  (parallel_product bool bool u (tuple21 (tuple21 bool bool) bool) r1
  (t2tb11 r2)))
  (exists ((x (tuple2 (tuple2 Bool Bool) Bool)) (y Bool) (z uni) (a Bool))
  (and (sort u z)
  (and
  (= (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (tuple21 u bool) (t2tb8 (Tuple23 x y)) (Tuple2 u bool z (t2tb13 a))) e)
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) u)
  (Tuple2 (tuple21 (tuple21 bool bool) bool) u (t2tb10 x) z) r1) (mem
  (tuple21 bool bool) (t2tb12 (Tuple21 y a)) (t2tb11 r2)))))))
  (=>
  (exists ((x (tuple2 (tuple2 Bool Bool) Bool)) (y Bool) (z uni) (a Bool))
  (and
  (= (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (tuple21 u bool) (t2tb8 (Tuple23 x y)) (Tuple2 u bool z (t2tb13 a))) e)
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) u)
  (Tuple2 (tuple21 (tuple21 bool bool) bool) u (t2tb10 x) z) r1) (mem
  (tuple21 bool bool) (t2tb12 (Tuple21 y a)) (t2tb11 r2))))) (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 u bool)) e
  (parallel_product bool bool u (tuple21 (tuple21 bool bool) bool) r1
  (t2tb11 r2)))))))))

;; parallel_product_def
  (assert
  (forall ((u ty) (w ty))
  (forall ((e uni) (r1 uni) (r2 uni))
  (=> (sort
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (tuple21 u w))
  e)
  (and
  (=> (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (tuple21 u w)) e
  (parallel_product w bool u (tuple21 (tuple21 bool bool) bool) r1 r2))
  (exists ((x (tuple2 (tuple2 Bool Bool) Bool)) (y Bool) (z uni) (a uni))
  (and (sort u z)
  (and (sort w a)
  (and
  (= (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (tuple21 u w)
     (t2tb8 (Tuple23 x y)) (Tuple2 u w z a)) e)
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) u)
  (Tuple2 (tuple21 (tuple21 bool bool) bool) u (t2tb10 x) z) r1) (mem
  (tuple21 bool w) (Tuple2 bool w (t2tb13 y) a) r2)))))))
  (=>
  (exists ((x (tuple2 (tuple2 Bool Bool) Bool)) (y Bool) (z uni) (a uni))
  (and
  (= (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (tuple21 u w)
     (t2tb8 (Tuple23 x y)) (Tuple2 u w z a)) e)
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) u)
  (Tuple2 (tuple21 (tuple21 bool bool) bool) u (t2tb10 x) z) r1) (mem
  (tuple21 bool w) (Tuple2 bool w (t2tb13 y) a) r2)))) (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (tuple21 u w)) e
  (parallel_product w bool u (tuple21 (tuple21 bool bool) bool) r1 r2))))))))

;; parallel_product_def
  (assert
  (forall ((e (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (r1 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) (tuple2 (tuple2 Bool
  Bool) Bool)))) (r2 (set (tuple2 Bool Bool))))
  (= (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb148 e)
  (parallel_product bool bool (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 bool bool) bool) (t2tb177 r1) (t2tb11 r2)))
  (exists ((x (tuple2 (tuple2 Bool Bool) Bool)) (y Bool)
  (z (tuple2 (tuple2 Bool Bool) Bool)) (a Bool))
  (and
  (= (tb2t148
     (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 (Tuple23 x y))
     (t2tb8 (Tuple23 z a)))) e)
  (and (mem
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 bool bool) bool))
  (Tuple2 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb10 z)) (t2tb177 r1))
  (mem (tuple21 bool bool) (t2tb12 (Tuple21 y a)) (t2tb11 r2))))))))

;; parallel_product_def
  (assert
  (forall ((e (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 (tuple2 Bool Bool) Bool))) (r1 (set (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) (tuple2 Bool Bool)))) (r2 (set (tuple2 Bool Bool))))
  (= (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 bool bool) bool)) (t2tb151 e)
  (parallel_product bool bool (tuple21 bool bool)
  (tuple21 (tuple21 bool bool) bool) (t2tb180 r1) (t2tb11 r2)))
  (exists ((x (tuple2 (tuple2 Bool Bool) Bool)) (y Bool) (z (tuple2 Bool
  Bool)) (a Bool))
  (and
  (= (tb2t151
     (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (tuple21 (tuple21 bool bool) bool) (t2tb8 (Tuple23 x y))
     (t2tb10 (Tuple22 z a)))) e)
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool))
  (Tuple2 (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool) (t2tb10 x)
  (t2tb12 z)) (t2tb180 r1)) (mem (tuple21 bool bool) (t2tb12 (Tuple21 y a))
  (t2tb11 r2))))))))

;; parallel_product_def
  (assert
  (forall ((v ty))
  (forall ((e uni) (r1 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (r2 uni))
  (=> (sort
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) v)
  (tuple21 bool bool)) e)
  (and
  (=> (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) v)
  (tuple21 bool bool)) e
  (parallel_product bool v bool (tuple21 (tuple21 bool bool) bool) (t2tb7 r1)
  r2))
  (exists ((x (tuple2 (tuple2 Bool Bool) Bool)) (y uni) (z Bool) (a Bool))
  (and (sort v y)
  (and
  (= (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) v)
     (tuple21 bool bool)
     (Tuple2 (tuple21 (tuple21 bool bool) bool) v (t2tb10 x) y)
     (t2tb12 (Tuple21 z a))) e)
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb8 (Tuple23 x z)) (t2tb7 r1)) (mem (tuple21 v bool)
  (Tuple2 v bool y (t2tb13 a)) r2))))))
  (=>
  (exists ((x (tuple2 (tuple2 Bool Bool) Bool)) (y uni) (z Bool) (a Bool))
  (and
  (= (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) v)
     (tuple21 bool bool)
     (Tuple2 (tuple21 (tuple21 bool bool) bool) v (t2tb10 x) y)
     (t2tb12 (Tuple21 z a))) e)
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb8 (Tuple23 x z)) (t2tb7 r1)) (mem (tuple21 v bool)
  (Tuple2 v bool y (t2tb13 a)) r2)))) (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) v)
  (tuple21 bool bool)) e
  (parallel_product bool v bool (tuple21 (tuple21 bool bool) bool) (t2tb7 r1)
  r2))))))))

(declare-fun t2tb256 ((set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 Bool Bool) Bool)) (tuple2 Bool Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 Bool Bool) Bool)) (tuple2 Bool Bool))))) (sort
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 bool bool) bool)) (tuple21 bool bool))) (t2tb256 x))))

(declare-fun tb2t256 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) (tuple2 (tuple2 Bool Bool) Bool)) (tuple2 Bool Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 Bool Bool) Bool)) (tuple2 Bool Bool)))))
  (! (= (tb2t256 (t2tb256 i)) i) :pattern ((t2tb256 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21
     (tuple21 (tuple21 (tuple21 bool bool) bool)
     (tuple21 (tuple21 bool bool) bool)) (tuple21 bool bool))) j)
     (= (t2tb256 (tb2t256 j)) j)) :pattern ((t2tb256 (tb2t256 j))) )))

(declare-fun t2tb257 ((tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 Bool Bool) Bool)) (tuple2 Bool Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 Bool Bool) Bool)) (tuple2 Bool Bool)))) (sort
  (tuple21
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 bool bool) bool)) (tuple21 bool bool)) (t2tb257 x))))

(declare-fun tb2t257 (uni) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 Bool Bool) Bool)) (tuple2 Bool Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 Bool Bool) Bool)) (tuple2 Bool Bool))))
  (! (= (tb2t257 (t2tb257 i)) i) :pattern ((t2tb257 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21
     (tuple21 (tuple21 (tuple21 bool bool) bool)
     (tuple21 (tuple21 bool bool) bool)) (tuple21 bool bool)) j)
     (= (t2tb257 (tb2t257 j)) j)) :pattern ((t2tb257 (tb2t257 j))) )))

;; parallel_product_def
  (assert
  (forall ((e (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 Bool Bool) Bool)) (tuple2 Bool Bool)))
  (r1 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (r2 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (= (mem
  (tuple21
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 bool bool) bool)) (tuple21 bool bool)) (t2tb257 e)
  (parallel_product bool (tuple21 (tuple21 bool bool) bool) bool
  (tuple21 (tuple21 bool bool) bool) (t2tb7 r1) (t2tb7 r2)))
  (exists ((x (tuple2 (tuple2 Bool Bool) Bool)) (y (tuple2 (tuple2 Bool Bool)
  Bool)) (z Bool) (a Bool))
  (and
  (= (tb2t257
     (Tuple2
     (tuple21 (tuple21 (tuple21 bool bool) bool)
     (tuple21 (tuple21 bool bool) bool)) (tuple21 bool bool)
     (Tuple2 (tuple21 (tuple21 bool bool) bool)
     (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb10 y))
     (t2tb12 (Tuple21 z a)))) e)
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb8 (Tuple23 x z)) (t2tb7 r1)) (mem
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 (Tuple23 y a))
  (t2tb7 r2))))))))

(declare-fun t2tb258 ((tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 Bool Bool)) (tuple2 Bool Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) (tuple2 Bool
  Bool)) (tuple2 Bool Bool)))) (sort
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool))
  (tuple21 bool bool)) (t2tb258 x))))

(declare-fun tb2t258 (uni) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 Bool Bool)) (tuple2 Bool Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) (tuple2 Bool
  Bool)) (tuple2 Bool Bool))))
  (! (= (tb2t258 (t2tb258 i)) i) :pattern ((t2tb258 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21
     (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool))
     (tuple21 bool bool)) j) (= (t2tb258 (tb2t258 j)) j)) :pattern ((t2tb258
                                                                    (tb2t258
                                                                    j))) )))

(declare-fun t2tb259 ((set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 Bool Bool)) (tuple2 Bool Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 Bool Bool)) (tuple2 Bool Bool))))) (sort
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool))
  (tuple21 bool bool))) (t2tb259 x))))

(declare-fun tb2t259 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) (tuple2 Bool Bool)) (tuple2 Bool Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 Bool Bool)) (tuple2 Bool Bool)))))
  (! (= (tb2t259 (t2tb259 i)) i) :pattern ((t2tb259 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21
     (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool))
     (tuple21 bool bool))) j) (= (t2tb259 (tb2t259 j)) j)) :pattern (
  (t2tb259 (tb2t259 j))) )))

;; parallel_product_def
  (assert
  (forall ((e (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) (tuple2 Bool
  Bool)) (tuple2 Bool Bool))) (r1 (set (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool))) (r2 (set (tuple2 (tuple2 Bool Bool) Bool))))
  (= (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool))
  (tuple21 bool bool)) (t2tb258 e)
  (parallel_product bool (tuple21 bool bool) bool
  (tuple21 (tuple21 bool bool) bool) (t2tb7 r1) (t2tb9 r2)))
  (exists ((x (tuple2 (tuple2 Bool Bool) Bool)) (y (tuple2 Bool Bool))
  (z Bool) (a Bool))
  (and
  (= (tb2t258
     (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool))
     (tuple21 bool bool)
     (Tuple2 (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool)
     (t2tb10 x) (t2tb12 y)) (t2tb12 (Tuple21 z a)))) e)
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb8 (Tuple23 x z)) (t2tb7 r1)) (mem (tuple21 (tuple21 bool bool) bool)
  (t2tb10 (Tuple22 y a)) (t2tb9 r2))))))))

;; parallel_product_def
  (assert
  (forall ((e (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 Bool Bool))) (r1 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))) (r2 (set (tuple2 Bool Bool))))
  (= (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 bool bool)) (t2tb154 e)
  (parallel_product bool bool bool (tuple21 (tuple21 bool bool) bool)
  (t2tb7 r1) (t2tb11 r2)))
  (exists ((x (tuple2 (tuple2 Bool Bool) Bool)) (y Bool) (z Bool) (a Bool))
  (and
  (= (tb2t154
     (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (tuple21 bool bool) (t2tb8 (Tuple23 x y)) (t2tb12 (Tuple21 z a)))) e)
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb8 (Tuple23 x z)) (t2tb7 r1)) (mem (tuple21 bool bool)
  (t2tb12 (Tuple21 y a)) (t2tb11 r2))))))))

;; parallel_product_def
  (assert
  (forall ((w ty))
  (forall ((e uni) (r1 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (r2 uni))
  (=> (sort
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 bool w)) e)
  (and
  (=> (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 bool w)) e
  (parallel_product w bool bool (tuple21 (tuple21 bool bool) bool) (t2tb7 r1)
  r2))
  (exists ((x (tuple2 (tuple2 Bool Bool) Bool)) (y Bool) (z Bool) (a uni))
  (and (sort w a)
  (and
  (= (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (tuple21 bool w) (t2tb8 (Tuple23 x y)) (Tuple2 bool w (t2tb13 z) a)) e)
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb8 (Tuple23 x z)) (t2tb7 r1)) (mem (tuple21 bool w)
  (Tuple2 bool w (t2tb13 y) a) r2))))))
  (=>
  (exists ((x (tuple2 (tuple2 Bool Bool) Bool)) (y Bool) (z Bool) (a uni))
  (and
  (= (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (tuple21 bool w) (t2tb8 (Tuple23 x y)) (Tuple2 bool w (t2tb13 z) a)) e)
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb8 (Tuple23 x z)) (t2tb7 r1)) (mem (tuple21 bool w)
  (Tuple2 bool w (t2tb13 y) a) r2)))) (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 bool w)) e
  (parallel_product w bool bool (tuple21 (tuple21 bool bool) bool) (t2tb7 r1)
  r2))))))))

;; parallel_product_def
  (assert
  (forall ((v ty) (w ty))
  (forall ((e uni) (r1 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (r2 uni))
  (=> (sort
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) v) (tuple21 bool w))
  e)
  (and
  (=> (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) v) (tuple21 bool w)) e
  (parallel_product w v bool (tuple21 (tuple21 bool bool) bool) (t2tb7 r1)
  r2))
  (exists ((x (tuple2 (tuple2 Bool Bool) Bool)) (y uni) (z Bool) (a uni))
  (and (sort v y)
  (and (sort w a)
  (and
  (= (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) v) (tuple21 bool w)
     (Tuple2 (tuple21 (tuple21 bool bool) bool) v (t2tb10 x) y)
     (Tuple2 bool w (t2tb13 z) a)) e)
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb8 (Tuple23 x z)) (t2tb7 r1)) (mem (tuple21 v w) (Tuple2 v w y a) r2)))))))
  (=>
  (exists ((x (tuple2 (tuple2 Bool Bool) Bool)) (y uni) (z Bool) (a uni))
  (and
  (= (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) v) (tuple21 bool w)
     (Tuple2 (tuple21 (tuple21 bool bool) bool) v (t2tb10 x) y)
     (Tuple2 bool w (t2tb13 z) a)) e)
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb8 (Tuple23 x z)) (t2tb7 r1)) (mem (tuple21 v w) (Tuple2 v w y a) r2))))
  (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) v) (tuple21 bool w)) e
  (parallel_product w v bool (tuple21 (tuple21 bool bool) bool) (t2tb7 r1)
  r2))))))))

;; parallel_product_def
  (assert
  (forall ((u ty))
  (forall ((e uni) (r1 uni) (r2 (set (tuple2 Bool Bool))))
  (=> (sort (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 u bool)) e)
  (and
  (=> (mem (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 u bool)) e
  (parallel_product bool bool u (tuple21 bool bool) r1 (t2tb11 r2)))
  (exists ((x (tuple2 Bool Bool)) (y Bool) (z uni) (a Bool))
  (and (sort u z)
  (and
  (= (Tuple2 (tuple21 (tuple21 bool bool) bool) (tuple21 u bool)
     (t2tb10 (Tuple22 x y)) (Tuple2 u bool z (t2tb13 a))) e)
  (and (mem (tuple21 (tuple21 bool bool) u)
  (Tuple2 (tuple21 bool bool) u (t2tb12 x) z) r1) (mem (tuple21 bool bool)
  (t2tb12 (Tuple21 y a)) (t2tb11 r2)))))))
  (=>
  (exists ((x (tuple2 Bool Bool)) (y Bool) (z uni) (a Bool))
  (and
  (= (Tuple2 (tuple21 (tuple21 bool bool) bool) (tuple21 u bool)
     (t2tb10 (Tuple22 x y)) (Tuple2 u bool z (t2tb13 a))) e)
  (and (mem (tuple21 (tuple21 bool bool) u)
  (Tuple2 (tuple21 bool bool) u (t2tb12 x) z) r1) (mem (tuple21 bool bool)
  (t2tb12 (Tuple21 y a)) (t2tb11 r2))))) (mem
  (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 u bool)) e
  (parallel_product bool bool u (tuple21 bool bool) r1 (t2tb11 r2)))))))))

;; parallel_product_def
  (assert
  (forall ((u ty) (w ty))
  (forall ((e uni) (r1 uni) (r2 uni))
  (=> (sort (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 u w)) e)
  (and
  (=> (mem (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 u w)) e
  (parallel_product w bool u (tuple21 bool bool) r1 r2))
  (exists ((x (tuple2 Bool Bool)) (y Bool) (z uni) (a uni))
  (and (sort u z)
  (and (sort w a)
  (and
  (= (Tuple2 (tuple21 (tuple21 bool bool) bool) (tuple21 u w)
     (t2tb10 (Tuple22 x y)) (Tuple2 u w z a)) e)
  (and (mem (tuple21 (tuple21 bool bool) u)
  (Tuple2 (tuple21 bool bool) u (t2tb12 x) z) r1) (mem (tuple21 bool w)
  (Tuple2 bool w (t2tb13 y) a) r2)))))))
  (=>
  (exists ((x (tuple2 Bool Bool)) (y Bool) (z uni) (a uni))
  (and
  (= (Tuple2 (tuple21 (tuple21 bool bool) bool) (tuple21 u w)
     (t2tb10 (Tuple22 x y)) (Tuple2 u w z a)) e)
  (and (mem (tuple21 (tuple21 bool bool) u)
  (Tuple2 (tuple21 bool bool) u (t2tb12 x) z) r1) (mem (tuple21 bool w)
  (Tuple2 bool w (t2tb13 y) a) r2)))) (mem
  (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 u w)) e
  (parallel_product w bool u (tuple21 bool bool) r1 r2))))))))

;; parallel_product_def
  (assert
  (forall ((e (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (r1 (set (tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 Bool Bool) Bool))))
  (r2 (set (tuple2 Bool Bool))))
  (= (mem
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb175 e)
  (parallel_product bool bool (tuple21 (tuple21 bool bool) bool)
  (tuple21 bool bool) (t2tb202 r1) (t2tb11 r2)))
  (exists ((x (tuple2 Bool Bool)) (y Bool) (z (tuple2 (tuple2 Bool Bool)
  Bool)) (a Bool))
  (and
  (= (tb2t175
     (Tuple2 (tuple21 (tuple21 bool bool) bool)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb10 (Tuple22 x y))
     (t2tb8 (Tuple23 z a)))) e)
  (and (mem (tuple21 (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool))
  (Tuple2 (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool) (t2tb12 x)
  (t2tb10 z)) (t2tb202 r1)) (mem (tuple21 bool bool) (t2tb12 (Tuple21 y a))
  (t2tb11 r2))))))))

;; parallel_product_def
  (assert
  (forall ((e (tuple2 (tuple2 (tuple2 Bool Bool) Bool) (tuple2 (tuple2 Bool
  Bool) Bool))) (r1 (set (tuple2 (tuple2 Bool Bool) (tuple2 Bool Bool))))
  (r2 (set (tuple2 Bool Bool))))
  (= (mem
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 bool bool) bool)) (t2tb178 e)
  (parallel_product bool bool (tuple21 bool bool) (tuple21 bool bool)
  (t2tb204 r1) (t2tb11 r2)))
  (exists ((x (tuple2 Bool Bool)) (y Bool) (z (tuple2 Bool Bool)) (a Bool))
  (and
  (= (tb2t178
     (Tuple2 (tuple21 (tuple21 bool bool) bool)
     (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 x y))
     (t2tb10 (Tuple22 z a)))) e)
  (and (mem (tuple21 (tuple21 bool bool) (tuple21 bool bool))
  (Tuple2 (tuple21 bool bool) (tuple21 bool bool) (t2tb12 x) (t2tb12 z))
  (t2tb204 r1)) (mem (tuple21 bool bool) (t2tb12 (Tuple21 y a)) (t2tb11 r2))))))))

;; parallel_product_def
  (assert
  (forall ((v ty))
  (forall ((e uni) (r1 (set (tuple2 (tuple2 Bool Bool) Bool))) (r2 uni))
  (=> (sort (tuple21 (tuple21 (tuple21 bool bool) v) (tuple21 bool bool)) e)
  (and
  (=> (mem (tuple21 (tuple21 (tuple21 bool bool) v) (tuple21 bool bool)) e
  (parallel_product bool v bool (tuple21 bool bool) (t2tb9 r1) r2))
  (exists ((x (tuple2 Bool Bool)) (y uni) (z Bool) (a Bool))
  (and (sort v y)
  (and
  (= (Tuple2 (tuple21 (tuple21 bool bool) v) (tuple21 bool bool)
     (Tuple2 (tuple21 bool bool) v (t2tb12 x) y) (t2tb12 (Tuple21 z a))) e)
  (and (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 x z))
  (t2tb9 r1)) (mem (tuple21 v bool) (Tuple2 v bool y (t2tb13 a)) r2))))))
  (=>
  (exists ((x (tuple2 Bool Bool)) (y uni) (z Bool) (a Bool))
  (and
  (= (Tuple2 (tuple21 (tuple21 bool bool) v) (tuple21 bool bool)
     (Tuple2 (tuple21 bool bool) v (t2tb12 x) y) (t2tb12 (Tuple21 z a))) e)
  (and (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 x z))
  (t2tb9 r1)) (mem (tuple21 v bool) (Tuple2 v bool y (t2tb13 a)) r2)))) (mem
  (tuple21 (tuple21 (tuple21 bool bool) v) (tuple21 bool bool)) e
  (parallel_product bool v bool (tuple21 bool bool) (t2tb9 r1) r2))))))))

(declare-fun t2tb260 ((set (tuple2 (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 Bool Bool) Bool)) (tuple2 Bool Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 Bool
  Bool) Bool)) (tuple2 Bool Bool))))) (sort
  (set1
  (tuple21 (tuple21 (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool))
  (tuple21 bool bool))) (t2tb260 x))))

(declare-fun tb2t260 (uni) (set (tuple2 (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 Bool Bool) Bool)) (tuple2 Bool Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 Bool
  Bool) Bool)) (tuple2 Bool Bool)))))
  (! (= (tb2t260 (t2tb260 i)) i) :pattern ((t2tb260 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21
     (tuple21 (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool))
     (tuple21 bool bool))) j) (= (t2tb260 (tb2t260 j)) j)) :pattern (
  (t2tb260 (tb2t260 j))) )))

(declare-fun t2tb261 ((tuple2 (tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 Bool
  Bool) Bool)) (tuple2 Bool Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 Bool Bool)
  Bool)) (tuple2 Bool Bool)))) (sort
  (tuple21 (tuple21 (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool))
  (tuple21 bool bool)) (t2tb261 x))))

(declare-fun tb2t261 (uni) (tuple2 (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 Bool Bool) Bool)) (tuple2 Bool Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 Bool Bool)
  Bool)) (tuple2 Bool Bool))))
  (! (= (tb2t261 (t2tb261 i)) i) :pattern ((t2tb261 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21
     (tuple21 (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool))
     (tuple21 bool bool)) j) (= (t2tb261 (tb2t261 j)) j)) :pattern ((t2tb261
                                                                    (tb2t261
                                                                    j))) )))

;; parallel_product_def
  (assert
  (forall ((e (tuple2 (tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 Bool Bool)
  Bool)) (tuple2 Bool Bool))) (r1 (set (tuple2 (tuple2 Bool Bool) Bool)))
  (r2 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (= (mem
  (tuple21 (tuple21 (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool))
  (tuple21 bool bool)) (t2tb261 e)
  (parallel_product bool (tuple21 (tuple21 bool bool) bool) bool
  (tuple21 bool bool) (t2tb9 r1) (t2tb7 r2)))
  (exists ((x (tuple2 Bool Bool)) (y (tuple2 (tuple2 Bool Bool) Bool))
  (z Bool) (a Bool))
  (and
  (= (tb2t261
     (Tuple2 (tuple21 (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool))
     (tuple21 bool bool)
     (Tuple2 (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool)
     (t2tb12 x) (t2tb10 y)) (t2tb12 (Tuple21 z a)))) e)
  (and (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 x z))
  (t2tb9 r1)) (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb8 (Tuple23 y a)) (t2tb7 r2))))))))

(declare-fun t2tb262 ((set (tuple2 (tuple2 (tuple2 Bool Bool) (tuple2 Bool
  Bool)) (tuple2 Bool Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 Bool Bool) (tuple2 Bool Bool))
  (tuple2 Bool Bool))))) (sort
  (set1
  (tuple21 (tuple21 (tuple21 bool bool) (tuple21 bool bool))
  (tuple21 bool bool))) (t2tb262 x))))

(declare-fun tb2t262 (uni) (set (tuple2 (tuple2 (tuple2 Bool Bool)
  (tuple2 Bool Bool)) (tuple2 Bool Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 Bool Bool) (tuple2 Bool Bool))
  (tuple2 Bool Bool)))))
  (! (= (tb2t262 (t2tb262 i)) i) :pattern ((t2tb262 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21 (tuple21 (tuple21 bool bool) (tuple21 bool bool))
     (tuple21 bool bool))) j) (= (t2tb262 (tb2t262 j)) j)) :pattern (
  (t2tb262 (tb2t262 j))) )))

(declare-fun t2tb263 ((tuple2 (tuple2 (tuple2 Bool Bool) (tuple2 Bool Bool))
  (tuple2 Bool Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) (tuple2 Bool Bool))
  (tuple2 Bool Bool)))) (sort
  (tuple21 (tuple21 (tuple21 bool bool) (tuple21 bool bool))
  (tuple21 bool bool)) (t2tb263 x))))

(declare-fun tb2t263 (uni) (tuple2 (tuple2 (tuple2 Bool Bool) (tuple2 Bool
  Bool)) (tuple2 Bool Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 Bool Bool) (tuple2 Bool Bool))
  (tuple2 Bool Bool))))
  (! (= (tb2t263 (t2tb263 i)) i) :pattern ((t2tb263 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 (tuple21 (tuple21 bool bool) (tuple21 bool bool))
     (tuple21 bool bool)) j) (= (t2tb263 (tb2t263 j)) j)) :pattern ((t2tb263
                                                                    (tb2t263
                                                                    j))) )))

;; parallel_product_def
  (assert
  (forall ((e (tuple2 (tuple2 (tuple2 Bool Bool) (tuple2 Bool Bool))
  (tuple2 Bool Bool))) (r1 (set (tuple2 (tuple2 Bool Bool) Bool)))
  (r2 (set (tuple2 (tuple2 Bool Bool) Bool))))
  (= (mem
  (tuple21 (tuple21 (tuple21 bool bool) (tuple21 bool bool))
  (tuple21 bool bool)) (t2tb263 e)
  (parallel_product bool (tuple21 bool bool) bool (tuple21 bool bool)
  (t2tb9 r1) (t2tb9 r2)))
  (exists ((x (tuple2 Bool Bool)) (y (tuple2 Bool Bool)) (z Bool) (a Bool))
  (and
  (= (tb2t263
     (Tuple2 (tuple21 (tuple21 bool bool) (tuple21 bool bool))
     (tuple21 bool bool)
     (Tuple2 (tuple21 bool bool) (tuple21 bool bool) (t2tb12 x) (t2tb12 y))
     (t2tb12 (Tuple21 z a)))) e)
  (and (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 x z))
  (t2tb9 r1)) (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 y a))
  (t2tb9 r2))))))))

;; parallel_product_def
  (assert
  (forall ((e (tuple2 (tuple2 (tuple2 Bool Bool) Bool) (tuple2 Bool Bool)))
  (r1 (set (tuple2 (tuple2 Bool Bool) Bool))) (r2 (set (tuple2 Bool Bool))))
  (= (mem (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool))
  (t2tb181 e)
  (parallel_product bool bool bool (tuple21 bool bool) (t2tb9 r1)
  (t2tb11 r2)))
  (exists ((x (tuple2 Bool Bool)) (y Bool) (z Bool) (a Bool))
  (and
  (= (tb2t181
     (Tuple2 (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool)
     (t2tb10 (Tuple22 x y)) (t2tb12 (Tuple21 z a)))) e)
  (and (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 x z))
  (t2tb9 r1)) (mem (tuple21 bool bool) (t2tb12 (Tuple21 y a)) (t2tb11 r2))))))))

;; parallel_product_def
  (assert
  (forall ((w ty))
  (forall ((e uni) (r1 (set (tuple2 (tuple2 Bool Bool) Bool))) (r2 uni))
  (=> (sort (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 bool w)) e)
  (and
  (=> (mem (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 bool w)) e
  (parallel_product w bool bool (tuple21 bool bool) (t2tb9 r1) r2))
  (exists ((x (tuple2 Bool Bool)) (y Bool) (z Bool) (a uni))
  (and (sort w a)
  (and
  (= (Tuple2 (tuple21 (tuple21 bool bool) bool) (tuple21 bool w)
     (t2tb10 (Tuple22 x y)) (Tuple2 bool w (t2tb13 z) a)) e)
  (and (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 x z))
  (t2tb9 r1)) (mem (tuple21 bool w) (Tuple2 bool w (t2tb13 y) a) r2))))))
  (=>
  (exists ((x (tuple2 Bool Bool)) (y Bool) (z Bool) (a uni))
  (and
  (= (Tuple2 (tuple21 (tuple21 bool bool) bool) (tuple21 bool w)
     (t2tb10 (Tuple22 x y)) (Tuple2 bool w (t2tb13 z) a)) e)
  (and (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 x z))
  (t2tb9 r1)) (mem (tuple21 bool w) (Tuple2 bool w (t2tb13 y) a) r2)))) (mem
  (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 bool w)) e
  (parallel_product w bool bool (tuple21 bool bool) (t2tb9 r1) r2))))))))

;; parallel_product_def
  (assert
  (forall ((v ty) (w ty))
  (forall ((e uni) (r1 (set (tuple2 (tuple2 Bool Bool) Bool))) (r2 uni))
  (=> (sort (tuple21 (tuple21 (tuple21 bool bool) v) (tuple21 bool w)) e)
  (and
  (=> (mem (tuple21 (tuple21 (tuple21 bool bool) v) (tuple21 bool w)) e
  (parallel_product w v bool (tuple21 bool bool) (t2tb9 r1) r2))
  (exists ((x (tuple2 Bool Bool)) (y uni) (z Bool) (a uni))
  (and (sort v y)
  (and (sort w a)
  (and
  (= (Tuple2 (tuple21 (tuple21 bool bool) v) (tuple21 bool w)
     (Tuple2 (tuple21 bool bool) v (t2tb12 x) y)
     (Tuple2 bool w (t2tb13 z) a)) e)
  (and (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 x z))
  (t2tb9 r1)) (mem (tuple21 v w) (Tuple2 v w y a) r2)))))))
  (=>
  (exists ((x (tuple2 Bool Bool)) (y uni) (z Bool) (a uni))
  (and
  (= (Tuple2 (tuple21 (tuple21 bool bool) v) (tuple21 bool w)
     (Tuple2 (tuple21 bool bool) v (t2tb12 x) y)
     (Tuple2 bool w (t2tb13 z) a)) e)
  (and (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 x z))
  (t2tb9 r1)) (mem (tuple21 v w) (Tuple2 v w y a) r2)))) (mem
  (tuple21 (tuple21 (tuple21 bool bool) v) (tuple21 bool w)) e
  (parallel_product w v bool (tuple21 bool bool) (t2tb9 r1) r2))))))))

;; parallel_product_def
  (assert
  (forall ((u ty))
  (forall ((e uni) (r1 uni) (r2 (set (tuple2 Bool Bool))))
  (=> (sort (tuple21 (tuple21 bool bool) (tuple21 u bool)) e)
  (and
  (=> (mem (tuple21 (tuple21 bool bool) (tuple21 u bool)) e
  (parallel_product bool bool u bool r1 (t2tb11 r2)))
  (exists ((x Bool) (y Bool) (z uni) (a Bool))
  (and (sort u z)
  (and
  (= (Tuple2 (tuple21 bool bool) (tuple21 u bool) (t2tb12 (Tuple21 x y))
     (Tuple2 u bool z (t2tb13 a))) e)
  (and (mem (tuple21 bool u) (Tuple2 bool u (t2tb13 x) z) r1) (mem
  (tuple21 bool bool) (t2tb12 (Tuple21 y a)) (t2tb11 r2)))))))
  (=>
  (exists ((x Bool) (y Bool) (z uni) (a Bool))
  (and
  (= (Tuple2 (tuple21 bool bool) (tuple21 u bool) (t2tb12 (Tuple21 x y))
     (Tuple2 u bool z (t2tb13 a))) e)
  (and (mem (tuple21 bool u) (Tuple2 bool u (t2tb13 x) z) r1) (mem
  (tuple21 bool bool) (t2tb12 (Tuple21 y a)) (t2tb11 r2))))) (mem
  (tuple21 (tuple21 bool bool) (tuple21 u bool)) e
  (parallel_product bool bool u bool r1 (t2tb11 r2)))))))))

;; parallel_product_def
  (assert
  (forall ((u ty) (w ty))
  (forall ((e uni) (r1 uni) (r2 uni))
  (=> (sort (tuple21 (tuple21 bool bool) (tuple21 u w)) e)
  (and
  (=> (mem (tuple21 (tuple21 bool bool) (tuple21 u w)) e
  (parallel_product w bool u bool r1 r2))
  (exists ((x Bool) (y Bool) (z uni) (a uni))
  (and (sort u z)
  (and (sort w a)
  (and
  (= (Tuple2 (tuple21 bool bool) (tuple21 u w) (t2tb12 (Tuple21 x y))
     (Tuple2 u w z a)) e)
  (and (mem (tuple21 bool u) (Tuple2 bool u (t2tb13 x) z) r1) (mem
  (tuple21 bool w) (Tuple2 bool w (t2tb13 y) a) r2)))))))
  (=>
  (exists ((x Bool) (y Bool) (z uni) (a uni))
  (and
  (= (Tuple2 (tuple21 bool bool) (tuple21 u w) (t2tb12 (Tuple21 x y))
     (Tuple2 u w z a)) e)
  (and (mem (tuple21 bool u) (Tuple2 bool u (t2tb13 x) z) r1) (mem
  (tuple21 bool w) (Tuple2 bool w (t2tb13 y) a) r2)))) (mem
  (tuple21 (tuple21 bool bool) (tuple21 u w)) e
  (parallel_product w bool u bool r1 r2))))))))

;; parallel_product_def
  (assert
  (forall ((e (tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool))) (r1 (set (tuple2 Bool (tuple2 (tuple2 Bool Bool) Bool))))
  (r2 (set (tuple2 Bool Bool))))
  (= (mem
  (tuple21 (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb199 e)
  (parallel_product bool bool (tuple21 (tuple21 bool bool) bool) bool
  (t2tb25 r1) (t2tb11 r2)))
  (exists ((x Bool) (y Bool) (z (tuple2 (tuple2 Bool Bool) Bool)) (a Bool))
  (and
  (= (tb2t199
     (Tuple2 (tuple21 bool bool)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb12 (Tuple21 x y))
     (t2tb8 (Tuple23 z a)))) e)
  (and (mem (tuple21 bool (tuple21 (tuple21 bool bool) bool))
  (Tuple2 bool (tuple21 (tuple21 bool bool) bool) (t2tb13 x) (t2tb10 z))
  (t2tb25 r1)) (mem (tuple21 bool bool) (t2tb12 (Tuple21 y a)) (t2tb11 r2))))))))

;; parallel_product_def
  (assert
  (forall ((e (tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 Bool Bool) Bool)))
  (r1 (set (tuple2 Bool (tuple2 Bool Bool)))) (r2 (set (tuple2 Bool Bool))))
  (= (mem (tuple21 (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool))
  (t2tb200 e)
  (parallel_product bool bool (tuple21 bool bool) bool (t2tb27 r1)
  (t2tb11 r2)))
  (exists ((x Bool) (y Bool) (z (tuple2 Bool Bool)) (a Bool))
  (and
  (= (tb2t200
     (Tuple2 (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool)
     (t2tb12 (Tuple21 x y)) (t2tb10 (Tuple22 z a)))) e)
  (and (mem (tuple21 bool (tuple21 bool bool))
  (Tuple2 bool (tuple21 bool bool) (t2tb13 x) (t2tb12 z)) (t2tb27 r1)) (mem
  (tuple21 bool bool) (t2tb12 (Tuple21 y a)) (t2tb11 r2))))))))

;; parallel_product_def
  (assert
  (forall ((v ty))
  (forall ((e uni) (r1 (set (tuple2 Bool Bool))) (r2 uni))
  (=> (sort (tuple21 (tuple21 bool v) (tuple21 bool bool)) e)
  (and
  (=> (mem (tuple21 (tuple21 bool v) (tuple21 bool bool)) e
  (parallel_product bool v bool bool (t2tb11 r1) r2))
  (exists ((x Bool) (y uni) (z Bool) (a Bool))
  (and (sort v y)
  (and
  (= (Tuple2 (tuple21 bool v) (tuple21 bool bool)
     (Tuple2 bool v (t2tb13 x) y) (t2tb12 (Tuple21 z a))) e)
  (and (mem (tuple21 bool bool) (t2tb12 (Tuple21 x z)) (t2tb11 r1)) (mem
  (tuple21 v bool) (Tuple2 v bool y (t2tb13 a)) r2))))))
  (=>
  (exists ((x Bool) (y uni) (z Bool) (a Bool))
  (and
  (= (Tuple2 (tuple21 bool v) (tuple21 bool bool)
     (Tuple2 bool v (t2tb13 x) y) (t2tb12 (Tuple21 z a))) e)
  (and (mem (tuple21 bool bool) (t2tb12 (Tuple21 x z)) (t2tb11 r1)) (mem
  (tuple21 v bool) (Tuple2 v bool y (t2tb13 a)) r2)))) (mem
  (tuple21 (tuple21 bool v) (tuple21 bool bool)) e
  (parallel_product bool v bool bool (t2tb11 r1) r2))))))))

(declare-fun t2tb264 ((set (tuple2 (tuple2 Bool (tuple2 (tuple2 Bool Bool)
  Bool)) (tuple2 Bool Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Bool (tuple2 (tuple2 Bool Bool) Bool))
  (tuple2 Bool Bool))))) (sort
  (set1
  (tuple21 (tuple21 bool (tuple21 (tuple21 bool bool) bool))
  (tuple21 bool bool))) (t2tb264 x))))

(declare-fun tb2t264 (uni) (set (tuple2 (tuple2 Bool (tuple2 (tuple2 Bool
  Bool) Bool)) (tuple2 Bool Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Bool (tuple2 (tuple2 Bool Bool) Bool))
  (tuple2 Bool Bool)))))
  (! (= (tb2t264 (t2tb264 i)) i) :pattern ((t2tb264 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21 (tuple21 bool (tuple21 (tuple21 bool bool) bool))
     (tuple21 bool bool))) j) (= (t2tb264 (tb2t264 j)) j)) :pattern (
  (t2tb264 (tb2t264 j))) )))

(declare-fun t2tb265 ((tuple2 (tuple2 Bool (tuple2 (tuple2 Bool Bool) Bool))
  (tuple2 Bool Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 Bool (tuple2 (tuple2 Bool Bool) Bool))
  (tuple2 Bool Bool)))) (sort
  (tuple21 (tuple21 bool (tuple21 (tuple21 bool bool) bool))
  (tuple21 bool bool)) (t2tb265 x))))

(declare-fun tb2t265 (uni) (tuple2 (tuple2 Bool (tuple2 (tuple2 Bool Bool)
  Bool)) (tuple2 Bool Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 Bool (tuple2 (tuple2 Bool Bool) Bool))
  (tuple2 Bool Bool))))
  (! (= (tb2t265 (t2tb265 i)) i) :pattern ((t2tb265 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 (tuple21 bool (tuple21 (tuple21 bool bool) bool))
     (tuple21 bool bool)) j) (= (t2tb265 (tb2t265 j)) j)) :pattern ((t2tb265
                                                                    (tb2t265
                                                                    j))) )))

;; parallel_product_def
  (assert
  (forall ((e (tuple2 (tuple2 Bool (tuple2 (tuple2 Bool Bool) Bool))
  (tuple2 Bool Bool))) (r1 (set (tuple2 Bool Bool)))
  (r2 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (= (mem
  (tuple21 (tuple21 bool (tuple21 (tuple21 bool bool) bool))
  (tuple21 bool bool)) (t2tb265 e)
  (parallel_product bool (tuple21 (tuple21 bool bool) bool) bool bool
  (t2tb11 r1) (t2tb7 r2)))
  (exists ((x Bool) (y (tuple2 (tuple2 Bool Bool) Bool)) (z Bool) (a Bool))
  (and
  (= (tb2t265
     (Tuple2 (tuple21 bool (tuple21 (tuple21 bool bool) bool))
     (tuple21 bool bool)
     (Tuple2 bool (tuple21 (tuple21 bool bool) bool) (t2tb13 x) (t2tb10 y))
     (t2tb12 (Tuple21 z a)))) e)
  (and (mem (tuple21 bool bool) (t2tb12 (Tuple21 x z)) (t2tb11 r1)) (mem
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 (Tuple23 y a))
  (t2tb7 r2))))))))

(declare-fun t2tb266 ((set (tuple2 (tuple2 Bool (tuple2 Bool Bool))
  (tuple2 Bool Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Bool (tuple2 Bool Bool)) (tuple2 Bool
  Bool))))) (sort
  (set1 (tuple21 (tuple21 bool (tuple21 bool bool)) (tuple21 bool bool)))
  (t2tb266 x))))

(declare-fun tb2t266 (uni) (set (tuple2 (tuple2 Bool (tuple2 Bool Bool))
  (tuple2 Bool Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Bool (tuple2 Bool Bool)) (tuple2 Bool
  Bool))))) (! (= (tb2t266 (t2tb266 i)) i) :pattern ((t2tb266 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1 (tuple21 (tuple21 bool (tuple21 bool bool)) (tuple21 bool bool)))
     j) (= (t2tb266 (tb2t266 j)) j)) :pattern ((t2tb266 (tb2t266 j))) )))

(declare-fun t2tb267 ((tuple2 (tuple2 Bool (tuple2 Bool Bool)) (tuple2 Bool
  Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 Bool (tuple2 Bool Bool)) (tuple2 Bool Bool))))
  (sort (tuple21 (tuple21 bool (tuple21 bool bool)) (tuple21 bool bool))
  (t2tb267 x))))

(declare-fun tb2t267 (uni) (tuple2 (tuple2 Bool (tuple2 Bool Bool))
  (tuple2 Bool Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 Bool (tuple2 Bool Bool)) (tuple2 Bool Bool))))
  (! (= (tb2t267 (t2tb267 i)) i) :pattern ((t2tb267 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 (tuple21 bool (tuple21 bool bool)) (tuple21 bool bool)) j)
     (= (t2tb267 (tb2t267 j)) j)) :pattern ((t2tb267 (tb2t267 j))) )))

;; parallel_product_def
  (assert
  (forall ((e (tuple2 (tuple2 Bool (tuple2 Bool Bool)) (tuple2 Bool Bool)))
  (r1 (set (tuple2 Bool Bool))) (r2 (set (tuple2 (tuple2 Bool Bool) Bool))))
  (= (mem (tuple21 (tuple21 bool (tuple21 bool bool)) (tuple21 bool bool))
  (t2tb267 e)
  (parallel_product bool (tuple21 bool bool) bool bool (t2tb11 r1)
  (t2tb9 r2)))
  (exists ((x Bool) (y (tuple2 Bool Bool)) (z Bool) (a Bool))
  (and
  (= (tb2t267
     (Tuple2 (tuple21 bool (tuple21 bool bool)) (tuple21 bool bool)
     (Tuple2 bool (tuple21 bool bool) (t2tb13 x) (t2tb12 y))
     (t2tb12 (Tuple21 z a)))) e)
  (and (mem (tuple21 bool bool) (t2tb12 (Tuple21 x z)) (t2tb11 r1)) (mem
  (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 y a)) (t2tb9 r2))))))))

;; parallel_product_def
  (assert
  (forall ((e (tuple2 (tuple2 Bool Bool) (tuple2 Bool Bool)))
  (r1 (set (tuple2 Bool Bool))) (r2 (set (tuple2 Bool Bool))))
  (= (mem (tuple21 (tuple21 bool bool) (tuple21 bool bool)) (t2tb205 e)
  (parallel_product bool bool bool bool (t2tb11 r1) (t2tb11 r2)))
  (exists ((x Bool) (y Bool) (z Bool) (a Bool))
  (and
  (= (tb2t205
     (Tuple2 (tuple21 bool bool) (tuple21 bool bool) (t2tb12 (Tuple21 x y))
     (t2tb12 (Tuple21 z a)))) e)
  (and (mem (tuple21 bool bool) (t2tb12 (Tuple21 x z)) (t2tb11 r1)) (mem
  (tuple21 bool bool) (t2tb12 (Tuple21 y a)) (t2tb11 r2))))))))

;; parallel_product_def
  (assert
  (forall ((w ty))
  (forall ((e uni) (r1 (set (tuple2 Bool Bool))) (r2 uni))
  (=> (sort (tuple21 (tuple21 bool bool) (tuple21 bool w)) e)
  (and
  (=> (mem (tuple21 (tuple21 bool bool) (tuple21 bool w)) e
  (parallel_product w bool bool bool (t2tb11 r1) r2))
  (exists ((x Bool) (y Bool) (z Bool) (a uni))
  (and (sort w a)
  (and
  (= (Tuple2 (tuple21 bool bool) (tuple21 bool w) (t2tb12 (Tuple21 x y))
     (Tuple2 bool w (t2tb13 z) a)) e)
  (and (mem (tuple21 bool bool) (t2tb12 (Tuple21 x z)) (t2tb11 r1)) (mem
  (tuple21 bool w) (Tuple2 bool w (t2tb13 y) a) r2))))))
  (=>
  (exists ((x Bool) (y Bool) (z Bool) (a uni))
  (and
  (= (Tuple2 (tuple21 bool bool) (tuple21 bool w) (t2tb12 (Tuple21 x y))
     (Tuple2 bool w (t2tb13 z) a)) e)
  (and (mem (tuple21 bool bool) (t2tb12 (Tuple21 x z)) (t2tb11 r1)) (mem
  (tuple21 bool w) (Tuple2 bool w (t2tb13 y) a) r2)))) (mem
  (tuple21 (tuple21 bool bool) (tuple21 bool w)) e
  (parallel_product w bool bool bool (t2tb11 r1) r2))))))))

;; parallel_product_def
  (assert
  (forall ((v ty) (w ty))
  (forall ((e uni) (r1 (set (tuple2 Bool Bool))) (r2 uni))
  (=> (sort (tuple21 (tuple21 bool v) (tuple21 bool w)) e)
  (and
  (=> (mem (tuple21 (tuple21 bool v) (tuple21 bool w)) e
  (parallel_product w v bool bool (t2tb11 r1) r2))
  (exists ((x Bool) (y uni) (z Bool) (a uni))
  (and (sort v y)
  (and (sort w a)
  (and
  (= (Tuple2 (tuple21 bool v) (tuple21 bool w) (Tuple2 bool v (t2tb13 x) y)
     (Tuple2 bool w (t2tb13 z) a)) e)
  (and (mem (tuple21 bool bool) (t2tb12 (Tuple21 x z)) (t2tb11 r1)) (mem
  (tuple21 v w) (Tuple2 v w y a) r2)))))))
  (=>
  (exists ((x Bool) (y uni) (z Bool) (a uni))
  (and
  (= (Tuple2 (tuple21 bool v) (tuple21 bool w) (Tuple2 bool v (t2tb13 x) y)
     (Tuple2 bool w (t2tb13 z) a)) e)
  (and (mem (tuple21 bool bool) (t2tb12 (Tuple21 x z)) (t2tb11 r1)) (mem
  (tuple21 v w) (Tuple2 v w y a) r2)))) (mem
  (tuple21 (tuple21 bool v) (tuple21 bool w)) e
  (parallel_product w v bool bool (t2tb11 r1) r2))))))))

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
  (forall ((a ty))
  (forall ((x uni) (f uni) (g (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type)))) (s uni)
  (t (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (u (set (set uninterpreted_type))))
  (=>
  (and (mem
  (set1 (tuple21 a (tuple21 (tuple21 (tuple21 bool bool) bool) bool))) f
  (infix_plmngt (tuple21 (tuple21 (tuple21 bool bool) bool) bool) a s
  (t2tb7 t)))
  (and (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))) (t2tb g)
  (infix_plmngt (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb7 t) (t2tb2 u)))
  (and (mem a x (dom (tuple21 (tuple21 (tuple21 bool bool) bool) bool) a f))
  (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (apply (tuple21 (tuple21 (tuple21 bool bool) bool) bool) a f x)
  (dom (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb g))))))
  (= (tb2t3
     (apply (set1 uninterpreted_type1) a
     (semicolon (set1 uninterpreted_type1)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) a f (t2tb g)) x)) 
  (apply5 g
  (tb2t8 (apply (tuple21 (tuple21 (tuple21 bool bool) bool) bool) a f x))))))))

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
  (t2tb7 t)))
  (and (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb5 g)
  (infix_plmngt (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb7 t) (t2tb24 u)))
  (and (mem a x (dom (tuple21 (tuple21 (tuple21 bool bool) bool) bool) a f))
  (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (apply (tuple21 (tuple21 (tuple21 bool bool) bool) bool) a f x)
  (dom (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 g))))))
  (= (tb2t15
     (apply (set1 int) a
     (semicolon (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     a f (t2tb5 g)) x)) (apply4 g
                        (tb2t8
                        (apply
                        (tuple21 (tuple21 (tuple21 bool bool) bool) bool) a f
                        x))))))))

;; apply_compose
  (assert
  (forall ((a ty))
  (forall ((x uni) (f uni) (g (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))) (s uni) (t (set (tuple2 (tuple2 Bool Bool) Bool))) (u (set Bool)))
  (=>
  (and (mem (set1 (tuple21 a (tuple21 (tuple21 bool bool) bool))) f
  (infix_plmngt (tuple21 (tuple21 bool bool) bool) a s (t2tb9 t)))
  (and (mem (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (t2tb7 g)
  (infix_plmngt bool (tuple21 (tuple21 bool bool) bool) (t2tb9 t) (t2tb14 u)))
  (and (mem a x (dom (tuple21 (tuple21 bool bool) bool) a f)) (mem
  (tuple21 (tuple21 bool bool) bool)
  (apply (tuple21 (tuple21 bool bool) bool) a f x)
  (dom bool (tuple21 (tuple21 bool bool) bool) (t2tb7 g))))))
  (= (tb2t13
     (apply bool a
     (semicolon bool (tuple21 (tuple21 bool bool) bool) a f (t2tb7 g)) x)) 
  (apply1 g (tb2t10 (apply (tuple21 (tuple21 bool bool) bool) a f x))))))))

;; apply_compose
  (assert
  (forall ((a ty))
  (forall ((x uni) (f uni) (g (set (tuple2 (tuple2 Bool Bool) Bool))) (s uni)
  (t (set (tuple2 Bool Bool))) (u (set Bool)))
  (=>
  (and (mem (set1 (tuple21 a (tuple21 bool bool))) f
  (infix_plmngt (tuple21 bool bool) a s (t2tb11 t)))
  (and (mem (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb9 g)
  (infix_plmngt bool (tuple21 bool bool) (t2tb11 t) (t2tb14 u)))
  (and (mem a x (dom (tuple21 bool bool) a f)) (mem (tuple21 bool bool)
  (apply (tuple21 bool bool) a f x)
  (dom bool (tuple21 bool bool) (t2tb9 g))))))
  (= (tb2t13
     (apply bool a (semicolon bool (tuple21 bool bool) a f (t2tb9 g)) x)) 
  (apply2 g (tb2t12 (apply (tuple21 bool bool) a f x))))))))

;; apply_compose
  (assert
  (forall ((a ty))
  (forall ((x uni) (f uni) (g (set (tuple2 Bool Bool))) (s uni)
  (t (set Bool)) (u (set Bool)))
  (=>
  (and (mem (set1 (tuple21 a bool)) f (infix_plmngt bool a s (t2tb14 t)))
  (and (mem (set1 (tuple21 bool bool)) (t2tb11 g)
  (infix_plmngt bool bool (t2tb14 t) (t2tb14 u)))
  (and (mem a x (dom bool a f)) (mem bool (apply bool a f x)
  (dom bool bool (t2tb11 g))))))
  (= (tb2t13 (apply bool a (semicolon bool bool a f (t2tb11 g)) x)) (apply3 g
                                                                    (tb2t13
                                                                    (apply
                                                                    bool a f
                                                                    x))))))))

;; apply_compose
  (assert
  (forall ((b ty))
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)) (f uni) (g uni)
  (s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))) (t uni)
  (u (set (set uninterpreted_type))))
  (=>
  (and (mem
  (set1 (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) b)) f
  (infix_plmngt b (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb7 s)
  t))
  (and (mem (set1 (tuple21 b (set1 uninterpreted_type1))) g
  (infix_plmngt (set1 uninterpreted_type1) b t (t2tb2 u)))
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 x)
  (dom b (tuple21 (tuple21 (tuple21 bool bool) bool) bool) f)) (mem b
  (apply b (tuple21 (tuple21 (tuple21 bool bool) bool) bool) f (t2tb8 x))
  (dom (set1 uninterpreted_type1) b g)))))
  (= (apply5
     (tb2t
     (semicolon (set1 uninterpreted_type1) b
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) f g)) x) (tb2t3
                                                                (apply
                                                                (set1
                                                                uninterpreted_type1)
                                                                b g
                                                                (apply b
                                                                (tuple21
                                                                (tuple21
                                                                (tuple21 
                                                                bool 
                                                                bool) 
                                                                bool) 
                                                                bool) f
                                                                (t2tb8 x)))))))))

;; apply_compose
  (assert
  (forall ((b ty))
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)) (f uni) (g uni)
  (s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))) (t uni)
  (u (set (set Int))))
  (=>
  (and (mem
  (set1 (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) b)) f
  (infix_plmngt b (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb7 s)
  t))
  (and (mem (set1 (tuple21 b (set1 int))) g
  (infix_plmngt (set1 int) b t (t2tb24 u)))
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 x)
  (dom b (tuple21 (tuple21 (tuple21 bool bool) bool) bool) f)) (mem b
  (apply b (tuple21 (tuple21 (tuple21 bool bool) bool) bool) f (t2tb8 x))
  (dom (set1 int) b g)))))
  (= (apply4
     (tb2t5
     (semicolon (set1 int) b
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) f g)) x) (tb2t15
                                                                (apply
                                                                (set1 int) b
                                                                g
                                                                (apply b
                                                                (tuple21
                                                                (tuple21
                                                                (tuple21 
                                                                bool 
                                                                bool) 
                                                                bool) 
                                                                bool) f
                                                                (t2tb8 x)))))))))

;; apply_compose
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))) (g (set (tuple2 (set uninterpreted_type)
  (set uninterpreted_type)))) (s (set (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool))) (t (set (set uninterpreted_type)))
  (u (set (set uninterpreted_type))))
  (=>
  (and (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))) (t2tb f)
  (infix_plmngt (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb7 s) (t2tb2 t)))
  (and (mem
  (set1 (tuple21 (set1 uninterpreted_type1) (set1 uninterpreted_type1)))
  (t2tb60 g)
  (infix_plmngt (set1 uninterpreted_type1) (set1 uninterpreted_type1)
  (t2tb2 t) (t2tb2 u)))
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 x)
  (dom (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb f))) (mem
  (set1 uninterpreted_type1) (t2tb3 (apply5 f x))
  (dom (set1 uninterpreted_type1) (set1 uninterpreted_type1) (t2tb60 g))))))
  (= (apply5
     (tb2t
     (semicolon (set1 uninterpreted_type1) (set1 uninterpreted_type1)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb f) (t2tb60 g)))
     x) (tb2t3
        (apply (set1 uninterpreted_type1) (set1 uninterpreted_type1)
        (t2tb60 g) (t2tb3 (apply5 f x))))))))

(declare-fun t2tb268 ((set (set (tuple2 (set uninterpreted_type)
  (set Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (set uninterpreted_type) (set Int)))))) (sort
  (set1 (set1 (tuple21 (set1 uninterpreted_type1) (set1 int)))) (t2tb268 x))))

(declare-fun tb2t268 (uni) (set (set (tuple2 (set uninterpreted_type)
  (set Int)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (set uninterpreted_type) (set Int))))))
  (! (= (tb2t268 (t2tb268 i)) i) :pattern ((t2tb268 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb268 (tb2t268 j)) j) :pattern ((t2tb268 (tb2t268 j))) )))

(declare-fun t2tb269 ((set (tuple2 (set uninterpreted_type) (set Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (set uninterpreted_type) (set Int))))) (sort
  (set1 (tuple21 (set1 uninterpreted_type1) (set1 int))) (t2tb269 x))))

(declare-fun tb2t269 (uni) (set (tuple2 (set uninterpreted_type) (set Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (set uninterpreted_type) (set Int)))))
  (! (= (tb2t269 (t2tb269 i)) i) :pattern ((t2tb269 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb269 (tb2t269 j)) j) :pattern ((t2tb269 (tb2t269 j))) )))

;; apply_compose
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))) (g (set (tuple2 (set uninterpreted_type)
  (set Int)))) (s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (t (set (set uninterpreted_type))) (u (set (set Int))))
  (=>
  (and (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))) (t2tb f)
  (infix_plmngt (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb7 s) (t2tb2 t)))
  (and (mem (set1 (tuple21 (set1 uninterpreted_type1) (set1 int)))
  (t2tb269 g)
  (infix_plmngt (set1 int) (set1 uninterpreted_type1) (t2tb2 t) (t2tb24 u)))
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 x)
  (dom (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb f))) (mem
  (set1 uninterpreted_type1) (t2tb3 (apply5 f x))
  (dom (set1 int) (set1 uninterpreted_type1) (t2tb269 g))))))
  (= (apply4
     (tb2t5
     (semicolon (set1 int) (set1 uninterpreted_type1)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb f) (t2tb269 g)))
     x) (tb2t15
        (apply (set1 int) (set1 uninterpreted_type1) (t2tb269 g)
        (t2tb3 (apply5 f x))))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))) (g uni) (s (set (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool))) (t (set (set uninterpreted_type))) (u uni))
  (=>
  (and (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))) (t2tb f)
  (infix_plmngt (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb7 s) (t2tb2 t)))
  (and (mem (set1 (tuple21 (set1 uninterpreted_type1) c)) g
  (infix_plmngt c (set1 uninterpreted_type1) (t2tb2 t) u))
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 x)
  (dom (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb f))) (mem
  (set1 uninterpreted_type1) (t2tb3 (apply5 f x))
  (dom c (set1 uninterpreted_type1) g)))))
  (= (apply c (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (semicolon c (set1 uninterpreted_type1)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb f) g) (t2tb8 x)) 
  (apply c (set1 uninterpreted_type1) g (t2tb3 (apply5 f x))))))))

;; apply_compose
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (g (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))) (s (set (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool))) (t (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (u (set (set uninterpreted_type))))
  (=>
  (and (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))) (t2tb147 f)
  (infix_plmngt (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb7 s) (t2tb7 t)))
  (and (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))) (t2tb g)
  (infix_plmngt (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb7 t) (t2tb2 u)))
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 x)
  (dom (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb147 f))) (mem
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (apply (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb147 f) (t2tb8 x))
  (dom (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb g))))))
  (= (apply5
     (tb2t
     (semicolon (set1 uninterpreted_type1)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb147 f) (t2tb g)))
     x) (apply5 g
        (tb2t8
        (apply (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb147 f)
        (t2tb8 x))))))))

;; apply_compose
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (g (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))
  (s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (t (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (u (set (set Int))))
  (=>
  (and (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))) (t2tb147 f)
  (infix_plmngt (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb7 s) (t2tb7 t)))
  (and (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb5 g)
  (infix_plmngt (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb7 t) (t2tb24 u)))
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 x)
  (dom (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb147 f))) (mem
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (apply (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb147 f) (t2tb8 x))
  (dom (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 g))))))
  (= (apply4
     (tb2t5
     (semicolon (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb147 f) (t2tb5 g)))
     x) (apply4 g
        (tb2t8
        (apply (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb147 f)
        (t2tb8 x))))))))

(declare-fun t2tb270 ((set (set (tuple2 (set Int)
  (set uninterpreted_type))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (set Int) (set uninterpreted_type)))))) (sort
  (set1 (set1 (tuple21 (set1 int) (set1 uninterpreted_type1)))) (t2tb270 x))))

(declare-fun tb2t270 (uni) (set (set (tuple2 (set Int)
  (set uninterpreted_type)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (set Int) (set uninterpreted_type))))))
  (! (= (tb2t270 (t2tb270 i)) i) :pattern ((t2tb270 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb270 (tb2t270 j)) j) :pattern ((t2tb270 (tb2t270 j))) )))

(declare-fun t2tb271 ((set (tuple2 (set Int) (set uninterpreted_type)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (set Int) (set uninterpreted_type))))) (sort
  (set1 (tuple21 (set1 int) (set1 uninterpreted_type1))) (t2tb271 x))))

(declare-fun tb2t271 (uni) (set (tuple2 (set Int) (set uninterpreted_type))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (set Int) (set uninterpreted_type)))))
  (! (= (tb2t271 (t2tb271 i)) i) :pattern ((t2tb271 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb271 (tb2t271 j)) j) :pattern ((t2tb271 (tb2t271 j))) )))

;; apply_compose
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))
  (g (set (tuple2 (set Int) (set uninterpreted_type))))
  (s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (t (set (set Int))) (u (set (set uninterpreted_type))))
  (=>
  (and (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb5 f)
  (infix_plmngt (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb7 s) (t2tb24 t)))
  (and (mem (set1 (tuple21 (set1 int) (set1 uninterpreted_type1)))
  (t2tb271 g)
  (infix_plmngt (set1 uninterpreted_type1) (set1 int) (t2tb24 t) (t2tb2 u)))
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 x)
  (dom (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 f))) (mem (set1 int) (t2tb15 (apply4 f x))
  (dom (set1 uninterpreted_type1) (set1 int) (t2tb271 g))))))
  (= (apply5
     (tb2t
     (semicolon (set1 uninterpreted_type1) (set1 int)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb5 f) (t2tb271 g)))
     x) (tb2t3
        (apply (set1 uninterpreted_type1) (set1 int) (t2tb271 g)
        (t2tb15 (apply4 f x))))))))

(declare-fun t2tb272 ((set (set (tuple2 (set Int) (set Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (set Int) (set Int)))))) (sort
  (set1 (set1 (tuple21 (set1 int) (set1 int)))) (t2tb272 x))))

(declare-fun tb2t272 (uni) (set (set (tuple2 (set Int) (set Int)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (set Int) (set Int))))))
  (! (= (tb2t272 (t2tb272 i)) i) :pattern ((t2tb272 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb272 (tb2t272 j)) j) :pattern ((t2tb272 (tb2t272 j))) )))

(declare-fun t2tb273 ((set (tuple2 (set Int) (set Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (set Int) (set Int))))) (sort
  (set1 (tuple21 (set1 int) (set1 int))) (t2tb273 x))))

(declare-fun tb2t273 (uni) (set (tuple2 (set Int) (set Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (set Int) (set Int)))))
  (! (= (tb2t273 (t2tb273 i)) i) :pattern ((t2tb273 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb273 (tb2t273 j)) j) :pattern ((t2tb273 (tb2t273 j))) )))

;; apply_compose
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))
  (g (set (tuple2 (set Int) (set Int)))) (s (set (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool))) (t (set (set Int))) (u (set (set Int))))
  (=>
  (and (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb5 f)
  (infix_plmngt (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb7 s) (t2tb24 t)))
  (and (mem (set1 (tuple21 (set1 int) (set1 int))) (t2tb273 g)
  (infix_plmngt (set1 int) (set1 int) (t2tb24 t) (t2tb24 u)))
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 x)
  (dom (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 f))) (mem (set1 int) (t2tb15 (apply4 f x))
  (dom (set1 int) (set1 int) (t2tb273 g))))))
  (= (apply4
     (tb2t5
     (semicolon (set1 int) (set1 int)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb5 f) (t2tb273 g)))
     x) (tb2t15
        (apply (set1 int) (set1 int) (t2tb273 g) (t2tb15 (apply4 f x))))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))
  (g uni) (s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (t (set (set Int))) (u uni))
  (=>
  (and (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb5 f)
  (infix_plmngt (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb7 s) (t2tb24 t)))
  (and (mem (set1 (tuple21 (set1 int) c)) g
  (infix_plmngt c (set1 int) (t2tb24 t) u))
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 x)
  (dom (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 f))) (mem (set1 int) (t2tb15 (apply4 f x)) (dom c (set1 int) g)))))
  (= (apply c (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (semicolon c (set1 int)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb5 f) g)
     (t2tb8 x)) (apply c (set1 int) g (t2tb15 (apply4 f x))))))))

;; apply_compose
  (assert
  (forall ((b ty))
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)) (f uni) (g uni)
  (s (set (tuple2 (tuple2 Bool Bool) Bool))) (t uni) (u (set Bool)))
  (=>
  (and (mem (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) b)) f
  (infix_plmngt b (tuple21 (tuple21 bool bool) bool) (t2tb9 s) t))
  (and (mem (set1 (tuple21 b bool)) g (infix_plmngt bool b t (t2tb14 u)))
  (and (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x)
  (dom b (tuple21 (tuple21 bool bool) bool) f)) (mem b
  (apply b (tuple21 (tuple21 bool bool) bool) f (t2tb10 x)) (dom bool b g)))))
  (= (apply1
     (tb2t7 (semicolon bool b (tuple21 (tuple21 bool bool) bool) f g)) x) 
  (tb2t13
  (apply bool b g (apply b (tuple21 (tuple21 bool bool) bool) f (t2tb10 x)))))))))

;; apply_compose
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool))
  (f (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) (tuple2 (tuple2 Bool Bool)
  Bool)))) (g (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (s (set (tuple2 (tuple2 Bool Bool) Bool))) (t (set (tuple2 (tuple2 Bool
  Bool) Bool))) (u (set Bool)))
  (=>
  (and (mem
  (set1
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 bool bool) bool))) (t2tb177 f)
  (infix_plmngt (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 bool bool) bool) (t2tb9 s) (t2tb9 t)))
  (and (mem (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (t2tb7 g)
  (infix_plmngt bool (tuple21 (tuple21 bool bool) bool) (t2tb9 t) (t2tb14 u)))
  (and (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x)
  (dom (tuple21 (tuple21 bool bool) bool) (tuple21 (tuple21 bool bool) bool)
  (t2tb177 f))) (mem (tuple21 (tuple21 bool bool) bool)
  (apply (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 bool bool) bool) (t2tb177 f) (t2tb10 x))
  (dom bool (tuple21 (tuple21 bool bool) bool) (t2tb7 g))))))
  (= (apply1
     (tb2t7
     (semicolon bool (tuple21 (tuple21 bool bool) bool)
     (tuple21 (tuple21 bool bool) bool) (t2tb177 f) (t2tb7 g))) x) (apply1 g
                                                                   (tb2t10
                                                                   (apply
                                                                   (tuple21
                                                                   (tuple21
                                                                   bool 
                                                                   bool)
                                                                   bool)
                                                                   (tuple21
                                                                   (tuple21
                                                                   bool 
                                                                   bool)
                                                                   bool)
                                                                   (t2tb177
                                                                   f)
                                                                   (t2tb10 x))))))))

;; apply_compose
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool))
  (f (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) (tuple2 Bool Bool))))
  (g (set (tuple2 (tuple2 Bool Bool) Bool))) (s (set (tuple2 (tuple2 Bool
  Bool) Bool))) (t (set (tuple2 Bool Bool))) (u (set Bool)))
  (=>
  (and (mem
  (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool)))
  (t2tb180 f)
  (infix_plmngt (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool)
  (t2tb9 s) (t2tb11 t)))
  (and (mem (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb9 g)
  (infix_plmngt bool (tuple21 bool bool) (t2tb11 t) (t2tb14 u)))
  (and (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x)
  (dom (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool) (t2tb180 f)))
  (mem (tuple21 bool bool)
  (apply (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool) (t2tb180 f)
  (t2tb10 x)) (dom bool (tuple21 bool bool) (t2tb9 g))))))
  (= (apply1
     (tb2t7
     (semicolon bool (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool)
     (t2tb180 f) (t2tb9 g))) x) (apply2 g
                                (tb2t12
                                (apply (tuple21 bool bool)
                                (tuple21 (tuple21 bool bool) bool)
                                (t2tb180 f) (t2tb10 x))))))))

;; apply_compose
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool))
  (f (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (g (set (tuple2 Bool Bool))) (s (set (tuple2 (tuple2 Bool Bool) Bool)))
  (t (set Bool)) (u (set Bool)))
  (=>
  (and (mem (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (t2tb7 f)
  (infix_plmngt bool (tuple21 (tuple21 bool bool) bool) (t2tb9 s) (t2tb14 t)))
  (and (mem (set1 (tuple21 bool bool)) (t2tb11 g)
  (infix_plmngt bool bool (t2tb14 t) (t2tb14 u)))
  (and (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x)
  (dom bool (tuple21 (tuple21 bool bool) bool) (t2tb7 f))) (mem bool
  (t2tb13 (apply1 f x)) (dom bool bool (t2tb11 g))))))
  (= (apply1
     (tb2t7
     (semicolon bool bool (tuple21 (tuple21 bool bool) bool) (t2tb7 f)
     (t2tb11 g))) x) (apply3 g (apply1 f x))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool))
  (f (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))) (g uni)
  (s (set (tuple2 (tuple2 Bool Bool) Bool))) (t (set Bool)) (u uni))
  (=>
  (and (mem (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (t2tb7 f)
  (infix_plmngt bool (tuple21 (tuple21 bool bool) bool) (t2tb9 s) (t2tb14 t)))
  (and (mem (set1 (tuple21 bool c)) g (infix_plmngt c bool (t2tb14 t) u))
  (and (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x)
  (dom bool (tuple21 (tuple21 bool bool) bool) (t2tb7 f))) (mem bool
  (t2tb13 (apply1 f x)) (dom c bool g)))))
  (= (apply c (tuple21 (tuple21 bool bool) bool)
     (semicolon c bool (tuple21 (tuple21 bool bool) bool) (t2tb7 f) g)
     (t2tb10 x)) (apply c bool g (t2tb13 (apply1 f x))))))))

;; apply_compose
  (assert
  (forall ((b ty))
  (forall ((x (tuple2 Bool Bool)) (f uni) (g uni) (s (set (tuple2 Bool
  Bool))) (t uni) (u (set Bool)))
  (=>
  (and (mem (set1 (tuple21 (tuple21 bool bool) b)) f
  (infix_plmngt b (tuple21 bool bool) (t2tb11 s) t))
  (and (mem (set1 (tuple21 b bool)) g (infix_plmngt bool b t (t2tb14 u)))
  (and (mem (tuple21 bool bool) (t2tb12 x) (dom b (tuple21 bool bool) f))
  (mem b (apply b (tuple21 bool bool) f (t2tb12 x)) (dom bool b g)))))
  (= (apply2 (tb2t9 (semicolon bool b (tuple21 bool bool) f g)) x) (tb2t13
                                                                   (apply
                                                                   bool b g
                                                                   (apply b
                                                                   (tuple21
                                                                   bool 
                                                                   bool) f
                                                                   (t2tb12 x)))))))))

;; apply_compose
  (assert
  (forall ((x (tuple2 Bool Bool)) (f (set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 Bool Bool) Bool)))) (g (set (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool))) (s (set (tuple2 Bool Bool)))
  (t (set (tuple2 (tuple2 Bool Bool) Bool))) (u (set Bool)))
  (=>
  (and (mem
  (set1 (tuple21 (tuple21 bool bool) (tuple21 (tuple21 bool bool) bool)))
  (t2tb202 f)
  (infix_plmngt (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool)
  (t2tb11 s) (t2tb9 t)))
  (and (mem (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (t2tb7 g)
  (infix_plmngt bool (tuple21 (tuple21 bool bool) bool) (t2tb9 t) (t2tb14 u)))
  (and (mem (tuple21 bool bool) (t2tb12 x)
  (dom (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool) (t2tb202 f)))
  (mem (tuple21 (tuple21 bool bool) bool)
  (apply (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool) (t2tb202 f)
  (t2tb12 x)) (dom bool (tuple21 (tuple21 bool bool) bool) (t2tb7 g))))))
  (= (apply2
     (tb2t9
     (semicolon bool (tuple21 (tuple21 bool bool) bool) (tuple21 bool bool)
     (t2tb202 f) (t2tb7 g))) x) (apply1 g
                                (tb2t10
                                (apply (tuple21 (tuple21 bool bool) bool)
                                (tuple21 bool bool) (t2tb202 f) (t2tb12 x))))))))

;; apply_compose
  (assert
  (forall ((x (tuple2 Bool Bool)) (f (set (tuple2 (tuple2 Bool Bool)
  (tuple2 Bool Bool)))) (g (set (tuple2 (tuple2 Bool Bool) Bool)))
  (s (set (tuple2 Bool Bool))) (t (set (tuple2 Bool Bool))) (u (set Bool)))
  (=>
  (and (mem (set1 (tuple21 (tuple21 bool bool) (tuple21 bool bool)))
  (t2tb204 f)
  (infix_plmngt (tuple21 bool bool) (tuple21 bool bool) (t2tb11 s)
  (t2tb11 t)))
  (and (mem (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb9 g)
  (infix_plmngt bool (tuple21 bool bool) (t2tb11 t) (t2tb14 u)))
  (and (mem (tuple21 bool bool) (t2tb12 x)
  (dom (tuple21 bool bool) (tuple21 bool bool) (t2tb204 f))) (mem
  (tuple21 bool bool)
  (apply (tuple21 bool bool) (tuple21 bool bool) (t2tb204 f) (t2tb12 x))
  (dom bool (tuple21 bool bool) (t2tb9 g))))))
  (= (apply2
     (tb2t9
     (semicolon bool (tuple21 bool bool) (tuple21 bool bool) (t2tb204 f)
     (t2tb9 g))) x) (apply2 g
                    (tb2t12
                    (apply (tuple21 bool bool) (tuple21 bool bool)
                    (t2tb204 f) (t2tb12 x))))))))

;; apply_compose
  (assert
  (forall ((x (tuple2 Bool Bool)) (f (set (tuple2 (tuple2 Bool Bool) Bool)))
  (g (set (tuple2 Bool Bool))) (s (set (tuple2 Bool Bool))) (t (set Bool))
  (u (set Bool)))
  (=>
  (and (mem (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb9 f)
  (infix_plmngt bool (tuple21 bool bool) (t2tb11 s) (t2tb14 t)))
  (and (mem (set1 (tuple21 bool bool)) (t2tb11 g)
  (infix_plmngt bool bool (t2tb14 t) (t2tb14 u)))
  (and (mem (tuple21 bool bool) (t2tb12 x)
  (dom bool (tuple21 bool bool) (t2tb9 f))) (mem bool (t2tb13 (apply2 f x))
  (dom bool bool (t2tb11 g))))))
  (= (apply2
     (tb2t9 (semicolon bool bool (tuple21 bool bool) (t2tb9 f) (t2tb11 g)))
     x) (apply3 g (apply2 f x))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x (tuple2 Bool Bool)) (f (set (tuple2 (tuple2 Bool Bool) Bool)))
  (g uni) (s (set (tuple2 Bool Bool))) (t (set Bool)) (u uni))
  (=>
  (and (mem (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb9 f)
  (infix_plmngt bool (tuple21 bool bool) (t2tb11 s) (t2tb14 t)))
  (and (mem (set1 (tuple21 bool c)) g (infix_plmngt c bool (t2tb14 t) u))
  (and (mem (tuple21 bool bool) (t2tb12 x)
  (dom bool (tuple21 bool bool) (t2tb9 f))) (mem bool (t2tb13 (apply2 f x))
  (dom c bool g)))))
  (= (apply c (tuple21 bool bool)
     (semicolon c bool (tuple21 bool bool) (t2tb9 f) g) (t2tb12 x)) (apply c
                                                                    bool g
                                                                    (t2tb13
                                                                    (apply2 f
                                                                    x))))))))

;; apply_compose
  (assert
  (forall ((b ty))
  (forall ((x Bool) (f uni) (g uni) (s (set Bool)) (t uni) (u (set Bool)))
  (=>
  (and (mem (set1 (tuple21 bool b)) f (infix_plmngt b bool (t2tb14 s) t))
  (and (mem (set1 (tuple21 b bool)) g (infix_plmngt bool b t (t2tb14 u)))
  (and (mem bool (t2tb13 x) (dom b bool f)) (mem b
  (apply b bool f (t2tb13 x)) (dom bool b g)))))
  (= (apply3 (tb2t11 (semicolon bool b bool f g)) x) (tb2t13
                                                     (apply bool b g
                                                     (apply b bool f
                                                     (t2tb13 x)))))))))

;; apply_compose
  (assert
  (forall ((x Bool) (f (set (tuple2 Bool (tuple2 (tuple2 Bool Bool) Bool))))
  (g (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))) (s (set Bool))
  (t (set (tuple2 (tuple2 Bool Bool) Bool))) (u (set Bool)))
  (=>
  (and (mem (set1 (tuple21 bool (tuple21 (tuple21 bool bool) bool)))
  (t2tb25 f)
  (infix_plmngt (tuple21 (tuple21 bool bool) bool) bool (t2tb14 s) (t2tb9 t)))
  (and (mem (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (t2tb7 g)
  (infix_plmngt bool (tuple21 (tuple21 bool bool) bool) (t2tb9 t) (t2tb14 u)))
  (and (mem bool (t2tb13 x)
  (dom (tuple21 (tuple21 bool bool) bool) bool (t2tb25 f))) (mem
  (tuple21 (tuple21 bool bool) bool)
  (apply (tuple21 (tuple21 bool bool) bool) bool (t2tb25 f) (t2tb13 x))
  (dom bool (tuple21 (tuple21 bool bool) bool) (t2tb7 g))))))
  (= (apply3
     (tb2t11
     (semicolon bool (tuple21 (tuple21 bool bool) bool) bool (t2tb25 f)
     (t2tb7 g))) x) (apply1 g
                    (tb2t10
                    (apply (tuple21 (tuple21 bool bool) bool) bool (t2tb25 f)
                    (t2tb13 x))))))))

;; apply_compose
  (assert
  (forall ((x Bool) (f (set (tuple2 Bool (tuple2 Bool Bool))))
  (g (set (tuple2 (tuple2 Bool Bool) Bool))) (s (set Bool))
  (t (set (tuple2 Bool Bool))) (u (set Bool)))
  (=>
  (and (mem (set1 (tuple21 bool (tuple21 bool bool))) (t2tb27 f)
  (infix_plmngt (tuple21 bool bool) bool (t2tb14 s) (t2tb11 t)))
  (and (mem (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb9 g)
  (infix_plmngt bool (tuple21 bool bool) (t2tb11 t) (t2tb14 u)))
  (and (mem bool (t2tb13 x) (dom (tuple21 bool bool) bool (t2tb27 f))) (mem
  (tuple21 bool bool) (apply (tuple21 bool bool) bool (t2tb27 f) (t2tb13 x))
  (dom bool (tuple21 bool bool) (t2tb9 g))))))
  (= (apply3
     (tb2t11 (semicolon bool (tuple21 bool bool) bool (t2tb27 f) (t2tb9 g)))
     x) (apply2 g
        (tb2t12 (apply (tuple21 bool bool) bool (t2tb27 f) (t2tb13 x))))))))

;; apply_compose
  (assert
  (forall ((x Bool) (f (set (tuple2 Bool Bool))) (g (set (tuple2 Bool Bool)))
  (s (set Bool)) (t (set Bool)) (u (set Bool)))
  (=>
  (and (mem (set1 (tuple21 bool bool)) (t2tb11 f)
  (infix_plmngt bool bool (t2tb14 s) (t2tb14 t)))
  (and (mem (set1 (tuple21 bool bool)) (t2tb11 g)
  (infix_plmngt bool bool (t2tb14 t) (t2tb14 u)))
  (and (mem bool (t2tb13 x) (dom bool bool (t2tb11 f))) (mem bool
  (t2tb13 (apply3 f x)) (dom bool bool (t2tb11 g))))))
  (= (apply3 (tb2t11 (semicolon bool bool bool (t2tb11 f) (t2tb11 g))) x) 
  (apply3 g (apply3 f x))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x Bool) (f (set (tuple2 Bool Bool))) (g uni) (s (set Bool))
  (t (set Bool)) (u uni))
  (=>
  (and (mem (set1 (tuple21 bool bool)) (t2tb11 f)
  (infix_plmngt bool bool (t2tb14 s) (t2tb14 t)))
  (and (mem (set1 (tuple21 bool c)) g (infix_plmngt c bool (t2tb14 t) u))
  (and (mem bool (t2tb13 x) (dom bool bool (t2tb11 f))) (mem bool
  (t2tb13 (apply3 f x)) (dom c bool g)))))
  (= (apply c bool (semicolon c bool bool (t2tb11 f) g) (t2tb13 x)) (apply c
                                                                    bool g
                                                                    (t2tb13
                                                                    (apply3 f
                                                                    x))))))))

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
  (forall ((f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))) (s (set (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool))) (t (set (set uninterpreted_type))))
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (y (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (=> (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))) (t2tb f)
  (infix_gtmngt (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb7 s) (t2tb2 t)))
  (=> (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 x)
  (t2tb7 s))
  (=> (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 y)
  (t2tb7 s)) (=> (= (apply5 f x) (apply5 f y)) (= x y))))))))

;; injection
  (assert
  (forall ((f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (t (set (set Int))))
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (y (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (=> (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb5 f)
  (infix_gtmngt (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb7 s) (t2tb24 t)))
  (=> (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 x)
  (t2tb7 s))
  (=> (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 y)
  (t2tb7 s)) (=> (= (apply4 f x) (apply4 f y)) (= x y))))))))

;; injection
  (assert
  (forall ((f (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (s (set (tuple2 (tuple2 Bool Bool) Bool))) (t (set Bool)))
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)) (y (tuple2 (tuple2 Bool Bool)
  Bool)))
  (=> (mem (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb7 f)
  (infix_gtmngt bool (tuple21 (tuple21 bool bool) bool) (t2tb9 s) (t2tb14 t)))
  (=> (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb9 s))
  (=> (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 y) (t2tb9 s))
  (=> (= (apply1 f x) (apply1 f y)) (= x y))))))))

;; injection
  (assert
  (forall ((f (set (tuple2 (tuple2 Bool Bool) Bool))) (s (set (tuple2 Bool
  Bool))) (t (set Bool)))
  (forall ((x (tuple2 Bool Bool)) (y (tuple2 Bool Bool)))
  (=> (mem (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb9 f)
  (infix_gtmngt bool (tuple21 bool bool) (t2tb11 s) (t2tb14 t)))
  (=> (mem (tuple21 bool bool) (t2tb12 x) (t2tb11 s))
  (=> (mem (tuple21 bool bool) (t2tb12 y) (t2tb11 s))
  (=> (= (apply2 f x) (apply2 f y)) (= x y))))))))

;; injection
  (assert
  (forall ((f (set (tuple2 Bool Bool))) (s (set Bool)) (t (set Bool)))
  (forall ((x Bool) (y Bool))
  (=> (mem (set1 (tuple21 bool bool)) (t2tb11 f)
  (infix_gtmngt bool bool (t2tb14 s) (t2tb14 t)))
  (=> (mem bool (t2tb13 x) (t2tb14 s))
  (=> (mem bool (t2tb13 y) (t2tb14 s))
  (=> (= (apply3 f x) (apply3 f y)) (= x y))))))))

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
  (forall ((x Bool) (y Bool) (s (set Bool)))
  (= (mem (tuple21 bool bool) (t2tb12 (Tuple21 x y)) (id bool (t2tb14 s)))
  (and (mem bool (t2tb13 x) (t2tb14 s)) (= x y)))))

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
  (= (seq_length a n s) (infix_mnmngt a int (t2tb15 (mk 1 n)) s)))))

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
  (infix_mnmngt a int (t2tb15 (mk 1 (size a r))) s))))))

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
  (forall ((s (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))))) (is_finite_subset
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb empty6) (t2tb s) 0)))

;; Empty
  (assert
  (forall ((s (set (set uninterpreted_type)))) (is_finite_subset
  (set1 uninterpreted_type1) (t2tb2 empty5) (t2tb2 s) 0)))

;; Empty
  (assert
  (forall ((s (set uninterpreted_type))) (is_finite_subset
  uninterpreted_type1 (t2tb3 empty4) (t2tb3 s) 0)))

;; Empty
  (assert
  (forall ((s (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (is_finite_subset
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb5 empty3) (t2tb5 s) 0)))

;; Empty
  (assert
  (forall ((s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (is_finite_subset (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb7 empty7) (t2tb7 s) 0)))

;; Empty
  (assert
  (forall ((s (set (tuple2 (tuple2 Bool Bool) Bool)))) (is_finite_subset
  (tuple21 (tuple21 bool bool) bool) (t2tb9 empty8) (t2tb9 s) 0)))

;; Empty
  (assert
  (forall ((s (set (tuple2 Bool Bool)))) (is_finite_subset
  (tuple21 bool bool) (t2tb11 empty9) (t2tb11 s) 0)))

;; Empty
  (assert
  (forall ((s (set Bool))) (is_finite_subset bool (t2tb14 empty1) (t2tb14 s)
  0)))

;; Empty
  (assert
  (forall ((s (set Int))) (is_finite_subset int (t2tb15 empty2) (t2tb15 s)
  0)))

;; Empty
  (assert
  (forall ((a ty)) (forall ((s uni)) (is_finite_subset a (empty a) s 0))))

;; Add_mem
  (assert
  (forall ((x (set uninterpreted_type)) (s1 (set (set uninterpreted_type)))
  (s2 (set (set uninterpreted_type))) (c Int))
  (=> (is_finite_subset (set1 uninterpreted_type1) (t2tb2 s1) (t2tb2 s2) c)
  (=> (mem (set1 uninterpreted_type1) (t2tb3 x) (t2tb2 s2))
  (=> (mem (set1 uninterpreted_type1) (t2tb3 x) (t2tb2 s1)) (is_finite_subset
  (set1 uninterpreted_type1) (t2tb2 (add3 x s1)) (t2tb2 s2) c))))))

;; Add_mem
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (s1 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (s2 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))) (c Int))
  (=> (is_finite_subset (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb7 s1) (t2tb7 s2) c)
  (=> (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 x)
  (t2tb7 s2))
  (=> (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 x)
  (t2tb7 s1)) (is_finite_subset
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb7 (add4 x s1))
  (t2tb7 s2) c))))))

;; Add_mem
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)) (s1 (set (tuple2 (tuple2 Bool
  Bool) Bool))) (s2 (set (tuple2 (tuple2 Bool Bool) Bool))) (c Int))
  (=> (is_finite_subset (tuple21 (tuple21 bool bool) bool) (t2tb9 s1)
  (t2tb9 s2) c)
  (=> (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb9 s2))
  (=> (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb9 s1))
  (is_finite_subset (tuple21 (tuple21 bool bool) bool) (t2tb9 (add5 x s1))
  (t2tb9 s2) c))))))

;; Add_mem
  (assert
  (forall ((x (tuple2 Bool Bool)) (s1 (set (tuple2 Bool Bool)))
  (s2 (set (tuple2 Bool Bool))) (c Int))
  (=> (is_finite_subset (tuple21 bool bool) (t2tb11 s1) (t2tb11 s2) c)
  (=> (mem (tuple21 bool bool) (t2tb12 x) (t2tb11 s2))
  (=> (mem (tuple21 bool bool) (t2tb12 x) (t2tb11 s1)) (is_finite_subset
  (tuple21 bool bool) (t2tb11 (add6 x s1)) (t2tb11 s2) c))))))

;; Add_mem
  (assert
  (forall ((x Bool) (s1 (set Bool)) (s2 (set Bool)) (c Int))
  (=> (is_finite_subset bool (t2tb14 s1) (t2tb14 s2) c)
  (=> (mem bool (t2tb13 x) (t2tb14 s2))
  (=> (mem bool (t2tb13 x) (t2tb14 s1)) (is_finite_subset bool
  (t2tb14 (add1 x s1)) (t2tb14 s2) c))))))

;; Add_mem
  (assert
  (forall ((x Int) (s1 (set Int)) (s2 (set Int)) (c Int))
  (=> (is_finite_subset int (t2tb15 s1) (t2tb15 s2) c)
  (=> (mem int (t2tb16 x) (t2tb15 s2))
  (=> (mem int (t2tb16 x) (t2tb15 s1)) (is_finite_subset int
  (t2tb15 (add2 x s1)) (t2tb15 s2) c))))))

;; Add_mem
  (assert
  (forall ((a ty))
  (forall ((x uni) (s1 uni) (s2 uni) (c Int))
  (=> (is_finite_subset a s1 s2 c)
  (=> (mem a x s2) (=> (mem a x s1) (is_finite_subset a (add a x s1) s2 c)))))))

;; Add_notmem
  (assert
  (forall ((x (set uninterpreted_type)) (s1 (set (set uninterpreted_type)))
  (s2 (set (set uninterpreted_type))) (c Int))
  (=> (is_finite_subset (set1 uninterpreted_type1) (t2tb2 s1) (t2tb2 s2) c)
  (=> (mem (set1 uninterpreted_type1) (t2tb3 x) (t2tb2 s2))
  (=> (not (mem (set1 uninterpreted_type1) (t2tb3 x) (t2tb2 s1)))
  (is_finite_subset (set1 uninterpreted_type1) (t2tb2 (add3 x s1)) (t2tb2 s2)
  (+ c 1)))))))

;; Add_notmem
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (s1 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (s2 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))) (c Int))
  (=> (is_finite_subset (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb7 s1) (t2tb7 s2) c)
  (=> (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 x)
  (t2tb7 s2))
  (=>
  (not (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 x)
  (t2tb7 s1))) (is_finite_subset
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb7 (add4 x s1))
  (t2tb7 s2) (+ c 1)))))))

;; Add_notmem
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)) (s1 (set (tuple2 (tuple2 Bool
  Bool) Bool))) (s2 (set (tuple2 (tuple2 Bool Bool) Bool))) (c Int))
  (=> (is_finite_subset (tuple21 (tuple21 bool bool) bool) (t2tb9 s1)
  (t2tb9 s2) c)
  (=> (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb9 s2))
  (=> (not (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb9 s1)))
  (is_finite_subset (tuple21 (tuple21 bool bool) bool) (t2tb9 (add5 x s1))
  (t2tb9 s2) (+ c 1)))))))

;; Add_notmem
  (assert
  (forall ((x (tuple2 Bool Bool)) (s1 (set (tuple2 Bool Bool)))
  (s2 (set (tuple2 Bool Bool))) (c Int))
  (=> (is_finite_subset (tuple21 bool bool) (t2tb11 s1) (t2tb11 s2) c)
  (=> (mem (tuple21 bool bool) (t2tb12 x) (t2tb11 s2))
  (=> (not (mem (tuple21 bool bool) (t2tb12 x) (t2tb11 s1)))
  (is_finite_subset (tuple21 bool bool) (t2tb11 (add6 x s1)) (t2tb11 s2)
  (+ c 1)))))))

;; Add_notmem
  (assert
  (forall ((x Bool) (s1 (set Bool)) (s2 (set Bool)) (c Int))
  (=> (is_finite_subset bool (t2tb14 s1) (t2tb14 s2) c)
  (=> (mem bool (t2tb13 x) (t2tb14 s2))
  (=> (not (mem bool (t2tb13 x) (t2tb14 s1))) (is_finite_subset bool
  (t2tb14 (add1 x s1)) (t2tb14 s2) (+ c 1)))))))

;; Add_notmem
  (assert
  (forall ((x Int) (s1 (set Int)) (s2 (set Int)) (c Int))
  (=> (is_finite_subset int (t2tb15 s1) (t2tb15 s2) c)
  (=> (mem int (t2tb16 x) (t2tb15 s2))
  (=> (not (mem int (t2tb16 x) (t2tb15 s1))) (is_finite_subset int
  (t2tb15 (add2 x s1)) (t2tb15 s2) (+ c 1)))))))

;; Add_notmem
  (assert
  (forall ((a ty))
  (forall ((x uni) (s1 uni) (s2 uni) (c Int))
  (=> (is_finite_subset a s1 s2 c)
  (=> (mem a x s2)
  (=> (not (mem a x s1)) (is_finite_subset a (add a x s1) s2 (+ c 1))))))))

;; is_finite_subset_inversion
  (assert
  (forall ((z (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))) (z1 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type)))) (z2 Int))
  (=> (is_finite_subset
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb z) (t2tb z1) z2)
  (or
  (or
  (exists ((s (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))))) (and (and (= z empty6) (= z1 s)) (= z2 0)))
  (exists ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))) (s1 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type))))
  (s2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))) (c Int))
  (and (is_finite_subset
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb s1) (t2tb s2) c)
  (and (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb1 x) (t2tb s2))
  (and (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb1 x) (t2tb s1))
  (and
  (and
  (= z (tb2t
       (add
       (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
       (set1 uninterpreted_type1)) (t2tb1 x) (t2tb s1))))
  (= z1 s2)) (= z2 c)))))))
  (exists ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))) (s1 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type))))
  (s2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))) (c Int))
  (and (is_finite_subset
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb s1) (t2tb s2) c)
  (and (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb1 x) (t2tb s2))
  (and
  (not (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb1 x) (t2tb s1)))
  (and
  (and
  (= z (tb2t
       (add
       (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
       (set1 uninterpreted_type1)) (t2tb1 x) (t2tb s1))))
  (= z1 s2)) (= z2 (+ c 1)))))))))))

;; is_finite_subset_inversion
  (assert
  (forall ((z (set (set uninterpreted_type)))
  (z1 (set (set uninterpreted_type))) (z2 Int))
  (=> (is_finite_subset (set1 uninterpreted_type1) (t2tb2 z) (t2tb2 z1) z2)
  (or
  (or
  (exists ((s (set (set uninterpreted_type))))
  (and (and (= z empty5) (= z1 s)) (= z2 0)))
  (exists ((x (set uninterpreted_type)) (s1 (set (set uninterpreted_type)))
  (s2 (set (set uninterpreted_type))) (c Int))
  (and (is_finite_subset (set1 uninterpreted_type1) (t2tb2 s1) (t2tb2 s2) c)
  (and (mem (set1 uninterpreted_type1) (t2tb3 x) (t2tb2 s2))
  (and (mem (set1 uninterpreted_type1) (t2tb3 x) (t2tb2 s1))
  (and (and (= z (add3 x s1)) (= z1 s2)) (= z2 c)))))))
  (exists ((x (set uninterpreted_type)) (s1 (set (set uninterpreted_type)))
  (s2 (set (set uninterpreted_type))) (c Int))
  (and (is_finite_subset (set1 uninterpreted_type1) (t2tb2 s1) (t2tb2 s2) c)
  (and (mem (set1 uninterpreted_type1) (t2tb3 x) (t2tb2 s2))
  (and (not (mem (set1 uninterpreted_type1) (t2tb3 x) (t2tb2 s1)))
  (and (and (= z (add3 x s1)) (= z1 s2)) (= z2 (+ c 1)))))))))))

;; is_finite_subset_inversion
  (assert
  (forall ((z (set uninterpreted_type)) (z1 (set uninterpreted_type))
  (z2 Int))
  (=> (is_finite_subset uninterpreted_type1 (t2tb3 z) (t2tb3 z1) z2)
  (or
  (or
  (exists ((s (set uninterpreted_type)))
  (and (and (= z empty4) (= z1 s)) (= z2 0)))
  (exists ((x uninterpreted_type) (s1 (set uninterpreted_type))
  (s2 (set uninterpreted_type)) (c Int))
  (and (is_finite_subset uninterpreted_type1 (t2tb3 s1) (t2tb3 s2) c)
  (and (mem uninterpreted_type1 (t2tb4 x) (t2tb3 s2))
  (and (mem uninterpreted_type1 (t2tb4 x) (t2tb3 s1))
  (and
  (and (= z (tb2t3 (add uninterpreted_type1 (t2tb4 x) (t2tb3 s1))))
  (= z1 s2)) (= z2 c)))))))
  (exists ((x uninterpreted_type) (s1 (set uninterpreted_type))
  (s2 (set uninterpreted_type)) (c Int))
  (and (is_finite_subset uninterpreted_type1 (t2tb3 s1) (t2tb3 s2) c)
  (and (mem uninterpreted_type1 (t2tb4 x) (t2tb3 s2))
  (and (not (mem uninterpreted_type1 (t2tb4 x) (t2tb3 s1)))
  (and
  (and (= z (tb2t3 (add uninterpreted_type1 (t2tb4 x) (t2tb3 s1))))
  (= z1 s2)) (= z2 (+ c 1)))))))))))

;; is_finite_subset_inversion
  (assert
  (forall ((z (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (z1 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))) (z2 Int))
  (=> (is_finite_subset
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb5 z) (t2tb5 z1) z2)
  (or
  (or
  (exists ((s (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (and (and (= z empty3) (= z1 s)) (= z2 0)))
  (exists ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))) (s1 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))) (c Int))
  (and (is_finite_subset
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb5 s1) (t2tb5 s2) c)
  (and (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb6 x) (t2tb5 s2))
  (and (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb6 x) (t2tb5 s1))
  (and
  (and
  (= z (tb2t5
       (add
       (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
       (t2tb6 x) (t2tb5 s1))))
  (= z1 s2)) (= z2 c)))))))
  (exists ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))) (s1 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))) (c Int))
  (and (is_finite_subset
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb5 s1) (t2tb5 s2) c)
  (and (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb6 x) (t2tb5 s2))
  (and
  (not (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb6 x) (t2tb5 s1)))
  (and
  (and
  (= z (tb2t5
       (add
       (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
       (t2tb6 x) (t2tb5 s1))))
  (= z1 s2)) (= z2 (+ c 1)))))))))))

;; is_finite_subset_inversion
  (assert
  (forall ((z (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (z1 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))) (z2 Int))
  (=> (is_finite_subset (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb7 z) (t2tb7 z1) z2)
  (or
  (or
  (exists ((s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (and (and (= z empty7) (= z1 s)) (= z2 0)))
  (exists ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (s1 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (s2 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))) (c Int))
  (and (is_finite_subset (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb7 s1) (t2tb7 s2) c)
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 x)
  (t2tb7 s2))
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 x)
  (t2tb7 s1)) (and (and (= z (add4 x s1)) (= z1 s2)) (= z2 c)))))))
  (exists ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (s1 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (s2 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))) (c Int))
  (and (is_finite_subset (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb7 s1) (t2tb7 s2) c)
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 x)
  (t2tb7 s2))
  (and
  (not (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 x)
  (t2tb7 s1))) (and (and (= z (add4 x s1)) (= z1 s2)) (= z2 (+ c 1)))))))))))

;; is_finite_subset_inversion
  (assert
  (forall ((z (set (tuple2 (tuple2 Bool Bool) Bool)))
  (z1 (set (tuple2 (tuple2 Bool Bool) Bool))) (z2 Int))
  (=> (is_finite_subset (tuple21 (tuple21 bool bool) bool) (t2tb9 z)
  (t2tb9 z1) z2)
  (or
  (or
  (exists ((s (set (tuple2 (tuple2 Bool Bool) Bool))))
  (and (and (= z empty8) (= z1 s)) (= z2 0)))
  (exists ((x (tuple2 (tuple2 Bool Bool) Bool)) (s1 (set (tuple2 (tuple2 Bool
  Bool) Bool))) (s2 (set (tuple2 (tuple2 Bool Bool) Bool))) (c Int))
  (and (is_finite_subset (tuple21 (tuple21 bool bool) bool) (t2tb9 s1)
  (t2tb9 s2) c)
  (and (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb9 s2))
  (and (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb9 s1))
  (and (and (= z (add5 x s1)) (= z1 s2)) (= z2 c)))))))
  (exists ((x (tuple2 (tuple2 Bool Bool) Bool)) (s1 (set (tuple2 (tuple2 Bool
  Bool) Bool))) (s2 (set (tuple2 (tuple2 Bool Bool) Bool))) (c Int))
  (and (is_finite_subset (tuple21 (tuple21 bool bool) bool) (t2tb9 s1)
  (t2tb9 s2) c)
  (and (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb9 s2))
  (and (not (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb9 s1)))
  (and (and (= z (add5 x s1)) (= z1 s2)) (= z2 (+ c 1)))))))))))

;; is_finite_subset_inversion
  (assert
  (forall ((z (set (tuple2 Bool Bool))) (z1 (set (tuple2 Bool Bool)))
  (z2 Int))
  (=> (is_finite_subset (tuple21 bool bool) (t2tb11 z) (t2tb11 z1) z2)
  (or
  (or
  (exists ((s (set (tuple2 Bool Bool))))
  (and (and (= z empty9) (= z1 s)) (= z2 0)))
  (exists ((x (tuple2 Bool Bool)) (s1 (set (tuple2 Bool Bool)))
  (s2 (set (tuple2 Bool Bool))) (c Int))
  (and (is_finite_subset (tuple21 bool bool) (t2tb11 s1) (t2tb11 s2) c)
  (and (mem (tuple21 bool bool) (t2tb12 x) (t2tb11 s2))
  (and (mem (tuple21 bool bool) (t2tb12 x) (t2tb11 s1))
  (and (and (= z (add6 x s1)) (= z1 s2)) (= z2 c)))))))
  (exists ((x (tuple2 Bool Bool)) (s1 (set (tuple2 Bool Bool)))
  (s2 (set (tuple2 Bool Bool))) (c Int))
  (and (is_finite_subset (tuple21 bool bool) (t2tb11 s1) (t2tb11 s2) c)
  (and (mem (tuple21 bool bool) (t2tb12 x) (t2tb11 s2))
  (and (not (mem (tuple21 bool bool) (t2tb12 x) (t2tb11 s1)))
  (and (and (= z (add6 x s1)) (= z1 s2)) (= z2 (+ c 1)))))))))))

;; is_finite_subset_inversion
  (assert
  (forall ((z (set Bool)) (z1 (set Bool)) (z2 Int))
  (=> (is_finite_subset bool (t2tb14 z) (t2tb14 z1) z2)
  (or
  (or (exists ((s (set Bool))) (and (and (= z empty1) (= z1 s)) (= z2 0)))
  (exists ((x Bool) (s1 (set Bool)) (s2 (set Bool)) (c Int))
  (and (is_finite_subset bool (t2tb14 s1) (t2tb14 s2) c)
  (and (mem bool (t2tb13 x) (t2tb14 s2))
  (and (mem bool (t2tb13 x) (t2tb14 s1))
  (and (and (= z (add1 x s1)) (= z1 s2)) (= z2 c)))))))
  (exists ((x Bool) (s1 (set Bool)) (s2 (set Bool)) (c Int))
  (and (is_finite_subset bool (t2tb14 s1) (t2tb14 s2) c)
  (and (mem bool (t2tb13 x) (t2tb14 s2))
  (and (not (mem bool (t2tb13 x) (t2tb14 s1)))
  (and (and (= z (add1 x s1)) (= z1 s2)) (= z2 (+ c 1)))))))))))

;; is_finite_subset_inversion
  (assert
  (forall ((z (set Int)) (z1 (set Int)) (z2 Int))
  (=> (is_finite_subset int (t2tb15 z) (t2tb15 z1) z2)
  (or
  (or (exists ((s (set Int))) (and (and (= z empty2) (= z1 s)) (= z2 0)))
  (exists ((x Int) (s1 (set Int)) (s2 (set Int)) (c Int))
  (and (is_finite_subset int (t2tb15 s1) (t2tb15 s2) c)
  (and (mem int (t2tb16 x) (t2tb15 s2))
  (and (mem int (t2tb16 x) (t2tb15 s1))
  (and (and (= z (add2 x s1)) (= z1 s2)) (= z2 c)))))))
  (exists ((x Int) (s1 (set Int)) (s2 (set Int)) (c Int))
  (and (is_finite_subset int (t2tb15 s1) (t2tb15 s2) c)
  (and (mem int (t2tb16 x) (t2tb15 s2))
  (and (not (mem int (t2tb16 x) (t2tb15 s1)))
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
  (=> (<= a b) (is_finite_subset int (t2tb15 (mk a b)) (t2tb15 integer)
  (+ (- b a) 1)))))

;; finite_interval_empty
  (assert
  (forall ((a Int) (b Int))
  (=> (< b a) (is_finite_subset int (t2tb15 (mk a b)) (t2tb15 integer) 0))))

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
  (forall ((s (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))))) (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))) (t2tb empty6)
  (finite_subsets
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb s)))))

;; finite_Empty
  (assert
  (forall ((s (set (set uninterpreted_type)))) (mem
  (set1 (set1 uninterpreted_type1)) (t2tb2 empty5)
  (finite_subsets (set1 uninterpreted_type1) (t2tb2 s)))))

;; finite_Empty
  (assert
  (forall ((s (set uninterpreted_type))) (mem (set1 uninterpreted_type1)
  (t2tb3 empty4) (finite_subsets uninterpreted_type1 (t2tb3 s)))))

;; finite_Empty
  (assert
  (forall ((s (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb5 empty3)
  (finite_subsets
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb5 s)))))

;; finite_Empty
  (assert
  (forall ((s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))) (mem
  (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb7 empty7)
  (finite_subsets (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb7 s)))))

;; finite_Empty
  (assert
  (forall ((s (set (tuple2 (tuple2 Bool Bool) Bool)))) (mem
  (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb9 empty8)
  (finite_subsets (tuple21 (tuple21 bool bool) bool) (t2tb9 s)))))

;; finite_Empty
  (assert
  (forall ((s (set (tuple2 Bool Bool)))) (mem (set1 (tuple21 bool bool))
  (t2tb11 empty9) (finite_subsets (tuple21 bool bool) (t2tb11 s)))))

;; finite_Empty
  (assert
  (forall ((s (set Bool))) (mem (set1 bool) (t2tb14 empty1)
  (finite_subsets bool (t2tb14 s)))))

;; finite_Empty
  (assert
  (forall ((s (set Int))) (mem (set1 int) (t2tb15 empty2)
  (finite_subsets int (t2tb15 s)))))

;; finite_Empty
  (assert
  (forall ((a ty))
  (forall ((s uni)) (mem (set1 a) (empty a) (finite_subsets a s)))))

;; finite_Add
  (assert
  (forall ((x (set uninterpreted_type)) (s1 (set (set uninterpreted_type)))
  (s2 (set (set uninterpreted_type))))
  (=> (mem (set1 (set1 uninterpreted_type1)) (t2tb2 s1)
  (finite_subsets (set1 uninterpreted_type1) (t2tb2 s2)))
  (=> (mem (set1 uninterpreted_type1) (t2tb3 x) (t2tb2 s2)) (mem
  (set1 (set1 uninterpreted_type1)) (t2tb2 (add3 x s1))
  (finite_subsets (set1 uninterpreted_type1) (t2tb2 s2)))))))

;; finite_Add
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (s1 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (s2 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (=> (mem (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (t2tb7 s1)
  (finite_subsets (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb7 s2)))
  (=> (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 x)
  (t2tb7 s2)) (mem (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (t2tb7 (add4 x s1))
  (finite_subsets (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb7 s2)))))))

;; finite_Add
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)) (s1 (set (tuple2 (tuple2 Bool
  Bool) Bool))) (s2 (set (tuple2 (tuple2 Bool Bool) Bool))))
  (=> (mem (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb9 s1)
  (finite_subsets (tuple21 (tuple21 bool bool) bool) (t2tb9 s2)))
  (=> (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb9 s2)) (mem
  (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb9 (add5 x s1))
  (finite_subsets (tuple21 (tuple21 bool bool) bool) (t2tb9 s2)))))))

;; finite_Add
  (assert
  (forall ((x (tuple2 Bool Bool)) (s1 (set (tuple2 Bool Bool)))
  (s2 (set (tuple2 Bool Bool))))
  (=> (mem (set1 (tuple21 bool bool)) (t2tb11 s1)
  (finite_subsets (tuple21 bool bool) (t2tb11 s2)))
  (=> (mem (tuple21 bool bool) (t2tb12 x) (t2tb11 s2)) (mem
  (set1 (tuple21 bool bool)) (t2tb11 (add6 x s1))
  (finite_subsets (tuple21 bool bool) (t2tb11 s2)))))))

;; finite_Add
  (assert
  (forall ((x Bool) (s1 (set Bool)) (s2 (set Bool)))
  (=> (mem (set1 bool) (t2tb14 s1) (finite_subsets bool (t2tb14 s2)))
  (=> (mem bool (t2tb13 x) (t2tb14 s2)) (mem (set1 bool) (t2tb14 (add1 x s1))
  (finite_subsets bool (t2tb14 s2)))))))

;; finite_Add
  (assert
  (forall ((x Int) (s1 (set Int)) (s2 (set Int)))
  (=> (mem (set1 int) (t2tb15 s1) (finite_subsets int (t2tb15 s2)))
  (=> (mem int (t2tb16 x) (t2tb15 s2)) (mem (set1 int) (t2tb15 (add2 x s1))
  (finite_subsets int (t2tb15 s2)))))))

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
  (forall ((s1 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))) (s2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type)))))
  (=> (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))) (t2tb s1)
  (finite_subsets
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb s2)))
  (or (= s1 empty6)
  (exists ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type))) (s3 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type)))))
  (and
  (= s1 (tb2t
        (add
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 uninterpreted_type1)) (t2tb1 x) (t2tb s3))))
  (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))) (t2tb s3)
  (finite_subsets
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb s2)))))))))

;; finite_inversion
  (assert
  (forall ((s1 (set (set uninterpreted_type)))
  (s2 (set (set uninterpreted_type))))
  (=> (mem (set1 (set1 uninterpreted_type1)) (t2tb2 s1)
  (finite_subsets (set1 uninterpreted_type1) (t2tb2 s2)))
  (or (= s1 empty5)
  (exists ((x (set uninterpreted_type)) (s3 (set (set uninterpreted_type))))
  (and (= s1 (add3 x s3)) (mem (set1 (set1 uninterpreted_type1)) (t2tb2 s3)
  (finite_subsets (set1 uninterpreted_type1) (t2tb2 s2)))))))))

;; finite_inversion
  (assert
  (forall ((s1 (set uninterpreted_type)) (s2 (set uninterpreted_type)))
  (=> (mem (set1 uninterpreted_type1) (t2tb3 s1)
  (finite_subsets uninterpreted_type1 (t2tb3 s2)))
  (or (= s1 empty4)
  (exists ((x uninterpreted_type) (s3 (set uninterpreted_type)))
  (and (= s1 (tb2t3 (add uninterpreted_type1 (t2tb4 x) (t2tb3 s3)))) (mem
  (set1 uninterpreted_type1) (t2tb3 s3)
  (finite_subsets uninterpreted_type1 (t2tb3 s2)))))))))

;; finite_inversion
  (assert
  (forall ((s1 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))))
  (=> (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb5 s1)
  (finite_subsets
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb5 s2)))
  (or (= s1 empty3)
  (exists ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))) (s3 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))
  (and
  (= s1 (tb2t5
        (add
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int)) (t2tb6 x) (t2tb5 s3))))
  (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb5 s3)
  (finite_subsets
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb5 s2)))))))))

;; finite_inversion
  (assert
  (forall ((s1 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (s2 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (=> (mem (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (t2tb7 s1)
  (finite_subsets (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb7 s2)))
  (or (= s1 empty7)
  (exists ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (s3 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (and (= s1 (add4 x s3)) (mem
  (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb7 s3)
  (finite_subsets (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb7 s2)))))))))

;; finite_inversion
  (assert
  (forall ((s1 (set (tuple2 (tuple2 Bool Bool) Bool)))
  (s2 (set (tuple2 (tuple2 Bool Bool) Bool))))
  (=> (mem (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb9 s1)
  (finite_subsets (tuple21 (tuple21 bool bool) bool) (t2tb9 s2)))
  (or (= s1 empty8)
  (exists ((x (tuple2 (tuple2 Bool Bool) Bool)) (s3 (set (tuple2 (tuple2 Bool
  Bool) Bool))))
  (and (= s1 (add5 x s3)) (mem (set1 (tuple21 (tuple21 bool bool) bool))
  (t2tb9 s3) (finite_subsets (tuple21 (tuple21 bool bool) bool) (t2tb9 s2)))))))))

;; finite_inversion
  (assert
  (forall ((s1 (set (tuple2 Bool Bool))) (s2 (set (tuple2 Bool Bool))))
  (=> (mem (set1 (tuple21 bool bool)) (t2tb11 s1)
  (finite_subsets (tuple21 bool bool) (t2tb11 s2)))
  (or (= s1 empty9)
  (exists ((x (tuple2 Bool Bool)) (s3 (set (tuple2 Bool Bool))))
  (and (= s1 (add6 x s3)) (mem (set1 (tuple21 bool bool)) (t2tb11 s3)
  (finite_subsets (tuple21 bool bool) (t2tb11 s2)))))))))

;; finite_inversion
  (assert
  (forall ((s1 (set Bool)) (s2 (set Bool)))
  (=> (mem (set1 bool) (t2tb14 s1) (finite_subsets bool (t2tb14 s2)))
  (or (= s1 empty1)
  (exists ((x Bool) (s3 (set Bool)))
  (and (= s1 (add1 x s3)) (mem (set1 bool) (t2tb14 s3)
  (finite_subsets bool (t2tb14 s2)))))))))

;; finite_inversion
  (assert
  (forall ((s1 (set Int)) (s2 (set Int)))
  (=> (mem (set1 int) (t2tb15 s1) (finite_subsets int (t2tb15 s2)))
  (or (= s1 empty2)
  (exists ((x Int) (s3 (set Int)))
  (and (= s1 (add2 x s3)) (mem (set1 int) (t2tb15 s3)
  (finite_subsets int (t2tb15 s2)))))))))

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
  (forall ((s (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))) (x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type)))))
  (= (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))) (t2tb x)
  (non_empty_finite_subsets
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb s)))
  (exists ((c Int))
  (and (is_finite_subset
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb x) (t2tb s) c) (not (= x empty6)))))))

;; non_empty_finite_subsets_def
  (assert
  (forall ((s (set (set uninterpreted_type)))
  (x (set (set uninterpreted_type))))
  (= (mem (set1 (set1 uninterpreted_type1)) (t2tb2 x)
  (non_empty_finite_subsets (set1 uninterpreted_type1) (t2tb2 s)))
  (exists ((c Int))
  (and (is_finite_subset (set1 uninterpreted_type1) (t2tb2 x) (t2tb2 s) c)
  (not (= x empty5)))))))

;; non_empty_finite_subsets_def
  (assert
  (forall ((s (set uninterpreted_type)) (x (set uninterpreted_type)))
  (= (mem (set1 uninterpreted_type1) (t2tb3 x)
  (non_empty_finite_subsets uninterpreted_type1 (t2tb3 s)))
  (exists ((c Int))
  (and (is_finite_subset uninterpreted_type1 (t2tb3 x) (t2tb3 s) c)
  (not (= x empty4)))))))

;; non_empty_finite_subsets_def
  (assert
  (forall ((s (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))
  (= (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb5 x)
  (non_empty_finite_subsets
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb5 s)))
  (exists ((c Int))
  (and (is_finite_subset
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb5 x) (t2tb5 s) c) (not (= x empty3)))))))

;; non_empty_finite_subsets_def
  (assert
  (forall ((s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (x (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (= (mem (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb7 x)
  (non_empty_finite_subsets (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb7 s)))
  (exists ((c Int))
  (and (is_finite_subset (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb7 x) (t2tb7 s) c) (not (= x empty7)))))))

;; non_empty_finite_subsets_def
  (assert
  (forall ((s (set (tuple2 (tuple2 Bool Bool) Bool)))
  (x (set (tuple2 (tuple2 Bool Bool) Bool))))
  (= (mem (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb9 x)
  (non_empty_finite_subsets (tuple21 (tuple21 bool bool) bool) (t2tb9 s)))
  (exists ((c Int))
  (and (is_finite_subset (tuple21 (tuple21 bool bool) bool) (t2tb9 x)
  (t2tb9 s) c) (not (= x empty8)))))))

;; non_empty_finite_subsets_def
  (assert
  (forall ((s (set (tuple2 Bool Bool))) (x (set (tuple2 Bool Bool))))
  (= (mem (set1 (tuple21 bool bool)) (t2tb11 x)
  (non_empty_finite_subsets (tuple21 bool bool) (t2tb11 s)))
  (exists ((c Int))
  (and (is_finite_subset (tuple21 bool bool) (t2tb11 x) (t2tb11 s) c)
  (not (= x empty9)))))))

;; non_empty_finite_subsets_def
  (assert
  (forall ((s (set Bool)) (x (set Bool)))
  (= (mem (set1 bool) (t2tb14 x) (non_empty_finite_subsets bool (t2tb14 s)))
  (exists ((c Int))
  (and (is_finite_subset bool (t2tb14 x) (t2tb14 s) c) (not (= x empty1)))))))

;; non_empty_finite_subsets_def
  (assert
  (forall ((s (set Int)) (x (set Int)))
  (= (mem (set1 int) (t2tb15 x) (non_empty_finite_subsets int (t2tb15 s)))
  (exists ((c Int))
  (and (is_finite_subset int (t2tb15 x) (t2tb15 s) c) (not (= x empty2)))))))

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
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1)) (t2tb empty6)) 0))

;; card_Empty
  (assert (= (card (set1 uninterpreted_type1) (t2tb2 empty5)) 0))

;; card_Empty
  (assert (= (card uninterpreted_type1 (t2tb3 empty4)) 0))

;; card_Empty
  (assert
  (= (card
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
     (t2tb5 empty3)) 0))

;; card_Empty
  (assert
  (= (card (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb7 empty7)) 0))

;; card_Empty
  (assert (= (card (tuple21 (tuple21 bool bool) bool) (t2tb9 empty8)) 0))

;; card_Empty
  (assert (= (card (tuple21 bool bool) (t2tb11 empty9)) 0))

;; card_Empty
  (assert (= (card bool (t2tb14 empty1)) 0))

;; card_Empty
  (assert (= (card int (t2tb15 empty2)) 0))

;; card_Empty
  (assert (forall ((a ty)) (= (card a (empty a)) 0)))

;; card_Add_not_mem
  (assert
  (forall ((x (set uninterpreted_type)) (s1 (set (set uninterpreted_type)))
  (s2 (set (set uninterpreted_type))))
  (! (=> (mem (set1 (set1 uninterpreted_type1)) (t2tb2 s1)
     (finite_subsets (set1 uninterpreted_type1) (t2tb2 s2)))
     (=> (not (mem (set1 uninterpreted_type1) (t2tb3 x) (t2tb2 s1)))
     (= (card (set1 uninterpreted_type1) (t2tb2 (add3 x s1))) (+ (card
                                                                 (set1
                                                                 uninterpreted_type1)
                                                                 (t2tb2 s1)) 1)))) :pattern ((mem
  (set1 (set1 uninterpreted_type1)) (t2tb2 s1)
  (finite_subsets (set1 uninterpreted_type1) (t2tb2 s2)))
  (card (set1 uninterpreted_type1) (t2tb2 (add3 x s1)))) )))

;; card_Add_not_mem
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (s1 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (s2 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (! (=> (mem (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
     (t2tb7 s1)
     (finite_subsets (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (t2tb7 s2)))
     (=>
     (not (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 x)
     (t2tb7 s1)))
     (= (card (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (t2tb7 (add4 x s1))) (+ (card
                                (tuple21 (tuple21 (tuple21 bool bool) bool)
                                bool) (t2tb7 s1)) 1)))) :pattern ((mem
  (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb7 s1)
  (finite_subsets (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb7 s2)))
  (card (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb7 (add4 x s1)))) )))

;; card_Add_not_mem
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)) (s1 (set (tuple2 (tuple2 Bool
  Bool) Bool))) (s2 (set (tuple2 (tuple2 Bool Bool) Bool))))
  (! (=> (mem (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb9 s1)
     (finite_subsets (tuple21 (tuple21 bool bool) bool) (t2tb9 s2)))
     (=> (not (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb9 s1)))
     (= (card (tuple21 (tuple21 bool bool) bool) (t2tb9 (add5 x s1))) (+ 
     (card (tuple21 (tuple21 bool bool) bool) (t2tb9 s1)) 1)))) :pattern ((mem
  (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb9 s1)
  (finite_subsets (tuple21 (tuple21 bool bool) bool) (t2tb9 s2)))
  (card (tuple21 (tuple21 bool bool) bool) (t2tb9 (add5 x s1)))) )))

;; card_Add_not_mem
  (assert
  (forall ((x (tuple2 Bool Bool)) (s1 (set (tuple2 Bool Bool)))
  (s2 (set (tuple2 Bool Bool))))
  (! (=> (mem (set1 (tuple21 bool bool)) (t2tb11 s1)
     (finite_subsets (tuple21 bool bool) (t2tb11 s2)))
     (=> (not (mem (tuple21 bool bool) (t2tb12 x) (t2tb11 s1)))
     (= (card (tuple21 bool bool) (t2tb11 (add6 x s1))) (+ (card
                                                           (tuple21 bool
                                                           bool) (t2tb11 s1)) 1)))) :pattern ((mem
  (set1 (tuple21 bool bool)) (t2tb11 s1)
  (finite_subsets (tuple21 bool bool) (t2tb11 s2)))
  (card (tuple21 bool bool) (t2tb11 (add6 x s1)))) )))

;; card_Add_not_mem
  (assert
  (forall ((x Bool) (s1 (set Bool)) (s2 (set Bool)))
  (! (=> (mem (set1 bool) (t2tb14 s1) (finite_subsets bool (t2tb14 s2)))
     (=> (not (mem bool (t2tb13 x) (t2tb14 s1)))
     (= (card bool (t2tb14 (add1 x s1))) (+ (card bool (t2tb14 s1)) 1)))) :pattern ((mem
  (set1 bool) (t2tb14 s1) (finite_subsets bool (t2tb14 s2)))
  (card bool (t2tb14 (add1 x s1)))) )))

;; card_Add_not_mem
  (assert
  (forall ((x Int) (s1 (set Int)) (s2 (set Int)))
  (! (=> (mem (set1 int) (t2tb15 s1) (finite_subsets int (t2tb15 s2)))
     (=> (not (mem int (t2tb16 x) (t2tb15 s1)))
     (= (card int (t2tb15 (add2 x s1))) (+ (card int (t2tb15 s1)) 1)))) :pattern ((mem
  (set1 int) (t2tb15 s1) (finite_subsets int (t2tb15 s2)))
  (card int (t2tb15 (add2 x s1)))) )))

;; card_Add_not_mem
  (assert
  (forall ((a ty))
  (forall ((x uni) (s1 uni) (s2 uni))
  (! (=> (mem (set1 a) s1 (finite_subsets a s2))
     (=> (not (mem a x s1)) (= (card a (add a x s1)) (+ (card a s1) 1)))) :pattern ((mem
  (set1 a) s1 (finite_subsets a s2)) (card a (add a x s1))) ))))

;; card_Add_mem
  (assert
  (forall ((x (set uninterpreted_type)) (s1 (set (set uninterpreted_type)))
  (s2 (set (set uninterpreted_type))))
  (! (=> (mem (set1 (set1 uninterpreted_type1)) (t2tb2 s1)
     (finite_subsets (set1 uninterpreted_type1) (t2tb2 s2)))
     (=> (mem (set1 uninterpreted_type1) (t2tb3 x) (t2tb2 s1))
     (= (card (set1 uninterpreted_type1) (t2tb2 (add3 x s1))) (card
                                                              (set1
                                                              uninterpreted_type1)
                                                              (t2tb2 s1))))) :pattern ((mem
  (set1 (set1 uninterpreted_type1)) (t2tb2 s1)
  (finite_subsets (set1 uninterpreted_type1) (t2tb2 s2)))
  (card (set1 uninterpreted_type1) (t2tb2 (add3 x s1)))) )))

;; card_Add_mem
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (s1 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (s2 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (! (=> (mem (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
     (t2tb7 s1)
     (finite_subsets (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (t2tb7 s2)))
     (=> (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 x)
     (t2tb7 s1))
     (= (card (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (t2tb7 (add4 x s1))) (card
                             (tuple21 (tuple21 (tuple21 bool bool) bool)
                             bool) (t2tb7 s1))))) :pattern ((mem
  (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb7 s1)
  (finite_subsets (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb7 s2)))
  (card (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb7 (add4 x s1)))) )))

;; card_Add_mem
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)) (s1 (set (tuple2 (tuple2 Bool
  Bool) Bool))) (s2 (set (tuple2 (tuple2 Bool Bool) Bool))))
  (! (=> (mem (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb9 s1)
     (finite_subsets (tuple21 (tuple21 bool bool) bool) (t2tb9 s2)))
     (=> (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb9 s1))
     (= (card (tuple21 (tuple21 bool bool) bool) (t2tb9 (add5 x s1))) 
     (card (tuple21 (tuple21 bool bool) bool) (t2tb9 s1))))) :pattern ((mem
  (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb9 s1)
  (finite_subsets (tuple21 (tuple21 bool bool) bool) (t2tb9 s2)))
  (card (tuple21 (tuple21 bool bool) bool) (t2tb9 (add5 x s1)))) )))

;; card_Add_mem
  (assert
  (forall ((x (tuple2 Bool Bool)) (s1 (set (tuple2 Bool Bool)))
  (s2 (set (tuple2 Bool Bool))))
  (! (=> (mem (set1 (tuple21 bool bool)) (t2tb11 s1)
     (finite_subsets (tuple21 bool bool) (t2tb11 s2)))
     (=> (mem (tuple21 bool bool) (t2tb12 x) (t2tb11 s1))
     (= (card (tuple21 bool bool) (t2tb11 (add6 x s1))) (card
                                                        (tuple21 bool bool)
                                                        (t2tb11 s1))))) :pattern ((mem
  (set1 (tuple21 bool bool)) (t2tb11 s1)
  (finite_subsets (tuple21 bool bool) (t2tb11 s2)))
  (card (tuple21 bool bool) (t2tb11 (add6 x s1)))) )))

;; card_Add_mem
  (assert
  (forall ((x Bool) (s1 (set Bool)) (s2 (set Bool)))
  (! (=> (mem (set1 bool) (t2tb14 s1) (finite_subsets bool (t2tb14 s2)))
     (=> (mem bool (t2tb13 x) (t2tb14 s1))
     (= (card bool (t2tb14 (add1 x s1))) (card bool (t2tb14 s1))))) :pattern ((mem
  (set1 bool) (t2tb14 s1) (finite_subsets bool (t2tb14 s2)))
  (card bool (t2tb14 (add1 x s1)))) )))

;; card_Add_mem
  (assert
  (forall ((x Int) (s1 (set Int)) (s2 (set Int)))
  (! (=> (mem (set1 int) (t2tb15 s1) (finite_subsets int (t2tb15 s2)))
     (=> (mem int (t2tb16 x) (t2tb15 s1))
     (= (card int (t2tb15 (add2 x s1))) (card int (t2tb15 s1))))) :pattern ((mem
  (set1 int) (t2tb15 s1) (finite_subsets int (t2tb15 s2)))
  (card int (t2tb15 (add2 x s1)))) )))

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

(declare-fun times1 ((set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (set (set uninterpreted_type))) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type))))

(declare-fun times2 ((set (tuple2 (tuple2 Bool Bool) Bool))
  (set Bool)) (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))

(declare-fun times3 ((set (tuple2 Bool Bool))
  (set Bool)) (set (tuple2 (tuple2 Bool Bool) Bool)))

(declare-fun times4 ((set Bool) (set Bool)) (set (tuple2 Bool Bool)))

;; times_def
  (assert
  (forall ((a (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (b (set (set uninterpreted_type))) (x (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool)) (y (set uninterpreted_type)))
  (! (= (mem
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1))
     (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1) (t2tb8 x) (t2tb3 y)) (t2tb (times1 a b)))
     (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 x)
     (t2tb7 a)) (mem (set1 uninterpreted_type1) (t2tb3 y) (t2tb2 b)))) :pattern ((mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1) (t2tb8 x) (t2tb3 y)) (t2tb (times1 a b)))) )))

;; times_def
  (assert
  (forall ((a (set (tuple2 (tuple2 Bool Bool) Bool))) (b (set Bool))
  (x (tuple2 (tuple2 Bool Bool) Bool)) (y Bool))
  (! (= (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (t2tb8 (Tuple23 x y)) (t2tb7 (times2 a b)))
     (and (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb9 a)) (mem
     bool (t2tb13 y) (t2tb14 b)))) :pattern ((mem
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 (Tuple23 x y))
  (t2tb7 (times2 a b)))) )))

;; times_def
  (assert
  (forall ((a (set (tuple2 Bool Bool))) (b (set Bool)) (x (tuple2 Bool Bool))
  (y Bool))
  (! (= (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 x y))
     (t2tb9 (times3 a b)))
     (and (mem (tuple21 bool bool) (t2tb12 x) (t2tb11 a)) (mem bool
     (t2tb13 y) (t2tb14 b)))) :pattern ((mem
  (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 x y))
  (t2tb9 (times3 a b)))) )))

;; times_def
  (assert
  (forall ((a (set Bool)) (b (set Bool)) (x Bool) (y Bool))
  (! (= (mem (tuple21 bool bool) (t2tb12 (Tuple21 x y))
     (t2tb11 (times4 a b)))
     (and (mem bool (t2tb13 x) (t2tb14 a)) (mem bool (t2tb13 y) (t2tb14 b)))) :pattern ((mem
  (tuple21 bool bool) (t2tb12 (Tuple21 x y)) (t2tb11 (times4 a b)))) )))

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
  (v (set (set uninterpreted_type))))
  (= (tb2t17
     (relations (set1 uninterpreted_type1)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb7 u) (t2tb2 v))) 
  (tb2t17
  (power
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb (times1 u v)))))))

;; relations_def
  (assert
  (forall ((u (set (tuple2 (tuple2 Bool Bool) Bool))) (v (set Bool)))
  (= (tb2t20
     (relations bool (tuple21 (tuple21 bool bool) bool) (t2tb9 u) (t2tb14 v))) 
  (tb2t20
  (power (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb7 (times2 u v)))))))

;; relations_def
  (assert
  (forall ((u (set (tuple2 Bool Bool))) (v (set Bool)))
  (= (tb2t21 (relations bool (tuple21 bool bool) (t2tb11 u) (t2tb14 v))) 
  (tb2t21 (power (tuple21 (tuple21 bool bool) bool) (t2tb9 (times3 u v)))))))

;; relations_def
  (assert
  (forall ((u (set Bool)) (v (set Bool)))
  (= (tb2t22 (relations bool bool (t2tb14 u) (t2tb14 v))) (tb2t22
                                                          (power
                                                          (tuple21 bool bool)
                                                          (t2tb11
                                                          (times4 u v)))))))

;; relations_def
  (assert
  (forall ((a ty) (b ty))
  (forall ((u uni) (v uni))
  (= (relations b a u v) (power (tuple21 a b) (times b a u v))))))

;; break_mem_in_add
  (assert
  (forall ((c (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (x (tuple2 (tuple2 Bool Bool) Bool)) (y Bool))
  (= (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 c)
  (t2tb7 (add4 (Tuple23 x y) s)))
  (or (= c (Tuple23 x y)) (mem
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 c) (t2tb7 s))))))

;; break_mem_in_add
  (assert
  (forall ((c (tuple2 (tuple2 Bool Bool) Bool)) (s (set (tuple2 (tuple2 Bool
  Bool) Bool))) (x (tuple2 Bool Bool)) (y Bool))
  (= (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 c)
  (t2tb9 (add5 (Tuple22 x y) s)))
  (or (= c (Tuple22 x y)) (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 c)
  (t2tb9 s))))))

;; break_mem_in_add
  (assert
  (forall ((c (tuple2 Bool Bool)) (s (set (tuple2 Bool Bool))) (x Bool)
  (y Bool))
  (= (mem (tuple21 bool bool) (t2tb12 c) (t2tb11 (add6 (Tuple21 x y) s)))
  (or (= c (Tuple21 x y)) (mem (tuple21 bool bool) (t2tb12 c) (t2tb11 s))))))

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
  (set uninterpreted_type)))) (u (set (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool))) (v (set (set uninterpreted_type))))
  (= (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))) (t2tb r)
  (power
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb (times1 u v)))) (subset
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb r) (t2tb (times1 u v))))))

;; break_power_times
  (assert
  (forall ((r (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (u (set (tuple2 (tuple2 Bool Bool) Bool))) (v (set Bool)))
  (= (mem (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb7 r)
  (power (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb7 (times2 u v)))) (subset
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb7 r)
  (t2tb7 (times2 u v))))))

;; break_power_times
  (assert
  (forall ((r (set (tuple2 (tuple2 Bool Bool) Bool))) (u (set (tuple2 Bool
  Bool))) (v (set Bool)))
  (= (mem (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb9 r)
  (power (tuple21 (tuple21 bool bool) bool) (t2tb9 (times3 u v)))) (subset
  (tuple21 (tuple21 bool bool) bool) (t2tb9 r) (t2tb9 (times3 u v))))))

;; break_power_times
  (assert
  (forall ((r (set (tuple2 Bool Bool))) (u (set Bool)) (v (set Bool)))
  (= (mem (set1 (tuple21 bool bool)) (t2tb11 r)
  (power (tuple21 bool bool) (t2tb11 (times4 u v)))) (subset
  (tuple21 bool bool) (t2tb11 r) (t2tb11 (times4 u v))))))

;; break_power_times
  (assert
  (forall ((a ty) (b ty))
  (forall ((r uni) (u uni) (v uni))
  (= (mem (set1 (tuple21 a b)) r (power (tuple21 a b) (times b a u v)))
  (subset (tuple21 a b) r (times b a u v))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))) (u (set (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool))) (v (set (set uninterpreted_type))))
  (= (subset
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb r) (t2tb (times1 u v)))
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (y (set uninterpreted_type)))
  (=> (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1) (t2tb8 x) (t2tb3 y)) (t2tb r))
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 x)
  (t2tb7 u)) (mem (set1 uninterpreted_type1) (t2tb3 y) (t2tb2 v))))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (u (set (tuple2 (tuple2 Bool Bool) Bool))) (v (set Bool)))
  (= (subset (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb7 r)
  (t2tb7 (times2 u v)))
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)) (y Bool))
  (=> (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb8 (Tuple23 x y)) (t2tb7 r))
  (and (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb9 u)) (mem
  bool (t2tb13 y) (t2tb14 v))))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 (tuple2 Bool Bool) Bool))) (u (set (tuple2 Bool
  Bool))) (v (set Bool)))
  (= (subset (tuple21 (tuple21 bool bool) bool) (t2tb9 r)
  (t2tb9 (times3 u v)))
  (forall ((x (tuple2 Bool Bool)) (y Bool))
  (=> (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 x y))
  (t2tb9 r))
  (and (mem (tuple21 bool bool) (t2tb12 x) (t2tb11 u)) (mem bool (t2tb13 y)
  (t2tb14 v))))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 Bool Bool))) (u (set Bool)) (v (set Bool)))
  (= (subset (tuple21 bool bool) (t2tb11 r) (t2tb11 (times4 u v)))
  (forall ((x Bool) (y Bool))
  (=> (mem (tuple21 bool bool) (t2tb12 (Tuple21 x y)) (t2tb11 r))
  (and (mem bool (t2tb13 x) (t2tb14 u)) (mem bool (t2tb13 y) (t2tb14 v))))))))

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
  (forall ((s uni) (x uni) (y (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type))))
  (! (=> (mem a x s)
     (= (tb2t1
        (apply
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 uninterpreted_type1)) a
        (times
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 uninterpreted_type1)) a s
        (add
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 uninterpreted_type1)) (t2tb1 y) (t2tb empty6))) x)) y)) :pattern (
  (tb2t1
  (apply
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) a
  (times
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) a s
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1)) (t2tb1 y) (t2tb empty6))) x))) ))))

;; apply_times
  (assert
  (forall ((a ty))
  (forall ((s uni) (x uni) (y (set uninterpreted_type)))
  (! (=> (mem a x s)
     (= (tb2t3
        (apply (set1 uninterpreted_type1) a
        (times (set1 uninterpreted_type1) a s (t2tb2 (add3 y empty5))) x)) y)) :pattern (
  (tb2t3
  (apply (set1 uninterpreted_type1) a
  (times (set1 uninterpreted_type1) a s (t2tb2 (add3 y empty5))) x))) ))))

;; apply_times
  (assert
  (forall ((a ty))
  (forall ((s uni) (x uni) (y uninterpreted_type))
  (! (=> (mem a x s)
     (= (tb2t4
        (apply uninterpreted_type1 a
        (times uninterpreted_type1 a s
        (add uninterpreted_type1 (t2tb4 y) (t2tb3 empty4))) x)) y)) :pattern (
  (tb2t4
  (apply uninterpreted_type1 a
  (times uninterpreted_type1 a s
  (add uninterpreted_type1 (t2tb4 y) (t2tb3 empty4))) x))) ))))

;; apply_times
  (assert
  (forall ((a ty))
  (forall ((s uni) (x uni) (y (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))
  (! (=> (mem a x s)
     (= (tb2t6
        (apply
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int)) a
        (times
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int)) a s
        (add
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int)) (t2tb6 y) (t2tb5 empty3))) x)) y)) :pattern ((tb2t6
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
                                                                 (t2tb6 y)
                                                                 (t2tb5
                                                                 empty3))) x))) ))))

;; apply_times
  (assert
  (forall ((a ty))
  (forall ((s uni) (x uni) (y (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool)))
  (! (=> (mem a x s)
     (= (tb2t8
        (apply (tuple21 (tuple21 (tuple21 bool bool) bool) bool) a
        (times (tuple21 (tuple21 (tuple21 bool bool) bool) bool) a s
        (t2tb7 (add4 y empty7))) x)) y)) :pattern ((tb2t8
                                                   (apply
                                                   (tuple21
                                                   (tuple21
                                                   (tuple21 bool bool) 
                                                   bool) bool) a
                                                   (times
                                                   (tuple21
                                                   (tuple21
                                                   (tuple21 bool bool) 
                                                   bool) bool) a s
                                                   (t2tb7 (add4 y empty7)))
                                                   x))) ))))

;; apply_times
  (assert
  (forall ((a ty))
  (forall ((s uni) (x uni) (y (tuple2 (tuple2 Bool Bool) Bool)))
  (! (=> (mem a x s)
     (= (tb2t10
        (apply (tuple21 (tuple21 bool bool) bool) a
        (times (tuple21 (tuple21 bool bool) bool) a s
        (t2tb9 (add5 y empty8))) x)) y)) :pattern ((tb2t10
                                                   (apply
                                                   (tuple21
                                                   (tuple21 bool bool) 
                                                   bool) a
                                                   (times
                                                   (tuple21
                                                   (tuple21 bool bool) 
                                                   bool) a s
                                                   (t2tb9 (add5 y empty8)))
                                                   x))) ))))

;; apply_times
  (assert
  (forall ((a ty))
  (forall ((s uni) (x uni) (y (tuple2 Bool Bool)))
  (! (=> (mem a x s)
     (= (tb2t12
        (apply (tuple21 bool bool) a
        (times (tuple21 bool bool) a s (t2tb11 (add6 y empty9))) x)) y)) :pattern (
  (tb2t12
  (apply (tuple21 bool bool) a
  (times (tuple21 bool bool) a s (t2tb11 (add6 y empty9))) x))) ))))

;; apply_times
  (assert
  (forall ((a ty))
  (forall ((s uni) (x uni) (y Bool))
  (! (=> (mem a x s)
     (= (tb2t13 (apply bool a (times bool a s (t2tb14 (add1 y empty1))) x)) y)) :pattern (
  (tb2t13 (apply bool a (times bool a s (t2tb14 (add1 y empty1))) x))) ))))

;; apply_times
  (assert
  (forall ((a ty))
  (forall ((s uni) (x uni) (y Int))
  (! (=> (mem a x s)
     (= (tb2t16 (apply int a (times int a s (t2tb15 (add2 y empty2))) x)) y)) :pattern (
  (tb2t16 (apply int a (times int a s (t2tb15 (add2 y empty2))) x))) ))))

;; apply_times
  (assert
  (forall ((s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (y (set uninterpreted_type)))
  (! (=> (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 x)
     (t2tb7 s)) (= (apply5 (times1 s (add3 y empty5)) x) y)) :pattern (
  (apply5 (times1 s (add3 y empty5)) x)) )))

;; apply_times
  (assert
  (forall ((s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)) (y (set Int)))
  (! (=> (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 x)
     (t2tb7 s))
     (= (apply4
        (tb2t5
        (times (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (t2tb7 s) (add (set1 int) (t2tb15 y) (empty (set1 int))))) x) y)) :pattern (
  (apply4
  (tb2t5
  (times (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb7 s) (add (set1 int) (t2tb15 y) (empty (set1 int))))) x)) )))

;; apply_times
  (assert
  (forall ((s (set (tuple2 (tuple2 Bool Bool) Bool))) (x (tuple2 (tuple2 Bool
  Bool) Bool)) (y Bool))
  (! (=> (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb9 s))
     (= (apply1 (times2 s (add1 y empty1)) x) y)) :pattern ((apply1
                                                            (times2 s
                                                            (add1 y empty1))
                                                            x)) )))

;; apply_times
  (assert
  (forall ((s (set (tuple2 Bool Bool))) (x (tuple2 Bool Bool)) (y Bool))
  (! (=> (mem (tuple21 bool bool) (t2tb12 x) (t2tb11 s))
     (= (apply2 (times3 s (add1 y empty1)) x) y)) :pattern ((apply2
                                                            (times3 s
                                                            (add1 y empty1))
                                                            x)) )))

;; apply_times
  (assert
  (forall ((s (set Bool)) (x Bool) (y Bool))
  (! (=> (mem bool (t2tb13 x) (t2tb14 s))
     (= (apply3 (times4 s (add1 y empty1)) x) y)) :pattern ((apply3
                                                            (times4 s
                                                            (add1 y empty1))
                                                            x)) )))

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
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)) (y Bool)
  (q (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (r (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (= (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb8 (Tuple23 x y))
  (infix_lspl bool (tuple21 (tuple21 bool bool) bool) (t2tb7 q) (t2tb7 r)))
  (ite (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x)
  (dom bool (tuple21 (tuple21 bool bool) bool) (t2tb7 r))) (mem
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 (Tuple23 x y))
  (t2tb7 r)) (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb8 (Tuple23 x y)) (t2tb7 q))))))

;; overriding_def
  (assert
  (forall ((x (tuple2 Bool Bool)) (y Bool) (q (set (tuple2 (tuple2 Bool Bool)
  Bool))) (r (set (tuple2 (tuple2 Bool Bool) Bool))))
  (= (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 x y))
  (infix_lspl bool (tuple21 bool bool) (t2tb9 q) (t2tb9 r)))
  (ite (mem (tuple21 bool bool) (t2tb12 x)
  (dom bool (tuple21 bool bool) (t2tb9 r))) (mem
  (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 x y)) (t2tb9 r)) (mem
  (tuple21 (tuple21 bool bool) bool) (t2tb10 (Tuple22 x y)) (t2tb9 q))))))

;; overriding_def
  (assert
  (forall ((x Bool) (y Bool) (q (set (tuple2 Bool Bool)))
  (r (set (tuple2 Bool Bool))))
  (= (mem (tuple21 bool bool) (t2tb12 (Tuple21 x y))
  (infix_lspl bool bool (t2tb11 q) (t2tb11 r)))
  (ite (mem bool (t2tb13 x) (dom bool bool (t2tb11 r))) (mem
  (tuple21 bool bool) (t2tb12 (Tuple21 x y)) (t2tb11 r)) (mem
  (tuple21 bool bool) (t2tb12 (Tuple21 x y)) (t2tb11 q))))))

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
  (forall ((s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (t (set (set uninterpreted_type)))
  (f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))) (g (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type))))
  (x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (! (=>
     (and (mem
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1))) (t2tb f)
     (infix_plmngt (set1 uninterpreted_type1)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb7 s) (t2tb2 t)))
     (mem
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1))) (t2tb g)
     (infix_plmngt (set1 uninterpreted_type1)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb7 s) (t2tb2 t))))
     (=> (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 x)
     (dom (set1 uninterpreted_type1)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb g)))
     (= (apply5
        (tb2t
        (infix_lspl (set1 uninterpreted_type1)
        (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb f) (t2tb g)))
        x) (apply5 g x)))) :pattern ((mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))) (t2tb f)
  (infix_plmngt (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb7 s) (t2tb2 t)))
  (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))) (t2tb g)
  (infix_plmngt (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb7 s) (t2tb2 t)))
  (apply5
  (tb2t
  (infix_lspl (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb f) (t2tb g))) x)) )))

;; apply_overriding_1
  (assert
  (forall ((s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (t (set (set Int))) (f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))) (g (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))) (x (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool)))
  (! (=>
     (and (mem
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb5 f)
     (infix_plmngt (set1 int)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb7 s) (t2tb24 t)))
     (mem
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb5 g)
     (infix_plmngt (set1 int)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb7 s) (t2tb24 t))))
     (=> (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 x)
     (dom (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (t2tb5 g)))
     (= (apply4
        (tb2t5
        (infix_lspl (set1 int)
        (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb5 f)
        (t2tb5 g))) x) (apply4 g x)))) :pattern ((mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb5 f)
  (infix_plmngt (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb7 s) (t2tb24 t))) (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb5 g)
  (infix_plmngt (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb7 s) (t2tb24 t)))
  (apply4
  (tb2t5
  (infix_lspl (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 f) (t2tb5 g))) x)) )))

;; apply_overriding_1
  (assert
  (forall ((s (set (tuple2 (tuple2 Bool Bool) Bool))) (t (set Bool))
  (f (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (g (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (x (tuple2 (tuple2 Bool Bool) Bool)))
  (! (=>
     (and (mem (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
     (t2tb7 f)
     (infix_plmngt bool (tuple21 (tuple21 bool bool) bool) (t2tb9 s)
     (t2tb14 t))) (mem
     (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb7 g)
     (infix_plmngt bool (tuple21 (tuple21 bool bool) bool) (t2tb9 s)
     (t2tb14 t))))
     (=> (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x)
     (dom bool (tuple21 (tuple21 bool bool) bool) (t2tb7 g)))
     (= (apply1
        (tb2t7
        (infix_lspl bool (tuple21 (tuple21 bool bool) bool) (t2tb7 f)
        (t2tb7 g))) x) (apply1 g x)))) :pattern ((mem
  (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb7 f)
  (infix_plmngt bool (tuple21 (tuple21 bool bool) bool) (t2tb9 s) (t2tb14 t)))
  (mem (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb7 g)
  (infix_plmngt bool (tuple21 (tuple21 bool bool) bool) (t2tb9 s) (t2tb14 t)))
  (apply1
  (tb2t7
  (infix_lspl bool (tuple21 (tuple21 bool bool) bool) (t2tb7 f) (t2tb7 g)))
  x)) )))

;; apply_overriding_1
  (assert
  (forall ((s (set (tuple2 Bool Bool))) (t (set Bool))
  (f (set (tuple2 (tuple2 Bool Bool) Bool))) (g (set (tuple2 (tuple2 Bool
  Bool) Bool))) (x (tuple2 Bool Bool)))
  (! (=>
     (and (mem (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb9 f)
     (infix_plmngt bool (tuple21 bool bool) (t2tb11 s) (t2tb14 t))) (mem
     (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb9 g)
     (infix_plmngt bool (tuple21 bool bool) (t2tb11 s) (t2tb14 t))))
     (=> (mem (tuple21 bool bool) (t2tb12 x)
     (dom bool (tuple21 bool bool) (t2tb9 g)))
     (= (apply2
        (tb2t9 (infix_lspl bool (tuple21 bool bool) (t2tb9 f) (t2tb9 g))) x) 
     (apply2 g x)))) :pattern ((mem
  (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb9 f)
  (infix_plmngt bool (tuple21 bool bool) (t2tb11 s) (t2tb14 t))) (mem
  (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb9 g)
  (infix_plmngt bool (tuple21 bool bool) (t2tb11 s) (t2tb14 t)))
  (apply2 (tb2t9 (infix_lspl bool (tuple21 bool bool) (t2tb9 f) (t2tb9 g)))
  x)) )))

;; apply_overriding_1
  (assert
  (forall ((s (set Bool)) (t (set Bool)) (f (set (tuple2 Bool Bool)))
  (g (set (tuple2 Bool Bool))) (x Bool))
  (! (=>
     (and (mem (set1 (tuple21 bool bool)) (t2tb11 f)
     (infix_plmngt bool bool (t2tb14 s) (t2tb14 t))) (mem
     (set1 (tuple21 bool bool)) (t2tb11 g)
     (infix_plmngt bool bool (t2tb14 s) (t2tb14 t))))
     (=> (mem bool (t2tb13 x) (dom bool bool (t2tb11 g)))
     (= (apply3 (tb2t11 (infix_lspl bool bool (t2tb11 f) (t2tb11 g))) x) 
     (apply3 g x)))) :pattern ((mem
  (set1 (tuple21 bool bool)) (t2tb11 f)
  (infix_plmngt bool bool (t2tb14 s) (t2tb14 t))) (mem
  (set1 (tuple21 bool bool)) (t2tb11 g)
  (infix_plmngt bool bool (t2tb14 s) (t2tb14 t)))
  (apply3 (tb2t11 (infix_lspl bool bool (t2tb11 f) (t2tb11 g))) x)) )))

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
  (forall ((s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (t (set (set uninterpreted_type)))
  (f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type)))) (g (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type))))
  (x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (! (=>
     (and (mem
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1))) (t2tb f)
     (infix_plmngt (set1 uninterpreted_type1)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb7 s) (t2tb2 t)))
     (mem
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type1))) (t2tb g)
     (infix_plmngt (set1 uninterpreted_type1)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb7 s) (t2tb2 t))))
     (=>
     (not (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 x)
     (dom (set1 uninterpreted_type1)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb g))))
     (=> (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 x)
     (dom (set1 uninterpreted_type1)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb f)))
     (= (apply5
        (tb2t
        (infix_lspl (set1 uninterpreted_type1)
        (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb f) (t2tb g)))
        x) (apply5 f x))))) :pattern ((mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))) (t2tb f)
  (infix_plmngt (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb7 s) (t2tb2 t)))
  (apply5
  (tb2t
  (infix_lspl (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb f) (t2tb g))) x)) :pattern ((mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type1))) (t2tb g)
  (infix_plmngt (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb7 s) (t2tb2 t)))
  (apply5
  (tb2t
  (infix_lspl (set1 uninterpreted_type1)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb f) (t2tb g))) x)) )))

;; apply_overriding_2
  (assert
  (forall ((s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (t (set (set Int))) (f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))) (g (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))) (x (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool)))
  (! (=>
     (and (mem
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb5 f)
     (infix_plmngt (set1 int)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb7 s) (t2tb24 t)))
     (mem
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb5 g)
     (infix_plmngt (set1 int)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb7 s) (t2tb24 t))))
     (=>
     (not (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 x)
     (dom (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (t2tb5 g))))
     (=> (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb8 x)
     (dom (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (t2tb5 f)))
     (= (apply4
        (tb2t5
        (infix_lspl (set1 int)
        (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb5 f)
        (t2tb5 g))) x) (apply4 f x))))) :pattern ((mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb5 f)
  (infix_plmngt (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb7 s) (t2tb24 t)))
  (apply4
  (tb2t5
  (infix_lspl (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 f) (t2tb5 g))) x)) :pattern ((mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb5 g)
  (infix_plmngt (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb7 s) (t2tb24 t)))
  (apply4
  (tb2t5
  (infix_lspl (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 f) (t2tb5 g))) x)) )))

;; apply_overriding_2
  (assert
  (forall ((s (set (tuple2 (tuple2 Bool Bool) Bool))) (t (set Bool))
  (f (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (g (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (x (tuple2 (tuple2 Bool Bool) Bool)))
  (! (=>
     (and (mem (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
     (t2tb7 f)
     (infix_plmngt bool (tuple21 (tuple21 bool bool) bool) (t2tb9 s)
     (t2tb14 t))) (mem
     (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb7 g)
     (infix_plmngt bool (tuple21 (tuple21 bool bool) bool) (t2tb9 s)
     (t2tb14 t))))
     (=>
     (not (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x)
     (dom bool (tuple21 (tuple21 bool bool) bool) (t2tb7 g))))
     (=> (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x)
     (dom bool (tuple21 (tuple21 bool bool) bool) (t2tb7 f)))
     (= (apply1
        (tb2t7
        (infix_lspl bool (tuple21 (tuple21 bool bool) bool) (t2tb7 f)
        (t2tb7 g))) x) (apply1 f x))))) :pattern ((mem
  (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb7 f)
  (infix_plmngt bool (tuple21 (tuple21 bool bool) bool) (t2tb9 s) (t2tb14 t)))
  (apply1
  (tb2t7
  (infix_lspl bool (tuple21 (tuple21 bool bool) bool) (t2tb7 f) (t2tb7 g)))
  x)) :pattern ((mem (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (t2tb7 g)
  (infix_plmngt bool (tuple21 (tuple21 bool bool) bool) (t2tb9 s) (t2tb14 t)))
  (apply1
  (tb2t7
  (infix_lspl bool (tuple21 (tuple21 bool bool) bool) (t2tb7 f) (t2tb7 g)))
  x)) )))

;; apply_overriding_2
  (assert
  (forall ((s (set (tuple2 Bool Bool))) (t (set Bool))
  (f (set (tuple2 (tuple2 Bool Bool) Bool))) (g (set (tuple2 (tuple2 Bool
  Bool) Bool))) (x (tuple2 Bool Bool)))
  (! (=>
     (and (mem (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb9 f)
     (infix_plmngt bool (tuple21 bool bool) (t2tb11 s) (t2tb14 t))) (mem
     (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb9 g)
     (infix_plmngt bool (tuple21 bool bool) (t2tb11 s) (t2tb14 t))))
     (=>
     (not (mem (tuple21 bool bool) (t2tb12 x)
     (dom bool (tuple21 bool bool) (t2tb9 g))))
     (=> (mem (tuple21 bool bool) (t2tb12 x)
     (dom bool (tuple21 bool bool) (t2tb9 f)))
     (= (apply2
        (tb2t9 (infix_lspl bool (tuple21 bool bool) (t2tb9 f) (t2tb9 g))) x) 
     (apply2 f x))))) :pattern ((mem
  (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb9 f)
  (infix_plmngt bool (tuple21 bool bool) (t2tb11 s) (t2tb14 t)))
  (apply2 (tb2t9 (infix_lspl bool (tuple21 bool bool) (t2tb9 f) (t2tb9 g)))
  x)) :pattern ((mem (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb9 g)
  (infix_plmngt bool (tuple21 bool bool) (t2tb11 s) (t2tb14 t)))
  (apply2 (tb2t9 (infix_lspl bool (tuple21 bool bool) (t2tb9 f) (t2tb9 g)))
  x)) )))

;; apply_overriding_2
  (assert
  (forall ((s (set Bool)) (t (set Bool)) (f (set (tuple2 Bool Bool)))
  (g (set (tuple2 Bool Bool))) (x Bool))
  (! (=>
     (and (mem (set1 (tuple21 bool bool)) (t2tb11 f)
     (infix_plmngt bool bool (t2tb14 s) (t2tb14 t))) (mem
     (set1 (tuple21 bool bool)) (t2tb11 g)
     (infix_plmngt bool bool (t2tb14 s) (t2tb14 t))))
     (=> (not (mem bool (t2tb13 x) (dom bool bool (t2tb11 g))))
     (=> (mem bool (t2tb13 x) (dom bool bool (t2tb11 f)))
     (= (apply3 (tb2t11 (infix_lspl bool bool (t2tb11 f) (t2tb11 g))) x) 
     (apply3 f x))))) :pattern ((mem
  (set1 (tuple21 bool bool)) (t2tb11 f)
  (infix_plmngt bool bool (t2tb14 s) (t2tb14 t)))
  (apply3 (tb2t11 (infix_lspl bool bool (t2tb11 f) (t2tb11 g))) x)) :pattern ((mem
  (set1 (tuple21 bool bool)) (t2tb11 g)
  (infix_plmngt bool bool (t2tb14 s) (t2tb14 t)))
  (apply3 (tb2t11 (infix_lspl bool bool (t2tb11 f) (t2tb11 g))) x)) )))

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

(declare-fun t2tb274 ((set enum_aa)) uni)

;; t2tb_sort
  (assert (forall ((x (set enum_aa))) (sort (set1 enum_aa1) (t2tb274 x))))

(declare-fun tb2t274 (uni) (set enum_aa))

;; BridgeL
  (assert
  (forall ((i (set enum_aa)))
  (! (= (tb2t274 (t2tb274 i)) i) :pattern ((t2tb274 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 enum_aa1) j) (= (t2tb274 (tb2t274 j)) j)) :pattern (
  (t2tb274 (tb2t274 j))) )))

(declare-fun t2tb275 (enum_aa) uni)

;; t2tb_sort
  (assert (forall ((x enum_aa)) (sort enum_aa1 (t2tb275 x))))

(declare-fun tb2t275 (uni) enum_aa)

;; BridgeL
  (assert
  (forall ((i enum_aa))
  (! (= (tb2t275 (t2tb275 i)) i) :pattern ((t2tb275 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort enum_aa1 j) (= (t2tb275 (tb2t275 j)) j)) :pattern ((t2tb275
                                                                  (tb2t275 j))) )))

;; set_enum_aa_axiom
  (assert
  (forall ((x enum_aa)) (mem enum_aa1 (t2tb275 x) (t2tb274 set_enum_aa))))

(declare-fun f1 ((set Int) (set Int) (set Int) Bool Bool Bool Bool Int
  (set Int) (set Int) (set Int) (set Int) Int Bool Bool Bool Bool Int Int Int
  Int Int Bool Bool Bool Bool Bool Int Int Int Int Int Int Int
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))) Int
  Int Int Int Int Int Int (set Int)) Bool)

;; f1_def
  (assert
  (forall ((v_zz (set Int)) (v_yy (set Int)) (v_xx (set Int)) (v_ww Bool)
  (v_vv Bool) (v_uu Bool) (v_tt Bool) (v_ss Int) (v_rr (set Int))
  (v_qq (set Int)) (v_pp (set Int)) (v_oo (set Int)) (v_nn Int) (v_mm Bool)
  (v_ll Bool) (v_kk Bool) (v_jj Bool) (v_bbzz Int) (v_bbyy Int) (v_bbxx Int)
  (v_bbww Int) (v_bbvv Int) (v_bbuu Bool) (v_bbtt Bool) (v_bbss Bool)
  (v_bbrr Bool) (v_bbqq Bool) (v_bbpp Int) (v_bboo Int) (v_bbnn Int)
  (v_bbmm Int) (v_bbll Int) (v_bbkk Int) (v_bbjj Int)
  (v_bbii (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (v_bbhh Int) (v_bbgg Int) (v_bbff Int) (v_bbee Int)
  (v_bbdd Int) (v_bbcc Int) (v_bbbb Int) (v_bbaa (set Int)))
  (= (f1 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbzz v_bbyy v_bbxx v_bbww v_bbvv v_bbuu v_bbtt v_bbss
  v_bbrr v_bbqq v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
  v_bbhh v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (= v_bbvv 0) (= v_bbww 1)) (mem int (t2tb16 v_bbxx)
  (t2tb15 integer))) (<= 0 v_bbxx)) (<= v_bbxx 2147483647)) (mem int
  (t2tb16 v_bbyy) (t2tb15 integer))) (<= 0 v_bbyy)) (<= v_bbyy 2147483647))
  (mem int (t2tb16 v_bbzz) (t2tb15 integer))) (<= 0 v_bbzz))
  (<= v_bbzz 2147483647)) (mem int (t2tb16 v_bbnn) (t2tb15 integer)))
  (<= 0 v_bbnn)) (<= v_bbnn 2147483647)) (<= 1 v_bbnn)) (<= v_bbnn 254))
  (= v_bbnn v_bbyy)) (mem int (t2tb16 v_bboo) (t2tb15 integer)))
  (<= 0 v_bboo)) (<= v_bboo 2147483647)) (<= 1 v_bboo)) (<= v_bboo 254))
  (= v_bboo v_bbyy)) (mem int (t2tb16 v_bbpp) (t2tb15 integer)))
  (<= 0 v_bbpp)) (<= v_bbpp 2147483647)) (<= 1 v_bbpp))
  (<= (+ v_bbpp 1) 2147483647)) (= v_bbpp v_bbzz)) (mem int (t2tb16 v_bbll)
  (t2tb15 integer))) (<= 0 v_bbll)) (<= v_bbll 2147483647)) (<= 2 v_bbll))
  (= v_bbll v_bbxx)) (<= (+ v_bbll v_bboo) 253))
  (<= (+ (+ v_bbll v_bbnn) v_bboo) 251)) (mem int (t2tb16 v_bbmm)
  (t2tb15 integer))) (<= 0 v_bbmm)) (<= v_bbmm 2147483647)) (<= 1 v_bbmm))
  (<= (+ v_bbmm 1) 254)) (= v_bbmm v_bbxx)))))

(declare-fun f2 ((set Int) (set Int) (set Int) Bool Bool Bool Bool Int
  (set Int) (set Int) (set Int) (set Int) Int Bool Bool Bool Bool Int Int Int
  Int Int Bool Bool Bool Bool Bool Int Int Int Int Int Int Int
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))) Int
  Int Int Int Int Int Int (set Int)) Bool)

;; f2_def
  (assert
  (forall ((v_zz (set Int)) (v_yy (set Int)) (v_xx (set Int)) (v_ww Bool)
  (v_vv Bool) (v_uu Bool) (v_tt Bool) (v_ss Int) (v_rr (set Int))
  (v_qq (set Int)) (v_pp (set Int)) (v_oo (set Int)) (v_nn Int) (v_mm Bool)
  (v_ll Bool) (v_kk Bool) (v_jj Bool) (v_bbzz Int) (v_bbyy Int) (v_bbxx Int)
  (v_bbww Int) (v_bbvv Int) (v_bbuu Bool) (v_bbtt Bool) (v_bbss Bool)
  (v_bbrr Bool) (v_bbqq Bool) (v_bbpp Int) (v_bboo Int) (v_bbnn Int)
  (v_bbmm Int) (v_bbll Int) (v_bbkk Int) (v_bbjj Int)
  (v_bbii (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (v_bbhh Int) (v_bbgg Int) (v_bbff Int) (v_bbee Int)
  (v_bbdd Int) (v_bbcc Int) (v_bbbb Int) (v_bbaa (set Int)))
  (= (f2 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbzz v_bbyy v_bbxx v_bbww v_bbvv v_bbuu v_bbtt v_bbss
  v_bbrr v_bbqq v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
  v_bbhh v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (mem int (t2tb16 v_bbbb) (t2tb15 integer)) (<= 0 v_bbbb)) (mem
  (set1 int) (t2tb15 v_xx) (power int (t2tb15 natural)))) (mem (set1 int)
  (t2tb15 v_yy) (power int (t2tb15 natural)))) (mem (set1 int) (t2tb15 v_zz)
  (power int (t2tb15 natural)))) (mem (set1 int) (t2tb15 v_bbaa)
  (power int (t2tb15 natural))))
  (forall ((v_ss1 Int))
  (=>
  (and (and (mem int (t2tb16 v_ss1) (t2tb15 integer)) (<= 0 v_ss1))
  (<= (+ v_bbbb 1) v_ss1)) (not (mem int (t2tb16 v_ss1) (t2tb15 v_xx))))))
  (forall ((v_ss1 Int))
  (=>
  (and (and (mem int (t2tb16 v_ss1) (t2tb15 integer)) (<= 0 v_ss1))
  (<= (+ v_bbbb 1) v_ss1)) (not (mem int (t2tb16 v_ss1) (t2tb15 v_yy))))))
  (forall ((v_ss1 Int))
  (=>
  (and (and (mem int (t2tb16 v_ss1) (t2tb15 integer)) (<= 0 v_ss1))
  (<= (+ v_bbbb 1) v_ss1)) (not (mem int (t2tb16 v_ss1) (t2tb15 v_zz))))))
  (forall ((v_ss1 Int))
  (=>
  (and (and (mem int (t2tb16 v_ss1) (t2tb15 integer)) (<= 0 v_ss1))
  (<= (+ v_bbbb 1) v_ss1)) (not (mem int (t2tb16 v_ss1) (t2tb15 v_bbaa))))))
  (infix_eqeq2 (tb2t15 (inter int (t2tb15 v_yy) (t2tb15 v_xx))) empty2))
  (infix_eqeq2 (tb2t15 (inter int (t2tb15 v_zz) (t2tb15 v_xx))) empty2))
  (infix_eqeq2 (tb2t15 (inter int (t2tb15 v_bbaa) (t2tb15 v_xx))) empty2)))))

(declare-fun f3 ((set Int) (set Int) (set Int) Bool Bool Bool Bool Int
  (set Int) (set Int) (set Int) (set Int) Int Bool Bool Bool Bool Int Int Int
  Int Int Bool Bool Bool Bool Bool Int Int Int Int Int Int Int
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))) Int
  Int Int Int Int Int Int (set Int)) Bool)

;; f3_def
  (assert
  (forall ((v_zz (set Int)) (v_yy (set Int)) (v_xx (set Int)) (v_ww Bool)
  (v_vv Bool) (v_uu Bool) (v_tt Bool) (v_ss Int) (v_rr (set Int))
  (v_qq (set Int)) (v_pp (set Int)) (v_oo (set Int)) (v_nn Int) (v_mm Bool)
  (v_ll Bool) (v_kk Bool) (v_jj Bool) (v_bbzz Int) (v_bbyy Int) (v_bbxx Int)
  (v_bbww Int) (v_bbvv Int) (v_bbuu Bool) (v_bbtt Bool) (v_bbss Bool)
  (v_bbrr Bool) (v_bbqq Bool) (v_bbpp Int) (v_bboo Int) (v_bbnn Int)
  (v_bbmm Int) (v_bbll Int) (v_bbkk Int) (v_bbjj Int)
  (v_bbii (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (v_bbhh Int) (v_bbgg Int) (v_bbff Int) (v_bbee Int)
  (v_bbdd Int) (v_bbcc Int) (v_bbbb Int) (v_bbaa (set Int)))
  (= (f3 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbzz v_bbyy v_bbxx v_bbww v_bbvv v_bbuu v_bbtt v_bbss
  v_bbrr v_bbqq v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
  v_bbhh v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (and
  (and (mem int (t2tb16 0) (t2tb15 integer)) (mem (set1 int) (t2tb15 empty2)
  (power int (t2tb15 natural)))) (mem (set1 uninterpreted_type1)
  (t2tb3 empty4) (power uninterpreted_type1 (t2tb3 empty4)))))))

(declare-fun f12 ((set Int) (set Int) (set Int) Bool Bool Bool Bool Int
  (set Int) (set Int) (set Int) (set Int) Int Bool Bool Bool Bool Int Int Int
  Int Int Bool Bool Bool Bool Bool Int Int Int Int Int Int Int
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))) Int
  Int Int Int Int Int Int (set Int)) Bool)

;; f12_def
  (assert
  (forall ((v_zz (set Int)) (v_yy (set Int)) (v_xx (set Int)) (v_ww Bool)
  (v_vv Bool) (v_uu Bool) (v_tt Bool) (v_ss Int) (v_rr (set Int))
  (v_qq (set Int)) (v_pp (set Int)) (v_oo (set Int)) (v_nn Int) (v_mm Bool)
  (v_ll Bool) (v_kk Bool) (v_jj Bool) (v_bbzz Int) (v_bbyy Int) (v_bbxx Int)
  (v_bbww Int) (v_bbvv Int) (v_bbuu Bool) (v_bbtt Bool) (v_bbss Bool)
  (v_bbrr Bool) (v_bbqq Bool) (v_bbpp Int) (v_bboo Int) (v_bbnn Int)
  (v_bbmm Int) (v_bbll Int) (v_bbkk Int) (v_bbjj Int)
  (v_bbii (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (v_bbhh Int) (v_bbgg Int) (v_bbff Int) (v_bbee Int)
  (v_bbdd Int) (v_bbcc Int) (v_bbbb Int) (v_bbaa (set Int)))
  (= (f12 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbzz v_bbyy v_bbxx v_bbww v_bbvv v_bbuu v_bbtt v_bbss
  v_bbrr v_bbqq v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
  v_bbhh v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (mem int (t2tb16 v_bbbb) (t2tb15 integer)) (<= 0 v_bbbb)) (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb5 v_bbii)
  (infix_plmngt (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb7 (times2 (times3 (times4 b_bool b_bool) b_bool) b_bool))
  (power int (t2tb15 natural))))) (infix_eqeq7
  (tb2t7
  (dom (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 v_bbii))) (times2 (times3 (times4 b_bool b_bool) b_bool) b_bool)))
  (infix_eqeq2 v_xx
  (apply4 v_bbii (Tuple23 (Tuple22 (Tuple21 false true) true) false))))
  (infix_eqeq2 v_yy
  (apply4 v_bbii (Tuple23 (Tuple22 (Tuple21 true true) false) false))))
  (infix_eqeq2 v_zz
  (apply4 v_bbii (Tuple23 (Tuple22 (Tuple21 true true) true) false))))
  (infix_eqeq2 v_bbaa
  (apply4 v_bbii (Tuple23 (Tuple22 (Tuple21 false true) false) false))))
  (= v_jj v_tt)) (= v_kk v_uu)) (= v_ll v_vv)) (= v_mm v_ww))
  (= v_nn v_bbbb)))))

(declare-fun f13 ((set Int) (set Int) (set Int) Bool Bool Bool Bool Int
  (set Int) (set Int) (set Int) (set Int) Int Bool Bool Bool Bool Int Int Int
  Int Int Bool Bool Bool Bool Bool Int Int Int Int Int Int Int
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))) Int
  Int Int Int Int Int Int (set Int)) Bool)

;; f13_def
  (assert
  (forall ((v_zz (set Int)) (v_yy (set Int)) (v_xx (set Int)) (v_ww Bool)
  (v_vv Bool) (v_uu Bool) (v_tt Bool) (v_ss Int) (v_rr (set Int))
  (v_qq (set Int)) (v_pp (set Int)) (v_oo (set Int)) (v_nn Int) (v_mm Bool)
  (v_ll Bool) (v_kk Bool) (v_jj Bool) (v_bbzz Int) (v_bbyy Int) (v_bbxx Int)
  (v_bbww Int) (v_bbvv Int) (v_bbuu Bool) (v_bbtt Bool) (v_bbss Bool)
  (v_bbrr Bool) (v_bbqq Bool) (v_bbpp Int) (v_bboo Int) (v_bbnn Int)
  (v_bbmm Int) (v_bbll Int) (v_bbkk Int) (v_bbjj Int)
  (v_bbii (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (v_bbhh Int) (v_bbgg Int) (v_bbff Int) (v_bbee Int)
  (v_bbdd Int) (v_bbcc Int) (v_bbbb Int) (v_bbaa (set Int)))
  (= (f13 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbzz v_bbyy v_bbxx v_bbww v_bbvv v_bbuu v_bbtt v_bbss
  v_bbrr v_bbqq v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
  v_bbhh v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (and (= v_ww false) (= v_tt false)) (= v_uu true)) (= v_vv true))
  (mem int (t2tb16 (+ v_bbbb 1)) (t2tb15 integer))) (<= 0 (+ v_bbbb 1)))
  (forall ((v_ss1 Int))
  (=>
  (and (and (mem int (t2tb16 v_ss1) (t2tb15 integer)) (<= 0 v_ss1))
  (<= (+ (+ v_bbbb 1) 1) v_ss1))
  (and (not (mem int (t2tb16 v_ss1) (t2tb15 v_xx)))
  (not (= v_ss1 (+ v_bbbb 1)))))))
  (forall ((v_ss1 Int))
  (=>
  (and (and (mem int (t2tb16 v_ss1) (t2tb15 integer)) (<= 0 v_ss1))
  (<= (+ (+ v_bbbb 1) 1) v_ss1))
  (not (mem int (t2tb16 v_ss1) (t2tb15 v_yy))))))
  (forall ((v_ss1 Int))
  (=>
  (and (and (mem int (t2tb16 v_ss1) (t2tb15 integer)) (<= 0 v_ss1))
  (<= (+ (+ v_bbbb 1) 1) v_ss1))
  (not (mem int (t2tb16 v_ss1) (t2tb15 v_zz))))))
  (forall ((v_ss1 Int))
  (=>
  (and (and (mem int (t2tb16 v_ss1) (t2tb15 integer)) (<= 0 v_ss1))
  (<= (+ (+ v_bbbb 1) 1) v_ss1))
  (not (mem int (t2tb16 v_ss1) (t2tb15 v_bbaa))))))
  (not (mem int (t2tb16 (+ v_bbbb 1)) (t2tb15 v_yy))))
  (not (mem int (t2tb16 (+ v_bbbb 1)) (t2tb15 v_zz))))
  (not (mem int (t2tb16 (+ v_bbbb 1)) (t2tb15 v_bbaa)))))))

(declare-fun f15 ((set Int) (set Int) (set Int) Bool Bool Bool Bool Int
  (set Int) (set Int) (set Int) (set Int) Int Bool Bool Bool Bool Int Int Int
  Int Int Bool Bool Bool Bool Bool Int Int Int Int Int Int Int
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))) Int
  Int Int Int Int Int Int (set Int)) Bool)

;; f15_def
  (assert
  (forall ((v_zz (set Int)) (v_yy (set Int)) (v_xx (set Int)) (v_ww Bool)
  (v_vv Bool) (v_uu Bool) (v_tt Bool) (v_ss Int) (v_rr (set Int))
  (v_qq (set Int)) (v_pp (set Int)) (v_oo (set Int)) (v_nn Int) (v_mm Bool)
  (v_ll Bool) (v_kk Bool) (v_jj Bool) (v_bbzz Int) (v_bbyy Int) (v_bbxx Int)
  (v_bbww Int) (v_bbvv Int) (v_bbuu Bool) (v_bbtt Bool) (v_bbss Bool)
  (v_bbrr Bool) (v_bbqq Bool) (v_bbpp Int) (v_bboo Int) (v_bbnn Int)
  (v_bbmm Int) (v_bbll Int) (v_bbkk Int) (v_bbjj Int)
  (v_bbii (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (v_bbhh Int) (v_bbgg Int) (v_bbff Int) (v_bbee Int)
  (v_bbdd Int) (v_bbcc Int) (v_bbbb Int) (v_bbaa (set Int)))
  (= (f15 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbzz v_bbyy v_bbxx v_bbww v_bbvv v_bbuu v_bbtt v_bbss
  v_bbrr v_bbqq v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
  v_bbhh v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa) (infix_eqeq2
  (tb2t15 (union int (t2tb15 v_xx) (t2tb15 (add2 (+ v_bbbb 1) empty2))))
  (apply4
  (tb2t5
  (infix_lspl (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 v_bbii)
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb8 (Tuple23 (Tuple22 (Tuple21 v_tt v_uu) v_vv) v_ww))
  (union int
  (t2tb15 (apply4 v_bbii (Tuple23 (Tuple22 (Tuple21 v_tt v_uu) v_vv) v_ww)))
  (t2tb15 (add2 (+ v_bbbb 1) empty2)))) (t2tb5 empty3))))
  (Tuple23 (Tuple22 (Tuple21 false true) true) false))))))

(declare-fun f17 ((set Int) (set Int) (set Int) Bool Bool Bool Bool Int
  (set Int) (set Int) (set Int) (set Int) Int Bool Bool Bool Bool Int Int Int
  Int Int Bool Bool Bool Bool Bool Int Int Int Int Int Int Int
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))) Int
  Int Int Int Int Int Int (set Int)) Bool)

;; f17_def
  (assert
  (forall ((v_zz (set Int)) (v_yy (set Int)) (v_xx (set Int)) (v_ww Bool)
  (v_vv Bool) (v_uu Bool) (v_tt Bool) (v_ss Int) (v_rr (set Int))
  (v_qq (set Int)) (v_pp (set Int)) (v_oo (set Int)) (v_nn Int) (v_mm Bool)
  (v_ll Bool) (v_kk Bool) (v_jj Bool) (v_bbzz Int) (v_bbyy Int) (v_bbxx Int)
  (v_bbww Int) (v_bbvv Int) (v_bbuu Bool) (v_bbtt Bool) (v_bbss Bool)
  (v_bbrr Bool) (v_bbqq Bool) (v_bbpp Int) (v_bboo Int) (v_bbnn Int)
  (v_bbmm Int) (v_bbll Int) (v_bbkk Int) (v_bbjj Int)
  (v_bbii (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (v_bbhh Int) (v_bbgg Int) (v_bbff Int) (v_bbee Int)
  (v_bbdd Int) (v_bbcc Int) (v_bbbb Int) (v_bbaa (set Int)))
  (= (f17 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbzz v_bbyy v_bbxx v_bbww v_bbvv v_bbuu v_bbtt v_bbss
  v_bbrr v_bbqq v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
  v_bbhh v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa) (infix_eqeq2 v_yy
  (apply4
  (tb2t5
  (infix_lspl (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 v_bbii)
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb8 (Tuple23 (Tuple22 (Tuple21 v_tt v_uu) v_vv) v_ww))
  (union int
  (t2tb15 (apply4 v_bbii (Tuple23 (Tuple22 (Tuple21 v_tt v_uu) v_vv) v_ww)))
  (t2tb15 (add2 (+ v_bbbb 1) empty2)))) (t2tb5 empty3))))
  (Tuple23 (Tuple22 (Tuple21 true true) false) false))))))

(declare-fun f19 ((set Int) (set Int) (set Int) Bool Bool Bool Bool Int
  (set Int) (set Int) (set Int) (set Int) Int Bool Bool Bool Bool Int Int Int
  Int Int Bool Bool Bool Bool Bool Int Int Int Int Int Int Int
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))) Int
  Int Int Int Int Int Int (set Int)) Bool)

;; f19_def
  (assert
  (forall ((v_zz (set Int)) (v_yy (set Int)) (v_xx (set Int)) (v_ww Bool)
  (v_vv Bool) (v_uu Bool) (v_tt Bool) (v_ss Int) (v_rr (set Int))
  (v_qq (set Int)) (v_pp (set Int)) (v_oo (set Int)) (v_nn Int) (v_mm Bool)
  (v_ll Bool) (v_kk Bool) (v_jj Bool) (v_bbzz Int) (v_bbyy Int) (v_bbxx Int)
  (v_bbww Int) (v_bbvv Int) (v_bbuu Bool) (v_bbtt Bool) (v_bbss Bool)
  (v_bbrr Bool) (v_bbqq Bool) (v_bbpp Int) (v_bboo Int) (v_bbnn Int)
  (v_bbmm Int) (v_bbll Int) (v_bbkk Int) (v_bbjj Int)
  (v_bbii (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (v_bbhh Int) (v_bbgg Int) (v_bbff Int) (v_bbee Int)
  (v_bbdd Int) (v_bbcc Int) (v_bbbb Int) (v_bbaa (set Int)))
  (= (f19 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbzz v_bbyy v_bbxx v_bbww v_bbvv v_bbuu v_bbtt v_bbss
  v_bbrr v_bbqq v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
  v_bbhh v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa) (infix_eqeq2 v_zz
  (apply4
  (tb2t5
  (infix_lspl (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 v_bbii)
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb8 (Tuple23 (Tuple22 (Tuple21 v_tt v_uu) v_vv) v_ww))
  (union int
  (t2tb15 (apply4 v_bbii (Tuple23 (Tuple22 (Tuple21 v_tt v_uu) v_vv) v_ww)))
  (t2tb15 (add2 (+ v_bbbb 1) empty2)))) (t2tb5 empty3))))
  (Tuple23 (Tuple22 (Tuple21 true true) true) false))))))

(declare-fun f21 ((set Int) (set Int) (set Int) Bool Bool Bool Bool Int
  (set Int) (set Int) (set Int) (set Int) Int Bool Bool Bool Bool Int Int Int
  Int Int Bool Bool Bool Bool Bool Int Int Int Int Int Int Int
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))) Int
  Int Int Int Int Int Int (set Int)) Bool)

;; f21_def
  (assert
  (forall ((v_zz (set Int)) (v_yy (set Int)) (v_xx (set Int)) (v_ww Bool)
  (v_vv Bool) (v_uu Bool) (v_tt Bool) (v_ss Int) (v_rr (set Int))
  (v_qq (set Int)) (v_pp (set Int)) (v_oo (set Int)) (v_nn Int) (v_mm Bool)
  (v_ll Bool) (v_kk Bool) (v_jj Bool) (v_bbzz Int) (v_bbyy Int) (v_bbxx Int)
  (v_bbww Int) (v_bbvv Int) (v_bbuu Bool) (v_bbtt Bool) (v_bbss Bool)
  (v_bbrr Bool) (v_bbqq Bool) (v_bbpp Int) (v_bboo Int) (v_bbnn Int)
  (v_bbmm Int) (v_bbll Int) (v_bbkk Int) (v_bbjj Int)
  (v_bbii (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (v_bbhh Int) (v_bbgg Int) (v_bbff Int) (v_bbee Int)
  (v_bbdd Int) (v_bbcc Int) (v_bbbb Int) (v_bbaa (set Int)))
  (= (f21 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbzz v_bbyy v_bbxx v_bbww v_bbvv v_bbuu v_bbtt v_bbss
  v_bbrr v_bbqq v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
  v_bbhh v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa) (infix_eqeq2
  v_bbaa
  (apply4
  (tb2t5
  (infix_lspl (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 v_bbii)
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb8 (Tuple23 (Tuple22 (Tuple21 v_tt v_uu) v_vv) v_ww))
  (union int
  (t2tb15 (apply4 v_bbii (Tuple23 (Tuple22 (Tuple21 v_tt v_uu) v_vv) v_ww)))
  (t2tb15 (add2 (+ v_bbbb 1) empty2)))) (t2tb5 empty3))))
  (Tuple23 (Tuple22 (Tuple21 false true) false) false))))))

(declare-fun f22 ((set Int) (set Int) (set Int) Bool Bool Bool Bool Int
  (set Int) (set Int) (set Int) (set Int) Int Bool Bool Bool Bool Int Int Int
  Int Int Bool Bool Bool Bool Bool Int Int Int Int Int Int Int
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))) Int
  Int Int Int Int Int Int (set Int)) Bool)

;; f22_def
  (assert
  (forall ((v_zz (set Int)) (v_yy (set Int)) (v_xx (set Int)) (v_ww Bool)
  (v_vv Bool) (v_uu Bool) (v_tt Bool) (v_ss Int) (v_rr (set Int))
  (v_qq (set Int)) (v_pp (set Int)) (v_oo (set Int)) (v_nn Int) (v_mm Bool)
  (v_ll Bool) (v_kk Bool) (v_jj Bool) (v_bbzz Int) (v_bbyy Int) (v_bbxx Int)
  (v_bbww Int) (v_bbvv Int) (v_bbuu Bool) (v_bbtt Bool) (v_bbss Bool)
  (v_bbrr Bool) (v_bbqq Bool) (v_bbpp Int) (v_bboo Int) (v_bbnn Int)
  (v_bbmm Int) (v_bbll Int) (v_bbkk Int) (v_bbjj Int)
  (v_bbii (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (v_bbhh Int) (v_bbgg Int) (v_bbff Int) (v_bbee Int)
  (v_bbdd Int) (v_bbcc Int) (v_bbbb Int) (v_bbaa (set Int)))
  (= (f22 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbzz v_bbyy v_bbxx v_bbww v_bbvv v_bbuu v_bbtt v_bbss
  v_bbrr v_bbqq v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
  v_bbhh v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (and (= v_ww false) (= v_tt true)) (= v_uu true)) (= v_vv false))
  (mem int (t2tb16 (+ v_bbbb 1)) (t2tb15 integer))) (<= 0 (+ v_bbbb 1)))
  (forall ((v_ss1 Int))
  (=>
  (and (and (mem int (t2tb16 v_ss1) (t2tb15 integer)) (<= 0 v_ss1))
  (<= (+ (+ v_bbbb 1) 1) v_ss1))
  (not (mem int (t2tb16 v_ss1) (t2tb15 v_xx))))))
  (forall ((v_ss1 Int))
  (=>
  (and (and (mem int (t2tb16 v_ss1) (t2tb15 integer)) (<= 0 v_ss1))
  (<= (+ (+ v_bbbb 1) 1) v_ss1))
  (and (not (mem int (t2tb16 v_ss1) (t2tb15 v_yy)))
  (not (= v_ss1 (+ v_bbbb 1)))))))
  (forall ((v_ss1 Int))
  (=>
  (and (and (mem int (t2tb16 v_ss1) (t2tb15 integer)) (<= 0 v_ss1))
  (<= (+ (+ v_bbbb 1) 1) v_ss1))
  (not (mem int (t2tb16 v_ss1) (t2tb15 v_zz))))))
  (forall ((v_ss1 Int))
  (=>
  (and (and (mem int (t2tb16 v_ss1) (t2tb15 integer)) (<= 0 v_ss1))
  (<= (+ (+ v_bbbb 1) 1) v_ss1))
  (not (mem int (t2tb16 v_ss1) (t2tb15 v_bbaa)))))) (infix_eqeq2
  (tb2t15
  (inter int (union int (t2tb15 v_yy) (t2tb15 (add2 (+ v_bbbb 1) empty2)))
  (t2tb15 v_xx))) empty2)))))

(declare-fun f23 ((set Int) (set Int) (set Int) Bool Bool Bool Bool Int
  (set Int) (set Int) (set Int) (set Int) Int Bool Bool Bool Bool Int Int Int
  Int Int Bool Bool Bool Bool Bool Int Int Int Int Int Int Int
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))) Int
  Int Int Int Int Int Int (set Int)) Bool)

;; f23_def
  (assert
  (forall ((v_zz (set Int)) (v_yy (set Int)) (v_xx (set Int)) (v_ww Bool)
  (v_vv Bool) (v_uu Bool) (v_tt Bool) (v_ss Int) (v_rr (set Int))
  (v_qq (set Int)) (v_pp (set Int)) (v_oo (set Int)) (v_nn Int) (v_mm Bool)
  (v_ll Bool) (v_kk Bool) (v_jj Bool) (v_bbzz Int) (v_bbyy Int) (v_bbxx Int)
  (v_bbww Int) (v_bbvv Int) (v_bbuu Bool) (v_bbtt Bool) (v_bbss Bool)
  (v_bbrr Bool) (v_bbqq Bool) (v_bbpp Int) (v_bboo Int) (v_bbnn Int)
  (v_bbmm Int) (v_bbll Int) (v_bbkk Int) (v_bbjj Int)
  (v_bbii (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (v_bbhh Int) (v_bbgg Int) (v_bbff Int) (v_bbee Int)
  (v_bbdd Int) (v_bbcc Int) (v_bbbb Int) (v_bbaa (set Int)))
  (= (f23 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbzz v_bbyy v_bbxx v_bbww v_bbvv v_bbuu v_bbtt v_bbss
  v_bbrr v_bbqq v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
  v_bbhh v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa) (infix_eqeq2 v_xx
  (apply4
  (tb2t5
  (infix_lspl (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 v_bbii)
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb8 (Tuple23 (Tuple22 (Tuple21 v_tt v_uu) v_vv) v_ww))
  (union int
  (t2tb15 (apply4 v_bbii (Tuple23 (Tuple22 (Tuple21 v_tt v_uu) v_vv) v_ww)))
  (t2tb15 (add2 (+ v_bbbb 1) empty2)))) (t2tb5 empty3))))
  (Tuple23 (Tuple22 (Tuple21 false true) true) false))))))

(declare-fun f24 ((set Int) (set Int) (set Int) Bool Bool Bool Bool Int
  (set Int) (set Int) (set Int) (set Int) Int Bool Bool Bool Bool Int Int Int
  Int Int Bool Bool Bool Bool Bool Int Int Int Int Int Int Int
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))) Int
  Int Int Int Int Int Int (set Int)) Bool)

;; f24_def
  (assert
  (forall ((v_zz (set Int)) (v_yy (set Int)) (v_xx (set Int)) (v_ww Bool)
  (v_vv Bool) (v_uu Bool) (v_tt Bool) (v_ss Int) (v_rr (set Int))
  (v_qq (set Int)) (v_pp (set Int)) (v_oo (set Int)) (v_nn Int) (v_mm Bool)
  (v_ll Bool) (v_kk Bool) (v_jj Bool) (v_bbzz Int) (v_bbyy Int) (v_bbxx Int)
  (v_bbww Int) (v_bbvv Int) (v_bbuu Bool) (v_bbtt Bool) (v_bbss Bool)
  (v_bbrr Bool) (v_bbqq Bool) (v_bbpp Int) (v_bboo Int) (v_bbnn Int)
  (v_bbmm Int) (v_bbll Int) (v_bbkk Int) (v_bbjj Int)
  (v_bbii (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (v_bbhh Int) (v_bbgg Int) (v_bbff Int) (v_bbee Int)
  (v_bbdd Int) (v_bbcc Int) (v_bbbb Int) (v_bbaa (set Int)))
  (= (f24 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbzz v_bbyy v_bbxx v_bbww v_bbvv v_bbuu v_bbtt v_bbss
  v_bbrr v_bbqq v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
  v_bbhh v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa) (infix_eqeq2
  (tb2t15 (union int (t2tb15 v_yy) (t2tb15 (add2 (+ v_bbbb 1) empty2))))
  (apply4
  (tb2t5
  (infix_lspl (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 v_bbii)
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb8 (Tuple23 (Tuple22 (Tuple21 v_tt v_uu) v_vv) v_ww))
  (union int
  (t2tb15 (apply4 v_bbii (Tuple23 (Tuple22 (Tuple21 v_tt v_uu) v_vv) v_ww)))
  (t2tb15 (add2 (+ v_bbbb 1) empty2)))) (t2tb5 empty3))))
  (Tuple23 (Tuple22 (Tuple21 true true) false) false))))))

(declare-fun f25 ((set Int) (set Int) (set Int) Bool Bool Bool Bool Int
  (set Int) (set Int) (set Int) (set Int) Int Bool Bool Bool Bool Int Int Int
  Int Int Bool Bool Bool Bool Bool Int Int Int Int Int Int Int
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))) Int
  Int Int Int Int Int Int (set Int)) Bool)

;; f25_def
  (assert
  (forall ((v_zz (set Int)) (v_yy (set Int)) (v_xx (set Int)) (v_ww Bool)
  (v_vv Bool) (v_uu Bool) (v_tt Bool) (v_ss Int) (v_rr (set Int))
  (v_qq (set Int)) (v_pp (set Int)) (v_oo (set Int)) (v_nn Int) (v_mm Bool)
  (v_ll Bool) (v_kk Bool) (v_jj Bool) (v_bbzz Int) (v_bbyy Int) (v_bbxx Int)
  (v_bbww Int) (v_bbvv Int) (v_bbuu Bool) (v_bbtt Bool) (v_bbss Bool)
  (v_bbrr Bool) (v_bbqq Bool) (v_bbpp Int) (v_bboo Int) (v_bbnn Int)
  (v_bbmm Int) (v_bbll Int) (v_bbkk Int) (v_bbjj Int)
  (v_bbii (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (v_bbhh Int) (v_bbgg Int) (v_bbff Int) (v_bbee Int)
  (v_bbdd Int) (v_bbcc Int) (v_bbbb Int) (v_bbaa (set Int)))
  (= (f25 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbzz v_bbyy v_bbxx v_bbww v_bbvv v_bbuu v_bbtt v_bbss
  v_bbrr v_bbqq v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
  v_bbhh v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (and (= v_ww false) (= v_tt true)) (= v_uu true)) (= v_vv true))
  (mem int (t2tb16 (+ v_bbbb 1)) (t2tb15 integer))) (<= 0 (+ v_bbbb 1)))
  (forall ((v_ss1 Int))
  (=>
  (and (and (mem int (t2tb16 v_ss1) (t2tb15 integer)) (<= 0 v_ss1))
  (<= (+ (+ v_bbbb 1) 1) v_ss1))
  (not (mem int (t2tb16 v_ss1) (t2tb15 v_xx))))))
  (forall ((v_ss1 Int))
  (=>
  (and (and (mem int (t2tb16 v_ss1) (t2tb15 integer)) (<= 0 v_ss1))
  (<= (+ (+ v_bbbb 1) 1) v_ss1))
  (not (mem int (t2tb16 v_ss1) (t2tb15 v_yy))))))
  (forall ((v_ss1 Int))
  (=>
  (and (and (mem int (t2tb16 v_ss1) (t2tb15 integer)) (<= 0 v_ss1))
  (<= (+ (+ v_bbbb 1) 1) v_ss1))
  (and (not (mem int (t2tb16 v_ss1) (t2tb15 v_zz)))
  (not (= v_ss1 (+ v_bbbb 1)))))))
  (forall ((v_ss1 Int))
  (=>
  (and (and (mem int (t2tb16 v_ss1) (t2tb15 integer)) (<= 0 v_ss1))
  (<= (+ (+ v_bbbb 1) 1) v_ss1))
  (not (mem int (t2tb16 v_ss1) (t2tb15 v_bbaa)))))) (infix_eqeq2
  (tb2t15
  (inter int (union int (t2tb15 v_zz) (t2tb15 (add2 (+ v_bbbb 1) empty2)))
  (t2tb15 v_xx))) empty2)))))

(declare-fun f26 ((set Int) (set Int) (set Int) Bool Bool Bool Bool Int
  (set Int) (set Int) (set Int) (set Int) Int Bool Bool Bool Bool Int Int Int
  Int Int Bool Bool Bool Bool Bool Int Int Int Int Int Int Int
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))) Int
  Int Int Int Int Int Int (set Int)) Bool)

;; f26_def
  (assert
  (forall ((v_zz (set Int)) (v_yy (set Int)) (v_xx (set Int)) (v_ww Bool)
  (v_vv Bool) (v_uu Bool) (v_tt Bool) (v_ss Int) (v_rr (set Int))
  (v_qq (set Int)) (v_pp (set Int)) (v_oo (set Int)) (v_nn Int) (v_mm Bool)
  (v_ll Bool) (v_kk Bool) (v_jj Bool) (v_bbzz Int) (v_bbyy Int) (v_bbxx Int)
  (v_bbww Int) (v_bbvv Int) (v_bbuu Bool) (v_bbtt Bool) (v_bbss Bool)
  (v_bbrr Bool) (v_bbqq Bool) (v_bbpp Int) (v_bboo Int) (v_bbnn Int)
  (v_bbmm Int) (v_bbll Int) (v_bbkk Int) (v_bbjj Int)
  (v_bbii (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (v_bbhh Int) (v_bbgg Int) (v_bbff Int) (v_bbee Int)
  (v_bbdd Int) (v_bbcc Int) (v_bbbb Int) (v_bbaa (set Int)))
  (= (f26 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbzz v_bbyy v_bbxx v_bbww v_bbvv v_bbuu v_bbtt v_bbss
  v_bbrr v_bbqq v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
  v_bbhh v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa) (infix_eqeq2
  (tb2t15 (union int (t2tb15 v_zz) (t2tb15 (add2 (+ v_bbbb 1) empty2))))
  (apply4
  (tb2t5
  (infix_lspl (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 v_bbii)
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb8 (Tuple23 (Tuple22 (Tuple21 v_tt v_uu) v_vv) v_ww))
  (union int
  (t2tb15 (apply4 v_bbii (Tuple23 (Tuple22 (Tuple21 v_tt v_uu) v_vv) v_ww)))
  (t2tb15 (add2 (+ v_bbbb 1) empty2)))) (t2tb5 empty3))))
  (Tuple23 (Tuple22 (Tuple21 true true) true) false))))))

(declare-fun f27 ((set Int) (set Int) (set Int) Bool Bool Bool Bool Int
  (set Int) (set Int) (set Int) (set Int) Int Bool Bool Bool Bool Int Int Int
  Int Int Bool Bool Bool Bool Bool Int Int Int Int Int Int Int
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))) Int
  Int Int Int Int Int Int (set Int)) Bool)

;; f27_def
  (assert
  (forall ((v_zz (set Int)) (v_yy (set Int)) (v_xx (set Int)) (v_ww Bool)
  (v_vv Bool) (v_uu Bool) (v_tt Bool) (v_ss Int) (v_rr (set Int))
  (v_qq (set Int)) (v_pp (set Int)) (v_oo (set Int)) (v_nn Int) (v_mm Bool)
  (v_ll Bool) (v_kk Bool) (v_jj Bool) (v_bbzz Int) (v_bbyy Int) (v_bbxx Int)
  (v_bbww Int) (v_bbvv Int) (v_bbuu Bool) (v_bbtt Bool) (v_bbss Bool)
  (v_bbrr Bool) (v_bbqq Bool) (v_bbpp Int) (v_bboo Int) (v_bbnn Int)
  (v_bbmm Int) (v_bbll Int) (v_bbkk Int) (v_bbjj Int)
  (v_bbii (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (v_bbhh Int) (v_bbgg Int) (v_bbff Int) (v_bbee Int)
  (v_bbdd Int) (v_bbcc Int) (v_bbbb Int) (v_bbaa (set Int)))
  (= (f27 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbzz v_bbyy v_bbxx v_bbww v_bbvv v_bbuu v_bbtt v_bbss
  v_bbrr v_bbqq v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
  v_bbhh v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (and (= v_ww false) (= v_tt false)) (= v_uu true))
  (= v_vv false)) (mem int (t2tb16 (+ v_bbbb 1)) (t2tb15 integer)))
  (<= 0 (+ v_bbbb 1)))
  (forall ((v_ss1 Int))
  (=>
  (and (and (mem int (t2tb16 v_ss1) (t2tb15 integer)) (<= 0 v_ss1))
  (<= (+ (+ v_bbbb 1) 1) v_ss1))
  (not (mem int (t2tb16 v_ss1) (t2tb15 v_xx))))))
  (forall ((v_ss1 Int))
  (=>
  (and (and (mem int (t2tb16 v_ss1) (t2tb15 integer)) (<= 0 v_ss1))
  (<= (+ (+ v_bbbb 1) 1) v_ss1))
  (not (mem int (t2tb16 v_ss1) (t2tb15 v_yy))))))
  (forall ((v_ss1 Int))
  (=>
  (and (and (mem int (t2tb16 v_ss1) (t2tb15 integer)) (<= 0 v_ss1))
  (<= (+ (+ v_bbbb 1) 1) v_ss1))
  (not (mem int (t2tb16 v_ss1) (t2tb15 v_zz))))))
  (forall ((v_ss1 Int))
  (=>
  (and (and (mem int (t2tb16 v_ss1) (t2tb15 integer)) (<= 0 v_ss1))
  (<= (+ (+ v_bbbb 1) 1) v_ss1))
  (and (not (mem int (t2tb16 v_ss1) (t2tb15 v_bbaa)))
  (not (= v_ss1 (+ v_bbbb 1))))))) (infix_eqeq2
  (tb2t15
  (inter int (union int (t2tb15 v_bbaa) (t2tb15 (add2 (+ v_bbbb 1) empty2)))
  (t2tb15 v_xx))) empty2)))))

(declare-fun f28 ((set Int) (set Int) (set Int) Bool Bool Bool Bool Int
  (set Int) (set Int) (set Int) (set Int) Int Bool Bool Bool Bool Int Int Int
  Int Int Bool Bool Bool Bool Bool Int Int Int Int Int Int Int
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))) Int
  Int Int Int Int Int Int (set Int)) Bool)

;; f28_def
  (assert
  (forall ((v_zz (set Int)) (v_yy (set Int)) (v_xx (set Int)) (v_ww Bool)
  (v_vv Bool) (v_uu Bool) (v_tt Bool) (v_ss Int) (v_rr (set Int))
  (v_qq (set Int)) (v_pp (set Int)) (v_oo (set Int)) (v_nn Int) (v_mm Bool)
  (v_ll Bool) (v_kk Bool) (v_jj Bool) (v_bbzz Int) (v_bbyy Int) (v_bbxx Int)
  (v_bbww Int) (v_bbvv Int) (v_bbuu Bool) (v_bbtt Bool) (v_bbss Bool)
  (v_bbrr Bool) (v_bbqq Bool) (v_bbpp Int) (v_bboo Int) (v_bbnn Int)
  (v_bbmm Int) (v_bbll Int) (v_bbkk Int) (v_bbjj Int)
  (v_bbii (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (v_bbhh Int) (v_bbgg Int) (v_bbff Int) (v_bbee Int)
  (v_bbdd Int) (v_bbcc Int) (v_bbbb Int) (v_bbaa (set Int)))
  (= (f28 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbzz v_bbyy v_bbxx v_bbww v_bbvv v_bbuu v_bbtt v_bbss
  v_bbrr v_bbqq v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
  v_bbhh v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa) (infix_eqeq2
  (tb2t15 (union int (t2tb15 v_bbaa) (t2tb15 (add2 (+ v_bbbb 1) empty2))))
  (apply4
  (tb2t5
  (infix_lspl (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 v_bbii)
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb8 (Tuple23 (Tuple22 (Tuple21 v_tt v_uu) v_vv) v_ww))
  (union int
  (t2tb15 (apply4 v_bbii (Tuple23 (Tuple22 (Tuple21 v_tt v_uu) v_vv) v_ww)))
  (t2tb15 (add2 (+ v_bbbb 1) empty2)))) (t2tb5 empty3))))
  (Tuple23 (Tuple22 (Tuple21 false true) false) false))))))

(declare-fun f29 ((set Int) (set Int) (set Int) Bool Bool Bool Bool Int
  (set Int) (set Int) (set Int) (set Int) Int Bool Bool Bool Bool Int Int Int
  Int Int Bool Bool Bool Bool Bool Int Int Int Int Int Int Int
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))) Int
  Int Int Int Int Int Int (set Int)) Bool)

;; f29_def
  (assert
  (forall ((v_zz (set Int)) (v_yy (set Int)) (v_xx (set Int)) (v_ww Bool)
  (v_vv Bool) (v_uu Bool) (v_tt Bool) (v_ss Int) (v_rr (set Int))
  (v_qq (set Int)) (v_pp (set Int)) (v_oo (set Int)) (v_nn Int) (v_mm Bool)
  (v_ll Bool) (v_kk Bool) (v_jj Bool) (v_bbzz Int) (v_bbyy Int) (v_bbxx Int)
  (v_bbww Int) (v_bbvv Int) (v_bbuu Bool) (v_bbtt Bool) (v_bbss Bool)
  (v_bbrr Bool) (v_bbqq Bool) (v_bbpp Int) (v_bboo Int) (v_bbnn Int)
  (v_bbmm Int) (v_bbll Int) (v_bbkk Int) (v_bbjj Int)
  (v_bbii (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (v_bbhh Int) (v_bbgg Int) (v_bbff Int) (v_bbee Int)
  (v_bbdd Int) (v_bbcc Int) (v_bbbb Int) (v_bbaa (set Int)))
  (= (f29 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbzz v_bbyy v_bbxx v_bbww v_bbvv v_bbuu v_bbtt v_bbss
  v_bbrr v_bbqq v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
  v_bbhh v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_tt false) (= v_uu true)) (= v_vv true)) (= v_ww false)))
  (not
  (and (and (and (= v_tt true) (= v_uu true)) (= v_vv false)) (= v_ww false))))
  (not
  (and (and (and (= v_tt true) (= v_uu true)) (= v_vv true)) (= v_ww false))))
  (not
  (and (and (and (= v_tt false) (= v_uu true)) (= v_vv false))
  (= v_ww false)))) (mem int (t2tb16 (+ v_bbbb 1)) (t2tb15 integer)))
  (<= 0 (+ v_bbbb 1)))
  (forall ((v_ss1 Int))
  (=>
  (and (and (mem int (t2tb16 v_ss1) (t2tb15 integer)) (<= 0 v_ss1))
  (<= (+ (+ v_bbbb 1) 1) v_ss1))
  (not (mem int (t2tb16 v_ss1) (t2tb15 v_xx))))))
  (forall ((v_ss1 Int))
  (=>
  (and (and (mem int (t2tb16 v_ss1) (t2tb15 integer)) (<= 0 v_ss1))
  (<= (+ (+ v_bbbb 1) 1) v_ss1))
  (not (mem int (t2tb16 v_ss1) (t2tb15 v_yy))))))
  (forall ((v_ss1 Int))
  (=>
  (and (and (mem int (t2tb16 v_ss1) (t2tb15 integer)) (<= 0 v_ss1))
  (<= (+ (+ v_bbbb 1) 1) v_ss1))
  (not (mem int (t2tb16 v_ss1) (t2tb15 v_zz))))))
  (forall ((v_ss1 Int))
  (=>
  (and (and (mem int (t2tb16 v_ss1) (t2tb15 integer)) (<= 0 v_ss1))
  (<= (+ (+ v_bbbb 1) 1) v_ss1))
  (not (mem int (t2tb16 v_ss1) (t2tb15 v_bbaa)))))))))

(declare-fun f30 ((set Int) (set Int) (set Int) Bool Bool Bool Bool Int
  (set Int) (set Int) (set Int) (set Int) Int Bool Bool Bool Bool Int Int Int
  Int Int Bool Bool Bool Bool Bool Int Int Int Int Int Int Int
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))) Int
  Int Int Int Int Int Int (set Int)) Bool)

;; f30_def
  (assert
  (forall ((v_zz (set Int)) (v_yy (set Int)) (v_xx (set Int)) (v_ww Bool)
  (v_vv Bool) (v_uu Bool) (v_tt Bool) (v_ss Int) (v_rr (set Int))
  (v_qq (set Int)) (v_pp (set Int)) (v_oo (set Int)) (v_nn Int) (v_mm Bool)
  (v_ll Bool) (v_kk Bool) (v_jj Bool) (v_bbzz Int) (v_bbyy Int) (v_bbxx Int)
  (v_bbww Int) (v_bbvv Int) (v_bbuu Bool) (v_bbtt Bool) (v_bbss Bool)
  (v_bbrr Bool) (v_bbqq Bool) (v_bbpp Int) (v_bboo Int) (v_bbnn Int)
  (v_bbmm Int) (v_bbll Int) (v_bbkk Int) (v_bbjj Int)
  (v_bbii (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (v_bbhh Int) (v_bbgg Int) (v_bbff Int) (v_bbee Int)
  (v_bbdd Int) (v_bbcc Int) (v_bbbb Int) (v_bbaa (set Int)))
  (= (f30 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbzz v_bbyy v_bbxx v_bbww v_bbvv v_bbuu v_bbtt v_bbss
  v_bbrr v_bbqq v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
  v_bbhh v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (and
  (=> (= v_bbqq true)
  (exists ((v_bbcc1 Int) (v_bbdd1 Int) (v_bbee1 Int) (v_bbff1 Int)
  (v_bbgg1 Int))
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (mem int (t2tb16 v_bbcc1) (t2tb15 (mk 1 v_bbbb))) (mem int
  (t2tb16 v_bbdd1) (t2tb15 (mk v_bbcc1 v_bbbb)))) (mem int (t2tb16 v_bbee1)
  (t2tb15 (mk v_bbdd1 v_bbbb)))) (mem int (t2tb16 v_bbff1)
  (t2tb15 (mk v_bbee1 v_bbbb)))) (mem int (t2tb16 v_bbgg1)
  (t2tb15 (mk v_bbff1 v_bbbb)))) (mem (set1 int)
  (t2tb15 (mk v_bbcc1 v_bbdd1)) (power int (t2tb15 v_yy))))
  (not (mem int (t2tb16 (+ v_bbdd1 1)) (t2tb15 v_yy)))) (mem (set1 int)
  (t2tb15 (mk (+ v_bbdd1 1) v_bbee1))
  (power int (union int (t2tb15 v_yy) (t2tb15 v_bbaa))))) (mem (set1 int)
  (t2tb15 (mk (+ v_bbee1 1) v_bbff1)) (power int (t2tb15 v_bbaa))))
  (not (mem int (t2tb16 (+ v_bbff1 1)) (t2tb15 v_bbaa)))) (mem (set1 int)
  (t2tb15 (mk (+ v_bbff1 1) v_bbgg1))
  (power int
  (union int
  (union int (union int (t2tb15 v_xx) (t2tb15 v_yy)) (t2tb15 v_zz))
  (t2tb15 v_bbaa)))))
  (forall ((v_bbjj1 Int) (v_bbkk1 Int))
  (=>
  (and
  (and (mem int (t2tb16 v_bbjj1) (t2tb15 (mk (+ v_bbff1 1) v_bbgg1))) (mem
  int (t2tb16 v_bbkk1) (t2tb15 (mk (+ v_bbff1 1) v_bbgg1)))) (mem (set1 int)
  (t2tb15 (mk v_bbjj1 v_bbkk1)) (power int (t2tb15 v_xx))))
  (<= (+ (- v_bbkk1 v_bbjj1) 1) v_bbll)))) (mem (set1 int)
  (t2tb15 (mk (+ v_bbgg1 1) v_bbbb)) (power int (t2tb15 v_xx))))
  (= (- v_bbdd1 v_bbcc1) v_bbmm)) (<= (- (- v_bbee1 v_bbdd1) 1) v_bbnn))
  (<= (- (- v_bbgg1 v_bbff1) 1) v_bboo)) (mem int
  (t2tb16 (- (- v_bbbb v_bbgg1) 1)) (t2tb15 (mk v_bbll (+ v_bbll v_bbpp)))))))
  (= v_bbqq true)))))

(declare-fun f32 ((set Int) (set Int) (set Int) Bool Bool Bool Bool Int
  (set Int) (set Int) (set Int) (set Int) Int Bool Bool Bool Bool Int Int Int
  Int Int Bool Bool Bool Bool Bool Int Int Int Int Int Int Int
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))) Int
  Int Int Int Int Int Int (set Int)) Bool)

;; f32_def
  (assert
  (forall ((v_zz (set Int)) (v_yy (set Int)) (v_xx (set Int)) (v_ww Bool)
  (v_vv Bool) (v_uu Bool) (v_tt Bool) (v_ss Int) (v_rr (set Int))
  (v_qq (set Int)) (v_pp (set Int)) (v_oo (set Int)) (v_nn Int) (v_mm Bool)
  (v_ll Bool) (v_kk Bool) (v_jj Bool) (v_bbzz Int) (v_bbyy Int) (v_bbxx Int)
  (v_bbww Int) (v_bbvv Int) (v_bbuu Bool) (v_bbtt Bool) (v_bbss Bool)
  (v_bbrr Bool) (v_bbqq Bool) (v_bbpp Int) (v_bboo Int) (v_bbnn Int)
  (v_bbmm Int) (v_bbll Int) (v_bbkk Int) (v_bbjj Int)
  (v_bbii (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (v_bbhh Int) (v_bbgg Int) (v_bbff Int) (v_bbee Int)
  (v_bbdd Int) (v_bbcc Int) (v_bbbb Int) (v_bbaa (set Int)))
  (= (f32 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbzz v_bbyy v_bbxx v_bbww v_bbvv v_bbuu v_bbtt v_bbss
  v_bbrr v_bbqq v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
  v_bbhh v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (exists ((v_bbcc1 Int) (v_bbdd1 Int) (v_bbee1 Int) (v_bbff1 Int)
  (v_bbgg1 Int) (v_bbhh1 Int))
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (mem int (t2tb16 v_bbcc1) (t2tb15 (mk 1 v_bbbb))) (mem int
  (t2tb16 v_bbdd1) (t2tb15 (mk v_bbcc1 v_bbbb)))) (mem int (t2tb16 v_bbee1)
  (t2tb15 (mk v_bbdd1 v_bbbb)))) (mem int (t2tb16 v_bbff1)
  (t2tb15 (mk v_bbee1 v_bbbb)))) (mem int (t2tb16 v_bbgg1)
  (t2tb15 (mk v_bbff1 v_bbbb)))) (mem int (t2tb16 v_bbhh1)
  (t2tb15 (mk v_bbgg1 v_bbbb)))) (mem (set1 int)
  (t2tb15 (mk v_bbcc1 v_bbdd1))
  (power int
  (t2tb15
  (apply4 v_bbii (Tuple23 (Tuple22 (Tuple21 true true) false) false))))))
  (not (mem int (t2tb16 (+ v_bbdd1 1))
  (t2tb15
  (apply4 v_bbii (Tuple23 (Tuple22 (Tuple21 true true) false) false))))))
  (mem (set1 int) (t2tb15 (mk (+ v_bbdd1 1) v_bbee1))
  (power int
  (union int
  (t2tb15
  (apply4 v_bbii (Tuple23 (Tuple22 (Tuple21 true true) false) false)))
  (t2tb15
  (apply4 v_bbii (Tuple23 (Tuple22 (Tuple21 false true) false) false)))))))
  (mem (set1 int) (t2tb15 (mk (+ v_bbee1 1) v_bbff1))
  (power int
  (t2tb15
  (apply4 v_bbii (Tuple23 (Tuple22 (Tuple21 false true) false) false))))))
  (not (mem int (t2tb16 (+ v_bbff1 1))
  (t2tb15
  (apply4 v_bbii (Tuple23 (Tuple22 (Tuple21 false true) false) false))))))
  (mem (set1 int) (t2tb15 (mk (+ v_bbff1 1) v_bbgg1))
  (power int
  (union int
  (union int
  (union int
  (t2tb15
  (apply4 v_bbii (Tuple23 (Tuple22 (Tuple21 false true) true) false)))
  (t2tb15
  (apply4 v_bbii (Tuple23 (Tuple22 (Tuple21 true true) false) false))))
  (t2tb15 (apply4 v_bbii (Tuple23 (Tuple22 (Tuple21 true true) true) false))))
  (t2tb15
  (apply4 v_bbii (Tuple23 (Tuple22 (Tuple21 false true) false) false)))))))
  (forall ((v_bbjj1 Int) (v_bbkk1 Int))
  (=>
  (and
  (and (mem int (t2tb16 v_bbjj1) (t2tb15 (mk (+ v_bbff1 1) v_bbgg1))) (mem
  int (t2tb16 v_bbkk1) (t2tb15 (mk (+ v_bbff1 1) v_bbgg1)))) (mem (set1 int)
  (t2tb15 (mk v_bbjj1 v_bbkk1))
  (power int
  (t2tb15
  (apply4 v_bbii (Tuple23 (Tuple22 (Tuple21 false true) true) false))))))
  (<= (+ (- v_bbkk1 v_bbjj1) 1) v_bbll)))) (mem (set1 int)
  (t2tb15 (mk (+ v_bbgg1 1) v_bbhh1))
  (power int
  (t2tb15
  (apply4 v_bbii (Tuple23 (Tuple22 (Tuple21 false true) true) false))))))
  (mem (set1 int) (t2tb15 (mk (+ v_bbhh1 1) v_bbbb))
  (power int
  (t2tb15
  (apply4 v_bbii (Tuple23 (Tuple22 (Tuple21 false true) true) false))))))
  (= (- v_bbdd1 v_bbcc1) v_bbmm)) (<= (- (- v_bbee1 v_bbdd1) 1) v_bbnn))
  (<= (- (- v_bbgg1 v_bbff1) 1) v_bboo))
  (= (- (- v_bbhh1 v_bbgg1) 1) v_bbll)) (<= (- (- v_bbbb v_bbhh1) 1) v_bbpp))))))

(assert
;; ccaa_1
 ;; File "POwhy_bpo2why/p4/p4_32.why", line 769, characters 7-13
  (not
  (forall ((v_zz (set Int)) (v_yy (set Int)) (v_xx (set Int)) (v_ww Bool)
  (v_vv Bool) (v_uu Bool) (v_tt Bool) (v_ss Int) (v_rr (set Int))
  (v_qq (set Int)) (v_pp (set Int)) (v_oo (set Int)) (v_nn Int) (v_mm Bool)
  (v_ll Bool) (v_kk Bool) (v_jj Bool) (v_bbzz Int) (v_bbyy Int) (v_bbxx Int)
  (v_bbww Int) (v_bbvv Int) (v_bbuu Bool) (v_bbtt Bool) (v_bbss Bool)
  (v_bbrr Bool) (v_bbqq Bool) (v_bbpp Int) (v_bboo Int) (v_bbnn Int)
  (v_bbmm Int) (v_bbll Int) (v_bbkk Int) (v_bbjj Int)
  (v_bbii (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (v_bbhh Int) (v_bbgg Int) (v_bbff Int) (v_bbee Int)
  (v_bbdd Int) (v_bbcc Int) (v_bbbb Int) (v_bbaa (set Int)))
  (=>
  (and (f1 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbzz v_bbyy v_bbxx v_bbww v_bbvv v_bbuu v_bbtt v_bbss
  v_bbrr v_bbqq v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
  v_bbhh v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (and (f2 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbzz v_bbyy v_bbxx v_bbww v_bbvv v_bbuu v_bbtt v_bbss
  v_bbrr v_bbqq v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
  v_bbhh v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa) (f3 v_zz v_yy v_xx
  v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn v_mm v_ll v_kk v_jj
  v_bbzz v_bbyy v_bbxx v_bbww v_bbvv v_bbuu v_bbtt v_bbss v_bbrr v_bbqq
  v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii v_bbhh v_bbgg
  v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa))) (infix_eqeq4
  (apply5
  (times1 (times2 (times3 (times4 b_bool b_bool) b_bool) b_bool)
  (add3 empty4 empty5)) (Tuple23 (Tuple22 (Tuple21 false true) true) false))
  empty4)))))
(check-sat)
