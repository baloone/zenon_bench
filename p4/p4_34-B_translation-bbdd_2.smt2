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

(declare-sort uninterpreted_type1 0)

(declare-fun uninterpreted_type () ty)

(declare-sort tuple2 2)

(declare-fun tuple21 (ty ty) ty)

(declare-fun infix_eqeq (ty uni uni) Bool)

(declare-fun infix_eqeq1 ((set Bool) (set Bool)) Bool)

(declare-fun infix_eqeq2 ((set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))) Bool)

(declare-fun infix_eqeq3 ((set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool)) (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))) Bool)

(declare-fun infix_eqeq4 ((set (tuple2 (tuple2 Bool Bool) Bool))
  (set (tuple2 (tuple2 Bool Bool) Bool))) Bool)

(declare-fun infix_eqeq5 ((set (tuple2 Bool Bool)) (set (tuple2 Bool
  Bool))) Bool)

(declare-fun infix_eqeq6 ((set uninterpreted_type1)
  (set uninterpreted_type1)) Bool)

(declare-fun infix_eqeq7 ((set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)))
  (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))) Bool)

(declare-fun infix_eqeq8 ((set (set uninterpreted_type1))
  (set (set uninterpreted_type1))) Bool)

(declare-fun t2tb202 ((set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type1)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))))) (sort
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))) (t2tb202 x))))

(declare-fun tb2t202 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))))
  (! (= (tb2t202 (t2tb202 i)) i) :pattern ((t2tb202 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type))) j) (= (t2tb202 (tb2t202 j)) j)) :pattern (
  (t2tb202 (tb2t202 j))) )))

(declare-fun t2tb203 ((tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))) (sort
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb203 x))))

(declare-fun tb2t203 (uni) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type1)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))))
  (! (= (tb2t203 (t2tb203 i)) i) :pattern ((t2tb203 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type)) j) (= (t2tb203 (tb2t203 j)) j)) :pattern (
  (t2tb203 (tb2t203 j))) )))

;; infix ==_def
  (assert
  (forall ((s1 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))) (s2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1)))))
  (= (infix_eqeq7 s1 s2)
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))))
  (= (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb203 x) (t2tb202 s1)) (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb203 x) (t2tb202 s2)))))))

(declare-fun t2tb204 ((set (set uninterpreted_type1))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set uninterpreted_type1)))) (sort
  (set1 (set1 uninterpreted_type)) (t2tb204 x))))

(declare-fun tb2t204 (uni) (set (set uninterpreted_type1)))

;; BridgeL
  (assert
  (forall ((i (set (set uninterpreted_type1))))
  (! (= (tb2t204 (t2tb204 i)) i) :pattern ((t2tb204 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (set1 uninterpreted_type)) j)
     (= (t2tb204 (tb2t204 j)) j)) :pattern ((t2tb204 (tb2t204 j))) )))

(declare-fun t2tb205 ((set uninterpreted_type1)) uni)

;; t2tb_sort
  (assert
  (forall ((x (set uninterpreted_type1))) (sort (set1 uninterpreted_type)
  (t2tb205 x))))

(declare-fun tb2t205 (uni) (set uninterpreted_type1))

;; BridgeL
  (assert
  (forall ((i (set uninterpreted_type1)))
  (! (= (tb2t205 (t2tb205 i)) i) :pattern ((t2tb205 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 uninterpreted_type) j) (= (t2tb205 (tb2t205 j)) j)) :pattern (
  (t2tb205 (tb2t205 j))) )))

;; infix ==_def
  (assert
  (forall ((s1 (set (set uninterpreted_type1)))
  (s2 (set (set uninterpreted_type1))))
  (= (infix_eqeq8 s1 s2)
  (forall ((x (set uninterpreted_type1)))
  (= (mem (set1 uninterpreted_type) (t2tb205 x) (t2tb204 s1)) (mem
  (set1 uninterpreted_type) (t2tb205 x) (t2tb204 s2)))))))

(declare-fun t2tb206 (uninterpreted_type1) uni)

;; t2tb_sort
  (assert
  (forall ((x uninterpreted_type1)) (sort uninterpreted_type (t2tb206 x))))

(declare-fun tb2t206 (uni) uninterpreted_type1)

;; BridgeL
  (assert
  (forall ((i uninterpreted_type1))
  (! (= (tb2t206 (t2tb206 i)) i) :pattern ((t2tb206 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort uninterpreted_type j) (= (t2tb206 (tb2t206 j)) j)) :pattern (
  (t2tb206 (tb2t206 j))) )))

;; infix ==_def
  (assert
  (forall ((s1 (set uninterpreted_type1)) (s2 (set uninterpreted_type1)))
  (= (infix_eqeq6 s1 s2)
  (forall ((x uninterpreted_type1))
  (= (mem uninterpreted_type (t2tb206 x) (t2tb205 s1)) (mem
  uninterpreted_type (t2tb206 x) (t2tb205 s2)))))))

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

;; infix ==_def
  (assert
  (forall ((s1 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))))
  (= (infix_eqeq2 s1 s2)
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))
  (= (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb8 x) (t2tb4 s1)) (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb8 x) (t2tb4 s2)))))))

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

;; infix ==_def
  (assert
  (forall ((s1 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (s2 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (= (infix_eqeq3 s1 s2)
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (= (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
  (t2tb5 s1)) (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb9 x) (t2tb5 s2)))))))

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
  (= (infix_eqeq4 s1 s2)
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)))
  (= (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb6 s1)) (mem
  (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb6 s2)))))))

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

;; infix ==_def
  (assert
  (forall ((s1 (set (tuple2 Bool Bool))) (s2 (set (tuple2 Bool Bool))))
  (= (infix_eqeq5 s1 s2)
  (forall ((x (tuple2 Bool Bool)))
  (= (mem (tuple21 bool bool) (t2tb11 x) (t2tb7 s1)) (mem (tuple21 bool bool)
  (t2tb11 x) (t2tb7 s2)))))))

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
  (= (infix_eqeq1 s1 s2)
  (forall ((x Bool))
  (= (mem bool (t2tb12 x) (t2tb2 s1)) (mem bool (t2tb12 x) (t2tb2 s2)))))))

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
  (set uninterpreted_type1)))) (s2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1)))))
  (=> (infix_eqeq7 s1 s2) (= s1 s2))))

;; extensionality
  (assert
  (forall ((s1 (set (set uninterpreted_type1)))
  (s2 (set (set uninterpreted_type1)))) (=> (infix_eqeq8 s1 s2) (= s1 s2))))

;; extensionality
  (assert
  (forall ((s1 (set uninterpreted_type1)) (s2 (set uninterpreted_type1)))
  (=> (infix_eqeq6 s1 s2) (= s1 s2))))

;; extensionality
  (assert
  (forall ((s1 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (=> (infix_eqeq2 s1 s2) (= s1 s2))))

;; extensionality
  (assert
  (forall ((s1 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (s2 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (=> (infix_eqeq3 s1 s2) (= s1 s2))))

;; extensionality
  (assert
  (forall ((s1 (set (tuple2 (tuple2 Bool Bool) Bool)))
  (s2 (set (tuple2 (tuple2 Bool Bool) Bool))))
  (=> (infix_eqeq4 s1 s2) (= s1 s2))))

;; extensionality
  (assert
  (forall ((s1 (set (tuple2 Bool Bool))) (s2 (set (tuple2 Bool Bool))))
  (=> (infix_eqeq5 s1 s2) (= s1 s2))))

;; extensionality
  (assert
  (forall ((s1 (set Bool)) (s2 (set Bool)))
  (=> (infix_eqeq1 s1 s2) (= s1 s2))))

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

(declare-fun empty4 () (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))

(declare-fun empty5 () (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))

(declare-fun empty6 () (set (tuple2 (tuple2 Bool Bool) Bool)))

(declare-fun empty7 () (set (tuple2 Bool Bool)))

(declare-fun empty9 () (set uninterpreted_type1))

(declare-fun empty10 () (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type1))))

(declare-fun empty11 () (set (set uninterpreted_type1)))

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
  (set1 uninterpreted_type)) (t2tb202 empty10)))

;; empty_def1
  (assert (is_empty (set1 uninterpreted_type) (t2tb204 empty11)))

;; empty_def1
  (assert (is_empty uninterpreted_type (t2tb205 empty9)))

;; empty_def1
  (assert (is_empty
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb4 empty4)))

;; empty_def1
  (assert (is_empty (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 empty5)))

;; empty_def1
  (assert (is_empty (tuple21 (tuple21 bool bool) bool) (t2tb6 empty6)))

;; empty_def1
  (assert (is_empty (tuple21 bool bool) (t2tb7 empty7)))

;; empty_def1
  (assert (is_empty bool (t2tb2 empty1)))

;; empty_def1
  (assert (forall ((a ty)) (is_empty a (empty a))))

;; mem_empty
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))))
  (not (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb203 x) (t2tb202 empty10)))))

;; mem_empty
  (assert
  (forall ((x (set uninterpreted_type1)))
  (not (mem (set1 uninterpreted_type) (t2tb205 x) (t2tb204 empty11)))))

;; mem_empty
  (assert
  (forall ((x uninterpreted_type1))
  (not (mem uninterpreted_type (t2tb206 x) (t2tb205 empty9)))))

;; mem_empty
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))
  (not (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb8 x) (t2tb4 empty4)))))

;; mem_empty
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (not (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
  (t2tb5 empty5)))))

;; mem_empty
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)))
  (not (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb6 empty6)))))

;; mem_empty
  (assert
  (forall ((x (tuple2 Bool Bool)))
  (not (mem (tuple21 bool bool) (t2tb11 x) (t2tb7 empty7)))))

;; mem_empty
  (assert (forall ((x Bool)) (not (mem bool (t2tb12 x) (t2tb2 empty1)))))

;; mem_empty
  (assert (forall ((a ty)) (forall ((x uni)) (not (mem a x (empty a))))))

(declare-fun add (ty uni uni) uni)

;; add_sort
  (assert
  (forall ((a ty)) (forall ((x uni) (x1 uni)) (sort (set1 a) (add a x x1)))))

(declare-fun add1 (Bool (set Bool)) (set Bool))

(declare-fun add5 ((set uninterpreted_type1)
  (set (set uninterpreted_type1))) (set (set uninterpreted_type1)))

;; add_def1
  (assert
  (forall ((x (set uninterpreted_type1)) (y (set uninterpreted_type1)))
  (forall ((s (set (set uninterpreted_type1))))
  (= (mem (set1 uninterpreted_type) (t2tb205 x) (t2tb204 (add5 y s)))
  (or (= x y) (mem (set1 uninterpreted_type) (t2tb205 x) (t2tb204 s)))))))

;; add_def1
  (assert
  (forall ((x Bool) (y Bool))
  (forall ((s (set Bool)))
  (= (mem bool (t2tb12 x) (t2tb2 (add1 y s)))
  (or (= x y) (mem bool (t2tb12 x) (t2tb2 s)))))))

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
  (forall ((x (set uninterpreted_type1)) (s (set (set uninterpreted_type1))))
  (=> (mem (set1 uninterpreted_type) (t2tb205 x) (t2tb204 s))
  (= (add5 x
     (tb2t204 (remove (set1 uninterpreted_type) (t2tb205 x) (t2tb204 s)))) s))))

;; add_remove
  (assert
  (forall ((x Bool) (s (set Bool)))
  (=> (mem bool (t2tb12 x) (t2tb2 s))
  (= (add1 x (tb2t2 (remove bool (t2tb12 x) (t2tb2 s)))) s))))

;; add_remove
  (assert
  (forall ((a ty))
  (forall ((x uni) (s uni))
  (=> (sort (set1 a) s) (=> (mem a x s) (= (add a x (remove a x s)) s))))))

;; remove_add
  (assert
  (forall ((x (set uninterpreted_type1)) (s (set (set uninterpreted_type1))))
  (= (tb2t204
     (remove (set1 uninterpreted_type) (t2tb205 x) (t2tb204 (add5 x s)))) 
  (tb2t204 (remove (set1 uninterpreted_type) (t2tb205 x) (t2tb204 s))))))

;; remove_add
  (assert
  (forall ((x Bool) (s (set Bool)))
  (= (tb2t2 (remove bool (t2tb12 x) (t2tb2 (add1 x s)))) (tb2t2
                                                         (remove bool
                                                         (t2tb12 x)
                                                         (t2tb2 s))))))

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
  (assert (forall ((x Bool)) (mem bool (t2tb12 x) (t2tb2 b_bool))))

(declare-fun integer () (set Int))

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

;; mem_integer
  (assert (forall ((x Int)) (mem int (t2tb13 x) (t2tb3 integer))))

(declare-fun natural () (set Int))

;; mem_natural
  (assert
  (forall ((x Int)) (= (mem int (t2tb13 x) (t2tb3 natural)) (<= 0 x))))

(declare-fun natural1 () (set Int))

;; mem_natural1
  (assert
  (forall ((x Int)) (= (mem int (t2tb13 x) (t2tb3 natural1)) (< 0 x))))

(declare-fun nat () (set Int))

;; mem_nat
  (assert
  (forall ((x Int))
  (= (mem int (t2tb13 x) (t2tb3 nat)) (and (<= 0 x) (<= x 2147483647)))))

(declare-fun nat1 () (set Int))

;; mem_nat1
  (assert
  (forall ((x Int))
  (= (mem int (t2tb13 x) (t2tb3 nat1)) (and (< 0 x) (<= x 2147483647)))))

(declare-fun bounded_int () (set Int))

;; mem_bounded_int
  (assert
  (forall ((x Int))
  (= (mem int (t2tb13 x) (t2tb3 bounded_int))
  (and (<= (- 2147483647) x) (<= x 2147483647)))))

(declare-fun mk (Int Int) (set Int))

;; mem_interval
  (assert
  (forall ((x Int) (a Int) (b Int))
  (! (= (mem int (t2tb13 x) (t2tb3 (mk a b))) (and (<= a x) (<= x b))) :pattern ((mem
  int (t2tb13 x) (t2tb3 (mk a b)))) )))

;; interval_empty
  (assert
  (forall ((a Int) (b Int)) (=> (< b a) (= (mk a b) (tb2t3 (empty int))))))

;; interval_add
  (assert
  (forall ((a Int) (b Int))
  (=> (<= a b)
  (= (mk a b) (tb2t3 (add int (t2tb13 b) (t2tb3 (mk a (- b 1)))))))))

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

(declare-fun t2tb207 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type1)))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)))) (t2tb207 x))))

(declare-fun tb2t207 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type1))))))
  (! (= (tb2t207 (t2tb207 i)) i) :pattern ((t2tb207 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type)))) j) (= (t2tb207 (tb2t207 j)) j)) :pattern (
  (t2tb207 (tb2t207 j))) )))

;; mem_non_empty_power
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))) (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1)))))
  (! (= (mem
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type))) (t2tb202 x)
     (non_empty_power
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type)) (t2tb202 y)))
     (and (subset
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type)) (t2tb202 x) (t2tb202 y)) (not (= x empty10)))) :pattern ((mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))) (t2tb202 x)
  (non_empty_power
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb202 y)))) )))

(declare-fun t2tb208 ((set (set (set uninterpreted_type1)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (set uninterpreted_type1))))) (sort
  (set1 (set1 (set1 uninterpreted_type))) (t2tb208 x))))

(declare-fun tb2t208 (uni) (set (set (set uninterpreted_type1))))

;; BridgeL
  (assert
  (forall ((i (set (set (set uninterpreted_type1)))))
  (! (= (tb2t208 (t2tb208 i)) i) :pattern ((t2tb208 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (set1 (set1 uninterpreted_type))) j)
     (= (t2tb208 (tb2t208 j)) j)) :pattern ((t2tb208 (tb2t208 j))) )))

;; mem_non_empty_power
  (assert
  (forall ((x (set (set uninterpreted_type1)))
  (y (set (set uninterpreted_type1))))
  (! (= (mem (set1 (set1 uninterpreted_type)) (t2tb204 x)
     (non_empty_power (set1 uninterpreted_type) (t2tb204 y)))
     (and (subset (set1 uninterpreted_type) (t2tb204 x) (t2tb204 y))
     (not (= x empty11)))) :pattern ((mem
  (set1 (set1 uninterpreted_type)) (t2tb204 x)
  (non_empty_power (set1 uninterpreted_type) (t2tb204 y)))) )))

;; mem_non_empty_power
  (assert
  (forall ((x (set uninterpreted_type1)) (y (set uninterpreted_type1)))
  (! (= (mem (set1 uninterpreted_type) (t2tb205 x)
     (non_empty_power uninterpreted_type (t2tb205 y)))
     (and (subset uninterpreted_type (t2tb205 x) (t2tb205 y))
     (not (= x empty9)))) :pattern ((mem
  (set1 uninterpreted_type) (t2tb205 x)
  (non_empty_power uninterpreted_type (t2tb205 y)))) )))

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

;; mem_non_empty_power
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (y (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))
  (! (= (mem
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb4 x)
     (non_empty_power
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
     (t2tb4 y)))
     (and (subset
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
     (t2tb4 x) (t2tb4 y)) (not (= x empty4)))) :pattern ((mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb4 x)
  (non_empty_power
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb4 y)))) )))

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
  (forall ((r uni) (dom1 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1))))
  (x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))))
  (= (image b
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type)) r
     (add
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type)) (t2tb203 x) (t2tb202 dom1))) (union b
                                                             (image b
                                                             (tuple21
                                                             (tuple21
                                                             (tuple21
                                                             (tuple21 
                                                             bool bool) 
                                                             bool) bool)
                                                             (set1
                                                             uninterpreted_type))
                                                             r
                                                             (add
                                                             (tuple21
                                                             (tuple21
                                                             (tuple21
                                                             (tuple21 
                                                             bool bool) 
                                                             bool) bool)
                                                             (set1
                                                             uninterpreted_type))
                                                             (t2tb203 x)
                                                             (t2tb202
                                                             empty10)))
                                                             (image b
                                                             (tuple21
                                                             (tuple21
                                                             (tuple21
                                                             (tuple21 
                                                             bool bool) 
                                                             bool) bool)
                                                             (set1
                                                             uninterpreted_type))
                                                             r
                                                             (t2tb202 dom1)))))))

;; image_add
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom1 (set (set uninterpreted_type1)))
  (x (set uninterpreted_type1)))
  (= (image b (set1 uninterpreted_type) r (t2tb204 (add5 x dom1))) (union b
                                                                   (image b
                                                                   (set1
                                                                   uninterpreted_type)
                                                                   r
                                                                   (t2tb204
                                                                   (add5 x
                                                                   empty11)))
                                                                   (image b
                                                                   (set1
                                                                   uninterpreted_type)
                                                                   r
                                                                   (t2tb204
                                                                   dom1)))))))

;; image_add
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom1 (set uninterpreted_type1)) (x uninterpreted_type1))
  (= (image b uninterpreted_type r
     (add uninterpreted_type (t2tb206 x) (t2tb205 dom1))) (union b
                                                          (image b
                                                          uninterpreted_type
                                                          r
                                                          (add
                                                          uninterpreted_type
                                                          (t2tb206 x)
                                                          (t2tb205 empty9)))
                                                          (image b
                                                          uninterpreted_type
                                                          r (t2tb205 dom1)))))))

;; image_add
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom1 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))) (x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))
  (= (image b
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)) r
     (add
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
     (t2tb8 x) (t2tb4 dom1))) (union b
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
                              bool) (set1 int)) r (t2tb4 dom1)))))))

;; image_add
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom1 (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))) (x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (= (image b (tuple21 (tuple21 (tuple21 bool bool) bool) bool) r
     (add (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
     (t2tb5 dom1))) (union b
                    (image b
                    (tuple21 (tuple21 (tuple21 bool bool) bool) bool) r
                    (add (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
                    (t2tb9 x) (t2tb5 empty5)))
                    (image b
                    (tuple21 (tuple21 (tuple21 bool bool) bool) bool) r
                    (t2tb5 dom1)))))))

;; image_add
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom1 (set (tuple2 (tuple2 Bool Bool) Bool)))
  (x (tuple2 (tuple2 Bool Bool) Bool)))
  (= (image b (tuple21 (tuple21 bool bool) bool) r
     (add (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb6 dom1))) 
  (union b
  (image b (tuple21 (tuple21 bool bool) bool) r
  (add (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb6 empty6)))
  (image b (tuple21 (tuple21 bool bool) bool) r (t2tb6 dom1)))))))

;; image_add
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom1 (set (tuple2 Bool Bool))) (x (tuple2 Bool Bool)))
  (= (image b (tuple21 bool bool) r
     (add (tuple21 bool bool) (t2tb11 x) (t2tb7 dom1))) (union b
                                                        (image b
                                                        (tuple21 bool bool) r
                                                        (add
                                                        (tuple21 bool bool)
                                                        (t2tb11 x)
                                                        (t2tb7 empty7)))
                                                        (image b
                                                        (tuple21 bool bool) r
                                                        (t2tb7 dom1)))))))

;; image_add
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom1 (set Bool)) (x Bool))
  (= (image b bool r (t2tb2 (add1 x dom1))) (union b
                                            (image b bool r
                                            (t2tb2 (add1 x empty1)))
                                            (image b bool r (t2tb2 dom1)))))))

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

(declare-fun dom1 ((set (tuple2 Bool Bool))) (set Bool))

(declare-fun dom2 ((set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))) (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))

(declare-fun dom3 ((set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type1)))) (set (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool)))

(declare-fun dom4 ((set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))) (set (tuple2 (tuple2 Bool Bool) Bool)))

(declare-fun dom5 ((set (tuple2 (tuple2 Bool Bool) Bool))) (set (tuple2 Bool
  Bool)))

;; dom_def
  (assert
  (forall ((r (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))))
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (= (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
  (t2tb5 (dom3 r)))
  (exists ((y (set uninterpreted_type1))) (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type) (t2tb9 x) (t2tb205 y)) (t2tb202 r)))))))

;; dom_def
  (assert
  (forall ((r (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (= (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
  (t2tb5 (dom2 r)))
  (exists ((y (set Int))) (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb9 x) (t2tb3 y)) (t2tb4 r)))))))

;; dom_def
  (assert
  (forall ((r (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)))
  (= (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb6 (dom4 r)))
  (exists ((y Bool)) (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (Tuple2 (tuple21 (tuple21 bool bool) bool) bool (t2tb10 x) (t2tb12 y))
  (t2tb5 r)))))))

;; dom_def
  (assert
  (forall ((r (set (tuple2 (tuple2 Bool Bool) Bool))))
  (forall ((x (tuple2 Bool Bool)))
  (= (mem (tuple21 bool bool) (t2tb11 x) (t2tb7 (dom5 r)))
  (exists ((y Bool)) (mem (tuple21 (tuple21 bool bool) bool)
  (Tuple2 (tuple21 bool bool) bool (t2tb11 x) (t2tb12 y)) (t2tb6 r)))))))

;; dom_def
  (assert
  (forall ((r (set (tuple2 Bool Bool))))
  (forall ((x Bool))
  (= (mem bool (t2tb12 x) (t2tb2 (dom1 r)))
  (exists ((y Bool)) (mem (tuple21 bool bool)
  (Tuple2 bool bool (t2tb12 x) (t2tb12 y)) (t2tb7 r)))))))

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
  (= (tb2t202
     (dom b
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type))
     (empty
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type)) b)))) empty10)))

;; dom_empty
  (assert
  (forall ((b ty))
  (= (tb2t204
     (dom b (set1 uninterpreted_type)
     (empty (tuple21 (set1 uninterpreted_type) b)))) empty11)))

;; dom_empty
  (assert
  (forall ((b ty))
  (= (tb2t205
     (dom b uninterpreted_type (empty (tuple21 uninterpreted_type b)))) 
  empty9)))

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
  (assert (= (dom3 empty10) empty5))

;; dom_empty
  (assert (= (dom2 empty4) empty5))

;; dom_empty
  (assert
  (forall ((b ty))
  (= (tb2t5
     (dom b (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (empty (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) b)))) 
  empty5)))

;; dom_empty
  (assert (= (dom4 empty5) empty6))

;; dom_empty
  (assert
  (forall ((b ty))
  (= (tb2t6
     (dom b (tuple21 (tuple21 bool bool) bool)
     (empty (tuple21 (tuple21 (tuple21 bool bool) bool) b)))) empty6)))

;; dom_empty
  (assert (= (dom5 empty6) empty7))

;; dom_empty
  (assert
  (forall ((b ty))
  (= (tb2t7
     (dom b (tuple21 bool bool) (empty (tuple21 (tuple21 bool bool) b)))) 
  empty7)))

;; dom_empty
  (assert (= (dom1 empty7) empty1))

;; dom_empty
  (assert
  (forall ((b ty)) (= (tb2t2 (dom b bool (empty (tuple21 bool b)))) empty1)))

;; dom_empty
  (assert
  (forall ((a ty) (b ty)) (= (dom b a (empty (tuple21 a b))) (empty a))))

;; dom_add
  (assert
  (forall ((b ty))
  (forall ((f uni) (x (set uninterpreted_type1)) (y uni))
  (= (tb2t204
     (dom b (set1 uninterpreted_type)
     (add (tuple21 (set1 uninterpreted_type) b)
     (Tuple2 (set1 uninterpreted_type) b (t2tb205 x) y) f))) (add5 x
                                                             (tb2t204
                                                             (dom b
                                                             (set1
                                                             uninterpreted_type)
                                                             f)))))))

;; dom_add
  (assert
  (forall ((f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))) (x (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool)) (y (set uninterpreted_type1)))
  (= (dom3
     (tb2t202
     (add
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type))
     (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type) (t2tb9 x) (t2tb205 y)) (t2tb202 f)))) 
  (tb2t5
  (add (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
  (t2tb5 (dom3 f)))))))

;; dom_add
  (assert
  (forall ((f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (y (set Int)))
  (= (dom2
     (tb2t4
     (add
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
     (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
     (t2tb9 x) (t2tb3 y)) (t2tb4 f)))) (tb2t5
                                       (add
                                       (tuple21
                                       (tuple21 (tuple21 bool bool) bool)
                                       bool) (t2tb9 x) (t2tb5 (dom2 f)))))))

;; dom_add
  (assert
  (forall ((f (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (x (tuple2 (tuple2 Bool Bool) Bool)) (y Bool))
  (= (dom4
     (tb2t5
     (add (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (Tuple2 (tuple21 (tuple21 bool bool) bool) bool (t2tb10 x) (t2tb12 y))
     (t2tb5 f)))) (tb2t6
                  (add (tuple21 (tuple21 bool bool) bool) (t2tb10 x)
                  (t2tb6 (dom4 f)))))))

;; dom_add
  (assert
  (forall ((f (set (tuple2 (tuple2 Bool Bool) Bool))) (x (tuple2 Bool Bool))
  (y Bool))
  (= (dom5
     (tb2t6
     (add (tuple21 (tuple21 bool bool) bool)
     (Tuple2 (tuple21 bool bool) bool (t2tb11 x) (t2tb12 y)) (t2tb6 f)))) 
  (tb2t7 (add (tuple21 bool bool) (t2tb11 x) (t2tb7 (dom5 f)))))))

;; dom_add
  (assert
  (forall ((f (set (tuple2 Bool Bool))) (x Bool) (y Bool))
  (= (dom1
     (tb2t7
     (add (tuple21 bool bool) (Tuple2 bool bool (t2tb12 x) (t2tb12 y))
     (t2tb7 f)))) (add1 x (dom1 f)))))

;; dom_add
  (assert
  (forall ((b ty))
  (forall ((f uni) (x Bool) (y uni))
  (= (tb2t2
     (dom b bool (add (tuple21 bool b) (Tuple2 bool b (t2tb12 x) y) f))) 
  (add1 x (tb2t2 (dom b bool f)))))))

;; dom_add
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (x uni) (y uni))
  (= (dom b a (add (tuple21 a b) (Tuple2 a b x y) f)) (add a x (dom b a f))))))

;; dom_singleton
  (assert
  (forall ((b ty))
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))) (y uni))
  (= (tb2t202
     (dom b
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type))
     (add
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type)) b)
     (Tuple2
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type)) b (t2tb203 x) y)
     (empty
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type)) b))))) (tb2t202
                                       (add
                                       (tuple21
                                       (tuple21
                                       (tuple21 (tuple21 bool bool) bool)
                                       bool) (set1 uninterpreted_type))
                                       (t2tb203 x) (t2tb202 empty10)))))))

;; dom_singleton
  (assert
  (forall ((b ty))
  (forall ((x (set uninterpreted_type1)) (y uni))
  (= (tb2t204
     (dom b (set1 uninterpreted_type)
     (add (tuple21 (set1 uninterpreted_type) b)
     (Tuple2 (set1 uninterpreted_type) b (t2tb205 x) y)
     (empty (tuple21 (set1 uninterpreted_type) b))))) (add5 x empty11)))))

;; dom_singleton
  (assert
  (forall ((b ty))
  (forall ((x uninterpreted_type1) (y uni))
  (= (tb2t205
     (dom b uninterpreted_type
     (add (tuple21 uninterpreted_type b)
     (Tuple2 uninterpreted_type b (t2tb206 x) y)
     (empty (tuple21 uninterpreted_type b))))) (tb2t205
                                               (add uninterpreted_type
                                               (t2tb206 x) (t2tb205 empty9)))))))

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
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (y (set uninterpreted_type1)))
  (= (dom3
     (tb2t202
     (add
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type))
     (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type) (t2tb9 x) (t2tb205 y)) (t2tb202 empty10)))) 
  (tb2t5
  (add (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
  (t2tb5 empty5))))))

;; dom_singleton
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)) (y (set Int)))
  (= (dom2
     (tb2t4
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
  (= (dom4
     (tb2t5
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
  (forall ((x (tuple2 Bool Bool)) (y Bool))
  (= (dom5
     (tb2t6
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
  (= (dom1
     (tb2t7
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
  (set uninterpreted_type1)))) (s (set (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool))) (t (set (set uninterpreted_type1))))
  (= (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))) (t2tb202 f)
  (infix_mnmngt (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb5 s) (t2tb204 t)))
  (and (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))) (t2tb202 f)
  (infix_plmngt (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb5 s) (t2tb204 t)))
  (= (dom3 f) s)))))

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

;; mem_total_functions
  (assert
  (forall ((f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (t (set (set Int))))
  (= (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb4 f)
  (infix_mnmngt (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 s) (t2tb1 t)))
  (and (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb4 f)
  (infix_plmngt (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 s) (t2tb1 t))) (= (dom2 f) s)))))

;; mem_total_functions
  (assert
  (forall ((f (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (s (set (tuple2 (tuple2 Bool Bool) Bool))) (t (set Bool)))
  (= (mem (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb5 f)
  (infix_mnmngt bool (tuple21 (tuple21 bool bool) bool) (t2tb6 s) (t2tb2 t)))
  (and (mem (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (t2tb5 f)
  (infix_plmngt bool (tuple21 (tuple21 bool bool) bool) (t2tb6 s) (t2tb2 t)))
  (= (dom4 f) s)))))

;; mem_total_functions
  (assert
  (forall ((f (set (tuple2 (tuple2 Bool Bool) Bool))) (s (set (tuple2 Bool
  Bool))) (t (set Bool)))
  (= (mem (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb6 f)
  (infix_mnmngt bool (tuple21 bool bool) (t2tb7 s) (t2tb2 t)))
  (and (mem (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb6 f)
  (infix_plmngt bool (tuple21 bool bool) (t2tb7 s) (t2tb2 t)))
  (= (dom5 f) s)))))

;; mem_total_functions
  (assert
  (forall ((f (set (tuple2 Bool Bool))) (s (set Bool)) (t (set Bool)))
  (= (mem (set1 (tuple21 bool bool)) (t2tb7 f)
  (infix_mnmngt bool bool (t2tb2 s) (t2tb2 t)))
  (and (mem (set1 (tuple21 bool bool)) (t2tb7 f)
  (infix_plmngt bool bool (t2tb2 s) (t2tb2 t))) (= (dom1 f) s)))))

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
  (t (set (set uninterpreted_type1))) (x (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool)) (y (set uninterpreted_type1)))
  (=>
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
  (t2tb5 s)) (mem (set1 uninterpreted_type) (t2tb205 y) (t2tb204 t))) (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type) (t2tb9 x) (t2tb205 y)) (t2tb202 empty10))
  (infix_plmngt (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb5 s) (t2tb204 t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (t (set (set Int))) (x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (y (set Int)))
  (=>
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
  (t2tb5 s)) (mem (set1 int) (t2tb3 y) (t2tb1 t))) (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb9 x) (t2tb3 y)) (t2tb4 empty4))
  (infix_plmngt (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 s) (t2tb1 t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set (tuple2 (tuple2 Bool Bool) Bool))) (t (set Bool))
  (x (tuple2 (tuple2 Bool Bool) Bool)) (y Bool))
  (=>
  (and (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb6 s)) (mem
  bool (t2tb12 y) (t2tb2 t))) (mem
  (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (add (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (Tuple2 (tuple21 (tuple21 bool bool) bool) bool (t2tb10 x) (t2tb12 y))
  (t2tb5 empty5))
  (infix_plmngt bool (tuple21 (tuple21 bool bool) bool) (t2tb6 s) (t2tb2 t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set (tuple2 Bool Bool))) (t (set Bool)) (x (tuple2 Bool Bool))
  (y Bool))
  (=>
  (and (mem (tuple21 bool bool) (t2tb11 x) (t2tb7 s)) (mem bool (t2tb12 y)
  (t2tb2 t))) (mem (set1 (tuple21 (tuple21 bool bool) bool))
  (add (tuple21 (tuple21 bool bool) bool)
  (Tuple2 (tuple21 bool bool) bool (t2tb11 x) (t2tb12 y)) (t2tb6 empty6))
  (infix_plmngt bool (tuple21 bool bool) (t2tb7 s) (t2tb2 t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set Bool)) (t (set Bool)) (x Bool) (y Bool))
  (=> (and (mem bool (t2tb12 x) (t2tb2 s)) (mem bool (t2tb12 y) (t2tb2 t)))
  (mem (set1 (tuple21 bool bool))
  (add (tuple21 bool bool) (Tuple2 bool bool (t2tb12 x) (t2tb12 y))
  (t2tb7 empty7)) (infix_plmngt bool bool (t2tb2 s) (t2tb2 t))))))

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
  (set uninterpreted_type1)))) (! (mem
  (set1
  (tuple21 a
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))))
  (add
  (tuple21 a
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)))
  (Tuple2 a
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) x (t2tb203 y))
  (empty
  (tuple21 a
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)))))
  (infix_mnmngt
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) a (add a x (empty a))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb203 y) (t2tb202 empty10)))) :pattern (
  (add
  (tuple21 a
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)))
  (Tuple2 a
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) x (t2tb203 y))
  (empty
  (tuple21 a
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)))))) ))))

;; singleton_is_function
  (assert
  (forall ((a ty))
  (forall ((x uni) (y (set uninterpreted_type1))) (! (mem
  (set1 (tuple21 a (set1 uninterpreted_type)))
  (add (tuple21 a (set1 uninterpreted_type))
  (Tuple2 a (set1 uninterpreted_type) x (t2tb205 y))
  (empty (tuple21 a (set1 uninterpreted_type))))
  (infix_mnmngt (set1 uninterpreted_type) a (add a x (empty a))
  (t2tb204 (add5 y empty11)))) :pattern ((add
                                         (tuple21 a
                                         (set1 uninterpreted_type))
                                         (Tuple2 a (set1 uninterpreted_type)
                                         x (t2tb205 y))
                                         (empty
                                         (tuple21 a
                                         (set1 uninterpreted_type))))) ))))

;; singleton_is_function
  (assert
  (forall ((a ty))
  (forall ((x uni) (y uninterpreted_type1)) (! (mem
  (set1 (tuple21 a uninterpreted_type))
  (add (tuple21 a uninterpreted_type)
  (Tuple2 a uninterpreted_type x (t2tb206 y))
  (empty (tuple21 a uninterpreted_type)))
  (infix_mnmngt uninterpreted_type a (add a x (empty a))
  (add uninterpreted_type (t2tb206 y) (t2tb205 empty9)))) :pattern ((add
                                                                    (tuple21
                                                                    a
                                                                    uninterpreted_type)
                                                                    (Tuple2 a
                                                                    uninterpreted_type
                                                                    x
                                                                    (t2tb206
                                                                    y))
                                                                    (empty
                                                                    (tuple21
                                                                    a
                                                                    uninterpreted_type)))) ))))

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

(declare-fun t2tb209 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1))
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)) (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1))))))) (sort
  (set1
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))))) (t2tb209 x))))

(declare-fun tb2t209 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1))
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)) (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1)))))))
  (! (= (tb2t209 (t2tb209 i)) i) :pattern ((t2tb209 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type))
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type))))) j) (= (t2tb209 (tb2t209 j)) j)) :pattern (
  (t2tb209 (tb2t209 j))) )))

(declare-fun t2tb210 ((set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)) (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type1)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)))))) (sort
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)))) (t2tb210 x))))

(declare-fun tb2t210 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1))
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type1)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1))))))
  (! (= (tb2t210 (t2tb210 i)) i) :pattern ((t2tb210 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type))
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type)))) j) (= (t2tb210 (tb2t210 j)) j)) :pattern (
  (t2tb210 (tb2t210 j))) )))

(declare-fun t2tb211 ((tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)) (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type1))))) (sort
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))) (t2tb211 x))))

(declare-fun tb2t211 (uni) (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)) (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1))))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type1)))))
  (! (= (tb2t211 (t2tb211 i)) i) :pattern ((t2tb211 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type))
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type))) j) (= (t2tb211 (tb2t211 j)) j)) :pattern (
  (t2tb211 (tb2t211 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))) (y (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)))) (! (mem
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))))
  (add
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)))
  (Tuple2
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb203 x) (t2tb203 y))
  (empty
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)))))
  (infix_mnmngt
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb203 x) (t2tb202 empty10))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb203 y) (t2tb202 empty10)))) :pattern (
  (tb2t210
  (add
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)))
  (Tuple2
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb203 x) (t2tb203 y))
  (empty
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))))))) )))

(declare-fun t2tb212 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1))
  (set uninterpreted_type1))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)) (set uninterpreted_type1)))))) (sort
  (set1
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (set1 uninterpreted_type)))) (t2tb212 x))))

(declare-fun tb2t212 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1)) (set uninterpreted_type1)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)) (set uninterpreted_type1))))))
  (! (= (tb2t212 (t2tb212 i)) i) :pattern ((t2tb212 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type)) (set1 uninterpreted_type)))) j)
     (= (t2tb212 (tb2t212 j)) j)) :pattern ((t2tb212 (tb2t212 j))) )))

(declare-fun t2tb213 ((set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)) (set uninterpreted_type1)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type1)) (set uninterpreted_type1))))) (sort
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (set1 uninterpreted_type))) (t2tb213 x))))

(declare-fun tb2t213 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1)) (set uninterpreted_type1))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type1)) (set uninterpreted_type1)))))
  (! (= (tb2t213 (t2tb213 i)) i) :pattern ((t2tb213 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type)) (set1 uninterpreted_type))) j)
     (= (t2tb213 (tb2t213 j)) j)) :pattern ((t2tb213 (tb2t213 j))) )))

(declare-fun t2tb214 ((tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)) (set uninterpreted_type1))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)) (set uninterpreted_type1)))) (sort
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (set1 uninterpreted_type)) (t2tb214 x))))

(declare-fun tb2t214 (uni) (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)) (set uninterpreted_type1)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)) (set uninterpreted_type1))))
  (! (= (tb2t214 (t2tb214 i)) i) :pattern ((t2tb214 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type)) (set1 uninterpreted_type)) j)
     (= (t2tb214 (tb2t214 j)) j)) :pattern ((t2tb214 (tb2t214 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))) (y (set uninterpreted_type1))) (! (mem
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (set1 uninterpreted_type)))
  (add
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (set1 uninterpreted_type))
  (Tuple2
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (set1 uninterpreted_type) (t2tb203 x)
  (t2tb205 y))
  (empty
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (set1 uninterpreted_type))))
  (infix_mnmngt (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb203 x) (t2tb202 empty10))
  (t2tb204 (add5 y empty11)))) :pattern ((tb2t213
                                         (add
                                         (tuple21
                                         (tuple21
                                         (tuple21
                                         (tuple21 (tuple21 bool bool) bool)
                                         bool) (set1 uninterpreted_type))
                                         (set1 uninterpreted_type))
                                         (Tuple2
                                         (tuple21
                                         (tuple21
                                         (tuple21 (tuple21 bool bool) bool)
                                         bool) (set1 uninterpreted_type))
                                         (set1 uninterpreted_type)
                                         (t2tb203 x) (t2tb205 y))
                                         (empty
                                         (tuple21
                                         (tuple21
                                         (tuple21
                                         (tuple21 (tuple21 bool bool) bool)
                                         bool) (set1 uninterpreted_type))
                                         (set1 uninterpreted_type)))))) )))

(declare-fun t2tb215 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1)) uninterpreted_type1)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)) uninterpreted_type1))))) (sort
  (set1
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) uninterpreted_type))) (t2tb215 x))))

(declare-fun tb2t215 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1)) uninterpreted_type1))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)) uninterpreted_type1)))))
  (! (= (tb2t215 (t2tb215 i)) i) :pattern ((t2tb215 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type)) uninterpreted_type))) j)
     (= (t2tb215 (tb2t215 j)) j)) :pattern ((t2tb215 (tb2t215 j))) )))

(declare-fun t2tb216 ((set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)) uninterpreted_type1))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type1)) uninterpreted_type1)))) (sort
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) uninterpreted_type)) (t2tb216 x))))

(declare-fun tb2t216 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1)) uninterpreted_type1)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type1)) uninterpreted_type1))))
  (! (= (tb2t216 (t2tb216 i)) i) :pattern ((t2tb216 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type)) uninterpreted_type)) j)
     (= (t2tb216 (tb2t216 j)) j)) :pattern ((t2tb216 (tb2t216 j))) )))

(declare-fun t2tb217 ((tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)) uninterpreted_type1)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)) uninterpreted_type1))) (sort
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) uninterpreted_type) (t2tb217 x))))

(declare-fun tb2t217 (uni) (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)) uninterpreted_type1))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)) uninterpreted_type1)))
  (! (= (tb2t217 (t2tb217 i)) i) :pattern ((t2tb217 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type)) uninterpreted_type) j)
     (= (t2tb217 (tb2t217 j)) j)) :pattern ((t2tb217 (tb2t217 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))) (y uninterpreted_type1)) (! (mem
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) uninterpreted_type))
  (add
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) uninterpreted_type)
  (Tuple2
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) uninterpreted_type (t2tb203 x) (t2tb206 y))
  (empty
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) uninterpreted_type)))
  (infix_mnmngt uninterpreted_type
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb203 x) (t2tb202 empty10))
  (add uninterpreted_type (t2tb206 y) (t2tb205 empty9)))) :pattern ((tb2t216
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
                                                                    uninterpreted_type))
                                                                    uninterpreted_type)
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
                                                                    uninterpreted_type))
                                                                    uninterpreted_type
                                                                    (t2tb203
                                                                    x)
                                                                    (t2tb206
                                                                    y))
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
                                                                    uninterpreted_type))
                                                                    uninterpreted_type))))) )))

(declare-fun t2tb218 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1))
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)) (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))))) (sort
  (set1
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (t2tb218 x))))

(declare-fun tb2t218 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1))
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)) (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))))))
  (! (= (tb2t218 (t2tb218 i)) i) :pattern ((t2tb218 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb218 (tb2t218 j)) j) :pattern ((t2tb218 (tb2t218 j))) )))

(declare-fun t2tb219 ((set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)) (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type1)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))))) (sort
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (t2tb219 x))))

(declare-fun tb2t219 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1))
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type1)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int))))))
  (! (= (tb2t219 (t2tb219 i)) i) :pattern ((t2tb219 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb219 (tb2t219 j)) j) :pattern ((t2tb219 (tb2t219 j))) )))

(declare-fun t2tb220 ((tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)) (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int))))) (sort
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb220 x))))

(declare-fun tb2t220 (uni) (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)) (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int))))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))))
  (! (= (tb2t220 (t2tb220 i)) i) :pattern ((t2tb220 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb220 (tb2t220 j)) j) :pattern ((t2tb220 (tb2t220 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))) (y (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)))) (! (mem
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (add
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (Tuple2
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb203 x) (t2tb8 y))
  (empty
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (infix_mnmngt
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb203 x) (t2tb202 empty10))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb8 y) (t2tb4 empty4)))) :pattern ((tb2t219
                                        (add
                                        (tuple21
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 uninterpreted_type))
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int)))
                                        (Tuple2
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 uninterpreted_type))
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int)) (t2tb203 x)
                                        (t2tb8 y))
                                        (empty
                                        (tuple21
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 uninterpreted_type))
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int))))))) )))

(declare-fun t2tb221 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1)) (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)) (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool)))))) (sort
  (set1
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))) (t2tb221 x))))

(declare-fun tb2t221 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1)) (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)) (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool)))))) (! (= (tb2t221 (t2tb221 i)) i) :pattern ((t2tb221 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type))
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))) j)
     (= (t2tb221 (tb2t221 j)) j)) :pattern ((t2tb221 (tb2t221 j))) )))

(declare-fun t2tb222 ((set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)) (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type1)) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))))) (sort
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))) (t2tb222 x))))

(declare-fun tb2t222 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1)) (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type1)) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))))) (! (= (tb2t222 (t2tb222 i)) i) :pattern ((t2tb222 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type))
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool))) j)
     (= (t2tb222 (tb2t222 j)) j)) :pattern ((t2tb222 (tb2t222 j))) )))

(declare-fun t2tb223 ((tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)) (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool)))) (sort
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb223 x))))

(declare-fun tb2t223 (uni) (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)) (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool)))) (! (= (tb2t223 (t2tb223 i)) i) :pattern ((t2tb223 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type))
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) j)
     (= (t2tb223 (tb2t223 j)) j)) :pattern ((t2tb223 (tb2t223 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))) (y (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))) (! (mem
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))
  (add
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (Tuple2
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb203 x) (t2tb9 y))
  (empty
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))))
  (infix_mnmngt (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb203 x) (t2tb202 empty10))
  (add (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 y)
  (t2tb5 empty5)))) :pattern ((tb2t222
                              (add
                              (tuple21
                              (tuple21
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool) (set1 uninterpreted_type))
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool))
                              (Tuple2
                              (tuple21
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool) (set1 uninterpreted_type))
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool) (t2tb203 x) (t2tb9 y))
                              (empty
                              (tuple21
                              (tuple21
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool) (set1 uninterpreted_type))
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool)))))) )))

(declare-fun t2tb224 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1)) (tuple2 (tuple2 Bool Bool)
  Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)) (tuple2 (tuple2 Bool Bool)
  Bool)))))) (sort
  (set1
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (tuple21 (tuple21 bool bool) bool))))
  (t2tb224 x))))

(declare-fun tb2t224 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1)) (tuple2 (tuple2 Bool Bool)
  Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)) (tuple2 (tuple2 Bool Bool)
  Bool)))))) (! (= (tb2t224 (t2tb224 i)) i) :pattern ((t2tb224 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type)) (tuple21 (tuple21 bool bool) bool)))) j)
     (= (t2tb224 (tb2t224 j)) j)) :pattern ((t2tb224 (tb2t224 j))) )))

(declare-fun t2tb225 ((set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)) (tuple2 (tuple2 Bool Bool)
  Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type1)) (tuple2 (tuple2 Bool Bool) Bool))))) (sort
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (tuple21 (tuple21 bool bool) bool)))
  (t2tb225 x))))

(declare-fun tb2t225 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1)) (tuple2 (tuple2 Bool Bool)
  Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type1)) (tuple2 (tuple2 Bool Bool) Bool)))))
  (! (= (tb2t225 (t2tb225 i)) i) :pattern ((t2tb225 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type)) (tuple21 (tuple21 bool bool) bool))) j)
     (= (t2tb225 (tb2t225 j)) j)) :pattern ((t2tb225 (tb2t225 j))) )))

(declare-fun t2tb226 ((tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)) (tuple2 (tuple2 Bool Bool)
  Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)) (tuple2 (tuple2 Bool Bool) Bool)))) (sort
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (tuple21 (tuple21 bool bool) bool))
  (t2tb226 x))))

(declare-fun tb2t226 (uni) (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)) (tuple2 (tuple2 Bool Bool) Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)) (tuple2 (tuple2 Bool Bool) Bool))))
  (! (= (tb2t226 (t2tb226 i)) i) :pattern ((t2tb226 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type)) (tuple21 (tuple21 bool bool) bool)) j)
     (= (t2tb226 (tb2t226 j)) j)) :pattern ((t2tb226 (tb2t226 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))) (y (tuple2 (tuple2 Bool Bool) Bool))) (! (mem
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (tuple21 (tuple21 bool bool) bool)))
  (add
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (tuple21 (tuple21 bool bool) bool))
  (Tuple2
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (tuple21 (tuple21 bool bool) bool) (t2tb203 x)
  (t2tb10 y))
  (empty
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (tuple21 (tuple21 bool bool) bool))))
  (infix_mnmngt (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb203 x) (t2tb202 empty10))
  (add (tuple21 (tuple21 bool bool) bool) (t2tb10 y) (t2tb6 empty6)))) :pattern (
  (tb2t225
  (add
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (tuple21 (tuple21 bool bool) bool))
  (Tuple2
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (tuple21 (tuple21 bool bool) bool) (t2tb203 x)
  (t2tb10 y))
  (empty
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (tuple21 (tuple21 bool bool) bool)))))) )))

(declare-fun t2tb227 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1)) (tuple2 Bool Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)) (tuple2 Bool Bool)))))) (sort
  (set1
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (tuple21 bool bool)))) (t2tb227 x))))

(declare-fun tb2t227 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1)) (tuple2 Bool Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)) (tuple2 Bool Bool))))))
  (! (= (tb2t227 (t2tb227 i)) i) :pattern ((t2tb227 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type)) (tuple21 bool bool)))) j)
     (= (t2tb227 (tb2t227 j)) j)) :pattern ((t2tb227 (tb2t227 j))) )))

(declare-fun t2tb228 ((set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)) (tuple2 Bool Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type1)) (tuple2 Bool Bool))))) (sort
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (tuple21 bool bool))) (t2tb228 x))))

(declare-fun tb2t228 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1)) (tuple2 Bool Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type1)) (tuple2 Bool Bool)))))
  (! (= (tb2t228 (t2tb228 i)) i) :pattern ((t2tb228 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type)) (tuple21 bool bool))) j)
     (= (t2tb228 (tb2t228 j)) j)) :pattern ((t2tb228 (tb2t228 j))) )))

(declare-fun t2tb229 ((tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)) (tuple2 Bool Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)) (tuple2 Bool Bool)))) (sort
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (tuple21 bool bool)) (t2tb229 x))))

(declare-fun tb2t229 (uni) (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)) (tuple2 Bool Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)) (tuple2 Bool Bool))))
  (! (= (tb2t229 (t2tb229 i)) i) :pattern ((t2tb229 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type)) (tuple21 bool bool)) j)
     (= (t2tb229 (tb2t229 j)) j)) :pattern ((t2tb229 (tb2t229 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))) (y (tuple2 Bool Bool))) (! (mem
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (tuple21 bool bool)))
  (add
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (tuple21 bool bool))
  (Tuple2
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (tuple21 bool bool) (t2tb203 x) (t2tb11 y))
  (empty
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (tuple21 bool bool))))
  (infix_mnmngt (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb203 x) (t2tb202 empty10))
  (add (tuple21 bool bool) (t2tb11 y) (t2tb7 empty7)))) :pattern ((tb2t228
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
                                                                  uninterpreted_type))
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
                                                                  (set1
                                                                  uninterpreted_type))
                                                                  (tuple21
                                                                  bool 
                                                                  bool)
                                                                  (t2tb203 x)
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
                                                                  (set1
                                                                  uninterpreted_type))
                                                                  (tuple21
                                                                  bool 
                                                                  bool)))))) )))

(declare-fun t2tb230 ((set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)) Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type1)) Bool)))) (sort
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) bool)) (t2tb230 x))))

(declare-fun tb2t230 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1)) Bool)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type1)) Bool))))
  (! (= (tb2t230 (t2tb230 i)) i) :pattern ((t2tb230 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type)) bool)) j) (= (t2tb230 (tb2t230 j)) j)) :pattern (
  (t2tb230 (tb2t230 j))) )))

(declare-fun t2tb231 ((tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)) Bool)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)) Bool))) (sort
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) bool) (t2tb231 x))))

(declare-fun tb2t231 (uni) (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)) Bool))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)) Bool)))
  (! (= (tb2t231 (t2tb231 i)) i) :pattern ((t2tb231 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type)) bool) j) (= (t2tb231 (tb2t231 j)) j)) :pattern (
  (t2tb231 (tb2t231 j))) )))

(declare-fun t2tb232 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1)) Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)) Bool))))) (sort
  (set1
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) bool))) (t2tb232 x))))

(declare-fun tb2t232 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1)) Bool))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)) Bool)))))
  (! (= (tb2t232 (t2tb232 i)) i) :pattern ((t2tb232 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type)) bool))) j) (= (t2tb232 (tb2t232 j)) j)) :pattern (
  (t2tb232 (tb2t232 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))) (y Bool)) (! (mem
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) bool))
  (add
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) bool)
  (Tuple2
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) bool (t2tb203 x) (t2tb12 y))
  (empty
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) bool)))
  (infix_mnmngt bool
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb203 x) (t2tb202 empty10))
  (t2tb2 (add1 y empty1)))) :pattern ((tb2t230
                                      (add
                                      (tuple21
                                      (tuple21
                                      (tuple21
                                      (tuple21 (tuple21 bool bool) bool)
                                      bool) (set1 uninterpreted_type)) 
                                      bool)
                                      (Tuple2
                                      (tuple21
                                      (tuple21
                                      (tuple21 (tuple21 bool bool) bool)
                                      bool) (set1 uninterpreted_type)) 
                                      bool (t2tb203 x) (t2tb12 y))
                                      (empty
                                      (tuple21
                                      (tuple21
                                      (tuple21
                                      (tuple21 (tuple21 bool bool) bool)
                                      bool) (set1 uninterpreted_type)) 
                                      bool))))) )))

;; singleton_is_function
  (assert
  (forall ((b ty))
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))) (y uni)) (! (mem
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) b))
  (add
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) b)
  (Tuple2
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) b (t2tb203 x) y)
  (empty
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) b)))
  (infix_mnmngt b
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb203 x) (t2tb202 empty10))
  (add b y (empty b)))) :pattern ((add
                                  (tuple21
                                  (tuple21
                                  (tuple21 (tuple21 (tuple21 bool bool) bool)
                                  bool) (set1 uninterpreted_type)) b)
                                  (Tuple2
                                  (tuple21
                                  (tuple21 (tuple21 (tuple21 bool bool) bool)
                                  bool) (set1 uninterpreted_type)) b
                                  (t2tb203 x) y)
                                  (empty
                                  (tuple21
                                  (tuple21
                                  (tuple21 (tuple21 (tuple21 bool bool) bool)
                                  bool) (set1 uninterpreted_type)) b)))) ))))

(declare-fun t2tb233 ((set (set (tuple2 (set uninterpreted_type1)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (set uninterpreted_type1)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))))))) (sort
  (set1
  (set1
  (tuple21 (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))))) (t2tb233 x))))

(declare-fun tb2t233 (uni) (set (set (tuple2 (set uninterpreted_type1)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (set uninterpreted_type1)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))))))
  (! (= (tb2t233 (t2tb233 i)) i) :pattern ((t2tb233 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21 (set1 uninterpreted_type)
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type))))) j) (= (t2tb233 (tb2t233 j)) j)) :pattern (
  (t2tb233 (tb2t233 j))) )))

(declare-fun t2tb234 ((set (tuple2 (set uninterpreted_type1)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (set uninterpreted_type1)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))))) (sort
  (set1
  (tuple21 (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)))) (t2tb234 x))))

(declare-fun tb2t234 (uni) (set (tuple2 (set uninterpreted_type1)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (set uninterpreted_type1)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))))))
  (! (= (tb2t234 (t2tb234 i)) i) :pattern ((t2tb234 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21 (set1 uninterpreted_type)
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type)))) j) (= (t2tb234 (tb2t234 j)) j)) :pattern (
  (t2tb234 (tb2t234 j))) )))

(declare-fun t2tb235 ((tuple2 (set uninterpreted_type1)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (set uninterpreted_type1)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))))) (sort
  (tuple21 (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))) (t2tb235 x))))

(declare-fun tb2t235 (uni) (tuple2 (set uninterpreted_type1)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))))

;; BridgeL
  (assert
  (forall ((i (tuple2 (set uninterpreted_type1)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))))
  (! (= (tb2t235 (t2tb235 i)) i) :pattern ((t2tb235 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 (set1 uninterpreted_type)
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type))) j) (= (t2tb235 (tb2t235 j)) j)) :pattern (
  (t2tb235 (tb2t235 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (set uninterpreted_type1))
  (y (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))) (! (mem
  (set1
  (tuple21 (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))))
  (add
  (tuple21 (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)))
  (Tuple2 (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb205 x) (t2tb203 y))
  (empty
  (tuple21 (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)))))
  (infix_mnmngt
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (set1 uninterpreted_type)
  (t2tb204 (add5 x empty11))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb203 y) (t2tb202 empty10)))) :pattern (
  (tb2t234
  (add
  (tuple21 (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)))
  (Tuple2 (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb205 x) (t2tb203 y))
  (empty
  (tuple21 (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))))))) )))

(declare-fun t2tb236 ((set (set (tuple2 (set uninterpreted_type1)
  (set uninterpreted_type1))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (set uninterpreted_type1)
  (set uninterpreted_type1)))))) (sort
  (set1 (set1 (tuple21 (set1 uninterpreted_type) (set1 uninterpreted_type))))
  (t2tb236 x))))

(declare-fun tb2t236 (uni) (set (set (tuple2 (set uninterpreted_type1)
  (set uninterpreted_type1)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (set uninterpreted_type1)
  (set uninterpreted_type1))))))
  (! (= (tb2t236 (t2tb236 i)) i) :pattern ((t2tb236 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1 (tuple21 (set1 uninterpreted_type) (set1 uninterpreted_type)))) j)
     (= (t2tb236 (tb2t236 j)) j)) :pattern ((t2tb236 (tb2t236 j))) )))

(declare-fun t2tb237 ((set (tuple2 (set uninterpreted_type1)
  (set uninterpreted_type1)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (set uninterpreted_type1)
  (set uninterpreted_type1))))) (sort
  (set1 (tuple21 (set1 uninterpreted_type) (set1 uninterpreted_type)))
  (t2tb237 x))))

(declare-fun tb2t237 (uni) (set (tuple2 (set uninterpreted_type1)
  (set uninterpreted_type1))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (set uninterpreted_type1)
  (set uninterpreted_type1)))))
  (! (= (tb2t237 (t2tb237 i)) i) :pattern ((t2tb237 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1 (tuple21 (set1 uninterpreted_type) (set1 uninterpreted_type))) j)
     (= (t2tb237 (tb2t237 j)) j)) :pattern ((t2tb237 (tb2t237 j))) )))

(declare-fun t2tb238 ((tuple2 (set uninterpreted_type1)
  (set uninterpreted_type1))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (set uninterpreted_type1) (set uninterpreted_type1))))
  (sort (tuple21 (set1 uninterpreted_type) (set1 uninterpreted_type))
  (t2tb238 x))))

(declare-fun tb2t238 (uni) (tuple2 (set uninterpreted_type1)
  (set uninterpreted_type1)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (set uninterpreted_type1) (set uninterpreted_type1))))
  (! (= (tb2t238 (t2tb238 i)) i) :pattern ((t2tb238 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (tuple21 (set1 uninterpreted_type) (set1 uninterpreted_type))
     j) (= (t2tb238 (tb2t238 j)) j)) :pattern ((t2tb238 (tb2t238 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (set uninterpreted_type1)) (y (set uninterpreted_type1)))
  (! (mem
  (set1 (tuple21 (set1 uninterpreted_type) (set1 uninterpreted_type)))
  (add (tuple21 (set1 uninterpreted_type) (set1 uninterpreted_type))
  (Tuple2 (set1 uninterpreted_type) (set1 uninterpreted_type) (t2tb205 x)
  (t2tb205 y))
  (empty (tuple21 (set1 uninterpreted_type) (set1 uninterpreted_type))))
  (infix_mnmngt (set1 uninterpreted_type) (set1 uninterpreted_type)
  (t2tb204 (add5 x empty11)) (t2tb204 (add5 y empty11)))) :pattern ((tb2t237
                                                                    (add
                                                                    (tuple21
                                                                    (set1
                                                                    uninterpreted_type)
                                                                    (set1
                                                                    uninterpreted_type))
                                                                    (Tuple2
                                                                    (set1
                                                                    uninterpreted_type)
                                                                    (set1
                                                                    uninterpreted_type)
                                                                    (t2tb205
                                                                    x)
                                                                    (t2tb205
                                                                    y))
                                                                    (empty
                                                                    (tuple21
                                                                    (set1
                                                                    uninterpreted_type)
                                                                    (set1
                                                                    uninterpreted_type)))))) )))

(declare-fun t2tb239 ((set (set (tuple2 (set uninterpreted_type1)
  uninterpreted_type1)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (set uninterpreted_type1)
  uninterpreted_type1))))) (sort
  (set1 (set1 (tuple21 (set1 uninterpreted_type) uninterpreted_type)))
  (t2tb239 x))))

(declare-fun tb2t239 (uni) (set (set (tuple2 (set uninterpreted_type1)
  uninterpreted_type1))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (set uninterpreted_type1)
  uninterpreted_type1)))))
  (! (= (tb2t239 (t2tb239 i)) i) :pattern ((t2tb239 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1 (set1 (tuple21 (set1 uninterpreted_type) uninterpreted_type))) j)
     (= (t2tb239 (tb2t239 j)) j)) :pattern ((t2tb239 (tb2t239 j))) )))

(declare-fun t2tb240 ((set (tuple2 (set uninterpreted_type1)
  uninterpreted_type1))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (set uninterpreted_type1) uninterpreted_type1))))
  (sort (set1 (tuple21 (set1 uninterpreted_type) uninterpreted_type))
  (t2tb240 x))))

(declare-fun tb2t240 (uni) (set (tuple2 (set uninterpreted_type1)
  uninterpreted_type1)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (set uninterpreted_type1) uninterpreted_type1))))
  (! (= (tb2t240 (t2tb240 i)) i) :pattern ((t2tb240 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (tuple21 (set1 uninterpreted_type) uninterpreted_type))
     j) (= (t2tb240 (tb2t240 j)) j)) :pattern ((t2tb240 (tb2t240 j))) )))

(declare-fun t2tb241 ((tuple2 (set uninterpreted_type1)
  uninterpreted_type1)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (set uninterpreted_type1) uninterpreted_type1))) (sort
  (tuple21 (set1 uninterpreted_type) uninterpreted_type) (t2tb241 x))))

(declare-fun tb2t241 (uni) (tuple2 (set uninterpreted_type1)
  uninterpreted_type1))

;; BridgeL
  (assert
  (forall ((i (tuple2 (set uninterpreted_type1) uninterpreted_type1)))
  (! (= (tb2t241 (t2tb241 i)) i) :pattern ((t2tb241 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (tuple21 (set1 uninterpreted_type) uninterpreted_type) j)
     (= (t2tb241 (tb2t241 j)) j)) :pattern ((t2tb241 (tb2t241 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (set uninterpreted_type1)) (y uninterpreted_type1)) (! (mem
  (set1 (tuple21 (set1 uninterpreted_type) uninterpreted_type))
  (add (tuple21 (set1 uninterpreted_type) uninterpreted_type)
  (Tuple2 (set1 uninterpreted_type) uninterpreted_type (t2tb205 x)
  (t2tb206 y))
  (empty (tuple21 (set1 uninterpreted_type) uninterpreted_type)))
  (infix_mnmngt uninterpreted_type (set1 uninterpreted_type)
  (t2tb204 (add5 x empty11))
  (add uninterpreted_type (t2tb206 y) (t2tb205 empty9)))) :pattern ((tb2t240
                                                                    (add
                                                                    (tuple21
                                                                    (set1
                                                                    uninterpreted_type)
                                                                    uninterpreted_type)
                                                                    (Tuple2
                                                                    (set1
                                                                    uninterpreted_type)
                                                                    uninterpreted_type
                                                                    (t2tb205
                                                                    x)
                                                                    (t2tb206
                                                                    y))
                                                                    (empty
                                                                    (tuple21
                                                                    (set1
                                                                    uninterpreted_type)
                                                                    uninterpreted_type))))) )))

(declare-fun t2tb242 ((set (set (tuple2 (set uninterpreted_type1)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (set uninterpreted_type1)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))))
  (sort
  (set1
  (set1
  (tuple21 (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (t2tb242 x))))

(declare-fun tb2t242 (uni) (set (set (tuple2 (set uninterpreted_type1)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (set uninterpreted_type1)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))))
  (! (= (tb2t242 (t2tb242 i)) i) :pattern ((t2tb242 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb242 (tb2t242 j)) j) :pattern ((t2tb242 (tb2t242 j))) )))

(declare-fun t2tb243 ((set (tuple2 (set uninterpreted_type1)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (set uninterpreted_type1)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))) (sort
  (set1
  (tuple21 (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (t2tb243 x))))

(declare-fun tb2t243 (uni) (set (tuple2 (set uninterpreted_type1)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (set uninterpreted_type1)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))))
  (! (= (tb2t243 (t2tb243 i)) i) :pattern ((t2tb243 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb243 (tb2t243 j)) j) :pattern ((t2tb243 (tb2t243 j))) )))

(declare-fun t2tb244 ((tuple2 (set uninterpreted_type1)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (set uninterpreted_type1)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))) (sort
  (tuple21 (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb244 x))))

(declare-fun tb2t244 (uni) (tuple2 (set uninterpreted_type1)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))

;; BridgeL
  (assert
  (forall ((i (tuple2 (set uninterpreted_type1)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))
  (! (= (tb2t244 (t2tb244 i)) i) :pattern ((t2tb244 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb244 (tb2t244 j)) j) :pattern ((t2tb244 (tb2t244 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (set uninterpreted_type1))
  (y (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))
  (! (mem
  (set1
  (tuple21 (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (add
  (tuple21 (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (Tuple2 (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb205 x) (t2tb8 y))
  (empty
  (tuple21 (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (infix_mnmngt
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (set1 uninterpreted_type) (t2tb204 (add5 x empty11))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb8 y) (t2tb4 empty4)))) :pattern ((tb2t243
                                        (add
                                        (tuple21 (set1 uninterpreted_type)
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int)))
                                        (Tuple2 (set1 uninterpreted_type)
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int)) (t2tb205 x)
                                        (t2tb8 y))
                                        (empty
                                        (tuple21 (set1 uninterpreted_type)
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int))))))) )))

(declare-fun t2tb245 ((set (tuple2 (set uninterpreted_type1)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (set uninterpreted_type1)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))) (sort
  (set1
  (tuple21 (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))) (t2tb245 x))))

(declare-fun tb2t245 (uni) (set (tuple2 (set uninterpreted_type1)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (set uninterpreted_type1)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))))
  (! (= (tb2t245 (t2tb245 i)) i) :pattern ((t2tb245 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21 (set1 uninterpreted_type)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool))) j)
     (= (t2tb245 (tb2t245 j)) j)) :pattern ((t2tb245 (tb2t245 j))) )))

(declare-fun t2tb246 ((tuple2 (set uninterpreted_type1)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (set uninterpreted_type1) (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool)))) (sort
  (tuple21 (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb246 x))))

(declare-fun tb2t246 (uni) (tuple2 (set uninterpreted_type1)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (set uninterpreted_type1) (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool))))
  (! (= (tb2t246 (t2tb246 i)) i) :pattern ((t2tb246 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 (set1 uninterpreted_type)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) j)
     (= (t2tb246 (tb2t246 j)) j)) :pattern ((t2tb246 (tb2t246 j))) )))

(declare-fun t2tb247 ((set (set (tuple2 (set uninterpreted_type1)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (set uninterpreted_type1)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))))) (sort
  (set1
  (set1
  (tuple21 (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))) (t2tb247 x))))

(declare-fun tb2t247 (uni) (set (set (tuple2 (set uninterpreted_type1)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (set uninterpreted_type1)
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))))
  (! (= (tb2t247 (t2tb247 i)) i) :pattern ((t2tb247 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21 (set1 uninterpreted_type)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))) j)
     (= (t2tb247 (tb2t247 j)) j)) :pattern ((t2tb247 (tb2t247 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (set uninterpreted_type1)) (y (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool))) (! (mem
  (set1
  (tuple21 (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))
  (add
  (tuple21 (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (Tuple2 (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb205 x) (t2tb9 y))
  (empty
  (tuple21 (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))))
  (infix_mnmngt (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type) (t2tb204 (add5 x empty11))
  (add (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 y)
  (t2tb5 empty5)))) :pattern ((tb2t245
                              (add
                              (tuple21 (set1 uninterpreted_type)
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool))
                              (Tuple2 (set1 uninterpreted_type)
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool) (t2tb205 x) (t2tb9 y))
                              (empty
                              (tuple21 (set1 uninterpreted_type)
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool)))))) )))

(declare-fun t2tb248 ((set (set (tuple2 (set uninterpreted_type1)
  (tuple2 (tuple2 Bool Bool) Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (set uninterpreted_type1)
  (tuple2 (tuple2 Bool Bool) Bool)))))) (sort
  (set1
  (set1
  (tuple21 (set1 uninterpreted_type) (tuple21 (tuple21 bool bool) bool))))
  (t2tb248 x))))

(declare-fun tb2t248 (uni) (set (set (tuple2 (set uninterpreted_type1)
  (tuple2 (tuple2 Bool Bool) Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (set uninterpreted_type1)
  (tuple2 (tuple2 Bool Bool) Bool))))))
  (! (= (tb2t248 (t2tb248 i)) i) :pattern ((t2tb248 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21 (set1 uninterpreted_type) (tuple21 (tuple21 bool bool) bool))))
     j) (= (t2tb248 (tb2t248 j)) j)) :pattern ((t2tb248 (tb2t248 j))) )))

(declare-fun t2tb249 ((set (tuple2 (set uninterpreted_type1)
  (tuple2 (tuple2 Bool Bool) Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (set uninterpreted_type1) (tuple2 (tuple2 Bool
  Bool) Bool))))) (sort
  (set1
  (tuple21 (set1 uninterpreted_type) (tuple21 (tuple21 bool bool) bool)))
  (t2tb249 x))))

(declare-fun tb2t249 (uni) (set (tuple2 (set uninterpreted_type1)
  (tuple2 (tuple2 Bool Bool) Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (set uninterpreted_type1) (tuple2 (tuple2 Bool
  Bool) Bool))))) (! (= (tb2t249 (t2tb249 i)) i) :pattern ((t2tb249 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21 (set1 uninterpreted_type) (tuple21 (tuple21 bool bool) bool)))
     j) (= (t2tb249 (tb2t249 j)) j)) :pattern ((t2tb249 (tb2t249 j))) )))

(declare-fun t2tb250 ((tuple2 (set uninterpreted_type1) (tuple2 (tuple2 Bool
  Bool) Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (set uninterpreted_type1) (tuple2 (tuple2 Bool Bool)
  Bool)))) (sort
  (tuple21 (set1 uninterpreted_type) (tuple21 (tuple21 bool bool) bool))
  (t2tb250 x))))

(declare-fun tb2t250 (uni) (tuple2 (set uninterpreted_type1)
  (tuple2 (tuple2 Bool Bool) Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (set uninterpreted_type1) (tuple2 (tuple2 Bool Bool)
  Bool)))) (! (= (tb2t250 (t2tb250 i)) i) :pattern ((t2tb250 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 (set1 uninterpreted_type) (tuple21 (tuple21 bool bool) bool))
     j) (= (t2tb250 (tb2t250 j)) j)) :pattern ((t2tb250 (tb2t250 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (set uninterpreted_type1)) (y (tuple2 (tuple2 Bool Bool)
  Bool))) (! (mem
  (set1
  (tuple21 (set1 uninterpreted_type) (tuple21 (tuple21 bool bool) bool)))
  (add (tuple21 (set1 uninterpreted_type) (tuple21 (tuple21 bool bool) bool))
  (Tuple2 (set1 uninterpreted_type) (tuple21 (tuple21 bool bool) bool)
  (t2tb205 x) (t2tb10 y))
  (empty
  (tuple21 (set1 uninterpreted_type) (tuple21 (tuple21 bool bool) bool))))
  (infix_mnmngt (tuple21 (tuple21 bool bool) bool) (set1 uninterpreted_type)
  (t2tb204 (add5 x empty11))
  (add (tuple21 (tuple21 bool bool) bool) (t2tb10 y) (t2tb6 empty6)))) :pattern (
  (tb2t249
  (add (tuple21 (set1 uninterpreted_type) (tuple21 (tuple21 bool bool) bool))
  (Tuple2 (set1 uninterpreted_type) (tuple21 (tuple21 bool bool) bool)
  (t2tb205 x) (t2tb10 y))
  (empty
  (tuple21 (set1 uninterpreted_type) (tuple21 (tuple21 bool bool) bool)))))) )))

(declare-fun t2tb251 ((set (set (tuple2 (set uninterpreted_type1)
  (tuple2 Bool Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (set uninterpreted_type1) (tuple2 Bool
  Bool)))))) (sort
  (set1 (set1 (tuple21 (set1 uninterpreted_type) (tuple21 bool bool))))
  (t2tb251 x))))

(declare-fun tb2t251 (uni) (set (set (tuple2 (set uninterpreted_type1)
  (tuple2 Bool Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (set uninterpreted_type1) (tuple2 Bool
  Bool)))))) (! (= (tb2t251 (t2tb251 i)) i) :pattern ((t2tb251 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1 (set1 (tuple21 (set1 uninterpreted_type) (tuple21 bool bool)))) j)
     (= (t2tb251 (tb2t251 j)) j)) :pattern ((t2tb251 (tb2t251 j))) )))

(declare-fun t2tb252 ((set (tuple2 (set uninterpreted_type1) (tuple2 Bool
  Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (set uninterpreted_type1) (tuple2 Bool Bool)))))
  (sort (set1 (tuple21 (set1 uninterpreted_type) (tuple21 bool bool)))
  (t2tb252 x))))

(declare-fun tb2t252 (uni) (set (tuple2 (set uninterpreted_type1)
  (tuple2 Bool Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (set uninterpreted_type1) (tuple2 Bool Bool)))))
  (! (= (tb2t252 (t2tb252 i)) i) :pattern ((t2tb252 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (tuple21 (set1 uninterpreted_type) (tuple21 bool bool)))
     j) (= (t2tb252 (tb2t252 j)) j)) :pattern ((t2tb252 (tb2t252 j))) )))

(declare-fun t2tb253 ((tuple2 (set uninterpreted_type1) (tuple2 Bool
  Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (set uninterpreted_type1) (tuple2 Bool Bool)))) (sort
  (tuple21 (set1 uninterpreted_type) (tuple21 bool bool)) (t2tb253 x))))

(declare-fun tb2t253 (uni) (tuple2 (set uninterpreted_type1) (tuple2 Bool
  Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (set uninterpreted_type1) (tuple2 Bool Bool))))
  (! (= (tb2t253 (t2tb253 i)) i) :pattern ((t2tb253 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (tuple21 (set1 uninterpreted_type) (tuple21 bool bool)) j)
     (= (t2tb253 (tb2t253 j)) j)) :pattern ((t2tb253 (tb2t253 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (set uninterpreted_type1)) (y (tuple2 Bool Bool))) (! (mem
  (set1 (tuple21 (set1 uninterpreted_type) (tuple21 bool bool)))
  (add (tuple21 (set1 uninterpreted_type) (tuple21 bool bool))
  (Tuple2 (set1 uninterpreted_type) (tuple21 bool bool) (t2tb205 x)
  (t2tb11 y))
  (empty (tuple21 (set1 uninterpreted_type) (tuple21 bool bool))))
  (infix_mnmngt (tuple21 bool bool) (set1 uninterpreted_type)
  (t2tb204 (add5 x empty11))
  (add (tuple21 bool bool) (t2tb11 y) (t2tb7 empty7)))) :pattern ((tb2t252
                                                                  (add
                                                                  (tuple21
                                                                  (set1
                                                                  uninterpreted_type)
                                                                  (tuple21
                                                                  bool 
                                                                  bool))
                                                                  (Tuple2
                                                                  (set1
                                                                  uninterpreted_type)
                                                                  (tuple21
                                                                  bool 
                                                                  bool)
                                                                  (t2tb205 x)
                                                                  (t2tb11 y))
                                                                  (empty
                                                                  (tuple21
                                                                  (set1
                                                                  uninterpreted_type)
                                                                  (tuple21
                                                                  bool 
                                                                  bool)))))) )))

(declare-fun t2tb254 ((set (set (tuple2 (set uninterpreted_type1)
  Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (set uninterpreted_type1) Bool))))) (sort
  (set1 (set1 (tuple21 (set1 uninterpreted_type) bool))) (t2tb254 x))))

(declare-fun tb2t254 (uni) (set (set (tuple2 (set uninterpreted_type1)
  Bool))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (set uninterpreted_type1) Bool)))))
  (! (= (tb2t254 (t2tb254 i)) i) :pattern ((t2tb254 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (set1 (tuple21 (set1 uninterpreted_type) bool))) j)
     (= (t2tb254 (tb2t254 j)) j)) :pattern ((t2tb254 (tb2t254 j))) )))

(declare-fun t2tb255 ((set (tuple2 (set uninterpreted_type1) Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (set uninterpreted_type1) Bool)))) (sort
  (set1 (tuple21 (set1 uninterpreted_type) bool)) (t2tb255 x))))

(declare-fun tb2t255 (uni) (set (tuple2 (set uninterpreted_type1) Bool)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (set uninterpreted_type1) Bool))))
  (! (= (tb2t255 (t2tb255 i)) i) :pattern ((t2tb255 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (tuple21 (set1 uninterpreted_type) bool)) j)
     (= (t2tb255 (tb2t255 j)) j)) :pattern ((t2tb255 (tb2t255 j))) )))

(declare-fun t2tb256 ((tuple2 (set uninterpreted_type1) Bool)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (set uninterpreted_type1) Bool))) (sort
  (tuple21 (set1 uninterpreted_type) bool) (t2tb256 x))))

(declare-fun tb2t256 (uni) (tuple2 (set uninterpreted_type1) Bool))

;; BridgeL
  (assert
  (forall ((i (tuple2 (set uninterpreted_type1) Bool)))
  (! (= (tb2t256 (t2tb256 i)) i) :pattern ((t2tb256 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (tuple21 (set1 uninterpreted_type) bool) j)
     (= (t2tb256 (tb2t256 j)) j)) :pattern ((t2tb256 (tb2t256 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (set uninterpreted_type1)) (y Bool)) (! (mem
  (set1 (tuple21 (set1 uninterpreted_type) bool))
  (add (tuple21 (set1 uninterpreted_type) bool)
  (Tuple2 (set1 uninterpreted_type) bool (t2tb205 x) (t2tb12 y))
  (empty (tuple21 (set1 uninterpreted_type) bool)))
  (infix_mnmngt bool (set1 uninterpreted_type) (t2tb204 (add5 x empty11))
  (t2tb2 (add1 y empty1)))) :pattern ((tb2t255
                                      (add
                                      (tuple21 (set1 uninterpreted_type)
                                      bool)
                                      (Tuple2 (set1 uninterpreted_type) 
                                      bool (t2tb205 x) (t2tb12 y))
                                      (empty
                                      (tuple21 (set1 uninterpreted_type)
                                      bool))))) )))

;; singleton_is_function
  (assert
  (forall ((b ty))
  (forall ((x (set uninterpreted_type1)) (y uni)) (! (mem
  (set1 (tuple21 (set1 uninterpreted_type) b))
  (add (tuple21 (set1 uninterpreted_type) b)
  (Tuple2 (set1 uninterpreted_type) b (t2tb205 x) y)
  (empty (tuple21 (set1 uninterpreted_type) b)))
  (infix_mnmngt b (set1 uninterpreted_type) (t2tb204 (add5 x empty11))
  (add b y (empty b)))) :pattern ((add (tuple21 (set1 uninterpreted_type) b)
                                  (Tuple2 (set1 uninterpreted_type) b
                                  (t2tb205 x) y)
                                  (empty
                                  (tuple21 (set1 uninterpreted_type) b)))) ))))

(declare-fun t2tb257 ((set (set (tuple2 uninterpreted_type1
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 uninterpreted_type1
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))))))) (sort
  (set1
  (set1
  (tuple21 uninterpreted_type
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))))) (t2tb257 x))))

(declare-fun tb2t257 (uni) (set (set (tuple2 uninterpreted_type1
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 uninterpreted_type1
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))))))
  (! (= (tb2t257 (t2tb257 i)) i) :pattern ((t2tb257 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21 uninterpreted_type
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type))))) j) (= (t2tb257 (tb2t257 j)) j)) :pattern (
  (t2tb257 (tb2t257 j))) )))

(declare-fun t2tb258 ((set (tuple2 uninterpreted_type1
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 uninterpreted_type1
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))))) (sort
  (set1
  (tuple21 uninterpreted_type
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)))) (t2tb258 x))))

(declare-fun tb2t258 (uni) (set (tuple2 uninterpreted_type1
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 uninterpreted_type1
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))))))
  (! (= (tb2t258 (t2tb258 i)) i) :pattern ((t2tb258 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21 uninterpreted_type
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type)))) j) (= (t2tb258 (tb2t258 j)) j)) :pattern (
  (t2tb258 (tb2t258 j))) )))

(declare-fun t2tb259 ((tuple2 uninterpreted_type1
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 uninterpreted_type1
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))))) (sort
  (tuple21 uninterpreted_type
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))) (t2tb259 x))))

(declare-fun tb2t259 (uni) (tuple2 uninterpreted_type1
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))))

;; BridgeL
  (assert
  (forall ((i (tuple2 uninterpreted_type1
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))))
  (! (= (tb2t259 (t2tb259 i)) i) :pattern ((t2tb259 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 uninterpreted_type
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type))) j) (= (t2tb259 (tb2t259 j)) j)) :pattern (
  (t2tb259 (tb2t259 j))) )))

;; singleton_is_function
  (assert
  (forall ((x uninterpreted_type1) (y (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1)))) (! (mem
  (set1
  (tuple21 uninterpreted_type
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))))
  (add
  (tuple21 uninterpreted_type
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)))
  (Tuple2 uninterpreted_type
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb206 x) (t2tb203 y))
  (empty
  (tuple21 uninterpreted_type
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)))))
  (infix_mnmngt
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) uninterpreted_type
  (add uninterpreted_type (t2tb206 x) (t2tb205 empty9))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb203 y) (t2tb202 empty10)))) :pattern (
  (tb2t258
  (add
  (tuple21 uninterpreted_type
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)))
  (Tuple2 uninterpreted_type
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb206 x) (t2tb203 y))
  (empty
  (tuple21 uninterpreted_type
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))))))) )))

(declare-fun t2tb260 ((set (tuple2 uninterpreted_type1
  (set uninterpreted_type1)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 uninterpreted_type1 (set uninterpreted_type1)))))
  (sort (set1 (tuple21 uninterpreted_type (set1 uninterpreted_type)))
  (t2tb260 x))))

(declare-fun tb2t260 (uni) (set (tuple2 uninterpreted_type1
  (set uninterpreted_type1))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 uninterpreted_type1 (set uninterpreted_type1)))))
  (! (= (tb2t260 (t2tb260 i)) i) :pattern ((t2tb260 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (tuple21 uninterpreted_type (set1 uninterpreted_type)))
     j) (= (t2tb260 (tb2t260 j)) j)) :pattern ((t2tb260 (tb2t260 j))) )))

(declare-fun t2tb261 ((tuple2 uninterpreted_type1
  (set uninterpreted_type1))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 uninterpreted_type1 (set uninterpreted_type1)))) (sort
  (tuple21 uninterpreted_type (set1 uninterpreted_type)) (t2tb261 x))))

(declare-fun tb2t261 (uni) (tuple2 uninterpreted_type1
  (set uninterpreted_type1)))

;; BridgeL
  (assert
  (forall ((i (tuple2 uninterpreted_type1 (set uninterpreted_type1))))
  (! (= (tb2t261 (t2tb261 i)) i) :pattern ((t2tb261 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (tuple21 uninterpreted_type (set1 uninterpreted_type)) j)
     (= (t2tb261 (tb2t261 j)) j)) :pattern ((t2tb261 (tb2t261 j))) )))

(declare-fun t2tb262 ((set (set (tuple2 uninterpreted_type1
  (set uninterpreted_type1))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 uninterpreted_type1
  (set uninterpreted_type1)))))) (sort
  (set1 (set1 (tuple21 uninterpreted_type (set1 uninterpreted_type))))
  (t2tb262 x))))

(declare-fun tb2t262 (uni) (set (set (tuple2 uninterpreted_type1
  (set uninterpreted_type1)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 uninterpreted_type1
  (set uninterpreted_type1))))))
  (! (= (tb2t262 (t2tb262 i)) i) :pattern ((t2tb262 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1 (set1 (tuple21 uninterpreted_type (set1 uninterpreted_type)))) j)
     (= (t2tb262 (tb2t262 j)) j)) :pattern ((t2tb262 (tb2t262 j))) )))

;; singleton_is_function
  (assert
  (forall ((x uninterpreted_type1) (y (set uninterpreted_type1))) (! (mem
  (set1 (tuple21 uninterpreted_type (set1 uninterpreted_type)))
  (add (tuple21 uninterpreted_type (set1 uninterpreted_type))
  (Tuple2 uninterpreted_type (set1 uninterpreted_type) (t2tb206 x)
  (t2tb205 y))
  (empty (tuple21 uninterpreted_type (set1 uninterpreted_type))))
  (infix_mnmngt (set1 uninterpreted_type) uninterpreted_type
  (add uninterpreted_type (t2tb206 x) (t2tb205 empty9))
  (t2tb204 (add5 y empty11)))) :pattern ((tb2t260
                                         (add
                                         (tuple21 uninterpreted_type
                                         (set1 uninterpreted_type))
                                         (Tuple2 uninterpreted_type
                                         (set1 uninterpreted_type)
                                         (t2tb206 x) (t2tb205 y))
                                         (empty
                                         (tuple21 uninterpreted_type
                                         (set1 uninterpreted_type)))))) )))

(declare-fun t2tb263 ((set (set (tuple2 uninterpreted_type1
  uninterpreted_type1)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 uninterpreted_type1 uninterpreted_type1)))))
  (sort (set1 (set1 (tuple21 uninterpreted_type uninterpreted_type)))
  (t2tb263 x))))

(declare-fun tb2t263 (uni) (set (set (tuple2 uninterpreted_type1
  uninterpreted_type1))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 uninterpreted_type1 uninterpreted_type1)))))
  (! (= (tb2t263 (t2tb263 i)) i) :pattern ((t2tb263 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (set1 (tuple21 uninterpreted_type uninterpreted_type)))
     j) (= (t2tb263 (tb2t263 j)) j)) :pattern ((t2tb263 (tb2t263 j))) )))

(declare-fun t2tb264 ((set (tuple2 uninterpreted_type1
  uninterpreted_type1))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 uninterpreted_type1 uninterpreted_type1)))) (sort
  (set1 (tuple21 uninterpreted_type uninterpreted_type)) (t2tb264 x))))

(declare-fun tb2t264 (uni) (set (tuple2 uninterpreted_type1
  uninterpreted_type1)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 uninterpreted_type1 uninterpreted_type1))))
  (! (= (tb2t264 (t2tb264 i)) i) :pattern ((t2tb264 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (tuple21 uninterpreted_type uninterpreted_type)) j)
     (= (t2tb264 (tb2t264 j)) j)) :pattern ((t2tb264 (tb2t264 j))) )))

(declare-fun t2tb265 ((tuple2 uninterpreted_type1 uninterpreted_type1)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 uninterpreted_type1 uninterpreted_type1))) (sort
  (tuple21 uninterpreted_type uninterpreted_type) (t2tb265 x))))

(declare-fun tb2t265 (uni) (tuple2 uninterpreted_type1 uninterpreted_type1))

;; BridgeL
  (assert
  (forall ((i (tuple2 uninterpreted_type1 uninterpreted_type1)))
  (! (= (tb2t265 (t2tb265 i)) i) :pattern ((t2tb265 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (tuple21 uninterpreted_type uninterpreted_type) j)
     (= (t2tb265 (tb2t265 j)) j)) :pattern ((t2tb265 (tb2t265 j))) )))

;; singleton_is_function
  (assert
  (forall ((x uninterpreted_type1) (y uninterpreted_type1)) (! (mem
  (set1 (tuple21 uninterpreted_type uninterpreted_type))
  (add (tuple21 uninterpreted_type uninterpreted_type)
  (Tuple2 uninterpreted_type uninterpreted_type (t2tb206 x) (t2tb206 y))
  (empty (tuple21 uninterpreted_type uninterpreted_type)))
  (infix_mnmngt uninterpreted_type uninterpreted_type
  (add uninterpreted_type (t2tb206 x) (t2tb205 empty9))
  (add uninterpreted_type (t2tb206 y) (t2tb205 empty9)))) :pattern ((tb2t264
                                                                    (add
                                                                    (tuple21
                                                                    uninterpreted_type
                                                                    uninterpreted_type)
                                                                    (Tuple2
                                                                    uninterpreted_type
                                                                    uninterpreted_type
                                                                    (t2tb206
                                                                    x)
                                                                    (t2tb206
                                                                    y))
                                                                    (empty
                                                                    (tuple21
                                                                    uninterpreted_type
                                                                    uninterpreted_type))))) )))

(declare-fun t2tb266 ((set (set (tuple2 uninterpreted_type1
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 uninterpreted_type1
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))))
  (sort
  (set1
  (set1
  (tuple21 uninterpreted_type
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (t2tb266 x))))

(declare-fun tb2t266 (uni) (set (set (tuple2 uninterpreted_type1
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 uninterpreted_type1
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))))
  (! (= (tb2t266 (t2tb266 i)) i) :pattern ((t2tb266 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb266 (tb2t266 j)) j) :pattern ((t2tb266 (tb2t266 j))) )))

(declare-fun t2tb267 ((set (tuple2 uninterpreted_type1
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 uninterpreted_type1
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))) (sort
  (set1
  (tuple21 uninterpreted_type
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (t2tb267 x))))

(declare-fun tb2t267 (uni) (set (tuple2 uninterpreted_type1
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 uninterpreted_type1
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))))
  (! (= (tb2t267 (t2tb267 i)) i) :pattern ((t2tb267 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb267 (tb2t267 j)) j) :pattern ((t2tb267 (tb2t267 j))) )))

(declare-fun t2tb268 ((tuple2 uninterpreted_type1
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 uninterpreted_type1
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))) (sort
  (tuple21 uninterpreted_type
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb268 x))))

(declare-fun tb2t268 (uni) (tuple2 uninterpreted_type1
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))

;; BridgeL
  (assert
  (forall ((i (tuple2 uninterpreted_type1
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int)))))
  (! (= (tb2t268 (t2tb268 i)) i) :pattern ((t2tb268 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb268 (tb2t268 j)) j) :pattern ((t2tb268 (tb2t268 j))) )))

;; singleton_is_function
  (assert
  (forall ((x uninterpreted_type1) (y (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)))) (! (mem
  (set1
  (tuple21 uninterpreted_type
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))))
  (add
  (tuple21 uninterpreted_type
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (Tuple2 uninterpreted_type
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb206 x) (t2tb8 y))
  (empty
  (tuple21 uninterpreted_type
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))))
  (infix_mnmngt
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  uninterpreted_type (add uninterpreted_type (t2tb206 x) (t2tb205 empty9))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb8 y) (t2tb4 empty4)))) :pattern ((tb2t267
                                        (add
                                        (tuple21 uninterpreted_type
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int)))
                                        (Tuple2 uninterpreted_type
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int)) (t2tb206 x)
                                        (t2tb8 y))
                                        (empty
                                        (tuple21 uninterpreted_type
                                        (tuple21
                                        (tuple21
                                        (tuple21 (tuple21 bool bool) bool)
                                        bool) (set1 int))))))) )))

(declare-fun t2tb269 ((set (set (tuple2 uninterpreted_type1
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 uninterpreted_type1
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))))) (sort
  (set1
  (set1
  (tuple21 uninterpreted_type
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))) (t2tb269 x))))

(declare-fun tb2t269 (uni) (set (set (tuple2 uninterpreted_type1
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 uninterpreted_type1
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))))
  (! (= (tb2t269 (t2tb269 i)) i) :pattern ((t2tb269 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21 uninterpreted_type
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))) j)
     (= (t2tb269 (tb2t269 j)) j)) :pattern ((t2tb269 (tb2t269 j))) )))

(declare-fun t2tb270 ((set (tuple2 uninterpreted_type1
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 uninterpreted_type1 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool))))) (sort
  (set1
  (tuple21 uninterpreted_type
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))) (t2tb270 x))))

(declare-fun tb2t270 (uni) (set (tuple2 uninterpreted_type1
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 uninterpreted_type1 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool)))))
  (! (= (tb2t270 (t2tb270 i)) i) :pattern ((t2tb270 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21 uninterpreted_type
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool))) j)
     (= (t2tb270 (tb2t270 j)) j)) :pattern ((t2tb270 (tb2t270 j))) )))

(declare-fun t2tb271 ((tuple2 uninterpreted_type1
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 uninterpreted_type1 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool)))) (sort
  (tuple21 uninterpreted_type
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb271 x))))

(declare-fun tb2t271 (uni) (tuple2 uninterpreted_type1
  (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 uninterpreted_type1 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool)))) (! (= (tb2t271 (t2tb271 i)) i) :pattern ((t2tb271 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 uninterpreted_type
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) j)
     (= (t2tb271 (tb2t271 j)) j)) :pattern ((t2tb271 (tb2t271 j))) )))

;; singleton_is_function
  (assert
  (forall ((x uninterpreted_type1) (y (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool))) (! (mem
  (set1
  (tuple21 uninterpreted_type
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)))
  (add
  (tuple21 uninterpreted_type
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (Tuple2 uninterpreted_type
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb206 x) (t2tb9 y))
  (empty
  (tuple21 uninterpreted_type
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool))))
  (infix_mnmngt (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  uninterpreted_type (add uninterpreted_type (t2tb206 x) (t2tb205 empty9))
  (add (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 y)
  (t2tb5 empty5)))) :pattern ((tb2t270
                              (add
                              (tuple21 uninterpreted_type
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool))
                              (Tuple2 uninterpreted_type
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool) (t2tb206 x) (t2tb9 y))
                              (empty
                              (tuple21 uninterpreted_type
                              (tuple21 (tuple21 (tuple21 bool bool) bool)
                              bool)))))) )))

(declare-fun t2tb272 ((set (set (tuple2 uninterpreted_type1
  (tuple2 (tuple2 Bool Bool) Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 uninterpreted_type1 (tuple2 (tuple2 Bool
  Bool) Bool)))))) (sort
  (set1
  (set1 (tuple21 uninterpreted_type (tuple21 (tuple21 bool bool) bool))))
  (t2tb272 x))))

(declare-fun tb2t272 (uni) (set (set (tuple2 uninterpreted_type1
  (tuple2 (tuple2 Bool Bool) Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 uninterpreted_type1 (tuple2 (tuple2 Bool
  Bool) Bool)))))) (! (= (tb2t272 (t2tb272 i)) i) :pattern ((t2tb272 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1 (tuple21 uninterpreted_type (tuple21 (tuple21 bool bool) bool))))
     j) (= (t2tb272 (tb2t272 j)) j)) :pattern ((t2tb272 (tb2t272 j))) )))

(declare-fun t2tb273 ((set (tuple2 uninterpreted_type1 (tuple2 (tuple2 Bool
  Bool) Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 uninterpreted_type1 (tuple2 (tuple2 Bool Bool)
  Bool))))) (sort
  (set1 (tuple21 uninterpreted_type (tuple21 (tuple21 bool bool) bool)))
  (t2tb273 x))))

(declare-fun tb2t273 (uni) (set (tuple2 uninterpreted_type1
  (tuple2 (tuple2 Bool Bool) Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 uninterpreted_type1 (tuple2 (tuple2 Bool Bool)
  Bool))))) (! (= (tb2t273 (t2tb273 i)) i) :pattern ((t2tb273 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1 (tuple21 uninterpreted_type (tuple21 (tuple21 bool bool) bool)))
     j) (= (t2tb273 (tb2t273 j)) j)) :pattern ((t2tb273 (tb2t273 j))) )))

(declare-fun t2tb274 ((tuple2 uninterpreted_type1 (tuple2 (tuple2 Bool Bool)
  Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 uninterpreted_type1 (tuple2 (tuple2 Bool Bool) Bool))))
  (sort (tuple21 uninterpreted_type (tuple21 (tuple21 bool bool) bool))
  (t2tb274 x))))

(declare-fun tb2t274 (uni) (tuple2 uninterpreted_type1 (tuple2 (tuple2 Bool
  Bool) Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 uninterpreted_type1 (tuple2 (tuple2 Bool Bool) Bool))))
  (! (= (tb2t274 (t2tb274 i)) i) :pattern ((t2tb274 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 uninterpreted_type (tuple21 (tuple21 bool bool) bool)) j)
     (= (t2tb274 (tb2t274 j)) j)) :pattern ((t2tb274 (tb2t274 j))) )))

;; singleton_is_function
  (assert
  (forall ((x uninterpreted_type1) (y (tuple2 (tuple2 Bool Bool) Bool)))
  (! (mem
  (set1 (tuple21 uninterpreted_type (tuple21 (tuple21 bool bool) bool)))
  (add (tuple21 uninterpreted_type (tuple21 (tuple21 bool bool) bool))
  (Tuple2 uninterpreted_type (tuple21 (tuple21 bool bool) bool) (t2tb206 x)
  (t2tb10 y))
  (empty (tuple21 uninterpreted_type (tuple21 (tuple21 bool bool) bool))))
  (infix_mnmngt (tuple21 (tuple21 bool bool) bool) uninterpreted_type
  (add uninterpreted_type (t2tb206 x) (t2tb205 empty9))
  (add (tuple21 (tuple21 bool bool) bool) (t2tb10 y) (t2tb6 empty6)))) :pattern (
  (tb2t273
  (add (tuple21 uninterpreted_type (tuple21 (tuple21 bool bool) bool))
  (Tuple2 uninterpreted_type (tuple21 (tuple21 bool bool) bool) (t2tb206 x)
  (t2tb10 y))
  (empty (tuple21 uninterpreted_type (tuple21 (tuple21 bool bool) bool)))))) )))

(declare-fun t2tb275 ((tuple2 uninterpreted_type1 (tuple2 Bool Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 uninterpreted_type1 (tuple2 Bool Bool)))) (sort
  (tuple21 uninterpreted_type (tuple21 bool bool)) (t2tb275 x))))

(declare-fun tb2t275 (uni) (tuple2 uninterpreted_type1 (tuple2 Bool Bool)))

;; BridgeL
  (assert
  (forall ((i (tuple2 uninterpreted_type1 (tuple2 Bool Bool))))
  (! (= (tb2t275 (t2tb275 i)) i) :pattern ((t2tb275 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (tuple21 uninterpreted_type (tuple21 bool bool)) j)
     (= (t2tb275 (tb2t275 j)) j)) :pattern ((t2tb275 (tb2t275 j))) )))

(declare-fun t2tb276 ((set (set (tuple2 uninterpreted_type1 (tuple2 Bool
  Bool))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 uninterpreted_type1 (tuple2 Bool Bool))))))
  (sort (set1 (set1 (tuple21 uninterpreted_type (tuple21 bool bool))))
  (t2tb276 x))))

(declare-fun tb2t276 (uni) (set (set (tuple2 uninterpreted_type1 (tuple2 Bool
  Bool)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 uninterpreted_type1 (tuple2 Bool Bool))))))
  (! (= (tb2t276 (t2tb276 i)) i) :pattern ((t2tb276 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (set1 (tuple21 uninterpreted_type (tuple21 bool bool))))
     j) (= (t2tb276 (tb2t276 j)) j)) :pattern ((t2tb276 (tb2t276 j))) )))

(declare-fun t2tb277 ((set (tuple2 uninterpreted_type1 (tuple2 Bool
  Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 uninterpreted_type1 (tuple2 Bool Bool))))) (sort
  (set1 (tuple21 uninterpreted_type (tuple21 bool bool))) (t2tb277 x))))

(declare-fun tb2t277 (uni) (set (tuple2 uninterpreted_type1 (tuple2 Bool
  Bool))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 uninterpreted_type1 (tuple2 Bool Bool)))))
  (! (= (tb2t277 (t2tb277 i)) i) :pattern ((t2tb277 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (tuple21 uninterpreted_type (tuple21 bool bool))) j)
     (= (t2tb277 (tb2t277 j)) j)) :pattern ((t2tb277 (tb2t277 j))) )))

;; singleton_is_function
  (assert
  (forall ((x uninterpreted_type1) (y (tuple2 Bool Bool))) (! (mem
  (set1 (tuple21 uninterpreted_type (tuple21 bool bool)))
  (add (tuple21 uninterpreted_type (tuple21 bool bool))
  (Tuple2 uninterpreted_type (tuple21 bool bool) (t2tb206 x) (t2tb11 y))
  (empty (tuple21 uninterpreted_type (tuple21 bool bool))))
  (infix_mnmngt (tuple21 bool bool) uninterpreted_type
  (add uninterpreted_type (t2tb206 x) (t2tb205 empty9))
  (add (tuple21 bool bool) (t2tb11 y) (t2tb7 empty7)))) :pattern ((tb2t277
                                                                  (add
                                                                  (tuple21
                                                                  uninterpreted_type
                                                                  (tuple21
                                                                  bool 
                                                                  bool))
                                                                  (Tuple2
                                                                  uninterpreted_type
                                                                  (tuple21
                                                                  bool 
                                                                  bool)
                                                                  (t2tb206 x)
                                                                  (t2tb11 y))
                                                                  (empty
                                                                  (tuple21
                                                                  uninterpreted_type
                                                                  (tuple21
                                                                  bool 
                                                                  bool)))))) )))

(declare-fun t2tb278 ((set (set (tuple2 uninterpreted_type1 Bool)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 uninterpreted_type1 Bool))))) (sort
  (set1 (set1 (tuple21 uninterpreted_type bool))) (t2tb278 x))))

(declare-fun tb2t278 (uni) (set (set (tuple2 uninterpreted_type1 Bool))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 uninterpreted_type1 Bool)))))
  (! (= (tb2t278 (t2tb278 i)) i) :pattern ((t2tb278 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (set1 (tuple21 uninterpreted_type bool))) j)
     (= (t2tb278 (tb2t278 j)) j)) :pattern ((t2tb278 (tb2t278 j))) )))

(declare-fun t2tb279 ((set (tuple2 uninterpreted_type1 Bool))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 uninterpreted_type1 Bool)))) (sort
  (set1 (tuple21 uninterpreted_type bool)) (t2tb279 x))))

(declare-fun tb2t279 (uni) (set (tuple2 uninterpreted_type1 Bool)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 uninterpreted_type1 Bool))))
  (! (= (tb2t279 (t2tb279 i)) i) :pattern ((t2tb279 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (tuple21 uninterpreted_type bool)) j)
     (= (t2tb279 (tb2t279 j)) j)) :pattern ((t2tb279 (tb2t279 j))) )))

(declare-fun t2tb280 ((tuple2 uninterpreted_type1 Bool)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 uninterpreted_type1 Bool))) (sort
  (tuple21 uninterpreted_type bool) (t2tb280 x))))

(declare-fun tb2t280 (uni) (tuple2 uninterpreted_type1 Bool))

;; BridgeL
  (assert
  (forall ((i (tuple2 uninterpreted_type1 Bool)))
  (! (= (tb2t280 (t2tb280 i)) i) :pattern ((t2tb280 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (tuple21 uninterpreted_type bool) j)
     (= (t2tb280 (tb2t280 j)) j)) :pattern ((t2tb280 (tb2t280 j))) )))

;; singleton_is_function
  (assert
  (forall ((x uninterpreted_type1) (y Bool)) (! (mem
  (set1 (tuple21 uninterpreted_type bool))
  (add (tuple21 uninterpreted_type bool)
  (Tuple2 uninterpreted_type bool (t2tb206 x) (t2tb12 y))
  (empty (tuple21 uninterpreted_type bool)))
  (infix_mnmngt bool uninterpreted_type
  (add uninterpreted_type (t2tb206 x) (t2tb205 empty9))
  (t2tb2 (add1 y empty1)))) :pattern ((tb2t279
                                      (add (tuple21 uninterpreted_type bool)
                                      (Tuple2 uninterpreted_type bool
                                      (t2tb206 x) (t2tb12 y))
                                      (empty
                                      (tuple21 uninterpreted_type bool))))) )))

;; singleton_is_function
  (assert
  (forall ((b ty))
  (forall ((x uninterpreted_type1) (y uni)) (! (mem
  (set1 (tuple21 uninterpreted_type b))
  (add (tuple21 uninterpreted_type b)
  (Tuple2 uninterpreted_type b (t2tb206 x) y)
  (empty (tuple21 uninterpreted_type b)))
  (infix_mnmngt b uninterpreted_type
  (add uninterpreted_type (t2tb206 x) (t2tb205 empty9)) (add b y (empty b)))) :pattern (
  (add (tuple21 uninterpreted_type b)
  (Tuple2 uninterpreted_type b (t2tb206 x) y)
  (empty (tuple21 uninterpreted_type b)))) ))))

(declare-fun t2tb281 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type1))))))) (sort
  (set1
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))))) (t2tb281 x))))

(declare-fun tb2t281 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type1)))))))
  (! (= (tb2t281 (t2tb281 i)) i) :pattern ((t2tb281 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb281 (tb2t281 j)) j) :pattern ((t2tb281 (tb2t281 j))) )))

(declare-fun t2tb282 ((set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type1))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))))) (sort
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)))) (t2tb282 x))))

(declare-fun tb2t282 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))))))
  (! (= (tb2t282 (t2tb282 i)) i) :pattern ((t2tb282 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb282 (tb2t282 j)) j) :pattern ((t2tb282 (tb2t282 j))) )))

(declare-fun t2tb283 ((tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type1)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))))) (sort
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))) (t2tb283 x))))

(declare-fun tb2t283 (uni) (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type1))))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))))
  (! (= (tb2t283 (t2tb283 i)) i) :pattern ((t2tb283 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb283 (tb2t283 j)) j) :pattern ((t2tb283 (tb2t283 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))) (y (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))) (! (mem
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))))
  (add
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)))
  (Tuple2
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb8 x) (t2tb203 y))
  (empty
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)))))
  (infix_mnmngt
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb8 x) (t2tb4 empty4))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb203 y) (t2tb202 empty10)))) :pattern (
  (tb2t282
  (add
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)))
  (Tuple2
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb8 x) (t2tb203 y))
  (empty
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))))))) )))

(declare-fun t2tb284 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) (set uninterpreted_type1))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (set uninterpreted_type1)))))) (sort
  (set1
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (set1 uninterpreted_type)))) (t2tb284 x))))

(declare-fun tb2t284 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) (set uninterpreted_type1)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (set uninterpreted_type1))))))
  (! (= (tb2t284 (t2tb284 i)) i) :pattern ((t2tb284 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb284 (tb2t284 j)) j) :pattern ((t2tb284 (tb2t284 j))) )))

(declare-fun t2tb285 ((set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (set uninterpreted_type1)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)) (set uninterpreted_type1))))) (sort
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (set1 uninterpreted_type))) (t2tb285 x))))

(declare-fun tb2t285 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) (set uninterpreted_type1))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)) (set uninterpreted_type1)))))
  (! (= (tb2t285 (t2tb285 i)) i) :pattern ((t2tb285 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb285 (tb2t285 j)) j) :pattern ((t2tb285 (tb2t285 j))) )))

(declare-fun t2tb286 ((tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (set uninterpreted_type1))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)) (set uninterpreted_type1)))) (sort
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (set1 uninterpreted_type)) (t2tb286 x))))

(declare-fun tb2t286 (uni) (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) (set uninterpreted_type1)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)) (set uninterpreted_type1))))
  (! (= (tb2t286 (t2tb286 i)) i) :pattern ((t2tb286 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb286 (tb2t286 j)) j) :pattern ((t2tb286 (tb2t286 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))) (y (set uninterpreted_type1))) (! (mem
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (set1 uninterpreted_type)))
  (add
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (set1 uninterpreted_type))
  (Tuple2
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (set1 uninterpreted_type) (t2tb8 x) (t2tb205 y))
  (empty
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (set1 uninterpreted_type))))
  (infix_mnmngt (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb8 x) (t2tb4 empty4)) (t2tb204 (add5 y empty11)))) :pattern ((tb2t285
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
                                                                   uninterpreted_type))
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
                                                                   uninterpreted_type)
                                                                   (t2tb8 x)
                                                                   (t2tb205
                                                                   y))
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
                                                                   uninterpreted_type)))))) )))

(declare-fun t2tb287 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) uninterpreted_type1)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) uninterpreted_type1))))) (sort
  (set1
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  uninterpreted_type))) (t2tb287 x))))

(declare-fun tb2t287 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) uninterpreted_type1))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) uninterpreted_type1)))))
  (! (= (tb2t287 (t2tb287 i)) i) :pattern ((t2tb287 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb287 (tb2t287 j)) j) :pattern ((t2tb287 (tb2t287 j))) )))

(declare-fun t2tb288 ((set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) uninterpreted_type1))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)) uninterpreted_type1)))) (sort
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  uninterpreted_type)) (t2tb288 x))))

(declare-fun tb2t288 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set Int)) uninterpreted_type1)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)) uninterpreted_type1))))
  (! (= (tb2t288 (t2tb288 i)) i) :pattern ((t2tb288 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb288 (tb2t288 j)) j) :pattern ((t2tb288 (tb2t288 j))) )))

(declare-fun t2tb289 ((tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) uninterpreted_type1)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)) uninterpreted_type1))) (sort
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  uninterpreted_type) (t2tb289 x))))

(declare-fun tb2t289 (uni) (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set Int)) uninterpreted_type1))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)) uninterpreted_type1)))
  (! (= (tb2t289 (t2tb289 i)) i) :pattern ((t2tb289 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb289 (tb2t289 j)) j) :pattern ((t2tb289 (tb2t289 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))) (y uninterpreted_type1)) (! (mem
  (set1
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  uninterpreted_type))
  (add
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  uninterpreted_type)
  (Tuple2
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  uninterpreted_type (t2tb8 x) (t2tb206 y))
  (empty
  (tuple21
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  uninterpreted_type)))
  (infix_mnmngt uninterpreted_type
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb8 x) (t2tb4 empty4))
  (add uninterpreted_type (t2tb206 y) (t2tb205 empty9)))) :pattern ((tb2t288
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
                                                                    int))
                                                                    uninterpreted_type)
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
                                                                    int))
                                                                    uninterpreted_type
                                                                    (t2tb8 x)
                                                                    (t2tb206
                                                                    y))
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
                                                                    int))
                                                                    uninterpreted_type))))) )))

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

(declare-fun t2tb290 ((tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))))) (sort
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))) (t2tb290 x))))

(declare-fun tb2t290 (uni) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))))
  (! (= (tb2t290 (t2tb290 i)) i) :pattern ((t2tb290 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type))) j) (= (t2tb290 (tb2t290 j)) j)) :pattern (
  (t2tb290 (tb2t290 j))) )))

(declare-fun t2tb291 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))))) (t2tb291 x))))

(declare-fun tb2t291 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))))))
  (! (= (tb2t291 (t2tb291 i)) i) :pattern ((t2tb291 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type))))) j) (= (t2tb291 (tb2t291 j)) j)) :pattern (
  (t2tb291 (tb2t291 j))) )))

(declare-fun t2tb292 ((set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))))) (sort
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)))) (t2tb292 x))))

(declare-fun tb2t292 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))))))
  (! (= (tb2t292 (t2tb292 i)) i) :pattern ((t2tb292 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type)))) j) (= (t2tb292 (tb2t292 j)) j)) :pattern (
  (t2tb292 (tb2t292 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (y (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))) (! (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb9 x) (t2tb203 y))
  (empty
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)))))
  (infix_mnmngt
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (add (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
  (t2tb5 empty5))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb203 y) (t2tb202 empty10)))) :pattern (
  (tb2t292
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb9 x) (t2tb203 y))
  (empty
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))))))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (y (set uninterpreted_type1))) (! (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type) (t2tb9 x) (t2tb205 y)) (t2tb202 empty10))
  (infix_mnmngt (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (add (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
  (t2tb5 empty5)) (t2tb204 (add5 y empty11)))) :pattern ((tb2t202
                                                         (add
                                                         (tuple21
                                                         (tuple21
                                                         (tuple21
                                                         (tuple21 bool bool)
                                                         bool) bool)
                                                         (set1
                                                         uninterpreted_type))
                                                         (Tuple2
                                                         (tuple21
                                                         (tuple21
                                                         (tuple21 bool bool)
                                                         bool) bool)
                                                         (set1
                                                         uninterpreted_type)
                                                         (t2tb9 x)
                                                         (t2tb205 y))
                                                         (t2tb202 empty10)))) )))

(declare-fun t2tb293 ((set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) uninterpreted_type1)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) uninterpreted_type1))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  uninterpreted_type))) (t2tb293 x))))

(declare-fun tb2t293 (uni) (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) uninterpreted_type1))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) uninterpreted_type1)))))
  (! (= (tb2t293 (t2tb293 i)) i) :pattern ((t2tb293 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     uninterpreted_type))) j) (= (t2tb293 (tb2t293 j)) j)) :pattern (
  (t2tb293 (tb2t293 j))) )))

(declare-fun t2tb294 ((set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) uninterpreted_type1))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  uninterpreted_type1)))) (sort
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  uninterpreted_type)) (t2tb294 x))))

(declare-fun tb2t294 (uni) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) uninterpreted_type1)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  uninterpreted_type1))))
  (! (= (tb2t294 (t2tb294 i)) i) :pattern ((t2tb294 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     uninterpreted_type)) j) (= (t2tb294 (tb2t294 j)) j)) :pattern ((t2tb294
                                                                    (tb2t294
                                                                    j))) )))

(declare-fun t2tb295 ((tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  uninterpreted_type1)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  uninterpreted_type1))) (sort
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  uninterpreted_type) (t2tb295 x))))

(declare-fun tb2t295 (uni) (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) uninterpreted_type1))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  uninterpreted_type1)))
  (! (= (tb2t295 (t2tb295 i)) i) :pattern ((t2tb295 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     uninterpreted_type) j) (= (t2tb295 (tb2t295 j)) j)) :pattern ((t2tb295
                                                                   (tb2t295
                                                                   j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (y uninterpreted_type1)) (! (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  uninterpreted_type))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  uninterpreted_type)
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  uninterpreted_type (t2tb9 x) (t2tb206 y))
  (empty
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  uninterpreted_type)))
  (infix_mnmngt uninterpreted_type
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (add (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
  (t2tb5 empty5)) (add uninterpreted_type (t2tb206 y) (t2tb205 empty9)))) :pattern (
  (tb2t294
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  uninterpreted_type)
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  uninterpreted_type (t2tb9 x) (t2tb206 y))
  (empty
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  uninterpreted_type))))) )))

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
  (! (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb9 x) (t2tb3 y)) (t2tb4 empty4))
  (infix_mnmngt (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (add (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
  (t2tb5 empty5)) (add (set1 int) (t2tb3 y) (empty (set1 int))))) :pattern (
  (tb2t4
  (add (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb9 x) (t2tb3 y)) (t2tb4 empty4)))) )))

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

(declare-fun t2tb296 ((set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))))) (t2tb296 x))))

(declare-fun tb2t296 (uni) (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))))))
  (! (= (tb2t296 (t2tb296 i)) i) :pattern ((t2tb296 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21 (tuple21 (tuple21 bool bool) bool)
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type))))) j) (= (t2tb296 (tb2t296 j)) j)) :pattern (
  (t2tb296 (tb2t296 j))) )))

(declare-fun t2tb297 ((set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))))) (sort
  (set1
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)))) (t2tb297 x))))

(declare-fun tb2t297 (uni) (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))))))
  (! (= (tb2t297 (t2tb297 i)) i) :pattern ((t2tb297 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21 (tuple21 (tuple21 bool bool) bool)
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type)))) j) (= (t2tb297 (tb2t297 j)) j)) :pattern (
  (t2tb297 (tb2t297 j))) )))

(declare-fun t2tb298 ((tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))))) (sort
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))) (t2tb298 x))))

(declare-fun tb2t298 (uni) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))))
  (! (= (tb2t298 (t2tb298 i)) i) :pattern ((t2tb298 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 (tuple21 (tuple21 bool bool) bool)
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type))) j) (= (t2tb298 (tb2t298 j)) j)) :pattern (
  (t2tb298 (tb2t298 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool))
  (y (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))) (! (mem
  (set1
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))))
  (add
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)))
  (Tuple2 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb10 x) (t2tb203 y))
  (empty
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)))))
  (infix_mnmngt
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (tuple21 (tuple21 bool bool) bool)
  (add (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb6 empty6))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb203 y) (t2tb202 empty10)))) :pattern (
  (tb2t297
  (add
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)))
  (Tuple2 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb10 x) (t2tb203 y))
  (empty
  (tuple21 (tuple21 (tuple21 bool bool) bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))))))) )))

(declare-fun t2tb299 ((set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (set uninterpreted_type1))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (set uninterpreted_type1)))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 (tuple21 bool bool) bool) (set1 uninterpreted_type))))
  (t2tb299 x))))

(declare-fun tb2t299 (uni) (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (set uninterpreted_type1)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (set uninterpreted_type1))))))
  (! (= (tb2t299 (t2tb299 i)) i) :pattern ((t2tb299 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21 (tuple21 (tuple21 bool bool) bool) (set1 uninterpreted_type))))
     j) (= (t2tb299 (tb2t299 j)) j)) :pattern ((t2tb299 (tb2t299 j))) )))

(declare-fun t2tb300 ((set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (set uninterpreted_type1)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (set uninterpreted_type1))))) (sort
  (set1
  (tuple21 (tuple21 (tuple21 bool bool) bool) (set1 uninterpreted_type)))
  (t2tb300 x))))

(declare-fun tb2t300 (uni) (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (set uninterpreted_type1))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (set uninterpreted_type1)))))
  (! (= (tb2t300 (t2tb300 i)) i) :pattern ((t2tb300 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21 (tuple21 (tuple21 bool bool) bool) (set1 uninterpreted_type)))
     j) (= (t2tb300 (tb2t300 j)) j)) :pattern ((t2tb300 (tb2t300 j))) )))

(declare-fun t2tb301 ((tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (set uninterpreted_type1))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (set uninterpreted_type1)))) (sort
  (tuple21 (tuple21 (tuple21 bool bool) bool) (set1 uninterpreted_type))
  (t2tb301 x))))

(declare-fun tb2t301 (uni) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (set uninterpreted_type1)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  (set uninterpreted_type1))))
  (! (= (tb2t301 (t2tb301 i)) i) :pattern ((t2tb301 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 (tuple21 (tuple21 bool bool) bool) (set1 uninterpreted_type))
     j) (= (t2tb301 (tb2t301 j)) j)) :pattern ((t2tb301 (tb2t301 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool))
  (y (set uninterpreted_type1))) (! (mem
  (set1
  (tuple21 (tuple21 (tuple21 bool bool) bool) (set1 uninterpreted_type)))
  (add (tuple21 (tuple21 (tuple21 bool bool) bool) (set1 uninterpreted_type))
  (Tuple2 (tuple21 (tuple21 bool bool) bool) (set1 uninterpreted_type)
  (t2tb10 x) (t2tb205 y))
  (empty
  (tuple21 (tuple21 (tuple21 bool bool) bool) (set1 uninterpreted_type))))
  (infix_mnmngt (set1 uninterpreted_type) (tuple21 (tuple21 bool bool) bool)
  (add (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb6 empty6))
  (t2tb204 (add5 y empty11)))) :pattern ((tb2t300
                                         (add
                                         (tuple21
                                         (tuple21 (tuple21 bool bool) bool)
                                         (set1 uninterpreted_type))
                                         (Tuple2
                                         (tuple21 (tuple21 bool bool) bool)
                                         (set1 uninterpreted_type) (t2tb10 x)
                                         (t2tb205 y))
                                         (empty
                                         (tuple21
                                         (tuple21 (tuple21 bool bool) bool)
                                         (set1 uninterpreted_type)))))) )))

(declare-fun t2tb302 ((set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  uninterpreted_type1)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  uninterpreted_type1))))) (sort
  (set1
  (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) uninterpreted_type)))
  (t2tb302 x))))

(declare-fun tb2t302 (uni) (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  uninterpreted_type1))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  uninterpreted_type1)))))
  (! (= (tb2t302 (t2tb302 i)) i) :pattern ((t2tb302 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) uninterpreted_type)))
     j) (= (t2tb302 (tb2t302 j)) j)) :pattern ((t2tb302 (tb2t302 j))) )))

(declare-fun t2tb303 ((set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  uninterpreted_type1))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  uninterpreted_type1)))) (sort
  (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) uninterpreted_type))
  (t2tb303 x))))

(declare-fun tb2t303 (uni) (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  uninterpreted_type1)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  uninterpreted_type1))))
  (! (= (tb2t303 (t2tb303 i)) i) :pattern ((t2tb303 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) uninterpreted_type))
     j) (= (t2tb303 (tb2t303 j)) j)) :pattern ((t2tb303 (tb2t303 j))) )))

(declare-fun t2tb304 ((tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  uninterpreted_type1)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) uninterpreted_type1)))
  (sort (tuple21 (tuple21 (tuple21 bool bool) bool) uninterpreted_type)
  (t2tb304 x))))

(declare-fun tb2t304 (uni) (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  uninterpreted_type1))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 (tuple2 Bool Bool) Bool) uninterpreted_type1)))
  (! (= (tb2t304 (t2tb304 i)) i) :pattern ((t2tb304 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 (tuple21 (tuple21 bool bool) bool) uninterpreted_type) j)
     (= (t2tb304 (tb2t304 j)) j)) :pattern ((t2tb304 (tb2t304 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)) (y uninterpreted_type1))
  (! (mem
  (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) uninterpreted_type))
  (add (tuple21 (tuple21 (tuple21 bool bool) bool) uninterpreted_type)
  (Tuple2 (tuple21 (tuple21 bool bool) bool) uninterpreted_type (t2tb10 x)
  (t2tb206 y))
  (empty (tuple21 (tuple21 (tuple21 bool bool) bool) uninterpreted_type)))
  (infix_mnmngt uninterpreted_type (tuple21 (tuple21 bool bool) bool)
  (add (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb6 empty6))
  (add uninterpreted_type (t2tb206 y) (t2tb205 empty9)))) :pattern ((tb2t303
                                                                    (add
                                                                    (tuple21
                                                                    (tuple21
                                                                    (tuple21
                                                                    bool
                                                                    bool)
                                                                    bool)
                                                                    uninterpreted_type)
                                                                    (Tuple2
                                                                    (tuple21
                                                                    (tuple21
                                                                    bool
                                                                    bool)
                                                                    bool)
                                                                    uninterpreted_type
                                                                    (t2tb10
                                                                    x)
                                                                    (t2tb206
                                                                    y))
                                                                    (empty
                                                                    (tuple21
                                                                    (tuple21
                                                                    (tuple21
                                                                    bool
                                                                    bool)
                                                                    bool)
                                                                    uninterpreted_type))))) )))

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

(declare-fun t2tb305 ((set (set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))))) (t2tb305 x))))

(declare-fun tb2t305 (uni) (set (set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))))))
  (! (= (tb2t305 (t2tb305 i)) i) :pattern ((t2tb305 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21 (tuple21 bool bool)
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type))))) j) (= (t2tb305 (tb2t305 j)) j)) :pattern (
  (t2tb305 (tb2t305 j))) )))

(declare-fun t2tb306 ((set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))))) (sort
  (set1
  (tuple21 (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)))) (t2tb306 x))))

(declare-fun tb2t306 (uni) (set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))))))
  (! (= (tb2t306 (t2tb306 i)) i) :pattern ((t2tb306 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21 (tuple21 bool bool)
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type)))) j) (= (t2tb306 (tb2t306 j)) j)) :pattern (
  (t2tb306 (tb2t306 j))) )))

(declare-fun t2tb307 ((tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1))))) (sort
  (tuple21 (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))) (t2tb307 x))))

(declare-fun tb2t307 (uni) (tuple2 (tuple2 Bool Bool)
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 Bool Bool) (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1)))))
  (! (= (tb2t307 (t2tb307 i)) i) :pattern ((t2tb307 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 (tuple21 bool bool)
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type))) j) (= (t2tb307 (tb2t307 j)) j)) :pattern (
  (t2tb307 (tb2t307 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 Bool Bool)) (y (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1)))) (! (mem
  (set1
  (tuple21 (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))))
  (add
  (tuple21 (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)))
  (Tuple2 (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb11 x) (t2tb203 y))
  (empty
  (tuple21 (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)))))
  (infix_mnmngt
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (tuple21 bool bool)
  (add (tuple21 bool bool) (t2tb11 x) (t2tb7 empty7))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb203 y) (t2tb202 empty10)))) :pattern (
  (tb2t306
  (add
  (tuple21 (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)))
  (Tuple2 (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb11 x) (t2tb203 y))
  (empty
  (tuple21 (tuple21 bool bool)
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))))))) )))

(declare-fun t2tb308 ((set (set (tuple2 (tuple2 Bool Bool)
  (set uninterpreted_type1))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 Bool Bool)
  (set uninterpreted_type1)))))) (sort
  (set1 (set1 (tuple21 (tuple21 bool bool) (set1 uninterpreted_type))))
  (t2tb308 x))))

(declare-fun tb2t308 (uni) (set (set (tuple2 (tuple2 Bool Bool)
  (set uninterpreted_type1)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 Bool Bool)
  (set uninterpreted_type1))))))
  (! (= (tb2t308 (t2tb308 i)) i) :pattern ((t2tb308 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1 (set1 (tuple21 (tuple21 bool bool) (set1 uninterpreted_type)))) j)
     (= (t2tb308 (tb2t308 j)) j)) :pattern ((t2tb308 (tb2t308 j))) )))

(declare-fun t2tb309 ((set (tuple2 (tuple2 Bool Bool)
  (set uninterpreted_type1)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Bool Bool) (set uninterpreted_type1)))))
  (sort (set1 (tuple21 (tuple21 bool bool) (set1 uninterpreted_type)))
  (t2tb309 x))))

(declare-fun tb2t309 (uni) (set (tuple2 (tuple2 Bool Bool)
  (set uninterpreted_type1))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Bool Bool) (set uninterpreted_type1)))))
  (! (= (tb2t309 (t2tb309 i)) i) :pattern ((t2tb309 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (tuple21 (tuple21 bool bool) (set1 uninterpreted_type)))
     j) (= (t2tb309 (tb2t309 j)) j)) :pattern ((t2tb309 (tb2t309 j))) )))

(declare-fun t2tb310 ((tuple2 (tuple2 Bool Bool)
  (set uninterpreted_type1))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) (set uninterpreted_type1)))) (sort
  (tuple21 (tuple21 bool bool) (set1 uninterpreted_type)) (t2tb310 x))))

(declare-fun tb2t310 (uni) (tuple2 (tuple2 Bool Bool)
  (set uninterpreted_type1)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 Bool Bool) (set uninterpreted_type1))))
  (! (= (tb2t310 (t2tb310 i)) i) :pattern ((t2tb310 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (tuple21 (tuple21 bool bool) (set1 uninterpreted_type)) j)
     (= (t2tb310 (tb2t310 j)) j)) :pattern ((t2tb310 (tb2t310 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 Bool Bool)) (y (set uninterpreted_type1))) (! (mem
  (set1 (tuple21 (tuple21 bool bool) (set1 uninterpreted_type)))
  (add (tuple21 (tuple21 bool bool) (set1 uninterpreted_type))
  (Tuple2 (tuple21 bool bool) (set1 uninterpreted_type) (t2tb11 x)
  (t2tb205 y))
  (empty (tuple21 (tuple21 bool bool) (set1 uninterpreted_type))))
  (infix_mnmngt (set1 uninterpreted_type) (tuple21 bool bool)
  (add (tuple21 bool bool) (t2tb11 x) (t2tb7 empty7))
  (t2tb204 (add5 y empty11)))) :pattern ((tb2t309
                                         (add
                                         (tuple21 (tuple21 bool bool)
                                         (set1 uninterpreted_type))
                                         (Tuple2 (tuple21 bool bool)
                                         (set1 uninterpreted_type) (t2tb11 x)
                                         (t2tb205 y))
                                         (empty
                                         (tuple21 (tuple21 bool bool)
                                         (set1 uninterpreted_type)))))) )))

(declare-fun t2tb311 ((set (set (tuple2 (tuple2 Bool Bool)
  uninterpreted_type1)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 Bool Bool) uninterpreted_type1)))))
  (sort (set1 (set1 (tuple21 (tuple21 bool bool) uninterpreted_type)))
  (t2tb311 x))))

(declare-fun tb2t311 (uni) (set (set (tuple2 (tuple2 Bool Bool)
  uninterpreted_type1))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 Bool Bool) uninterpreted_type1)))))
  (! (= (tb2t311 (t2tb311 i)) i) :pattern ((t2tb311 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (set1 (tuple21 (tuple21 bool bool) uninterpreted_type)))
     j) (= (t2tb311 (tb2t311 j)) j)) :pattern ((t2tb311 (tb2t311 j))) )))

(declare-fun t2tb312 ((set (tuple2 (tuple2 Bool Bool)
  uninterpreted_type1))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 Bool Bool) uninterpreted_type1)))) (sort
  (set1 (tuple21 (tuple21 bool bool) uninterpreted_type)) (t2tb312 x))))

(declare-fun tb2t312 (uni) (set (tuple2 (tuple2 Bool Bool)
  uninterpreted_type1)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 Bool Bool) uninterpreted_type1))))
  (! (= (tb2t312 (t2tb312 i)) i) :pattern ((t2tb312 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (tuple21 (tuple21 bool bool) uninterpreted_type)) j)
     (= (t2tb312 (tb2t312 j)) j)) :pattern ((t2tb312 (tb2t312 j))) )))

(declare-fun t2tb313 ((tuple2 (tuple2 Bool Bool) uninterpreted_type1)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) uninterpreted_type1))) (sort
  (tuple21 (tuple21 bool bool) uninterpreted_type) (t2tb313 x))))

(declare-fun tb2t313 (uni) (tuple2 (tuple2 Bool Bool) uninterpreted_type1))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 Bool Bool) uninterpreted_type1)))
  (! (= (tb2t313 (t2tb313 i)) i) :pattern ((t2tb313 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (tuple21 (tuple21 bool bool) uninterpreted_type) j)
     (= (t2tb313 (tb2t313 j)) j)) :pattern ((t2tb313 (tb2t313 j))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 Bool Bool)) (y uninterpreted_type1)) (! (mem
  (set1 (tuple21 (tuple21 bool bool) uninterpreted_type))
  (add (tuple21 (tuple21 bool bool) uninterpreted_type)
  (Tuple2 (tuple21 bool bool) uninterpreted_type (t2tb11 x) (t2tb206 y))
  (empty (tuple21 (tuple21 bool bool) uninterpreted_type)))
  (infix_mnmngt uninterpreted_type (tuple21 bool bool)
  (add (tuple21 bool bool) (t2tb11 x) (t2tb7 empty7))
  (add uninterpreted_type (t2tb206 y) (t2tb205 empty9)))) :pattern ((tb2t312
                                                                    (add
                                                                    (tuple21
                                                                    (tuple21
                                                                    bool
                                                                    bool)
                                                                    uninterpreted_type)
                                                                    (Tuple2
                                                                    (tuple21
                                                                    bool
                                                                    bool)
                                                                    uninterpreted_type
                                                                    (t2tb11
                                                                    x)
                                                                    (t2tb206
                                                                    y))
                                                                    (empty
                                                                    (tuple21
                                                                    (tuple21
                                                                    bool
                                                                    bool)
                                                                    uninterpreted_type))))) )))

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

(declare-fun t2tb314 ((set (set (tuple2 Bool
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Bool (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1))))))) (sort
  (set1
  (set1
  (tuple21 bool
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))))) (t2tb314 x))))

(declare-fun tb2t314 (uni) (set (set (tuple2 Bool
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Bool (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1)))))))
  (! (= (tb2t314 (t2tb314 i)) i) :pattern ((t2tb314 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21 bool
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type))))) j) (= (t2tb314 (tb2t314 j)) j)) :pattern (
  (t2tb314 (tb2t314 j))) )))

(declare-fun t2tb315 ((set (tuple2 Bool (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Bool (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)))))) (sort
  (set1
  (tuple21 bool
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)))) (t2tb315 x))))

(declare-fun tb2t315 (uni) (set (tuple2 Bool
  (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Bool (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1))))))
  (! (= (tb2t315 (t2tb315 i)) i) :pattern ((t2tb315 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21 bool
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type)))) j) (= (t2tb315 (tb2t315 j)) j)) :pattern (
  (t2tb315 (tb2t315 j))) )))

(declare-fun t2tb316 ((tuple2 Bool (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool) (set uninterpreted_type1)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Bool (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type1))))) (sort
  (tuple21 bool
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))) (t2tb316 x))))

(declare-fun tb2t316 (uni) (tuple2 Bool (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1))))

;; BridgeL
  (assert
  (forall ((i (tuple2 Bool (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set uninterpreted_type1)))))
  (! (= (tb2t316 (t2tb316 i)) i) :pattern ((t2tb316 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 bool
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type))) j) (= (t2tb316 (tb2t316 j)) j)) :pattern (
  (t2tb316 (tb2t316 j))) )))

;; singleton_is_function
  (assert
  (forall ((x Bool) (y (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))) (! (mem
  (set1
  (tuple21 bool
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))))
  (add
  (tuple21 bool
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)))
  (Tuple2 bool
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb12 x) (t2tb203 y))
  (empty
  (tuple21 bool
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)))))
  (infix_mnmngt
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) bool (t2tb2 (add1 x empty1))
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb203 y) (t2tb202 empty10)))) :pattern (
  (tb2t315
  (add
  (tuple21 bool
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)))
  (Tuple2 bool
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb12 x) (t2tb203 y))
  (empty
  (tuple21 bool
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))))))) )))

(declare-fun t2tb317 ((set (set (tuple2 Bool
  (set uninterpreted_type1))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Bool (set uninterpreted_type1)))))) (sort
  (set1 (set1 (tuple21 bool (set1 uninterpreted_type)))) (t2tb317 x))))

(declare-fun tb2t317 (uni) (set (set (tuple2 Bool
  (set uninterpreted_type1)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Bool (set uninterpreted_type1))))))
  (! (= (tb2t317 (t2tb317 i)) i) :pattern ((t2tb317 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (set1 (tuple21 bool (set1 uninterpreted_type)))) j)
     (= (t2tb317 (tb2t317 j)) j)) :pattern ((t2tb317 (tb2t317 j))) )))

(declare-fun t2tb318 ((set (tuple2 Bool (set uninterpreted_type1)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Bool (set uninterpreted_type1))))) (sort
  (set1 (tuple21 bool (set1 uninterpreted_type))) (t2tb318 x))))

(declare-fun tb2t318 (uni) (set (tuple2 Bool (set uninterpreted_type1))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Bool (set uninterpreted_type1)))))
  (! (= (tb2t318 (t2tb318 i)) i) :pattern ((t2tb318 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (tuple21 bool (set1 uninterpreted_type))) j)
     (= (t2tb318 (tb2t318 j)) j)) :pattern ((t2tb318 (tb2t318 j))) )))

(declare-fun t2tb319 ((tuple2 Bool (set uninterpreted_type1))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Bool (set uninterpreted_type1)))) (sort
  (tuple21 bool (set1 uninterpreted_type)) (t2tb319 x))))

(declare-fun tb2t319 (uni) (tuple2 Bool (set uninterpreted_type1)))

;; BridgeL
  (assert
  (forall ((i (tuple2 Bool (set uninterpreted_type1))))
  (! (= (tb2t319 (t2tb319 i)) i) :pattern ((t2tb319 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (tuple21 bool (set1 uninterpreted_type)) j)
     (= (t2tb319 (tb2t319 j)) j)) :pattern ((t2tb319 (tb2t319 j))) )))

;; singleton_is_function
  (assert
  (forall ((x Bool) (y (set uninterpreted_type1))) (! (mem
  (set1 (tuple21 bool (set1 uninterpreted_type)))
  (add (tuple21 bool (set1 uninterpreted_type))
  (Tuple2 bool (set1 uninterpreted_type) (t2tb12 x) (t2tb205 y))
  (empty (tuple21 bool (set1 uninterpreted_type))))
  (infix_mnmngt (set1 uninterpreted_type) bool (t2tb2 (add1 x empty1))
  (t2tb204 (add5 y empty11)))) :pattern ((tb2t318
                                         (add
                                         (tuple21 bool
                                         (set1 uninterpreted_type))
                                         (Tuple2 bool
                                         (set1 uninterpreted_type) (t2tb12 x)
                                         (t2tb205 y))
                                         (empty
                                         (tuple21 bool
                                         (set1 uninterpreted_type)))))) )))

(declare-fun t2tb320 ((set (set (tuple2 Bool uninterpreted_type1)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 Bool uninterpreted_type1))))) (sort
  (set1 (set1 (tuple21 bool uninterpreted_type))) (t2tb320 x))))

(declare-fun tb2t320 (uni) (set (set (tuple2 Bool uninterpreted_type1))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 Bool uninterpreted_type1)))))
  (! (= (tb2t320 (t2tb320 i)) i) :pattern ((t2tb320 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (set1 (tuple21 bool uninterpreted_type))) j)
     (= (t2tb320 (tb2t320 j)) j)) :pattern ((t2tb320 (tb2t320 j))) )))

(declare-fun t2tb321 ((set (tuple2 Bool uninterpreted_type1))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Bool uninterpreted_type1)))) (sort
  (set1 (tuple21 bool uninterpreted_type)) (t2tb321 x))))

(declare-fun tb2t321 (uni) (set (tuple2 Bool uninterpreted_type1)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Bool uninterpreted_type1))))
  (! (= (tb2t321 (t2tb321 i)) i) :pattern ((t2tb321 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (tuple21 bool uninterpreted_type)) j)
     (= (t2tb321 (tb2t321 j)) j)) :pattern ((t2tb321 (tb2t321 j))) )))

(declare-fun t2tb322 ((tuple2 Bool uninterpreted_type1)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 Bool uninterpreted_type1))) (sort
  (tuple21 bool uninterpreted_type) (t2tb322 x))))

(declare-fun tb2t322 (uni) (tuple2 Bool uninterpreted_type1))

;; BridgeL
  (assert
  (forall ((i (tuple2 Bool uninterpreted_type1)))
  (! (= (tb2t322 (t2tb322 i)) i) :pattern ((t2tb322 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (tuple21 bool uninterpreted_type) j)
     (= (t2tb322 (tb2t322 j)) j)) :pattern ((t2tb322 (tb2t322 j))) )))

;; singleton_is_function
  (assert
  (forall ((x Bool) (y uninterpreted_type1)) (! (mem
  (set1 (tuple21 bool uninterpreted_type))
  (add (tuple21 bool uninterpreted_type)
  (Tuple2 bool uninterpreted_type (t2tb12 x) (t2tb206 y))
  (empty (tuple21 bool uninterpreted_type)))
  (infix_mnmngt uninterpreted_type bool (t2tb2 (add1 x empty1))
  (add uninterpreted_type (t2tb206 y) (t2tb205 empty9)))) :pattern ((tb2t321
                                                                    (add
                                                                    (tuple21
                                                                    bool
                                                                    uninterpreted_type)
                                                                    (Tuple2
                                                                    bool
                                                                    uninterpreted_type
                                                                    (t2tb12
                                                                    x)
                                                                    (t2tb206
                                                                    y))
                                                                    (empty
                                                                    (tuple21
                                                                    bool
                                                                    uninterpreted_type))))) )))

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
  (forall ((b ty))
  (forall ((x Bool) (y uni)) (! (mem (set1 (tuple21 bool b))
  (add (tuple21 bool b) (Tuple2 bool b (t2tb12 x) y)
  (empty (tuple21 bool b)))
  (infix_mnmngt b bool (t2tb2 (add1 x empty1)) (add b y (empty b)))) :pattern (
  (add (tuple21 bool b) (Tuple2 bool b (t2tb12 x) y)
  (empty (tuple21 bool b)))) ))))

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
  (forall ((f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))) (s (set (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool))) (t (set (set uninterpreted_type1)))
  (a (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (=>
  (and (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))) (t2tb202 f)
  (infix_plmngt (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb5 s) (t2tb204 t)))
  (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 a)
  (t2tb5 (dom3 f)))) (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type) (t2tb9 a)
  (apply (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb202 f) (t2tb9 a)))
  (t2tb202 f)))))

;; apply_def0
  (assert
  (forall ((f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (t (set (set Int))) (a (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (=>
  (and (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb4 f)
  (infix_plmngt (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 s) (t2tb1 t))) (mem
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 a)
  (t2tb5 (dom2 f)))) (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb9 a)
  (apply (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb4 f) (t2tb9 a))) (t2tb4 f)))))

;; apply_def0
  (assert
  (forall ((f (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (s (set (tuple2 (tuple2 Bool Bool) Bool))) (t (set Bool))
  (a (tuple2 (tuple2 Bool Bool) Bool)))
  (=>
  (and (mem (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (t2tb5 f)
  (infix_plmngt bool (tuple21 (tuple21 bool bool) bool) (t2tb6 s) (t2tb2 t)))
  (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 a) (t2tb6 (dom4 f)))) (mem
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (Tuple2 (tuple21 (tuple21 bool bool) bool) bool (t2tb10 a)
  (apply bool (tuple21 (tuple21 bool bool) bool) (t2tb5 f) (t2tb10 a)))
  (t2tb5 f)))))

;; apply_def0
  (assert
  (forall ((f (set (tuple2 (tuple2 Bool Bool) Bool))) (s (set (tuple2 Bool
  Bool))) (t (set Bool)) (a (tuple2 Bool Bool)))
  (=>
  (and (mem (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb6 f)
  (infix_plmngt bool (tuple21 bool bool) (t2tb7 s) (t2tb2 t))) (mem
  (tuple21 bool bool) (t2tb11 a) (t2tb7 (dom5 f)))) (mem
  (tuple21 (tuple21 bool bool) bool)
  (Tuple2 (tuple21 bool bool) bool (t2tb11 a)
  (apply bool (tuple21 bool bool) (t2tb6 f) (t2tb11 a))) (t2tb6 f)))))

;; apply_def0
  (assert
  (forall ((f (set (tuple2 Bool Bool))) (s (set Bool)) (t (set Bool))
  (a Bool))
  (=>
  (and (mem (set1 (tuple21 bool bool)) (t2tb7 f)
  (infix_plmngt bool bool (t2tb2 s) (t2tb2 t))) (mem bool (t2tb12 a)
  (t2tb2 (dom1 f)))) (mem (tuple21 bool bool)
  (Tuple2 bool bool (t2tb12 a) (apply bool bool (t2tb7 f) (t2tb12 a)))
  (t2tb7 f)))))

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
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (y (set uninterpreted_type1)))
  (= (tb2t205
     (apply (set1 uninterpreted_type)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (add
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type))
     (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type) (t2tb9 x) (t2tb205 y)) (t2tb202 empty10))
     (t2tb9 x))) y)))

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
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))) (s (set (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool))) (t (set (set uninterpreted_type1))))
  (! (=>
     (and (mem
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type))) (t2tb202 f)
     (infix_plmngt (set1 uninterpreted_type)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb5 s) (t2tb204 t)))
     (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
     (t2tb5 (dom3 f)))) (mem (set1 uninterpreted_type)
     (apply (set1 uninterpreted_type)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb202 f) (t2tb9 x))
     (t2tb204 t))) :pattern ((mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))) (t2tb202 f)
  (infix_plmngt (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb5 s) (t2tb204 t)))
  (tb2t205
  (apply (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb202 f) (t2tb9 x)))) )))

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
     (t2tb4 f)
     (infix_plmngt (set1 int)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb5 s) (t2tb1 t)))
     (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
     (t2tb5 (dom2 f)))) (mem (set1 int)
     (apply (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (t2tb4 f) (t2tb9 x)) (t2tb1 t))) :pattern ((mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb4 f)
  (infix_plmngt (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 s) (t2tb1 t)))
  (tb2t3
  (apply (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb4 f) (t2tb9 x)))) )))

;; apply_range
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool))
  (f (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (s (set (tuple2 (tuple2 Bool Bool) Bool))) (t (set Bool)))
  (! (=>
     (and (mem (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
     (t2tb5 f)
     (infix_plmngt bool (tuple21 (tuple21 bool bool) bool) (t2tb6 s)
     (t2tb2 t))) (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x)
     (t2tb6 (dom4 f)))) (mem bool
     (apply bool (tuple21 (tuple21 bool bool) bool) (t2tb5 f) (t2tb10 x))
     (t2tb2 t))) :pattern ((mem
  (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb5 f)
  (infix_plmngt bool (tuple21 (tuple21 bool bool) bool) (t2tb6 s) (t2tb2 t)))
  (tb2t12
  (apply bool (tuple21 (tuple21 bool bool) bool) (t2tb5 f) (t2tb10 x)))) )))

;; apply_range
  (assert
  (forall ((x (tuple2 Bool Bool)) (f (set (tuple2 (tuple2 Bool Bool) Bool)))
  (s (set (tuple2 Bool Bool))) (t (set Bool)))
  (! (=>
     (and (mem (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb6 f)
     (infix_plmngt bool (tuple21 bool bool) (t2tb7 s) (t2tb2 t))) (mem
     (tuple21 bool bool) (t2tb11 x) (t2tb7 (dom5 f)))) (mem bool
     (apply bool (tuple21 bool bool) (t2tb6 f) (t2tb11 x)) (t2tb2 t))) :pattern ((mem
  (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb6 f)
  (infix_plmngt bool (tuple21 bool bool) (t2tb7 s) (t2tb2 t)))
  (tb2t12 (apply bool (tuple21 bool bool) (t2tb6 f) (t2tb11 x)))) )))

;; apply_range
  (assert
  (forall ((x Bool) (f (set (tuple2 Bool Bool))) (s (set Bool))
  (t (set Bool)))
  (! (=>
     (and (mem (set1 (tuple21 bool bool)) (t2tb7 f)
     (infix_plmngt bool bool (t2tb2 s) (t2tb2 t))) (mem bool (t2tb12 x)
     (t2tb2 (dom1 f)))) (mem bool (apply bool bool (t2tb7 f) (t2tb12 x))
     (t2tb2 t))) :pattern ((mem
  (set1 (tuple21 bool bool)) (t2tb7 f)
  (infix_plmngt bool bool (t2tb2 s) (t2tb2 t)))
  (tb2t12 (apply bool bool (t2tb7 f) (t2tb12 x)))) )))

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
  (forall ((b ty))
  (forall ((f uni) (g uni)) (subset
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5
  (dom3
  (tb2t202
  (semicolon (set1 uninterpreted_type) b
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) f g))))
  (dom b (tuple21 (tuple21 (tuple21 bool bool) bool) bool) f)))))

;; semicolon_dom
  (assert
  (forall ((b ty))
  (forall ((f uni) (g uni)) (subset
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5
  (dom2
  (tb2t4
  (semicolon (set1 int) b (tuple21 (tuple21 (tuple21 bool bool) bool) bool) f
  g)))) (dom b (tuple21 (tuple21 (tuple21 bool bool) bool) bool) f)))))

;; semicolon_dom
  (assert
  (forall ((f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))) (g (set (tuple2 (set uninterpreted_type1)
  (set uninterpreted_type1))))) (subset
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5
  (dom3
  (tb2t202
  (semicolon (set1 uninterpreted_type) (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb202 f) (t2tb237 g)))))
  (t2tb5 (dom3 f)))))

(declare-fun t2tb323 ((set (tuple2 (set uninterpreted_type1)
  (set Int)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (set uninterpreted_type1) (set Int))))) (sort
  (set1 (tuple21 (set1 uninterpreted_type) (set1 int))) (t2tb323 x))))

(declare-fun tb2t323 (uni) (set (tuple2 (set uninterpreted_type1)
  (set Int))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (set uninterpreted_type1) (set Int)))))
  (! (= (tb2t323 (t2tb323 i)) i) :pattern ((t2tb323 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb323 (tb2t323 j)) j) :pattern ((t2tb323 (tb2t323 j))) )))

;; semicolon_dom
  (assert
  (forall ((f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))) (g (set (tuple2 (set uninterpreted_type1)
  (set Int))))) (subset (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5
  (dom2
  (tb2t4
  (semicolon (set1 int) (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb202 f) (t2tb323 g)))))
  (t2tb5 (dom3 f)))))

;; semicolon_dom
  (assert
  (forall ((c ty))
  (forall ((f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))) (g uni)) (subset
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (dom c (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (semicolon c (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb202 f) g))
  (t2tb5 (dom3 f))))))

(declare-fun t2tb324 ((set (tuple2 (set Int)
  (set uninterpreted_type1)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (set Int) (set uninterpreted_type1))))) (sort
  (set1 (tuple21 (set1 int) (set1 uninterpreted_type))) (t2tb324 x))))

(declare-fun tb2t324 (uni) (set (tuple2 (set Int)
  (set uninterpreted_type1))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (set Int) (set uninterpreted_type1)))))
  (! (= (tb2t324 (t2tb324 i)) i) :pattern ((t2tb324 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb324 (tb2t324 j)) j) :pattern ((t2tb324 (tb2t324 j))) )))

;; semicolon_dom
  (assert
  (forall ((f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (g (set (tuple2 (set Int) (set uninterpreted_type1)))))
  (subset (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5
  (dom3
  (tb2t202
  (semicolon (set1 uninterpreted_type) (set1 int)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb4 f) (t2tb324 g)))))
  (t2tb5 (dom2 f)))))

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

;; semicolon_dom
  (assert
  (forall ((f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (g (set (tuple2 (set Int) (set Int))))) (subset
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5
  (dom2
  (tb2t4
  (semicolon (set1 int) (set1 int)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb4 f) (t2tb37 g)))))
  (t2tb5 (dom2 f)))))

;; semicolon_dom
  (assert
  (forall ((c ty))
  (forall ((f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (g uni)) (subset
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (dom c (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (semicolon c (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb4 f) g)) (t2tb5 (dom2 f))))))

;; semicolon_dom
  (assert
  (forall ((b ty))
  (forall ((f uni) (g uni)) (subset (tuple21 (tuple21 bool bool) bool)
  (t2tb6
  (dom4 (tb2t5 (semicolon bool b (tuple21 (tuple21 bool bool) bool) f g))))
  (dom b (tuple21 (tuple21 bool bool) bool) f)))))

;; semicolon_dom
  (assert
  (forall ((f (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (g (set (tuple2 Bool Bool)))) (subset (tuple21 (tuple21 bool bool) bool)
  (t2tb6
  (dom4
  (tb2t5
  (semicolon bool bool (tuple21 (tuple21 bool bool) bool) (t2tb5 f)
  (t2tb7 g))))) (t2tb6 (dom4 f)))))

;; semicolon_dom
  (assert
  (forall ((c ty))
  (forall ((f (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))) (g uni))
  (subset (tuple21 (tuple21 bool bool) bool)
  (dom c (tuple21 (tuple21 bool bool) bool)
  (semicolon c bool (tuple21 (tuple21 bool bool) bool) (t2tb5 f) g))
  (t2tb6 (dom4 f))))))

;; semicolon_dom
  (assert
  (forall ((b ty))
  (forall ((f uni) (g uni)) (subset (tuple21 bool bool)
  (t2tb7 (dom5 (tb2t6 (semicolon bool b (tuple21 bool bool) f g))))
  (dom b (tuple21 bool bool) f)))))

;; semicolon_dom
  (assert
  (forall ((f (set (tuple2 (tuple2 Bool Bool) Bool))) (g (set (tuple2 Bool
  Bool)))) (subset (tuple21 bool bool)
  (t2tb7
  (dom5
  (tb2t6 (semicolon bool bool (tuple21 bool bool) (t2tb6 f) (t2tb7 g)))))
  (t2tb7 (dom5 f)))))

;; semicolon_dom
  (assert
  (forall ((c ty))
  (forall ((f (set (tuple2 (tuple2 Bool Bool) Bool))) (g uni)) (subset
  (tuple21 bool bool)
  (dom c (tuple21 bool bool)
  (semicolon c bool (tuple21 bool bool) (t2tb6 f) g)) (t2tb7 (dom5 f))))))

;; semicolon_dom
  (assert
  (forall ((b ty))
  (forall ((f uni) (g uni)) (subset bool
  (t2tb2 (dom1 (tb2t7 (semicolon bool b bool f g)))) (dom b bool f)))))

;; semicolon_dom
  (assert
  (forall ((f (set (tuple2 Bool Bool))) (g (set (tuple2 Bool Bool)))) (subset
  bool (t2tb2 (dom1 (tb2t7 (semicolon bool bool bool (t2tb7 f) (t2tb7 g)))))
  (t2tb2 (dom1 f)))))

;; semicolon_dom
  (assert
  (forall ((c ty))
  (forall ((f (set (tuple2 Bool Bool))) (g uni)) (subset bool
  (dom c bool (semicolon c bool bool (t2tb7 f) g)) (t2tb2 (dom1 f))))))

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
  Bool) Bool) (set uninterpreted_type1)))) (s uni)
  (t (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (u (set (set uninterpreted_type1))))
  (=>
  (and (mem
  (set1 (tuple21 a (tuple21 (tuple21 (tuple21 bool bool) bool) bool))) f
  (infix_plmngt (tuple21 (tuple21 (tuple21 bool bool) bool) bool) a s
  (t2tb5 t)))
  (and (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))) (t2tb202 g)
  (infix_plmngt (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb5 t) (t2tb204 u)))
  (and (mem a x (dom (tuple21 (tuple21 (tuple21 bool bool) bool) bool) a f))
  (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (apply (tuple21 (tuple21 (tuple21 bool bool) bool) bool) a f x)
  (t2tb5 (dom3 g))))))
  (= (tb2t205
     (apply (set1 uninterpreted_type) a
     (semicolon (set1 uninterpreted_type)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) a f (t2tb202 g)) x)) 
  (tb2t205
  (apply (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb202 g)
  (apply (tuple21 (tuple21 (tuple21 bool bool) bool) bool) a f x))))))))

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
  (and (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb4 g)
  (infix_plmngt (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 t) (t2tb1 u)))
  (and (mem a x (dom (tuple21 (tuple21 (tuple21 bool bool) bool) bool) a f))
  (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (apply (tuple21 (tuple21 (tuple21 bool bool) bool) bool) a f x)
  (t2tb5 (dom2 g))))))
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
  (forall ((a ty))
  (forall ((x uni) (f uni) (g (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool))) (s uni) (t (set (tuple2 (tuple2 Bool Bool) Bool))) (u (set Bool)))
  (=>
  (and (mem (set1 (tuple21 a (tuple21 (tuple21 bool bool) bool))) f
  (infix_plmngt (tuple21 (tuple21 bool bool) bool) a s (t2tb6 t)))
  (and (mem (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (t2tb5 g)
  (infix_plmngt bool (tuple21 (tuple21 bool bool) bool) (t2tb6 t) (t2tb2 u)))
  (and (mem a x (dom (tuple21 (tuple21 bool bool) bool) a f)) (mem
  (tuple21 (tuple21 bool bool) bool)
  (apply (tuple21 (tuple21 bool bool) bool) a f x) (t2tb6 (dom4 g))))))
  (= (tb2t12
     (apply bool a
     (semicolon bool (tuple21 (tuple21 bool bool) bool) a f (t2tb5 g)) x)) 
  (tb2t12
  (apply bool (tuple21 (tuple21 bool bool) bool) (t2tb5 g)
  (apply (tuple21 (tuple21 bool bool) bool) a f x))))))))

;; apply_compose
  (assert
  (forall ((a ty))
  (forall ((x uni) (f uni) (g (set (tuple2 (tuple2 Bool Bool) Bool))) (s uni)
  (t (set (tuple2 Bool Bool))) (u (set Bool)))
  (=>
  (and (mem (set1 (tuple21 a (tuple21 bool bool))) f
  (infix_plmngt (tuple21 bool bool) a s (t2tb7 t)))
  (and (mem (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb6 g)
  (infix_plmngt bool (tuple21 bool bool) (t2tb7 t) (t2tb2 u)))
  (and (mem a x (dom (tuple21 bool bool) a f)) (mem (tuple21 bool bool)
  (apply (tuple21 bool bool) a f x) (t2tb7 (dom5 g))))))
  (= (tb2t12
     (apply bool a (semicolon bool (tuple21 bool bool) a f (t2tb6 g)) x)) 
  (tb2t12
  (apply bool (tuple21 bool bool) (t2tb6 g)
  (apply (tuple21 bool bool) a f x))))))))

;; apply_compose
  (assert
  (forall ((a ty))
  (forall ((x uni) (f uni) (g (set (tuple2 Bool Bool))) (s uni)
  (t (set Bool)) (u (set Bool)))
  (=>
  (and (mem (set1 (tuple21 a bool)) f (infix_plmngt bool a s (t2tb2 t)))
  (and (mem (set1 (tuple21 bool bool)) (t2tb7 g)
  (infix_plmngt bool bool (t2tb2 t) (t2tb2 u)))
  (and (mem a x (dom bool a f)) (mem bool (apply bool a f x)
  (t2tb2 (dom1 g))))))
  (= (tb2t12 (apply bool a (semicolon bool bool a f (t2tb7 g)) x)) (tb2t12
                                                                   (apply
                                                                   bool 
                                                                   bool
                                                                   (t2tb7 g)
                                                                   (apply
                                                                   bool a f
                                                                   x))))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))) (g uni) (s (set (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool))) (t (set (set uninterpreted_type1))) (u uni))
  (=>
  (and (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))) (t2tb202 f)
  (infix_plmngt (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb5 s) (t2tb204 t)))
  (and (mem (set1 (tuple21 (set1 uninterpreted_type) c)) g
  (infix_plmngt c (set1 uninterpreted_type) (t2tb204 t) u))
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
  (t2tb5 (dom3 f))) (mem (set1 uninterpreted_type)
  (apply (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb202 f) (t2tb9 x))
  (dom c (set1 uninterpreted_type) g)))))
  (= (apply c (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (semicolon c (set1 uninterpreted_type)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb202 f) g)
     (t2tb9 x)) (apply c (set1 uninterpreted_type) g
                (apply (set1 uninterpreted_type)
                (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb202 f)
                (t2tb9 x))))))))

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
  (t2tb4 f)
  (infix_plmngt (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 s) (t2tb1 t)))
  (and (mem (set1 (tuple21 (set1 int) c)) g
  (infix_plmngt c (set1 int) (t2tb1 t) u))
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
  (t2tb5 (dom2 f))) (mem (set1 int)
  (apply (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb4 f) (t2tb9 x)) (dom c (set1 int) g)))))
  (= (apply c (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (semicolon c (set1 int)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb4 f) g)
     (t2tb9 x)) (apply c (set1 int) g
                (apply (set1 int)
                (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb4 f)
                (t2tb9 x))))))))

;; apply_compose
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool))
  (f (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (g (set (tuple2 Bool Bool))) (s (set (tuple2 (tuple2 Bool Bool) Bool)))
  (t (set Bool)) (u (set Bool)))
  (=>
  (and (mem (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (t2tb5 f)
  (infix_plmngt bool (tuple21 (tuple21 bool bool) bool) (t2tb6 s) (t2tb2 t)))
  (and (mem (set1 (tuple21 bool bool)) (t2tb7 g)
  (infix_plmngt bool bool (t2tb2 t) (t2tb2 u)))
  (and (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb6 (dom4 f)))
  (mem bool
  (apply bool (tuple21 (tuple21 bool bool) bool) (t2tb5 f) (t2tb10 x))
  (t2tb2 (dom1 g))))))
  (= (tb2t12
     (apply bool (tuple21 (tuple21 bool bool) bool)
     (semicolon bool bool (tuple21 (tuple21 bool bool) bool) (t2tb5 f)
     (t2tb7 g)) (t2tb10 x))) (tb2t12
                             (apply bool bool (t2tb7 g)
                             (apply bool (tuple21 (tuple21 bool bool) bool)
                             (t2tb5 f) (t2tb10 x))))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool))
  (f (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))) (g uni)
  (s (set (tuple2 (tuple2 Bool Bool) Bool))) (t (set Bool)) (u uni))
  (=>
  (and (mem (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
  (t2tb5 f)
  (infix_plmngt bool (tuple21 (tuple21 bool bool) bool) (t2tb6 s) (t2tb2 t)))
  (and (mem (set1 (tuple21 bool c)) g (infix_plmngt c bool (t2tb2 t) u))
  (and (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb6 (dom4 f)))
  (mem bool
  (apply bool (tuple21 (tuple21 bool bool) bool) (t2tb5 f) (t2tb10 x))
  (dom c bool g)))))
  (= (apply c (tuple21 (tuple21 bool bool) bool)
     (semicolon c bool (tuple21 (tuple21 bool bool) bool) (t2tb5 f) g)
     (t2tb10 x)) (apply c bool g
                 (apply bool (tuple21 (tuple21 bool bool) bool) (t2tb5 f)
                 (t2tb10 x))))))))

;; apply_compose
  (assert
  (forall ((x (tuple2 Bool Bool)) (f (set (tuple2 (tuple2 Bool Bool) Bool)))
  (g (set (tuple2 Bool Bool))) (s (set (tuple2 Bool Bool))) (t (set Bool))
  (u (set Bool)))
  (=>
  (and (mem (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb6 f)
  (infix_plmngt bool (tuple21 bool bool) (t2tb7 s) (t2tb2 t)))
  (and (mem (set1 (tuple21 bool bool)) (t2tb7 g)
  (infix_plmngt bool bool (t2tb2 t) (t2tb2 u)))
  (and (mem (tuple21 bool bool) (t2tb11 x) (t2tb7 (dom5 f))) (mem bool
  (apply bool (tuple21 bool bool) (t2tb6 f) (t2tb11 x)) (t2tb2 (dom1 g))))))
  (= (tb2t12
     (apply bool (tuple21 bool bool)
     (semicolon bool bool (tuple21 bool bool) (t2tb6 f) (t2tb7 g))
     (t2tb11 x))) (tb2t12
                  (apply bool bool (t2tb7 g)
                  (apply bool (tuple21 bool bool) (t2tb6 f) (t2tb11 x))))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x (tuple2 Bool Bool)) (f (set (tuple2 (tuple2 Bool Bool) Bool)))
  (g uni) (s (set (tuple2 Bool Bool))) (t (set Bool)) (u uni))
  (=>
  (and (mem (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb6 f)
  (infix_plmngt bool (tuple21 bool bool) (t2tb7 s) (t2tb2 t)))
  (and (mem (set1 (tuple21 bool c)) g (infix_plmngt c bool (t2tb2 t) u))
  (and (mem (tuple21 bool bool) (t2tb11 x) (t2tb7 (dom5 f))) (mem bool
  (apply bool (tuple21 bool bool) (t2tb6 f) (t2tb11 x)) (dom c bool g)))))
  (= (apply c (tuple21 bool bool)
     (semicolon c bool (tuple21 bool bool) (t2tb6 f) g) (t2tb11 x)) (apply c
                                                                    bool g
                                                                    (apply
                                                                    bool
                                                                    (tuple21
                                                                    bool
                                                                    bool)
                                                                    (t2tb6 f)
                                                                    (t2tb11
                                                                    x))))))))

;; apply_compose
  (assert
  (forall ((x Bool) (f (set (tuple2 Bool Bool))) (g (set (tuple2 Bool Bool)))
  (s (set Bool)) (t (set Bool)) (u (set Bool)))
  (=>
  (and (mem (set1 (tuple21 bool bool)) (t2tb7 f)
  (infix_plmngt bool bool (t2tb2 s) (t2tb2 t)))
  (and (mem (set1 (tuple21 bool bool)) (t2tb7 g)
  (infix_plmngt bool bool (t2tb2 t) (t2tb2 u)))
  (and (mem bool (t2tb12 x) (t2tb2 (dom1 f))) (mem bool
  (apply bool bool (t2tb7 f) (t2tb12 x)) (t2tb2 (dom1 g))))))
  (= (tb2t12
     (apply bool bool (semicolon bool bool bool (t2tb7 f) (t2tb7 g))
     (t2tb12 x))) (tb2t12
                  (apply bool bool (t2tb7 g)
                  (apply bool bool (t2tb7 f) (t2tb12 x))))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x Bool) (f (set (tuple2 Bool Bool))) (g uni) (s (set Bool))
  (t (set Bool)) (u uni))
  (=>
  (and (mem (set1 (tuple21 bool bool)) (t2tb7 f)
  (infix_plmngt bool bool (t2tb2 s) (t2tb2 t)))
  (and (mem (set1 (tuple21 bool c)) g (infix_plmngt c bool (t2tb2 t) u))
  (and (mem bool (t2tb12 x) (t2tb2 (dom1 f))) (mem bool
  (apply bool bool (t2tb7 f) (t2tb12 x)) (dom c bool g)))))
  (= (apply c bool (semicolon c bool bool (t2tb7 f) g) (t2tb12 x)) (apply c
                                                                   bool g
                                                                   (apply
                                                                   bool 
                                                                   bool
                                                                   (t2tb7 f)
                                                                   (t2tb12 x))))))))

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
  (assert (forall ((s (set Bool))) (= (dom1 (tb2t7 (id bool (t2tb2 s)))) s)))

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
  (forall ((s (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))))) (is_finite_subset
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb202 empty10) (t2tb202 s) 0)))

;; Empty
  (assert
  (forall ((s (set (set uninterpreted_type1)))) (is_finite_subset
  (set1 uninterpreted_type) (t2tb204 empty11) (t2tb204 s) 0)))

;; Empty
  (assert
  (forall ((s (set uninterpreted_type1))) (is_finite_subset
  uninterpreted_type (t2tb205 empty9) (t2tb205 s) 0)))

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
  (forall ((s (set (tuple2 Bool Bool)))) (is_finite_subset
  (tuple21 bool bool) (t2tb7 empty7) (t2tb7 s) 0)))

;; Empty
  (assert
  (forall ((s (set Bool))) (is_finite_subset bool (t2tb2 empty1) (t2tb2 s)
  0)))

;; Empty
  (assert
  (forall ((a ty)) (forall ((s uni)) (is_finite_subset a (empty a) s 0))))

;; Add_mem
  (assert
  (forall ((x (set uninterpreted_type1)) (s1 (set (set uninterpreted_type1)))
  (s2 (set (set uninterpreted_type1))) (c Int))
  (=> (is_finite_subset (set1 uninterpreted_type) (t2tb204 s1) (t2tb204 s2)
  c)
  (=> (mem (set1 uninterpreted_type) (t2tb205 x) (t2tb204 s2))
  (=> (mem (set1 uninterpreted_type) (t2tb205 x) (t2tb204 s1))
  (is_finite_subset (set1 uninterpreted_type) (t2tb204 (add5 x s1))
  (t2tb204 s2) c))))))

;; Add_mem
  (assert
  (forall ((x Bool) (s1 (set Bool)) (s2 (set Bool)) (c Int))
  (=> (is_finite_subset bool (t2tb2 s1) (t2tb2 s2) c)
  (=> (mem bool (t2tb12 x) (t2tb2 s2))
  (=> (mem bool (t2tb12 x) (t2tb2 s1)) (is_finite_subset bool
  (t2tb2 (add1 x s1)) (t2tb2 s2) c))))))

;; Add_mem
  (assert
  (forall ((a ty))
  (forall ((x uni) (s1 uni) (s2 uni) (c Int))
  (=> (is_finite_subset a s1 s2 c)
  (=> (mem a x s2) (=> (mem a x s1) (is_finite_subset a (add a x s1) s2 c)))))))

;; Add_notmem
  (assert
  (forall ((x (set uninterpreted_type1)) (s1 (set (set uninterpreted_type1)))
  (s2 (set (set uninterpreted_type1))) (c Int))
  (=> (is_finite_subset (set1 uninterpreted_type) (t2tb204 s1) (t2tb204 s2)
  c)
  (=> (mem (set1 uninterpreted_type) (t2tb205 x) (t2tb204 s2))
  (=> (not (mem (set1 uninterpreted_type) (t2tb205 x) (t2tb204 s1)))
  (is_finite_subset (set1 uninterpreted_type) (t2tb204 (add5 x s1))
  (t2tb204 s2) (+ c 1)))))))

;; Add_notmem
  (assert
  (forall ((x Bool) (s1 (set Bool)) (s2 (set Bool)) (c Int))
  (=> (is_finite_subset bool (t2tb2 s1) (t2tb2 s2) c)
  (=> (mem bool (t2tb12 x) (t2tb2 s2))
  (=> (not (mem bool (t2tb12 x) (t2tb2 s1))) (is_finite_subset bool
  (t2tb2 (add1 x s1)) (t2tb2 s2) (+ c 1)))))))

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
  (set uninterpreted_type1)))) (z1 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1)))) (z2 Int))
  (=> (is_finite_subset
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb202 z) (t2tb202 z1) z2)
  (or
  (or
  (exists ((s (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))))) (and (and (= z empty10) (= z1 s)) (= z2 0)))
  (exists ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))) (s1 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1))))
  (s2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))) (c Int))
  (and (is_finite_subset
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb202 s1) (t2tb202 s2) c)
  (and (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb203 x) (t2tb202 s2))
  (and (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb203 x) (t2tb202 s1))
  (and
  (and
  (= z (tb2t202
       (add
       (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
       (set1 uninterpreted_type)) (t2tb203 x) (t2tb202 s1))))
  (= z1 s2)) (= z2 c)))))))
  (exists ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))) (s1 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1))))
  (s2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))) (c Int))
  (and (is_finite_subset
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb202 s1) (t2tb202 s2) c)
  (and (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb203 x) (t2tb202 s2))
  (and
  (not (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb203 x) (t2tb202 s1)))
  (and
  (and
  (= z (tb2t202
       (add
       (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
       (set1 uninterpreted_type)) (t2tb203 x) (t2tb202 s1))))
  (= z1 s2)) (= z2 (+ c 1)))))))))))

;; is_finite_subset_inversion
  (assert
  (forall ((z (set (set uninterpreted_type1)))
  (z1 (set (set uninterpreted_type1))) (z2 Int))
  (=> (is_finite_subset (set1 uninterpreted_type) (t2tb204 z) (t2tb204 z1)
  z2)
  (or
  (or
  (exists ((s (set (set uninterpreted_type1))))
  (and (and (= z empty11) (= z1 s)) (= z2 0)))
  (exists ((x (set uninterpreted_type1)) (s1 (set (set uninterpreted_type1)))
  (s2 (set (set uninterpreted_type1))) (c Int))
  (and (is_finite_subset (set1 uninterpreted_type) (t2tb204 s1) (t2tb204 s2)
  c)
  (and (mem (set1 uninterpreted_type) (t2tb205 x) (t2tb204 s2))
  (and (mem (set1 uninterpreted_type) (t2tb205 x) (t2tb204 s1))
  (and (and (= z (add5 x s1)) (= z1 s2)) (= z2 c)))))))
  (exists ((x (set uninterpreted_type1)) (s1 (set (set uninterpreted_type1)))
  (s2 (set (set uninterpreted_type1))) (c Int))
  (and (is_finite_subset (set1 uninterpreted_type) (t2tb204 s1) (t2tb204 s2)
  c)
  (and (mem (set1 uninterpreted_type) (t2tb205 x) (t2tb204 s2))
  (and (not (mem (set1 uninterpreted_type) (t2tb205 x) (t2tb204 s1)))
  (and (and (= z (add5 x s1)) (= z1 s2)) (= z2 (+ c 1)))))))))))

;; is_finite_subset_inversion
  (assert
  (forall ((z (set uninterpreted_type1)) (z1 (set uninterpreted_type1))
  (z2 Int))
  (=> (is_finite_subset uninterpreted_type (t2tb205 z) (t2tb205 z1) z2)
  (or
  (or
  (exists ((s (set uninterpreted_type1)))
  (and (and (= z empty9) (= z1 s)) (= z2 0)))
  (exists ((x uninterpreted_type1) (s1 (set uninterpreted_type1))
  (s2 (set uninterpreted_type1)) (c Int))
  (and (is_finite_subset uninterpreted_type (t2tb205 s1) (t2tb205 s2) c)
  (and (mem uninterpreted_type (t2tb206 x) (t2tb205 s2))
  (and (mem uninterpreted_type (t2tb206 x) (t2tb205 s1))
  (and
  (and (= z (tb2t205 (add uninterpreted_type (t2tb206 x) (t2tb205 s1))))
  (= z1 s2)) (= z2 c)))))))
  (exists ((x uninterpreted_type1) (s1 (set uninterpreted_type1))
  (s2 (set uninterpreted_type1)) (c Int))
  (and (is_finite_subset uninterpreted_type (t2tb205 s1) (t2tb205 s2) c)
  (and (mem uninterpreted_type (t2tb206 x) (t2tb205 s2))
  (and (not (mem uninterpreted_type (t2tb206 x) (t2tb205 s1)))
  (and
  (and (= z (tb2t205 (add uninterpreted_type (t2tb206 x) (t2tb205 s1))))
  (= z1 s2)) (= z2 (+ c 1)))))))))))

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
  (and (mem bool (t2tb12 x) (t2tb2 s2))
  (and (mem bool (t2tb12 x) (t2tb2 s1))
  (and (and (= z (add1 x s1)) (= z1 s2)) (= z2 c)))))))
  (exists ((x Bool) (s1 (set Bool)) (s2 (set Bool)) (c Int))
  (and (is_finite_subset bool (t2tb2 s1) (t2tb2 s2) c)
  (and (mem bool (t2tb12 x) (t2tb2 s2))
  (and (not (mem bool (t2tb12 x) (t2tb2 s1)))
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
  (forall ((a ty))
  (forall ((s uni) (x uni))
  (= (mem (set1 a) x (finite_subsets a s))
  (exists ((c Int)) (is_finite_subset a x s c))))))

;; finite_Empty
  (assert
  (forall ((s (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))))) (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))) (t2tb202 empty10)
  (finite_subsets
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb202 s)))))

;; finite_Empty
  (assert
  (forall ((s (set (set uninterpreted_type1)))) (mem
  (set1 (set1 uninterpreted_type)) (t2tb204 empty11)
  (finite_subsets (set1 uninterpreted_type) (t2tb204 s)))))

;; finite_Empty
  (assert
  (forall ((s (set uninterpreted_type1))) (mem (set1 uninterpreted_type)
  (t2tb205 empty9) (finite_subsets uninterpreted_type (t2tb205 s)))))

;; finite_Empty
  (assert
  (forall ((s (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))))) (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb4 empty4)
  (finite_subsets
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb4 s)))))

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
  (forall ((s (set (tuple2 Bool Bool)))) (mem (set1 (tuple21 bool bool))
  (t2tb7 empty7) (finite_subsets (tuple21 bool bool) (t2tb7 s)))))

;; finite_Empty
  (assert
  (forall ((s (set Bool))) (mem (set1 bool) (t2tb2 empty1)
  (finite_subsets bool (t2tb2 s)))))

;; finite_Empty
  (assert
  (forall ((a ty))
  (forall ((s uni)) (mem (set1 a) (empty a) (finite_subsets a s)))))

;; finite_Add
  (assert
  (forall ((x (set uninterpreted_type1)) (s1 (set (set uninterpreted_type1)))
  (s2 (set (set uninterpreted_type1))))
  (=> (mem (set1 (set1 uninterpreted_type)) (t2tb204 s1)
  (finite_subsets (set1 uninterpreted_type) (t2tb204 s2)))
  (=> (mem (set1 uninterpreted_type) (t2tb205 x) (t2tb204 s2)) (mem
  (set1 (set1 uninterpreted_type)) (t2tb204 (add5 x s1))
  (finite_subsets (set1 uninterpreted_type) (t2tb204 s2)))))))

;; finite_Add
  (assert
  (forall ((x Bool) (s1 (set Bool)) (s2 (set Bool)))
  (=> (mem (set1 bool) (t2tb2 s1) (finite_subsets bool (t2tb2 s2)))
  (=> (mem bool (t2tb12 x) (t2tb2 s2)) (mem (set1 bool) (t2tb2 (add1 x s1))
  (finite_subsets bool (t2tb2 s2)))))))

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
  (set uninterpreted_type1)))) (s2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1)))))
  (=> (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))) (t2tb202 s1)
  (finite_subsets
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb202 s2)))
  (or (= s1 empty10)
  (exists ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1))) (s3 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1)))))
  (and
  (= s1 (tb2t202
        (add
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 uninterpreted_type)) (t2tb203 x) (t2tb202 s3))))
  (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))) (t2tb202 s3)
  (finite_subsets
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb202 s2)))))))))

;; finite_inversion
  (assert
  (forall ((s1 (set (set uninterpreted_type1)))
  (s2 (set (set uninterpreted_type1))))
  (=> (mem (set1 (set1 uninterpreted_type)) (t2tb204 s1)
  (finite_subsets (set1 uninterpreted_type) (t2tb204 s2)))
  (or (= s1 empty11)
  (exists ((x (set uninterpreted_type1))
  (s3 (set (set uninterpreted_type1))))
  (and (= s1 (add5 x s3)) (mem (set1 (set1 uninterpreted_type)) (t2tb204 s3)
  (finite_subsets (set1 uninterpreted_type) (t2tb204 s2)))))))))

;; finite_inversion
  (assert
  (forall ((s1 (set uninterpreted_type1)) (s2 (set uninterpreted_type1)))
  (=> (mem (set1 uninterpreted_type) (t2tb205 s1)
  (finite_subsets uninterpreted_type (t2tb205 s2)))
  (or (= s1 empty9)
  (exists ((x uninterpreted_type1) (s3 (set uninterpreted_type1)))
  (and (= s1 (tb2t205 (add uninterpreted_type (t2tb206 x) (t2tb205 s3))))
  (mem (set1 uninterpreted_type) (t2tb205 s3)
  (finite_subsets uninterpreted_type (t2tb205 s2)))))))))

;; finite_inversion
  (assert
  (forall ((s1 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (s2 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool)
  Bool) (set Int)))))
  (=> (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb4 s1)
  (finite_subsets
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb4 s2)))
  (or (= s1 empty4)
  (exists ((x (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int))) (s3 (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))
  (and
  (= s1 (tb2t4
        (add
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 int)) (t2tb8 x) (t2tb4 s3))))
  (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb4 s3)
  (finite_subsets
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb4 s2)))))))))

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
  (set uninterpreted_type1)))) (x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1)))))
  (= (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))) (t2tb202 x)
  (non_empty_finite_subsets
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb202 s)))
  (exists ((c Int))
  (and (is_finite_subset
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb202 x) (t2tb202 s) c) (not (= x empty10)))))))

;; non_empty_finite_subsets_def
  (assert
  (forall ((s (set (set uninterpreted_type1)))
  (x (set (set uninterpreted_type1))))
  (= (mem (set1 (set1 uninterpreted_type)) (t2tb204 x)
  (non_empty_finite_subsets (set1 uninterpreted_type) (t2tb204 s)))
  (exists ((c Int))
  (and (is_finite_subset (set1 uninterpreted_type) (t2tb204 x) (t2tb204 s) c)
  (not (= x empty11)))))))

;; non_empty_finite_subsets_def
  (assert
  (forall ((s (set uninterpreted_type1)) (x (set uninterpreted_type1)))
  (= (mem (set1 uninterpreted_type) (t2tb205 x)
  (non_empty_finite_subsets uninterpreted_type (t2tb205 s)))
  (exists ((c Int))
  (and (is_finite_subset uninterpreted_type (t2tb205 x) (t2tb205 s) c)
  (not (= x empty9)))))))

;; non_empty_finite_subsets_def
  (assert
  (forall ((s (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (x (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))
  (= (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb4 x)
  (non_empty_finite_subsets
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (t2tb4 s)))
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
     (set1 uninterpreted_type)) (t2tb202 empty10)) 0))

;; card_Empty
  (assert (= (card (set1 uninterpreted_type) (t2tb204 empty11)) 0))

;; card_Empty
  (assert (= (card uninterpreted_type (t2tb205 empty9)) 0))

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
  (assert (= (card (tuple21 bool bool) (t2tb7 empty7)) 0))

;; card_Empty
  (assert (= (card bool (t2tb2 empty1)) 0))

;; card_Empty
  (assert (forall ((a ty)) (= (card a (empty a)) 0)))

;; card_Add_not_mem
  (assert
  (forall ((x (set uninterpreted_type1)) (s1 (set (set uninterpreted_type1)))
  (s2 (set (set uninterpreted_type1))))
  (! (=> (mem (set1 (set1 uninterpreted_type)) (t2tb204 s1)
     (finite_subsets (set1 uninterpreted_type) (t2tb204 s2)))
     (=> (not (mem (set1 uninterpreted_type) (t2tb205 x) (t2tb204 s1)))
     (= (card (set1 uninterpreted_type) (t2tb204 (add5 x s1))) (+ (card
                                                                  (set1
                                                                  uninterpreted_type)
                                                                  (t2tb204
                                                                  s1)) 1)))) :pattern ((mem
  (set1 (set1 uninterpreted_type)) (t2tb204 s1)
  (finite_subsets (set1 uninterpreted_type) (t2tb204 s2)))
  (card (set1 uninterpreted_type) (t2tb204 (add5 x s1)))) )))

;; card_Add_not_mem
  (assert
  (forall ((x Bool) (s1 (set Bool)) (s2 (set Bool)))
  (! (=> (mem (set1 bool) (t2tb2 s1) (finite_subsets bool (t2tb2 s2)))
     (=> (not (mem bool (t2tb12 x) (t2tb2 s1)))
     (= (card bool (t2tb2 (add1 x s1))) (+ (card bool (t2tb2 s1)) 1)))) :pattern ((mem
  (set1 bool) (t2tb2 s1) (finite_subsets bool (t2tb2 s2)))
  (card bool (t2tb2 (add1 x s1)))) )))

;; card_Add_not_mem
  (assert
  (forall ((a ty))
  (forall ((x uni) (s1 uni) (s2 uni))
  (! (=> (mem (set1 a) s1 (finite_subsets a s2))
     (=> (not (mem a x s1)) (= (card a (add a x s1)) (+ (card a s1) 1)))) :pattern ((mem
  (set1 a) s1 (finite_subsets a s2)) (card a (add a x s1))) ))))

;; card_Add_mem
  (assert
  (forall ((x (set uninterpreted_type1)) (s1 (set (set uninterpreted_type1)))
  (s2 (set (set uninterpreted_type1))))
  (! (=> (mem (set1 (set1 uninterpreted_type)) (t2tb204 s1)
     (finite_subsets (set1 uninterpreted_type) (t2tb204 s2)))
     (=> (mem (set1 uninterpreted_type) (t2tb205 x) (t2tb204 s1))
     (= (card (set1 uninterpreted_type) (t2tb204 (add5 x s1))) (card
                                                               (set1
                                                               uninterpreted_type)
                                                               (t2tb204 s1))))) :pattern ((mem
  (set1 (set1 uninterpreted_type)) (t2tb204 s1)
  (finite_subsets (set1 uninterpreted_type) (t2tb204 s2)))
  (card (set1 uninterpreted_type) (t2tb204 (add5 x s1)))) )))

;; card_Add_mem
  (assert
  (forall ((x Bool) (s1 (set Bool)) (s2 (set Bool)))
  (! (=> (mem (set1 bool) (t2tb2 s1) (finite_subsets bool (t2tb2 s2)))
     (=> (mem bool (t2tb12 x) (t2tb2 s1))
     (= (card bool (t2tb2 (add1 x s1))) (card bool (t2tb2 s1))))) :pattern ((mem
  (set1 bool) (t2tb2 s1) (finite_subsets bool (t2tb2 s2)))
  (card bool (t2tb2 (add1 x s1)))) )))

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

(declare-fun times2 ((set (tuple2 (tuple2 Bool Bool) Bool))
  (set Bool)) (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))

(declare-fun times3 ((set (tuple2 Bool Bool))
  (set Bool)) (set (tuple2 (tuple2 Bool Bool) Bool)))

(declare-fun times4 ((set Bool) (set Bool)) (set (tuple2 Bool Bool)))

(declare-fun times5 ((set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (set (set uninterpreted_type1))) (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1))))

;; times_def
  (assert
  (forall ((a (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (b (set (set uninterpreted_type1))) (x (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool)) (y (set uninterpreted_type1)))
  (! (= (mem
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type))
     (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type) (t2tb9 x) (t2tb205 y)) (t2tb202 (times5 a b)))
     (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
     (t2tb5 a)) (mem (set1 uninterpreted_type) (t2tb205 y) (t2tb204 b)))) :pattern ((mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type) (t2tb9 x) (t2tb205 y))
  (t2tb202 (times5 a b)))) )))

;; times_def
  (assert
  (forall ((a (set (tuple2 (tuple2 Bool Bool) Bool))) (b (set Bool))
  (x (tuple2 (tuple2 Bool Bool) Bool)) (y Bool))
  (! (= (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (Tuple2 (tuple21 (tuple21 bool bool) bool) bool (t2tb10 x) (t2tb12 y))
     (t2tb5 (times2 a b)))
     (and (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb6 a)) (mem
     bool (t2tb12 y) (t2tb2 b)))) :pattern ((mem
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (Tuple2 (tuple21 (tuple21 bool bool) bool) bool (t2tb10 x) (t2tb12 y))
  (t2tb5 (times2 a b)))) )))

;; times_def
  (assert
  (forall ((a (set (tuple2 Bool Bool))) (b (set Bool)) (x (tuple2 Bool Bool))
  (y Bool))
  (! (= (mem (tuple21 (tuple21 bool bool) bool)
     (Tuple2 (tuple21 bool bool) bool (t2tb11 x) (t2tb12 y))
     (t2tb6 (times3 a b)))
     (and (mem (tuple21 bool bool) (t2tb11 x) (t2tb7 a)) (mem bool (t2tb12 y)
     (t2tb2 b)))) :pattern ((mem
  (tuple21 (tuple21 bool bool) bool)
  (Tuple2 (tuple21 bool bool) bool (t2tb11 x) (t2tb12 y))
  (t2tb6 (times3 a b)))) )))

;; times_def
  (assert
  (forall ((a (set Bool)) (b (set Bool)) (x Bool) (y Bool))
  (! (= (mem (tuple21 bool bool) (Tuple2 bool bool (t2tb12 x) (t2tb12 y))
     (t2tb7 (times4 a b)))
     (and (mem bool (t2tb12 x) (t2tb2 a)) (mem bool (t2tb12 y) (t2tb2 b)))) :pattern ((mem
  (tuple21 bool bool) (Tuple2 bool bool (t2tb12 x) (t2tb12 y))
  (t2tb7 (times4 a b)))) )))

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
  (v (set (set uninterpreted_type1))))
  (= (tb2t207
     (relations (set1 uninterpreted_type)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb5 u) (t2tb204 v))) 
  (tb2t207
  (power
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb202 (times5 u v)))))))

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
  (set uninterpreted_type1)))) (u (set (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool))) (v (set (set uninterpreted_type1))))
  (= (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))) (t2tb202 r)
  (power
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb202 (times5 u v)))) (subset
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb202 r) (t2tb202 (times5 u v))))))

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
  (forall ((r (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))) (u (set (tuple2 (tuple2 (tuple2 Bool Bool)
  Bool) Bool))) (v (set (set uninterpreted_type1))))
  (= (subset
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb202 r) (t2tb202 (times5 u v)))
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (y (set uninterpreted_type1)))
  (=> (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type) (t2tb9 x) (t2tb205 y)) (t2tb202 r))
  (and (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
  (t2tb5 u)) (mem (set1 uninterpreted_type) (t2tb205 y) (t2tb204 v))))))))

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
  (and (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb6 u)) (mem
  bool (t2tb12 y) (t2tb2 v))))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 (tuple2 Bool Bool) Bool))) (u (set (tuple2 Bool
  Bool))) (v (set Bool)))
  (= (subset (tuple21 (tuple21 bool bool) bool) (t2tb6 r)
  (t2tb6 (times3 u v)))
  (forall ((x (tuple2 Bool Bool)) (y Bool))
  (=> (mem (tuple21 (tuple21 bool bool) bool)
  (Tuple2 (tuple21 bool bool) bool (t2tb11 x) (t2tb12 y)) (t2tb6 r))
  (and (mem (tuple21 bool bool) (t2tb11 x) (t2tb7 u)) (mem bool (t2tb12 y)
  (t2tb2 v))))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 Bool Bool))) (u (set Bool)) (v (set Bool)))
  (= (subset (tuple21 bool bool) (t2tb7 r) (t2tb7 (times4 u v)))
  (forall ((x Bool) (y Bool))
  (=> (mem (tuple21 bool bool) (Tuple2 bool bool (t2tb12 x) (t2tb12 y))
  (t2tb7 r))
  (and (mem bool (t2tb12 x) (t2tb2 u)) (mem bool (t2tb12 y) (t2tb2 v))))))))

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
  Bool) Bool) (set uninterpreted_type1))))
  (! (=> (mem a x s)
     (= (tb2t203
        (apply
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 uninterpreted_type)) a
        (times
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 uninterpreted_type)) a s
        (add
        (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (set1 uninterpreted_type)) (t2tb203 y) (t2tb202 empty10))) x)) y)) :pattern (
  (tb2t203
  (apply
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) a
  (times
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) a s
  (add
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type)) (t2tb203 y) (t2tb202 empty10))) x))) ))))

;; apply_times
  (assert
  (forall ((a ty))
  (forall ((s uni) (x uni) (y (set uninterpreted_type1)))
  (! (=> (mem a x s)
     (= (tb2t205
        (apply (set1 uninterpreted_type) a
        (times (set1 uninterpreted_type) a s (t2tb204 (add5 y empty11))) x)) y)) :pattern (
  (tb2t205
  (apply (set1 uninterpreted_type) a
  (times (set1 uninterpreted_type) a s (t2tb204 (add5 y empty11))) x))) ))))

;; apply_times
  (assert
  (forall ((a ty))
  (forall ((s uni) (x uni) (y uninterpreted_type1))
  (! (=> (mem a x s)
     (= (tb2t206
        (apply uninterpreted_type a
        (times uninterpreted_type a s
        (add uninterpreted_type (t2tb206 y) (t2tb205 empty9))) x)) y)) :pattern (
  (tb2t206
  (apply uninterpreted_type a
  (times uninterpreted_type a s
  (add uninterpreted_type (t2tb206 y) (t2tb205 empty9))) x))) ))))

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
  (forall ((s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (y (set uninterpreted_type1)))
  (! (=> (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
     (t2tb5 s))
     (= (tb2t205
        (apply (set1 uninterpreted_type)
        (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (t2tb202 (times5 s (add5 y empty11))) (t2tb9 x))) y)) :pattern (
  (tb2t205
  (apply (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb202 (times5 s (add5 y empty11))) (t2tb9 x)))) )))

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
  (forall ((s (set Bool)) (x Bool) (y Bool))
  (! (=> (mem bool (t2tb12 x) (t2tb2 s))
     (= (tb2t12
        (apply bool bool (t2tb7 (times4 s (add1 y empty1))) (t2tb12 x))) y)) :pattern (
  (tb2t12 (apply bool bool (t2tb7 (times4 s (add1 y empty1))) (t2tb12 x)))) )))

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
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))
  (y (set uninterpreted_type1)) (q (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1))))
  (r (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))))
  (= (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type) (t2tb9 x) (t2tb205 y))
  (infix_lspl (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb202 q) (t2tb202 r)))
  (ite (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
  (t2tb5 (dom3 r))) (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type) (t2tb9 x) (t2tb205 y)) (t2tb202 r)) (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type) (t2tb9 x) (t2tb205 y)) (t2tb202 q))))))

;; overriding_def
  (assert
  (forall ((x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)) (y (set Int))
  (q (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool) (set Int))))
  (r (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))
  (= (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb9 x) (t2tb3 y))
  (infix_lspl (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb4 q) (t2tb4 r)))
  (ite (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
  (t2tb5 (dom2 r))) (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb9 x) (t2tb3 y)) (t2tb4 r)) (mem
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int))
  (Tuple2 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)
  (t2tb9 x) (t2tb3 y)) (t2tb4 q))))))

;; overriding_def
  (assert
  (forall ((x (tuple2 (tuple2 Bool Bool) Bool)) (y Bool)
  (q (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (r (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (= (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (Tuple2 (tuple21 (tuple21 bool bool) bool) bool (t2tb10 x) (t2tb12 y))
  (infix_lspl bool (tuple21 (tuple21 bool bool) bool) (t2tb5 q) (t2tb5 r)))
  (ite (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb6 (dom4 r)))
  (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (Tuple2 (tuple21 (tuple21 bool bool) bool) bool (t2tb10 x) (t2tb12 y))
  (t2tb5 r)) (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (Tuple2 (tuple21 (tuple21 bool bool) bool) bool (t2tb10 x) (t2tb12 y))
  (t2tb5 q))))))

;; overriding_def
  (assert
  (forall ((x (tuple2 Bool Bool)) (y Bool) (q (set (tuple2 (tuple2 Bool Bool)
  Bool))) (r (set (tuple2 (tuple2 Bool Bool) Bool))))
  (= (mem (tuple21 (tuple21 bool bool) bool)
  (Tuple2 (tuple21 bool bool) bool (t2tb11 x) (t2tb12 y))
  (infix_lspl bool (tuple21 bool bool) (t2tb6 q) (t2tb6 r)))
  (ite (mem (tuple21 bool bool) (t2tb11 x) (t2tb7 (dom5 r))) (mem
  (tuple21 (tuple21 bool bool) bool)
  (Tuple2 (tuple21 bool bool) bool (t2tb11 x) (t2tb12 y)) (t2tb6 r)) (mem
  (tuple21 (tuple21 bool bool) bool)
  (Tuple2 (tuple21 bool bool) bool (t2tb11 x) (t2tb12 y)) (t2tb6 q))))))

;; overriding_def
  (assert
  (forall ((x Bool) (y Bool) (q (set (tuple2 Bool Bool)))
  (r (set (tuple2 Bool Bool))))
  (= (mem (tuple21 bool bool) (Tuple2 bool bool (t2tb12 x) (t2tb12 y))
  (infix_lspl bool bool (t2tb7 q) (t2tb7 r)))
  (ite (mem bool (t2tb12 x) (t2tb2 (dom1 r))) (mem (tuple21 bool bool)
  (Tuple2 bool bool (t2tb12 x) (t2tb12 y)) (t2tb7 r)) (mem
  (tuple21 bool bool) (Tuple2 bool bool (t2tb12 x) (t2tb12 y)) (t2tb7 q))))))

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
  (forall ((f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))) (g (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1)))))
  (! (= (dom3
        (tb2t202
        (infix_lspl (set1 uninterpreted_type)
        (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb202 f)
        (t2tb202 g)))) (tb2t5
                       (union
                       (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
                       (t2tb5 (dom3 f)) (t2tb5 (dom3 g))))) :pattern (
  (dom3
  (tb2t202
  (infix_lspl (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb202 f) (t2tb202 g))))) )))

;; dom_overriding
  (assert
  (forall ((f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))) (g (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set Int)))))
  (! (= (dom2
        (tb2t4
        (infix_lspl (set1 int)
        (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb4 f)
        (t2tb4 g)))) (tb2t5
                     (union (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
                     (t2tb5 (dom2 f)) (t2tb5 (dom2 g))))) :pattern ((dom2
                                                                    (tb2t4
                                                                    (infix_lspl
                                                                    (set1
                                                                    int)
                                                                    (tuple21
                                                                    (tuple21
                                                                    (tuple21
                                                                    bool
                                                                    bool)
                                                                    bool)
                                                                    bool)
                                                                    (t2tb4 f)
                                                                    (t2tb4 g))))) )))

;; dom_overriding
  (assert
  (forall ((f (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (g (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool))))
  (! (= (dom4
        (tb2t5
        (infix_lspl bool (tuple21 (tuple21 bool bool) bool) (t2tb5 f)
        (t2tb5 g)))) (tb2t6
                     (union (tuple21 (tuple21 bool bool) bool)
                     (t2tb6 (dom4 f)) (t2tb6 (dom4 g))))) :pattern ((dom4
                                                                    (tb2t5
                                                                    (infix_lspl
                                                                    bool
                                                                    (tuple21
                                                                    (tuple21
                                                                    bool
                                                                    bool)
                                                                    bool)
                                                                    (t2tb5 f)
                                                                    (t2tb5 g))))) )))

;; dom_overriding
  (assert
  (forall ((f (set (tuple2 (tuple2 Bool Bool) Bool)))
  (g (set (tuple2 (tuple2 Bool Bool) Bool))))
  (! (= (dom5
        (tb2t6 (infix_lspl bool (tuple21 bool bool) (t2tb6 f) (t2tb6 g)))) 
  (tb2t7 (union (tuple21 bool bool) (t2tb7 (dom5 f)) (t2tb7 (dom5 g))))) :pattern (
  (dom5 (tb2t6 (infix_lspl bool (tuple21 bool bool) (t2tb6 f) (t2tb6 g))))) )))

;; dom_overriding
  (assert
  (forall ((f (set (tuple2 Bool Bool))) (g (set (tuple2 Bool Bool))))
  (! (= (dom1 (tb2t7 (infix_lspl bool bool (t2tb7 f) (t2tb7 g)))) (tb2t2
                                                                  (union 
                                                                  bool
                                                                  (t2tb2
                                                                  (dom1 f))
                                                                  (t2tb2
                                                                  (dom1 g))))) :pattern (
  (dom1 (tb2t7 (infix_lspl bool bool (t2tb7 f) (t2tb7 g))))) )))

;; dom_overriding
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (g uni))
  (! (= (dom b a (infix_lspl b a f g)) (union a (dom b a f) (dom b a g))) :pattern (
  (dom b a (infix_lspl b a f g))) ))))

;; apply_overriding_1
  (assert
  (forall ((s (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (t (set (set uninterpreted_type1)))
  (f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))) (g (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1))))
  (x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (! (=>
     (and (mem
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type))) (t2tb202 f)
     (infix_plmngt (set1 uninterpreted_type)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb5 s) (t2tb204 t)))
     (mem
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type))) (t2tb202 g)
     (infix_plmngt (set1 uninterpreted_type)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb5 s) (t2tb204 t))))
     (=> (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
     (t2tb5 (dom3 g)))
     (= (tb2t205
        (apply (set1 uninterpreted_type)
        (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (infix_lspl (set1 uninterpreted_type)
        (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb202 f)
        (t2tb202 g)) (t2tb9 x))) (tb2t205
                                 (apply (set1 uninterpreted_type)
                                 (tuple21 (tuple21 (tuple21 bool bool) bool)
                                 bool) (t2tb202 g) (t2tb9 x)))))) :pattern ((mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))) (t2tb202 f)
  (infix_plmngt (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb5 s) (t2tb204 t)))
  (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))) (t2tb202 g)
  (infix_plmngt (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb5 s) (t2tb204 t)))
  (tb2t205
  (apply (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (infix_lspl (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb202 f) (t2tb202 g))
  (t2tb9 x)))) )))

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
     (t2tb4 f)
     (infix_plmngt (set1 int)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb5 s) (t2tb1 t)))
     (mem
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb4 g)
     (infix_plmngt (set1 int)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb5 s) (t2tb1 t))))
     (=> (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
     (t2tb5 (dom2 g)))
     (= (tb2t3
        (apply (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (infix_lspl (set1 int)
        (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb4 f)
        (t2tb4 g)) (t2tb9 x))) (tb2t3
                               (apply (set1 int)
                               (tuple21 (tuple21 (tuple21 bool bool) bool)
                               bool) (t2tb4 g) (t2tb9 x)))))) :pattern ((mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb4 f)
  (infix_plmngt (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 s) (t2tb1 t))) (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb4 g)
  (infix_plmngt (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 s) (t2tb1 t)))
  (tb2t3
  (apply (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (infix_lspl (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb4 f) (t2tb4 g)) (t2tb9 x)))) )))

;; apply_overriding_1
  (assert
  (forall ((s (set (tuple2 (tuple2 Bool Bool) Bool))) (t (set Bool))
  (f (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (g (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (x (tuple2 (tuple2 Bool Bool) Bool)))
  (! (=>
     (and (mem (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
     (t2tb5 f)
     (infix_plmngt bool (tuple21 (tuple21 bool bool) bool) (t2tb6 s)
     (t2tb2 t))) (mem
     (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb5 g)
     (infix_plmngt bool (tuple21 (tuple21 bool bool) bool) (t2tb6 s)
     (t2tb2 t))))
     (=> (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb6 (dom4 g)))
     (= (tb2t12
        (apply bool (tuple21 (tuple21 bool bool) bool)
        (infix_lspl bool (tuple21 (tuple21 bool bool) bool) (t2tb5 f)
        (t2tb5 g)) (t2tb10 x))) (tb2t12
                                (apply bool
                                (tuple21 (tuple21 bool bool) bool) (t2tb5 g)
                                (t2tb10 x)))))) :pattern ((mem
  (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb5 f)
  (infix_plmngt bool (tuple21 (tuple21 bool bool) bool) (t2tb6 s) (t2tb2 t)))
  (mem (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb5 g)
  (infix_plmngt bool (tuple21 (tuple21 bool bool) bool) (t2tb6 s) (t2tb2 t)))
  (tb2t12
  (apply bool (tuple21 (tuple21 bool bool) bool)
  (infix_lspl bool (tuple21 (tuple21 bool bool) bool) (t2tb5 f) (t2tb5 g))
  (t2tb10 x)))) )))

;; apply_overriding_1
  (assert
  (forall ((s (set (tuple2 Bool Bool))) (t (set Bool))
  (f (set (tuple2 (tuple2 Bool Bool) Bool))) (g (set (tuple2 (tuple2 Bool
  Bool) Bool))) (x (tuple2 Bool Bool)))
  (! (=>
     (and (mem (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb6 f)
     (infix_plmngt bool (tuple21 bool bool) (t2tb7 s) (t2tb2 t))) (mem
     (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb6 g)
     (infix_plmngt bool (tuple21 bool bool) (t2tb7 s) (t2tb2 t))))
     (=> (mem (tuple21 bool bool) (t2tb11 x) (t2tb7 (dom5 g)))
     (= (tb2t12
        (apply bool (tuple21 bool bool)
        (infix_lspl bool (tuple21 bool bool) (t2tb6 f) (t2tb6 g)) (t2tb11 x))) 
     (tb2t12 (apply bool (tuple21 bool bool) (t2tb6 g) (t2tb11 x)))))) :pattern ((mem
  (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb6 f)
  (infix_plmngt bool (tuple21 bool bool) (t2tb7 s) (t2tb2 t))) (mem
  (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb6 g)
  (infix_plmngt bool (tuple21 bool bool) (t2tb7 s) (t2tb2 t)))
  (tb2t12
  (apply bool (tuple21 bool bool)
  (infix_lspl bool (tuple21 bool bool) (t2tb6 f) (t2tb6 g)) (t2tb11 x)))) )))

;; apply_overriding_1
  (assert
  (forall ((s (set Bool)) (t (set Bool)) (f (set (tuple2 Bool Bool)))
  (g (set (tuple2 Bool Bool))) (x Bool))
  (! (=>
     (and (mem (set1 (tuple21 bool bool)) (t2tb7 f)
     (infix_plmngt bool bool (t2tb2 s) (t2tb2 t))) (mem
     (set1 (tuple21 bool bool)) (t2tb7 g)
     (infix_plmngt bool bool (t2tb2 s) (t2tb2 t))))
     (=> (mem bool (t2tb12 x) (t2tb2 (dom1 g)))
     (= (tb2t12
        (apply bool bool (infix_lspl bool bool (t2tb7 f) (t2tb7 g))
        (t2tb12 x))) (tb2t12 (apply bool bool (t2tb7 g) (t2tb12 x)))))) :pattern ((mem
  (set1 (tuple21 bool bool)) (t2tb7 f)
  (infix_plmngt bool bool (t2tb2 s) (t2tb2 t))) (mem
  (set1 (tuple21 bool bool)) (t2tb7 g)
  (infix_plmngt bool bool (t2tb2 s) (t2tb2 t)))
  (tb2t12
  (apply bool bool (infix_lspl bool bool (t2tb7 f) (t2tb7 g)) (t2tb12 x)))) )))

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
  (t (set (set uninterpreted_type1)))
  (f (set (tuple2 (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)
  (set uninterpreted_type1)))) (g (set (tuple2 (tuple2 (tuple2 (tuple2 Bool
  Bool) Bool) Bool) (set uninterpreted_type1))))
  (x (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (! (=>
     (and (mem
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type))) (t2tb202 f)
     (infix_plmngt (set1 uninterpreted_type)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb5 s) (t2tb204 t)))
     (mem
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
     (set1 uninterpreted_type))) (t2tb202 g)
     (infix_plmngt (set1 uninterpreted_type)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb5 s) (t2tb204 t))))
     (=>
     (not (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
     (t2tb5 (dom3 g))))
     (=> (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
     (t2tb5 (dom3 f)))
     (= (tb2t205
        (apply (set1 uninterpreted_type)
        (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (infix_lspl (set1 uninterpreted_type)
        (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb202 f)
        (t2tb202 g)) (t2tb9 x))) (tb2t205
                                 (apply (set1 uninterpreted_type)
                                 (tuple21 (tuple21 (tuple21 bool bool) bool)
                                 bool) (t2tb202 f) (t2tb9 x))))))) :pattern ((mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))) (t2tb202 f)
  (infix_plmngt (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb5 s) (t2tb204 t)))
  (tb2t205
  (apply (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (infix_lspl (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb202 f) (t2tb202 g))
  (t2tb9 x)))) :pattern ((mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (set1 uninterpreted_type))) (t2tb202 g)
  (infix_plmngt (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb5 s) (t2tb204 t)))
  (tb2t205
  (apply (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (infix_lspl (set1 uninterpreted_type)
  (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb202 f) (t2tb202 g))
  (t2tb9 x)))) )))

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
     (t2tb4 f)
     (infix_plmngt (set1 int)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb5 s) (t2tb1 t)))
     (mem
     (set1
     (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
     (t2tb4 g)
     (infix_plmngt (set1 int)
     (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb5 s) (t2tb1 t))))
     (=>
     (not (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
     (t2tb5 (dom2 g))))
     (=> (mem (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb9 x)
     (t2tb5 (dom2 f)))
     (= (tb2t3
        (apply (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
        (infix_lspl (set1 int)
        (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (t2tb4 f)
        (t2tb4 g)) (t2tb9 x))) (tb2t3
                               (apply (set1 int)
                               (tuple21 (tuple21 (tuple21 bool bool) bool)
                               bool) (t2tb4 f) (t2tb9 x))))))) :pattern ((mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb4 f)
  (infix_plmngt (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 s) (t2tb1 t)))
  (tb2t3
  (apply (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (infix_lspl (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb4 f) (t2tb4 g)) (t2tb9 x)))) :pattern ((mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb4 g)
  (infix_plmngt (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 s) (t2tb1 t)))
  (tb2t3
  (apply (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (infix_lspl (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb4 f) (t2tb4 g)) (t2tb9 x)))) )))

;; apply_overriding_2
  (assert
  (forall ((s (set (tuple2 (tuple2 Bool Bool) Bool))) (t (set Bool))
  (f (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (g (set (tuple2 (tuple2 (tuple2 Bool Bool) Bool) Bool)))
  (x (tuple2 (tuple2 Bool Bool) Bool)))
  (! (=>
     (and (mem (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool))
     (t2tb5 f)
     (infix_plmngt bool (tuple21 (tuple21 bool bool) bool) (t2tb6 s)
     (t2tb2 t))) (mem
     (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb5 g)
     (infix_plmngt bool (tuple21 (tuple21 bool bool) bool) (t2tb6 s)
     (t2tb2 t))))
     (=>
     (not (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x)
     (t2tb6 (dom4 g))))
     (=> (mem (tuple21 (tuple21 bool bool) bool) (t2tb10 x) (t2tb6 (dom4 f)))
     (= (tb2t12
        (apply bool (tuple21 (tuple21 bool bool) bool)
        (infix_lspl bool (tuple21 (tuple21 bool bool) bool) (t2tb5 f)
        (t2tb5 g)) (t2tb10 x))) (tb2t12
                                (apply bool
                                (tuple21 (tuple21 bool bool) bool) (t2tb5 f)
                                (t2tb10 x))))))) :pattern ((mem
  (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb5 f)
  (infix_plmngt bool (tuple21 (tuple21 bool bool) bool) (t2tb6 s) (t2tb2 t)))
  (tb2t12
  (apply bool (tuple21 (tuple21 bool bool) bool)
  (infix_lspl bool (tuple21 (tuple21 bool bool) bool) (t2tb5 f) (t2tb5 g))
  (t2tb10 x)))) :pattern ((mem
  (set1 (tuple21 (tuple21 (tuple21 bool bool) bool) bool)) (t2tb5 g)
  (infix_plmngt bool (tuple21 (tuple21 bool bool) bool) (t2tb6 s) (t2tb2 t)))
  (tb2t12
  (apply bool (tuple21 (tuple21 bool bool) bool)
  (infix_lspl bool (tuple21 (tuple21 bool bool) bool) (t2tb5 f) (t2tb5 g))
  (t2tb10 x)))) )))

;; apply_overriding_2
  (assert
  (forall ((s (set (tuple2 Bool Bool))) (t (set Bool))
  (f (set (tuple2 (tuple2 Bool Bool) Bool))) (g (set (tuple2 (tuple2 Bool
  Bool) Bool))) (x (tuple2 Bool Bool)))
  (! (=>
     (and (mem (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb6 f)
     (infix_plmngt bool (tuple21 bool bool) (t2tb7 s) (t2tb2 t))) (mem
     (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb6 g)
     (infix_plmngt bool (tuple21 bool bool) (t2tb7 s) (t2tb2 t))))
     (=> (not (mem (tuple21 bool bool) (t2tb11 x) (t2tb7 (dom5 g))))
     (=> (mem (tuple21 bool bool) (t2tb11 x) (t2tb7 (dom5 f)))
     (= (tb2t12
        (apply bool (tuple21 bool bool)
        (infix_lspl bool (tuple21 bool bool) (t2tb6 f) (t2tb6 g)) (t2tb11 x))) 
     (tb2t12 (apply bool (tuple21 bool bool) (t2tb6 f) (t2tb11 x))))))) :pattern ((mem
  (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb6 f)
  (infix_plmngt bool (tuple21 bool bool) (t2tb7 s) (t2tb2 t)))
  (tb2t12
  (apply bool (tuple21 bool bool)
  (infix_lspl bool (tuple21 bool bool) (t2tb6 f) (t2tb6 g)) (t2tb11 x)))) :pattern ((mem
  (set1 (tuple21 (tuple21 bool bool) bool)) (t2tb6 g)
  (infix_plmngt bool (tuple21 bool bool) (t2tb7 s) (t2tb2 t)))
  (tb2t12
  (apply bool (tuple21 bool bool)
  (infix_lspl bool (tuple21 bool bool) (t2tb6 f) (t2tb6 g)) (t2tb11 x)))) )))

;; apply_overriding_2
  (assert
  (forall ((s (set Bool)) (t (set Bool)) (f (set (tuple2 Bool Bool)))
  (g (set (tuple2 Bool Bool))) (x Bool))
  (! (=>
     (and (mem (set1 (tuple21 bool bool)) (t2tb7 f)
     (infix_plmngt bool bool (t2tb2 s) (t2tb2 t))) (mem
     (set1 (tuple21 bool bool)) (t2tb7 g)
     (infix_plmngt bool bool (t2tb2 s) (t2tb2 t))))
     (=> (not (mem bool (t2tb12 x) (t2tb2 (dom1 g))))
     (=> (mem bool (t2tb12 x) (t2tb2 (dom1 f)))
     (= (tb2t12
        (apply bool bool (infix_lspl bool bool (t2tb7 f) (t2tb7 g))
        (t2tb12 x))) (tb2t12 (apply bool bool (t2tb7 f) (t2tb12 x))))))) :pattern ((mem
  (set1 (tuple21 bool bool)) (t2tb7 f)
  (infix_plmngt bool bool (t2tb2 s) (t2tb2 t)))
  (tb2t12
  (apply bool bool (infix_lspl bool bool (t2tb7 f) (t2tb7 g)) (t2tb12 x)))) :pattern ((mem
  (set1 (tuple21 bool bool)) (t2tb7 g)
  (infix_plmngt bool bool (t2tb2 s) (t2tb2 t)))
  (tb2t12
  (apply bool bool (infix_lspl bool bool (t2tb7 f) (t2tb7 g)) (t2tb12 x)))) )))

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
  (and
  (and (and (= v_tt 0) (= v_uu 1)) (mem int (t2tb13 v_vv) (t2tb3 integer)))
  (<= 0 v_vv)) (<= v_vv 2147483647)) (mem int (t2tb13 v_ww) (t2tb3 integer)))
  (<= 0 v_ww)) (<= v_ww 2147483647)) (mem int (t2tb13 v_xx) (t2tb3 integer)))
  (<= 0 v_xx)) (<= v_xx 2147483647)) (mem int (t2tb13 v_yy) (t2tb3 integer)))
  (<= 0 v_yy)) (<= v_yy 2147483647)) (<= 1 v_yy)) (<= v_yy 254))
  (= v_yy v_ww)) (mem int (t2tb13 v_zz) (t2tb3 integer))) (<= 0 v_zz))
  (<= v_zz 2147483647)) (<= 1 v_zz)) (<= v_zz 254)) (= v_zz v_ww)) (mem 
  int (t2tb13 v_bbaa) (t2tb3 integer))) (<= 0 v_bbaa))
  (<= v_bbaa 2147483647)) (<= 1 v_bbaa)) (<= (+ v_bbaa 1) 2147483647))
  (= v_bbaa v_xx)) (mem int (t2tb13 v_bbbb) (t2tb3 integer))) (<= 0 v_bbbb))
  (<= v_bbbb 2147483647)) (<= 2 v_bbbb)) (= v_bbbb v_vv))
  (<= (+ v_bbbb v_zz) 253)) (<= (+ (+ v_bbbb v_yy) v_zz) 251)) (mem int
  (t2tb13 v_bbcc) (t2tb3 integer))) (<= 0 v_bbcc)) (<= v_bbcc 2147483647))
  (<= 1 v_bbcc)) (<= (+ v_bbcc 1) 254)) (= v_bbcc v_vv)))))

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
  (and (and (mem int (t2tb13 v_oo) (t2tb3 integer)) (<= 0 v_oo)) (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
  (t2tb4 v_jj)
  (infix_plmngt (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 (times2 (times3 (times4 b_bool b_bool) b_bool) b_bool))
  (power int (t2tb3 natural))))) (infix_eqeq3 (dom2 v_jj)
  (times2 (times3 (times4 b_bool b_bool) b_bool) b_bool))))))

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
  v_mm v_ll v_kk v_jj v_bbcc v_bbbb v_bbaa) (mem int (t2tb13 (+ v_oo 1))
  (t2tb3 integer)))))

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
  v_mm v_ll v_kk v_jj v_bbcc v_bbbb v_bbaa) (mem
  (set1
  (tuple21 (tuple21 (tuple21 (tuple21 bool bool) bool) bool) (set1 int)))
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
  (t2tb12 v_nn))) (add int (t2tb13 (+ v_oo 1)) (empty int)))) (t2tb4 empty4)))
  (infix_plmngt (set1 int) (tuple21 (tuple21 (tuple21 bool bool) bool) bool)
  (t2tb5 (times2 (times3 (times4 b_bool b_bool) b_bool) b_bool))
  (power int (t2tb3 natural)))))))

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
  v_mm v_ll v_kk v_jj v_bbcc v_bbbb v_bbaa) (infix_eqeq3
  (dom2
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
  (t2tb12 v_nn))) (add int (t2tb13 (+ v_oo 1)) (empty int)))) (t2tb4 empty4)))))
  (times2 (times3 (times4 b_bool b_bool) b_bool) b_bool)))))

(assert
;; bbdd_2
 ;; File "POwhy_bpo2why/p4/p4_34.why", line 195, characters 7-13
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
  v_bbaa)) (infix_eqeq3
  (dom3
  (times5 (times2 (times3 (times4 b_bool b_bool) b_bool) b_bool)
  (add5 empty9 empty11)))
  (times2 (times3 (times4 b_bool b_bool) b_bool) b_bool))))))
(check-sat)
