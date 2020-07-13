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

(declare-sort enum_t_AUTOMATON_STATE 0)

(declare-fun enum_t_AUTOMATON_STATE1 () ty)

(declare-sort tuple2 2)

(declare-fun tuple21 (ty ty) ty)

(declare-fun mem (ty uni uni) Bool)

(declare-fun mem1 (enum_t_AUTOMATON_STATE (set enum_t_AUTOMATON_STATE)) Bool)

(declare-fun mem2 ((tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)
  (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))) Bool)

(declare-fun mem3 ((set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) Bool)

(declare-fun infix_eqeq (ty uni uni) Bool)

(declare-fun t2tb ((set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))) (sort
  (set1 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (t2tb x))))

(declare-fun tb2t (uni) (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))) (! (= (tb2t (t2tb i)) i) :pattern ((t2tb i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
     j) (= (t2tb (tb2t j)) j)) :pattern ((t2tb (tb2t j))) )))

;; infix ==_def
  (assert
  (forall ((s1 (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (s2 (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))))
  (= (infix_eqeq
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s1)
  (t2tb s2))
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (= (mem3 x s1) (mem3 x s2))))))

(declare-fun t2tb1 ((set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (sort (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (t2tb1 x))))

(declare-fun tb2t1 (uni) (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (! (= (tb2t1 (t2tb1 i)) i) :pattern ((t2tb1 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) j)
     (= (t2tb1 (tb2t1 j)) j)) :pattern ((t2tb1 (tb2t1 j))) )))

;; infix ==_def
  (assert
  (forall ((s1 (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s2 (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (= (infix_eqeq (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 s1) (t2tb1 s2))
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (= (mem2 x s1) (mem2 x s2))))))

(declare-fun t2tb2 ((set enum_t_AUTOMATON_STATE)) uni)

;; t2tb_sort
  (assert
  (forall ((x (set enum_t_AUTOMATON_STATE))) (sort
  (set1 enum_t_AUTOMATON_STATE1) (t2tb2 x))))

(declare-fun tb2t2 (uni) (set enum_t_AUTOMATON_STATE))

;; BridgeL
  (assert
  (forall ((i (set enum_t_AUTOMATON_STATE)))
  (! (= (tb2t2 (t2tb2 i)) i) :pattern ((t2tb2 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 enum_t_AUTOMATON_STATE1) j) (= (t2tb2 (tb2t2 j)) j)) :pattern (
  (t2tb2 (tb2t2 j))) )))

;; infix ==_def
  (assert
  (forall ((s1 (set enum_t_AUTOMATON_STATE))
  (s2 (set enum_t_AUTOMATON_STATE)))
  (= (infix_eqeq enum_t_AUTOMATON_STATE1 (t2tb2 s1) (t2tb2 s2))
  (forall ((x enum_t_AUTOMATON_STATE)) (= (mem1 x s1) (mem1 x s2))))))

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
  (forall ((s1 (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (s2 (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))))
  (= (subset (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (t2tb s1) (t2tb s2))
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (=> (mem3 x s1) (mem3 x s2))))))

;; subset_def
  (assert
  (forall ((s1 (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s2 (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (= (subset (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 s1) (t2tb1 s2))
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (=> (mem2 x s1) (mem2 x s2))))))

;; subset_def
  (assert
  (forall ((s1 (set enum_t_AUTOMATON_STATE))
  (s2 (set enum_t_AUTOMATON_STATE)))
  (= (subset enum_t_AUTOMATON_STATE1 (t2tb2 s1) (t2tb2 s2))
  (forall ((x enum_t_AUTOMATON_STATE)) (=> (mem1 x s1) (mem1 x s2))))))

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

(declare-fun empty1 () (set enum_t_AUTOMATON_STATE))

(declare-fun empty2 () (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))

(declare-fun empty3 () (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))

(declare-fun is_empty (ty uni) Bool)

;; is_empty_def
  (assert
  (forall ((s (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))))
  (= (is_empty
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s))
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (not (mem3 x s))))))

;; is_empty_def
  (assert
  (forall ((s (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (= (is_empty (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 s))
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (not (mem2 x s))))))

;; is_empty_def
  (assert
  (forall ((s (set enum_t_AUTOMATON_STATE)))
  (= (is_empty enum_t_AUTOMATON_STATE1 (t2tb2 s))
  (forall ((x enum_t_AUTOMATON_STATE)) (not (mem1 x s))))))

;; is_empty_def
  (assert
  (forall ((a ty))
  (forall ((s uni))
  (and (=> (is_empty a s) (forall ((x uni)) (not (mem a x s))))
  (=> (forall ((x uni)) (=> (sort a x) (not (mem a x s)))) (is_empty a s))))))

;; empty_def1
  (assert (is_empty
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (t2tb empty3)))

;; empty_def1
  (assert (is_empty (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 empty2)))

;; empty_def1
  (assert (is_empty enum_t_AUTOMATON_STATE1 (t2tb2 empty1)))

;; empty_def1
  (assert (forall ((a ty)) (is_empty a (empty a))))

;; mem_empty
  (assert
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (not (mem3 x empty3))))

;; mem_empty
  (assert
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (not (mem2 x empty2))))

;; mem_empty
  (assert (forall ((x enum_t_AUTOMATON_STATE)) (not (mem1 x empty1))))

;; mem_empty
  (assert (forall ((a ty)) (forall ((x uni)) (not (mem a x (empty a))))))

(declare-fun add (ty uni uni) uni)

;; add_sort
  (assert
  (forall ((a ty)) (forall ((x uni) (x1 uni)) (sort (set1 a) (add a x x1)))))

(declare-fun add1 (enum_t_AUTOMATON_STATE
  (set enum_t_AUTOMATON_STATE)) (set enum_t_AUTOMATON_STATE))

(declare-fun add2 ((tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)
  (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))

(declare-fun add3 ((set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))

;; add_def1
  (assert
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (y (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (forall ((s (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))))
  (= (mem3 x (add3 y s)) (or (= x y) (mem3 x s))))))

;; add_def1
  (assert
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (y (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (forall ((s (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (= (mem2 x (add2 y s)) (or (= x y) (mem2 x s))))))

;; add_def1
  (assert
  (forall ((x enum_t_AUTOMATON_STATE) (y enum_t_AUTOMATON_STATE))
  (forall ((s (set enum_t_AUTOMATON_STATE)))
  (= (mem1 x (add1 y s)) (or (= x y) (mem1 x s))))))

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
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (y (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))))
  (= (mem3 x
  (tb2t
  (remove (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (t2tb1 y) (t2tb s)))) (and (not (= x y)) (mem3 x s)))))

(declare-fun t2tb3 ((tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))) (sort
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb3 x))))

(declare-fun tb2t3 (uni) (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))

;; BridgeL
  (assert
  (forall ((i (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (! (= (tb2t3 (t2tb3 i)) i) :pattern ((t2tb3 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) j)
     (= (t2tb3 (tb2t3 j)) j)) :pattern ((t2tb3 (tb2t3 j))) )))

;; remove_def1
  (assert
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (y (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (s (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (= (mem2 x
  (tb2t1
  (remove (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb3 y)
  (t2tb1 s)))) (and (not (= x y)) (mem2 x s)))))

(declare-fun t2tb4 (enum_t_AUTOMATON_STATE) uni)

;; t2tb_sort
  (assert
  (forall ((x enum_t_AUTOMATON_STATE)) (sort enum_t_AUTOMATON_STATE1
  (t2tb4 x))))

(declare-fun tb2t4 (uni) enum_t_AUTOMATON_STATE)

;; BridgeL
  (assert
  (forall ((i enum_t_AUTOMATON_STATE))
  (! (= (tb2t4 (t2tb4 i)) i) :pattern ((t2tb4 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort enum_t_AUTOMATON_STATE1 j) (= (t2tb4 (tb2t4 j)) j)) :pattern (
  (t2tb4 (tb2t4 j))) )))

;; remove_def1
  (assert
  (forall ((x enum_t_AUTOMATON_STATE) (y enum_t_AUTOMATON_STATE)
  (s (set enum_t_AUTOMATON_STATE)))
  (= (mem1 x (tb2t2 (remove enum_t_AUTOMATON_STATE1 (t2tb4 y) (t2tb2 s))))
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
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))))
  (=> (mem3 x s)
  (= (add3 x
     (tb2t
     (remove (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb1 x) (t2tb s)))) s))))

;; add_remove
  (assert
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (s (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (=> (mem2 x s)
  (= (add2 x
     (tb2t1
     (remove (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (t2tb3 x) (t2tb1 s)))) s))))

;; add_remove
  (assert
  (forall ((x enum_t_AUTOMATON_STATE) (s (set enum_t_AUTOMATON_STATE)))
  (=> (mem1 x s)
  (= (add1 x (tb2t2 (remove enum_t_AUTOMATON_STATE1 (t2tb4 x) (t2tb2 s)))) s))))

;; add_remove
  (assert
  (forall ((a ty))
  (forall ((x uni) (s uni))
  (=> (sort (set1 a) s) (=> (mem a x s) (= (add a x (remove a x s)) s))))))

;; remove_add
  (assert
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))))
  (= (tb2t
     (remove (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb1 x) (t2tb (add3 x s)))) (tb2t
                                   (remove
                                   (set1
                                   (tuple21 enum_t_AUTOMATON_STATE1
                                   enum_t_AUTOMATON_STATE1)) (t2tb1 x)
                                   (t2tb s))))))

;; remove_add
  (assert
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (s (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (= (tb2t1
     (remove (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (t2tb3 x) (t2tb1 (add2 x s)))) (tb2t1
                                    (remove
                                    (tuple21 enum_t_AUTOMATON_STATE1
                                    enum_t_AUTOMATON_STATE1) (t2tb3 x)
                                    (t2tb1 s))))))

;; remove_add
  (assert
  (forall ((x enum_t_AUTOMATON_STATE) (s (set enum_t_AUTOMATON_STATE)))
  (= (tb2t2 (remove enum_t_AUTOMATON_STATE1 (t2tb4 x) (t2tb2 (add1 x s)))) 
  (tb2t2 (remove enum_t_AUTOMATON_STATE1 (t2tb4 x) (t2tb2 s))))))

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

(declare-fun union1 ((set enum_t_AUTOMATON_STATE)
  (set enum_t_AUTOMATON_STATE)) (set enum_t_AUTOMATON_STATE))

(declare-fun union2 ((set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))

(declare-fun union3 ((set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))

;; union_def1
  (assert
  (forall ((s1 (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (s2 (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (x (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (= (mem3 x (union3 s1 s2)) (or (mem3 x s1) (mem3 x s2)))))

;; union_def1
  (assert
  (forall ((s1 (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s2 (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (= (mem2 x (union2 s1 s2)) (or (mem2 x s1) (mem2 x s2)))))

;; union_def1
  (assert
  (forall ((s1 (set enum_t_AUTOMATON_STATE))
  (s2 (set enum_t_AUTOMATON_STATE)) (x enum_t_AUTOMATON_STATE))
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
  (forall ((s1 (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (s2 (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (x (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (= (mem3 x
  (tb2t
  (inter (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (t2tb s1) (t2tb s2)))) (and (mem3 x s1) (mem3 x s2)))))

;; inter_def1
  (assert
  (forall ((s1 (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s2 (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (= (mem2 x
  (tb2t1
  (inter (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 s1)
  (t2tb1 s2)))) (and (mem2 x s1) (mem2 x s2)))))

;; inter_def1
  (assert
  (forall ((s1 (set enum_t_AUTOMATON_STATE))
  (s2 (set enum_t_AUTOMATON_STATE)) (x enum_t_AUTOMATON_STATE))
  (= (mem1 x (tb2t2 (inter enum_t_AUTOMATON_STATE1 (t2tb2 s1) (t2tb2 s2))))
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
  (forall ((s1 (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (s2 (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (x (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (= (mem3 x
  (tb2t
  (diff (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (t2tb s1) (t2tb s2)))) (and (mem3 x s1) (not (mem3 x s2))))))

;; diff_def1
  (assert
  (forall ((s1 (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s2 (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (= (mem2 x
  (tb2t1
  (diff (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 s1)
  (t2tb1 s2)))) (and (mem2 x s1) (not (mem2 x s2))))))

;; diff_def1
  (assert
  (forall ((s1 (set enum_t_AUTOMATON_STATE))
  (s2 (set enum_t_AUTOMATON_STATE)) (x enum_t_AUTOMATON_STATE))
  (= (mem1 x (tb2t2 (diff enum_t_AUTOMATON_STATE1 (t2tb2 s1) (t2tb2 s2))))
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
  (forall ((s (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))))
  (=>
  (not (is_empty
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s)))
  (mem3
  (tb2t1
  (choose (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (t2tb s))) s))))

;; choose_def
  (assert
  (forall ((s (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (=>
  (not (is_empty (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 s))) (mem2
  (tb2t3
  (choose (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 s))) s))))

;; choose_def
  (assert
  (forall ((s (set enum_t_AUTOMATON_STATE)))
  (=> (not (is_empty enum_t_AUTOMATON_STATE1 (t2tb2 s))) (mem1
  (tb2t4 (choose enum_t_AUTOMATON_STATE1 (t2tb2 s))) s))))

;; choose_def
  (assert
  (forall ((a ty))
  (forall ((s uni)) (=> (not (is_empty a s)) (mem a (choose a s) s)))))

(declare-fun all (ty) uni)

;; all_sort
  (assert (forall ((a ty)) (sort (set1 a) (all a))))

;; all_def
  (assert
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (mem3 x
  (tb2t
  (all (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))))))

;; all_def
  (assert
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))) (mem2
  x (tb2t1 (all (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))))))

;; all_def
  (assert
  (forall ((x enum_t_AUTOMATON_STATE)) (mem1 x
  (tb2t2 (all enum_t_AUTOMATON_STATE1)))))

;; all_def
  (assert (forall ((a ty)) (forall ((x uni)) (mem a x (all a)))))

(declare-fun b_bool () (set Bool))

(declare-fun t2tb5 (Bool) uni)

;; t2tb_sort
  (assert (forall ((x Bool)) (sort bool (t2tb5 x))))

(declare-fun tb2t5 (uni) Bool)

;; BridgeL
  (assert
  (forall ((i Bool)) (! (= (tb2t5 (t2tb5 i)) i) :pattern ((t2tb5 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort bool j) (= (t2tb5 (tb2t5 j)) j)) :pattern ((t2tb5 (tb2t5 j))) )))

(declare-fun t2tb6 ((set Bool)) uni)

;; t2tb_sort
  (assert (forall ((x (set Bool))) (sort (set1 bool) (t2tb6 x))))

(declare-fun tb2t6 (uni) (set Bool))

;; BridgeL
  (assert
  (forall ((i (set Bool))) (! (= (tb2t6 (t2tb6 i)) i) :pattern ((t2tb6 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 bool) j) (= (t2tb6 (tb2t6 j)) j)) :pattern ((t2tb6
                                                                 (tb2t6 j))) )))

;; mem_b_bool
  (assert (forall ((x Bool)) (mem bool (t2tb5 x) (t2tb6 b_bool))))

(declare-fun integer () (set Int))

(declare-fun t2tb7 ((set Int)) uni)

;; t2tb_sort
  (assert (forall ((x (set Int))) (sort (set1 int) (t2tb7 x))))

(declare-fun tb2t7 (uni) (set Int))

;; BridgeL
  (assert
  (forall ((i (set Int))) (! (= (tb2t7 (t2tb7 i)) i) :pattern ((t2tb7 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb7 (tb2t7 j)) j) :pattern ((t2tb7 (tb2t7 j))) )))

(declare-fun t2tb8 (Int) uni)

;; t2tb_sort
  (assert (forall ((x Int)) (sort int (t2tb8 x))))

(declare-fun tb2t8 (uni) Int)

;; BridgeL
  (assert
  (forall ((i Int)) (! (= (tb2t8 (t2tb8 i)) i) :pattern ((t2tb8 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb8 (tb2t8 j)) j) :pattern ((t2tb8 (tb2t8 j))) )))

;; mem_integer
  (assert (forall ((x Int)) (mem int (t2tb8 x) (t2tb7 integer))))

(declare-fun natural () (set Int))

;; mem_natural
  (assert
  (forall ((x Int)) (= (mem int (t2tb8 x) (t2tb7 natural)) (<= 0 x))))

(declare-fun natural1 () (set Int))

;; mem_natural1
  (assert
  (forall ((x Int)) (= (mem int (t2tb8 x) (t2tb7 natural1)) (< 0 x))))

(declare-fun nat () (set Int))

;; mem_nat
  (assert
  (forall ((x Int))
  (= (mem int (t2tb8 x) (t2tb7 nat)) (and (<= 0 x) (<= x 2147483647)))))

(declare-fun nat1 () (set Int))

;; mem_nat1
  (assert
  (forall ((x Int))
  (= (mem int (t2tb8 x) (t2tb7 nat1)) (and (< 0 x) (<= x 2147483647)))))

(declare-fun bounded_int () (set Int))

;; mem_bounded_int
  (assert
  (forall ((x Int))
  (= (mem int (t2tb8 x) (t2tb7 bounded_int))
  (and (<= (- 2147483647) x) (<= x 2147483647)))))

(declare-fun mk (Int Int) (set Int))

;; mem_interval
  (assert
  (forall ((x Int) (a Int) (b Int))
  (! (= (mem int (t2tb8 x) (t2tb7 (mk a b))) (and (<= a x) (<= x b))) :pattern ((mem
  int (t2tb8 x) (t2tb7 (mk a b)))) )))

;; interval_empty
  (assert
  (forall ((a Int) (b Int)) (=> (< b a) (= (mk a b) (tb2t7 (empty int))))))

;; interval_add
  (assert
  (forall ((a Int) (b Int))
  (=> (<= a b)
  (= (mk a b) (tb2t7 (add int (t2tb8 b) (t2tb7 (mk a (- b 1)))))))))

(declare-fun power1 (ty uni) uni)

;; power_sort
  (assert
  (forall ((a ty)) (forall ((x uni)) (sort (set1 (set1 a)) (power1 a x)))))

;; mem_power
  (assert
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (y (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (! (= (mem3 x
     (tb2t
     (power1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (t2tb1 y)))) (subset
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 x)
     (t2tb1 y))) :pattern ((mem3
  x
  (tb2t
  (power1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 y))))) )))

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

(declare-fun t2tb9 ((set (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))))) (sort
  (set1
  (set1 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))))
  (t2tb9 x))))

(declare-fun tb2t9 (uni) (set (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))))

;; BridgeL
  (assert
  (forall ((i (set (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))))
  (! (= (tb2t9 (t2tb9 i)) i) :pattern ((t2tb9 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))))
     j) (= (t2tb9 (tb2t9 j)) j)) :pattern ((t2tb9 (tb2t9 j))) )))

;; mem_non_empty_power
  (assert
  (forall ((x (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (y (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))))
  (! (= (mem
     (set1 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
     (t2tb x)
     (non_empty_power
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb y)))
     (and (subset
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb x) (t2tb y)) (not (= x empty3)))) :pattern ((mem
  (set1 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (t2tb x)
  (non_empty_power
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb y)))) )))

;; mem_non_empty_power
  (assert
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (y (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (! (= (mem3 x
     (tb2t
     (non_empty_power
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 y))))
     (and (subset (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (t2tb1 x) (t2tb1 y)) (not (= x empty2)))) :pattern ((mem3
  x
  (tb2t
  (non_empty_power (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 y))))) )))

(declare-fun t2tb10 ((set (set enum_t_AUTOMATON_STATE))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set enum_t_AUTOMATON_STATE)))) (sort
  (set1 (set1 enum_t_AUTOMATON_STATE1)) (t2tb10 x))))

(declare-fun tb2t10 (uni) (set (set enum_t_AUTOMATON_STATE)))

;; BridgeL
  (assert
  (forall ((i (set (set enum_t_AUTOMATON_STATE))))
  (! (= (tb2t10 (t2tb10 i)) i) :pattern ((t2tb10 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 (set1 enum_t_AUTOMATON_STATE1)) j)
     (= (t2tb10 (tb2t10 j)) j)) :pattern ((t2tb10 (tb2t10 j))) )))

;; mem_non_empty_power
  (assert
  (forall ((x (set enum_t_AUTOMATON_STATE)) (y (set enum_t_AUTOMATON_STATE)))
  (! (= (mem (set1 enum_t_AUTOMATON_STATE1) (t2tb2 x)
     (non_empty_power enum_t_AUTOMATON_STATE1 (t2tb2 y)))
     (and (subset enum_t_AUTOMATON_STATE1 (t2tb2 x) (t2tb2 y))
     (not (= x empty1)))) :pattern ((mem
  (set1 enum_t_AUTOMATON_STATE1) (t2tb2 x)
  (non_empty_power enum_t_AUTOMATON_STATE1 (t2tb2 y)))) )))

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

(declare-fun Tuple21 (enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))

(declare-fun Tuple2_proj_1 (ty ty uni) uni)

;; Tuple2_proj_1_sort
  (assert
  (forall ((a ty) (a1 ty))
  (forall ((x uni)) (sort a1 (Tuple2_proj_1 a1 a x)))))

;; Tuple2_proj_1_def
  (assert
  (forall ((u enum_t_AUTOMATON_STATE) (u1 enum_t_AUTOMATON_STATE))
  (= (tb2t4
     (Tuple2_proj_1 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
     (t2tb3 (Tuple21 u u1)))) u)))

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
  (forall ((u enum_t_AUTOMATON_STATE) (u1 enum_t_AUTOMATON_STATE))
  (= (tb2t4
     (Tuple2_proj_2 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
     (t2tb3 (Tuple21 u u1)))) u1)))

;; Tuple2_proj_2_def
  (assert
  (forall ((a ty) (a1 ty))
  (forall ((u uni) (u1 uni))
  (=> (sort a u1) (= (Tuple2_proj_2 a1 a (Tuple2 a1 a u u1)) u1)))))

;; tuple2_inversion
  (assert
  (forall ((u (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (= u (Tuple21
       (tb2t4
       (Tuple2_proj_1 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
       (t2tb3 u)))
       (tb2t4
       (Tuple2_proj_2 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
       (t2tb3 u)))))))

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

(declare-fun relation1 ((set enum_t_AUTOMATON_STATE)
  (set enum_t_AUTOMATON_STATE)) (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))

;; mem_relation
  (assert
  (forall ((a ty))
  (forall ((f uni) (s uni) (t (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))))
  (and
  (=> (mem
  (set1
  (tuple21 a
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))) f
  (relation (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  a s (t2tb t)))
  (forall ((x uni) (y (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (=> (mem
  (tuple21 a
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 a (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  x (t2tb1 y)) f) (and (mem a x s) (mem3 y t)))))
  (=>
  (forall ((x uni) (y (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (=> (sort a x)
  (=> (mem
  (tuple21 a
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 a (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  x (t2tb1 y)) f) (and (mem a x s) (mem3 y t))))) (mem
  (set1
  (tuple21 a
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))) f
  (relation (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  a s (t2tb t))))))))

;; mem_relation
  (assert
  (forall ((a ty))
  (forall ((f uni) (s uni) (t (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (and
  (=> (mem
  (set1
  (tuple21 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))) f
  (relation (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) a s
  (t2tb1 t)))
  (forall ((x uni) (y (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))
  (=> (mem
  (tuple21 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) x
  (t2tb3 y)) f) (and (mem a x s) (mem2 y t)))))
  (=>
  (forall ((x uni) (y (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))
  (=> (sort a x)
  (=> (mem
  (tuple21 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) x
  (t2tb3 y)) f) (and (mem a x s) (mem2 y t))))) (mem
  (set1
  (tuple21 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))) f
  (relation (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) a s
  (t2tb1 t))))))))

;; mem_relation
  (assert
  (forall ((a ty))
  (forall ((f uni) (s uni) (t (set enum_t_AUTOMATON_STATE)))
  (and
  (=> (mem (set1 (tuple21 a enum_t_AUTOMATON_STATE1)) f
  (relation enum_t_AUTOMATON_STATE1 a s (t2tb2 t)))
  (forall ((x uni) (y enum_t_AUTOMATON_STATE))
  (=> (mem (tuple21 a enum_t_AUTOMATON_STATE1)
  (Tuple2 a enum_t_AUTOMATON_STATE1 x (t2tb4 y)) f)
  (and (mem a x s) (mem1 y t)))))
  (=>
  (forall ((x uni) (y enum_t_AUTOMATON_STATE))
  (=> (sort a x)
  (=> (mem (tuple21 a enum_t_AUTOMATON_STATE1)
  (Tuple2 a enum_t_AUTOMATON_STATE1 x (t2tb4 y)) f)
  (and (mem a x s) (mem1 y t))))) (mem
  (set1 (tuple21 a enum_t_AUTOMATON_STATE1)) f
  (relation enum_t_AUTOMATON_STATE1 a s (t2tb2 t))))))))

(declare-fun t2tb11 ((set (set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))))) (sort
  (set1
  (set1
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))))
  (t2tb11 x))))

(declare-fun tb2t11 (uni) (set (set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))))))
  (! (= (tb2t11 (t2tb11 i)) i) :pattern ((t2tb11 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))))) j)
     (= (t2tb11 (tb2t11 j)) j)) :pattern ((t2tb11 (tb2t11 j))) )))

(declare-fun t2tb12 ((set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))))) (sort
  (set1
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))))
  (t2tb12 x))))

(declare-fun tb2t12 (uni) (set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))))
  (! (= (tb2t12 (t2tb12 i)) i) :pattern ((t2tb12 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))) j)
     (= (t2tb12 (tb2t12 j)) j)) :pattern ((t2tb12 (tb2t12 j))) )))

(declare-fun t2tb13 ((tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))) (sort
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (t2tb13 x))))

(declare-fun tb2t13 (uni) (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))

;; BridgeL
  (assert
  (forall ((i (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))))
  (! (= (tb2t13 (t2tb13 i)) i) :pattern ((t2tb13 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))) j)
     (= (t2tb13 (tb2t13 j)) j)) :pattern ((t2tb13 (tb2t13 j))) )))

;; mem_relation
  (assert
  (forall ((f (set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))) (s (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (t (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))))
  (= (mem
  (set1
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))))
  (t2tb12 f)
  (relation (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s)
  (t2tb t)))
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (y (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (=> (mem
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb1 x)
  (t2tb1 y)) (t2tb12 f)) (and (mem3 x s) (mem3 y t)))))))

(declare-fun t2tb14 ((set (set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))))) (sort
  (set1
  (set1
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))) (t2tb14 x))))

(declare-fun tb2t14 (uni) (set (set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))))
  (! (= (tb2t14 (t2tb14 i)) i) :pattern ((t2tb14 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))) j)
     (= (t2tb14 (tb2t14 j)) j)) :pattern ((t2tb14 (tb2t14 j))) )))

(declare-fun t2tb15 ((set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))) (sort
  (set1
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))) (t2tb15 x))))

(declare-fun tb2t15 (uni) (set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))))
  (! (= (tb2t15 (t2tb15 i)) i) :pattern ((t2tb15 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))) j)
     (= (t2tb15 (tb2t15 j)) j)) :pattern ((t2tb15 (tb2t15 j))) )))

(declare-fun t2tb16 ((tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (sort
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb16 x))))

(declare-fun tb2t16 (uni) (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (! (= (tb2t16 (t2tb16 i)) i) :pattern ((t2tb16 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) j)
     (= (t2tb16 (tb2t16 j)) j)) :pattern ((t2tb16 (tb2t16 j))) )))

;; mem_relation
  (assert
  (forall ((f (set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (s (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (t (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (= (mem
  (set1
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))) (t2tb15 f)
  (relation (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s)
  (t2tb1 t)))
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (y (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (=> (mem
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 x)
  (t2tb3 y)) (t2tb15 f)) (and (mem3 x s) (mem2 y t)))))))

(declare-fun t2tb17 ((set (set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) enum_t_AUTOMATON_STATE)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) enum_t_AUTOMATON_STATE))))) (sort
  (set1
  (set1
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  enum_t_AUTOMATON_STATE1))) (t2tb17 x))))

(declare-fun tb2t17 (uni) (set (set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) enum_t_AUTOMATON_STATE))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) enum_t_AUTOMATON_STATE)))))
  (! (= (tb2t17 (t2tb17 i)) i) :pattern ((t2tb17 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     enum_t_AUTOMATON_STATE1))) j) (= (t2tb17 (tb2t17 j)) j)) :pattern (
  (t2tb17 (tb2t17 j))) )))

(declare-fun t2tb18 ((set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) enum_t_AUTOMATON_STATE))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) enum_t_AUTOMATON_STATE)))) (sort
  (set1
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  enum_t_AUTOMATON_STATE1)) (t2tb18 x))))

(declare-fun tb2t18 (uni) (set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) enum_t_AUTOMATON_STATE)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) enum_t_AUTOMATON_STATE))))
  (! (= (tb2t18 (t2tb18 i)) i) :pattern ((t2tb18 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     enum_t_AUTOMATON_STATE1)) j) (= (t2tb18 (tb2t18 j)) j)) :pattern (
  (t2tb18 (tb2t18 j))) )))

(declare-fun t2tb19 ((tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) enum_t_AUTOMATON_STATE)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) enum_t_AUTOMATON_STATE))) (sort
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  enum_t_AUTOMATON_STATE1) (t2tb19 x))))

(declare-fun tb2t19 (uni) (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) enum_t_AUTOMATON_STATE))

;; BridgeL
  (assert
  (forall ((i (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) enum_t_AUTOMATON_STATE)))
  (! (= (tb2t19 (t2tb19 i)) i) :pattern ((t2tb19 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     enum_t_AUTOMATON_STATE1) j) (= (t2tb19 (tb2t19 j)) j)) :pattern (
  (t2tb19 (tb2t19 j))) )))

;; mem_relation
  (assert
  (forall ((f (set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) enum_t_AUTOMATON_STATE)))
  (s (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (t (set enum_t_AUTOMATON_STATE)))
  (= (mem
  (set1
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  enum_t_AUTOMATON_STATE1)) (t2tb18 f)
  (relation enum_t_AUTOMATON_STATE1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s)
  (t2tb2 t)))
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (y enum_t_AUTOMATON_STATE))
  (=> (mem
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  enum_t_AUTOMATON_STATE1)
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  enum_t_AUTOMATON_STATE1 (t2tb1 x) (t2tb4 y)) (t2tb18 f))
  (and (mem3 x s) (mem1 y t)))))))

;; mem_relation
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (t uni))
  (and
  (=> (mem
  (set1
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  b)) f
  (relation b
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s)
  t))
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (y uni))
  (=> (mem
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  b)
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) b
  (t2tb1 x) y) f) (and (mem3 x s) (mem b y t)))))
  (=>
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (y uni))
  (=> (sort b y)
  (=> (mem
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  b)
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) b
  (t2tb1 x) y) f) (and (mem3 x s) (mem b y t))))) (mem
  (set1
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  b)) f
  (relation b
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s)
  t)))))))

(declare-fun t2tb20 ((set (tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))))) (sort
  (set1
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))))
  (t2tb20 x))))

(declare-fun tb2t20 (uni) (set (tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))))
  (! (= (tb2t20 (t2tb20 i)) i) :pattern ((t2tb20 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))) j)
     (= (t2tb20 (tb2t20 j)) j)) :pattern ((t2tb20 (tb2t20 j))) )))

(declare-fun t2tb21 ((tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)
  (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))) (sort
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (t2tb21 x))))

(declare-fun tb2t21 (uni) (tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)
  (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))))
  (! (= (tb2t21 (t2tb21 i)) i) :pattern ((t2tb21 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))) j)
     (= (t2tb21 (tb2t21 j)) j)) :pattern ((t2tb21 (tb2t21 j))) )))

(declare-fun t2tb22 ((set (set (tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))))
  (t2tb22 x))))

(declare-fun tb2t22 (uni) (set (set (tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))))))
  (! (= (tb2t22 (t2tb22 i)) i) :pattern ((t2tb22 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))))) j)
     (= (t2tb22 (tb2t22 j)) j)) :pattern ((t2tb22 (tb2t22 j))) )))

;; mem_relation
  (assert
  (forall ((f (set (tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))) (s (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (t (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))))
  (= (mem
  (set1
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))))
  (t2tb20 f)
  (relation (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 s)
  (t2tb t)))
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (y (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (=> (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb3 x)
  (t2tb1 y)) (t2tb20 f)) (and (mem2 x s) (mem3 y t)))))))

(declare-fun t2tb23 ((set (set (tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))) (t2tb23 x))))

(declare-fun tb2t23 (uni) (set (set (tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))))
  (! (= (tb2t23 (t2tb23 i)) i) :pattern ((t2tb23 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))) j)
     (= (t2tb23 (tb2t23 j)) j)) :pattern ((t2tb23 (tb2t23 j))) )))

(declare-fun t2tb24 ((set (tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))) (sort
  (set1
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))) (t2tb24 x))))

(declare-fun tb2t24 (uni) (set (tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))))
  (! (= (tb2t24 (t2tb24 i)) i) :pattern ((t2tb24 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))) j)
     (= (t2tb24 (tb2t24 j)) j)) :pattern ((t2tb24 (tb2t24 j))) )))

(declare-fun t2tb25 ((tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)
  (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))) (sort
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb25 x))))

(declare-fun tb2t25 (uni) (tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)
  (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (! (= (tb2t25 (t2tb25 i)) i) :pattern ((t2tb25 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) j)
     (= (t2tb25 (tb2t25 j)) j)) :pattern ((t2tb25 (tb2t25 j))) )))

;; mem_relation
  (assert
  (forall ((f (set (tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (s (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (t (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (= (mem
  (set1
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))) (t2tb24 f)
  (relation (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 s)
  (t2tb1 t)))
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (y (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (=> (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb3 x)
  (t2tb3 y)) (t2tb24 f)) (and (mem2 x s) (mem2 y t)))))))

(declare-fun t2tb26 ((set (set (tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) enum_t_AUTOMATON_STATE)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) enum_t_AUTOMATON_STATE))))) (sort
  (set1
  (set1
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  enum_t_AUTOMATON_STATE1))) (t2tb26 x))))

(declare-fun tb2t26 (uni) (set (set (tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) enum_t_AUTOMATON_STATE))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) enum_t_AUTOMATON_STATE)))))
  (! (= (tb2t26 (t2tb26 i)) i) :pattern ((t2tb26 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     enum_t_AUTOMATON_STATE1))) j) (= (t2tb26 (tb2t26 j)) j)) :pattern (
  (t2tb26 (tb2t26 j))) )))

(declare-fun t2tb27 ((set (tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) enum_t_AUTOMATON_STATE))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) enum_t_AUTOMATON_STATE)))) (sort
  (set1
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  enum_t_AUTOMATON_STATE1)) (t2tb27 x))))

(declare-fun tb2t27 (uni) (set (tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) enum_t_AUTOMATON_STATE)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) enum_t_AUTOMATON_STATE))))
  (! (= (tb2t27 (t2tb27 i)) i) :pattern ((t2tb27 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     enum_t_AUTOMATON_STATE1)) j) (= (t2tb27 (tb2t27 j)) j)) :pattern (
  (t2tb27 (tb2t27 j))) )))

(declare-fun t2tb28 ((tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) enum_t_AUTOMATON_STATE)) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)
  enum_t_AUTOMATON_STATE))) (sort
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  enum_t_AUTOMATON_STATE1) (t2tb28 x))))

(declare-fun tb2t28 (uni) (tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) enum_t_AUTOMATON_STATE))

;; BridgeL
  (assert
  (forall ((i (tuple2 (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)
  enum_t_AUTOMATON_STATE)))
  (! (= (tb2t28 (t2tb28 i)) i) :pattern ((t2tb28 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     enum_t_AUTOMATON_STATE1) j) (= (t2tb28 (tb2t28 j)) j)) :pattern (
  (t2tb28 (tb2t28 j))) )))

;; mem_relation
  (assert
  (forall ((f (set (tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) enum_t_AUTOMATON_STATE)))
  (s (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (t (set enum_t_AUTOMATON_STATE)))
  (= (mem
  (set1
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  enum_t_AUTOMATON_STATE1)) (t2tb27 f)
  (relation enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 s)
  (t2tb2 t)))
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (y enum_t_AUTOMATON_STATE))
  (=> (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  enum_t_AUTOMATON_STATE1)
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  enum_t_AUTOMATON_STATE1 (t2tb3 x) (t2tb4 y)) (t2tb27 f))
  (and (mem2 x s) (mem1 y t)))))))

;; mem_relation
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (t uni))
  (and
  (=> (mem
  (set1
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)) f
  (relation b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 s) t))
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (y uni))
  (=> (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b
  (t2tb3 x) y) f) (and (mem2 x s) (mem b y t)))))
  (=>
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (y uni))
  (=> (sort b y)
  (=> (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b
  (t2tb3 x) y) f) (and (mem2 x s) (mem b y t))))) (mem
  (set1
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)) f
  (relation b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 s) t)))))))

(declare-fun t2tb29 ((set (set (tuple2 enum_t_AUTOMATON_STATE
  (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 enum_t_AUTOMATON_STATE
  (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))))) (sort
  (set1
  (set1
  (tuple21 enum_t_AUTOMATON_STATE1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))))
  (t2tb29 x))))

(declare-fun tb2t29 (uni) (set (set (tuple2 enum_t_AUTOMATON_STATE
  (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 enum_t_AUTOMATON_STATE
  (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))))))
  (! (= (tb2t29 (t2tb29 i)) i) :pattern ((t2tb29 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21 enum_t_AUTOMATON_STATE1
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))))) j)
     (= (t2tb29 (tb2t29 j)) j)) :pattern ((t2tb29 (tb2t29 j))) )))

(declare-fun t2tb30 ((set (tuple2 enum_t_AUTOMATON_STATE
  (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE
  (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))))) (sort
  (set1
  (tuple21 enum_t_AUTOMATON_STATE1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))))
  (t2tb30 x))))

(declare-fun tb2t30 (uni) (set (tuple2 enum_t_AUTOMATON_STATE
  (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 enum_t_AUTOMATON_STATE
  (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))))
  (! (= (tb2t30 (t2tb30 i)) i) :pattern ((t2tb30 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21 enum_t_AUTOMATON_STATE1
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))) j)
     (= (t2tb30 (tb2t30 j)) j)) :pattern ((t2tb30 (tb2t30 j))) )))

(declare-fun t2tb31 ((tuple2 enum_t_AUTOMATON_STATE
  (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE
  (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))) (sort
  (tuple21 enum_t_AUTOMATON_STATE1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (t2tb31 x))))

(declare-fun tb2t31 (uni) (tuple2 enum_t_AUTOMATON_STATE
  (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))

;; BridgeL
  (assert
  (forall ((i (tuple2 enum_t_AUTOMATON_STATE
  (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))))
  (! (= (tb2t31 (t2tb31 i)) i) :pattern ((t2tb31 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 enum_t_AUTOMATON_STATE1
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))) j)
     (= (t2tb31 (tb2t31 j)) j)) :pattern ((t2tb31 (tb2t31 j))) )))

;; mem_relation
  (assert
  (forall ((f (set (tuple2 enum_t_AUTOMATON_STATE
  (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))))
  (s (set enum_t_AUTOMATON_STATE))
  (t (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))))
  (= (mem
  (set1
  (tuple21 enum_t_AUTOMATON_STATE1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))))
  (t2tb30 f)
  (relation (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  enum_t_AUTOMATON_STATE1 (t2tb2 s) (t2tb t)))
  (forall ((x enum_t_AUTOMATON_STATE) (y (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (=> (mem
  (tuple21 enum_t_AUTOMATON_STATE1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 enum_t_AUTOMATON_STATE1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb4 x)
  (t2tb1 y)) (t2tb30 f)) (and (mem1 x s) (mem3 y t)))))))

(declare-fun t2tb32 ((tuple2 enum_t_AUTOMATON_STATE
  (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))) uni)

;; t2tb_sort
  (assert
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (sort
  (tuple21 enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb32 x))))

(declare-fun tb2t32 (uni) (tuple2 enum_t_AUTOMATON_STATE
  (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))

;; BridgeL
  (assert
  (forall ((i (tuple2 enum_t_AUTOMATON_STATE (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (! (= (tb2t32 (t2tb32 i)) i) :pattern ((t2tb32 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (tuple21 enum_t_AUTOMATON_STATE1
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) j)
     (= (t2tb32 (tb2t32 j)) j)) :pattern ((t2tb32 (tb2t32 j))) )))

(declare-fun t2tb33 ((set (set (tuple2 enum_t_AUTOMATON_STATE
  (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 enum_t_AUTOMATON_STATE
  (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))))) (sort
  (set1
  (set1
  (tuple21 enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))) (t2tb33 x))))

(declare-fun tb2t33 (uni) (set (set (tuple2 enum_t_AUTOMATON_STATE
  (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 enum_t_AUTOMATON_STATE
  (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))))
  (! (= (tb2t33 (t2tb33 i)) i) :pattern ((t2tb33 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (set1
     (tuple21 enum_t_AUTOMATON_STATE1
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))) j)
     (= (t2tb33 (tb2t33 j)) j)) :pattern ((t2tb33 (tb2t33 j))) )))

(declare-fun t2tb34 ((set (tuple2 enum_t_AUTOMATON_STATE
  (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE
  (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))) (sort
  (set1
  (tuple21 enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))) (t2tb34 x))))

(declare-fun tb2t34 (uni) (set (tuple2 enum_t_AUTOMATON_STATE
  (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 enum_t_AUTOMATON_STATE
  (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))))
  (! (= (tb2t34 (t2tb34 i)) i) :pattern ((t2tb34 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1
     (tuple21 enum_t_AUTOMATON_STATE1
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))) j)
     (= (t2tb34 (tb2t34 j)) j)) :pattern ((t2tb34 (tb2t34 j))) )))

;; mem_relation
  (assert
  (forall ((f (set (tuple2 enum_t_AUTOMATON_STATE
  (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (s (set enum_t_AUTOMATON_STATE)) (t (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (= (mem
  (set1
  (tuple21 enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))) (t2tb34 f)
  (relation (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  enum_t_AUTOMATON_STATE1 (t2tb2 s) (t2tb1 t)))
  (forall ((x enum_t_AUTOMATON_STATE) (y (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))
  (=> (mem
  (tuple21 enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb4 x)
  (t2tb3 y)) (t2tb34 f)) (and (mem1 x s) (mem2 y t)))))))

;; mem_relation
  (assert
  (forall ((f (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s (set enum_t_AUTOMATON_STATE)) (t (set enum_t_AUTOMATON_STATE)))
  (= (mem3 f (relation1 s t))
  (forall ((x enum_t_AUTOMATON_STATE) (y enum_t_AUTOMATON_STATE))
  (=> (mem2 (Tuple21 x y) f) (and (mem1 x s) (mem1 y t)))))))

;; mem_relation
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set enum_t_AUTOMATON_STATE)) (t uni))
  (and
  (=> (mem (set1 (tuple21 enum_t_AUTOMATON_STATE1 b)) f
  (relation b enum_t_AUTOMATON_STATE1 (t2tb2 s) t))
  (forall ((x enum_t_AUTOMATON_STATE) (y uni))
  (=> (mem (tuple21 enum_t_AUTOMATON_STATE1 b)
  (Tuple2 enum_t_AUTOMATON_STATE1 b (t2tb4 x) y) f)
  (and (mem1 x s) (mem b y t)))))
  (=>
  (forall ((x enum_t_AUTOMATON_STATE) (y uni))
  (=> (sort b y)
  (=> (mem (tuple21 enum_t_AUTOMATON_STATE1 b)
  (Tuple2 enum_t_AUTOMATON_STATE1 b (t2tb4 x) y) f)
  (and (mem1 x s) (mem b y t))))) (mem
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 b)) f
  (relation b enum_t_AUTOMATON_STATE1 (t2tb2 s) t)))))))

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
  (forall ((r uni) (dom uni) (y (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (! (and
     (=> (mem3 y
     (tb2t
     (image (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     a r dom)))
     (exists ((x uni))
     (and (sort a x)
     (and (mem a x dom) (mem
     (tuple21 a
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
     (Tuple2 a
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) x
     (t2tb1 y)) r)))))
     (=>
     (exists ((x uni))
     (and (mem a x dom) (mem
     (tuple21 a
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
     (Tuple2 a
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) x
     (t2tb1 y)) r))) (mem3 y
     (tb2t
     (image (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     a r dom))))) :pattern ((mem3
  y
  (tb2t
  (image (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) a r
  dom)))) ))))

;; mem_image
  (assert
  (forall ((a ty))
  (forall ((r uni) (dom uni) (y (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))
  (! (and
     (=> (mem2 y
     (tb2t1
     (image (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) a r
     dom)))
     (exists ((x uni))
     (and (sort a x)
     (and (mem a x dom) (mem
     (tuple21 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (Tuple2 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) x
     (t2tb3 y)) r)))))
     (=>
     (exists ((x uni))
     (and (mem a x dom) (mem
     (tuple21 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (Tuple2 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) x
     (t2tb3 y)) r))) (mem2 y
     (tb2t1
     (image (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) a r
     dom))))) :pattern ((mem2
  y
  (tb2t1
  (image (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) a r dom)))) ))))

;; mem_image
  (assert
  (forall ((a ty))
  (forall ((r uni) (dom uni) (y enum_t_AUTOMATON_STATE))
  (! (and
     (=> (mem1 y (tb2t2 (image enum_t_AUTOMATON_STATE1 a r dom)))
     (exists ((x uni))
     (and (sort a x)
     (and (mem a x dom) (mem (tuple21 a enum_t_AUTOMATON_STATE1)
     (Tuple2 a enum_t_AUTOMATON_STATE1 x (t2tb4 y)) r)))))
     (=>
     (exists ((x uni))
     (and (mem a x dom) (mem (tuple21 a enum_t_AUTOMATON_STATE1)
     (Tuple2 a enum_t_AUTOMATON_STATE1 x (t2tb4 y)) r))) (mem1 y
     (tb2t2 (image enum_t_AUTOMATON_STATE1 a r dom))))) :pattern ((mem1
  y (tb2t2 (image enum_t_AUTOMATON_STATE1 a r dom)))) ))))

;; mem_image
  (assert
  (forall ((r (set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))) (dom (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (y (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (! (= (mem3 y
     (tb2t
     (image (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb12 r) (t2tb dom))))
     (exists ((x (set (tuple2 enum_t_AUTOMATON_STATE
     enum_t_AUTOMATON_STATE))))
     (and (mem3 x dom) (mem
     (tuple21
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
     (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb1 x) (t2tb1 y)) (t2tb12 r))))) :pattern ((mem3
  y
  (tb2t
  (image (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb12 r)
  (t2tb dom))))) )))

;; mem_image
  (assert
  (forall ((r (set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (dom (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (y (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))
  (! (= (mem2 y
     (tb2t1
     (image (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb15 r) (t2tb dom))))
     (exists ((x (set (tuple2 enum_t_AUTOMATON_STATE
     enum_t_AUTOMATON_STATE))))
     (and (mem3 x dom) (mem
     (tuple21
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 x)
     (t2tb3 y)) (t2tb15 r))))) :pattern ((mem2
  y
  (tb2t1
  (image (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb15 r)
  (t2tb dom))))) )))

;; mem_image
  (assert
  (forall ((r (set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) enum_t_AUTOMATON_STATE)))
  (dom (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (y enum_t_AUTOMATON_STATE))
  (! (= (mem1 y
     (tb2t2
     (image enum_t_AUTOMATON_STATE1
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb18 r) (t2tb dom))))
     (exists ((x (set (tuple2 enum_t_AUTOMATON_STATE
     enum_t_AUTOMATON_STATE))))
     (and (mem3 x dom) (mem
     (tuple21
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     enum_t_AUTOMATON_STATE1)
     (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     enum_t_AUTOMATON_STATE1 (t2tb1 x) (t2tb4 y)) (t2tb18 r))))) :pattern ((mem1
  y
  (tb2t2
  (image enum_t_AUTOMATON_STATE1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb18 r)
  (t2tb dom))))) )))

;; mem_image
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (y uni))
  (! (= (mem b y
     (image b
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) r
     (t2tb dom)))
     (exists ((x (set (tuple2 enum_t_AUTOMATON_STATE
     enum_t_AUTOMATON_STATE))))
     (and (mem3 x dom) (mem
     (tuple21
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) b)
     (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     b (t2tb1 x) y) r)))) :pattern ((mem
  b y
  (image b (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) r
  (t2tb dom)))) ))))

;; mem_image
  (assert
  (forall ((r (set (tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))) (dom (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (y (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (! (= (mem3 y
     (tb2t
     (image (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb20 r)
     (t2tb1 dom))))
     (exists ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
     (and (mem2 x dom) (mem
     (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
     (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb3 x) (t2tb1 y)) (t2tb20 r))))) :pattern ((mem3
  y
  (tb2t
  (image (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb20 r)
  (t2tb1 dom))))) )))

;; mem_image
  (assert
  (forall ((r (set (tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (dom (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (y (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))
  (! (= (mem2 y
     (tb2t1
     (image (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb24 r)
     (t2tb1 dom))))
     (exists ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
     (and (mem2 x dom) (mem
     (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb3 x)
     (t2tb3 y)) (t2tb24 r))))) :pattern ((mem2
  y
  (tb2t1
  (image (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb24 r)
  (t2tb1 dom))))) )))

;; mem_image
  (assert
  (forall ((r (set (tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) enum_t_AUTOMATON_STATE)))
  (dom (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (y enum_t_AUTOMATON_STATE))
  (! (= (mem1 y
     (tb2t2
     (image enum_t_AUTOMATON_STATE1
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb27 r)
     (t2tb1 dom))))
     (exists ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
     (and (mem2 x dom) (mem
     (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     enum_t_AUTOMATON_STATE1)
     (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     enum_t_AUTOMATON_STATE1 (t2tb3 x) (t2tb4 y)) (t2tb27 r))))) :pattern ((mem1
  y
  (tb2t2
  (image enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb27 r)
  (t2tb1 dom))))) )))

;; mem_image
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (y uni))
  (! (= (mem b y
     (image b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) r
     (t2tb1 dom)))
     (exists ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
     (and (mem2 x dom) (mem
     (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)
     (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b
     (t2tb3 x) y) r)))) :pattern ((mem
  b y
  (image b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) r
  (t2tb1 dom)))) ))))

;; mem_image
  (assert
  (forall ((r (set (tuple2 enum_t_AUTOMATON_STATE
  (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))))
  (dom (set enum_t_AUTOMATON_STATE)) (y (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (! (= (mem3 y
     (tb2t
     (image (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     enum_t_AUTOMATON_STATE1 (t2tb30 r) (t2tb2 dom))))
     (exists ((x enum_t_AUTOMATON_STATE))
     (and (mem1 x dom) (mem
     (tuple21 enum_t_AUTOMATON_STATE1
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
     (Tuple2 enum_t_AUTOMATON_STATE1
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb4 x) (t2tb1 y)) (t2tb30 r))))) :pattern ((mem3
  y
  (tb2t
  (image (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  enum_t_AUTOMATON_STATE1 (t2tb30 r) (t2tb2 dom))))) )))

;; mem_image
  (assert
  (forall ((r (set (tuple2 enum_t_AUTOMATON_STATE
  (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (dom (set enum_t_AUTOMATON_STATE)) (y (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))
  (! (= (mem2 y
     (tb2t1
     (image (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     enum_t_AUTOMATON_STATE1 (t2tb34 r) (t2tb2 dom))))
     (exists ((x enum_t_AUTOMATON_STATE))
     (and (mem1 x dom) (mem
     (tuple21 enum_t_AUTOMATON_STATE1
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (Tuple2 enum_t_AUTOMATON_STATE1
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb4 x)
     (t2tb3 y)) (t2tb34 r))))) :pattern ((mem2
  y
  (tb2t1
  (image (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  enum_t_AUTOMATON_STATE1 (t2tb34 r) (t2tb2 dom))))) )))

;; mem_image
  (assert
  (forall ((r (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (dom (set enum_t_AUTOMATON_STATE)) (y enum_t_AUTOMATON_STATE))
  (! (= (mem1 y
     (tb2t2
     (image enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb1 r)
     (t2tb2 dom))))
     (exists ((x enum_t_AUTOMATON_STATE))
     (and (mem1 x dom) (mem2 (Tuple21 x y) r)))) :pattern ((mem1
  y
  (tb2t2
  (image enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb1 r)
  (t2tb2 dom))))) )))

;; mem_image
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom (set enum_t_AUTOMATON_STATE)) (y uni))
  (! (= (mem b y (image b enum_t_AUTOMATON_STATE1 r (t2tb2 dom)))
     (exists ((x enum_t_AUTOMATON_STATE))
     (and (mem1 x dom) (mem (tuple21 enum_t_AUTOMATON_STATE1 b)
     (Tuple2 enum_t_AUTOMATON_STATE1 b (t2tb4 x) y) r)))) :pattern ((mem
  b y (image b enum_t_AUTOMATON_STATE1 r (t2tb2 dom)))) ))))

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
  (forall ((a ty))
  (forall ((r uni) (s uni) (t uni))
  (= (tb2t
     (image (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     a r (union a s t))) (union3
                         (tb2t
                         (image
                         (set1
                         (tuple21 enum_t_AUTOMATON_STATE1
                         enum_t_AUTOMATON_STATE1)) a r s))
                         (tb2t
                         (image
                         (set1
                         (tuple21 enum_t_AUTOMATON_STATE1
                         enum_t_AUTOMATON_STATE1)) a r t)))))))

;; image_union
  (assert
  (forall ((a ty))
  (forall ((r uni) (s uni) (t uni))
  (= (tb2t1
     (image (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) a r
     (union a s t))) (union2
                     (tb2t1
                     (image
                     (tuple21 enum_t_AUTOMATON_STATE1
                     enum_t_AUTOMATON_STATE1) a r s))
                     (tb2t1
                     (image
                     (tuple21 enum_t_AUTOMATON_STATE1
                     enum_t_AUTOMATON_STATE1) a r t)))))))

;; image_union
  (assert
  (forall ((a ty))
  (forall ((r uni) (s uni) (t uni))
  (= (tb2t2 (image enum_t_AUTOMATON_STATE1 a r (union a s t))) (union1
                                                               (tb2t2
                                                               (image
                                                               enum_t_AUTOMATON_STATE1
                                                               a r s))
                                                               (tb2t2
                                                               (image
                                                               enum_t_AUTOMATON_STATE1
                                                               a r t)))))))

;; image_union
  (assert
  (forall ((r (set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))) (s (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (t (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))))
  (= (tb2t
     (image (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb12 r) (t2tb (union3 s t)))) (union3
                                      (tb2t
                                      (image
                                      (set1
                                      (tuple21 enum_t_AUTOMATON_STATE1
                                      enum_t_AUTOMATON_STATE1))
                                      (set1
                                      (tuple21 enum_t_AUTOMATON_STATE1
                                      enum_t_AUTOMATON_STATE1)) (t2tb12 r)
                                      (t2tb s)))
                                      (tb2t
                                      (image
                                      (set1
                                      (tuple21 enum_t_AUTOMATON_STATE1
                                      enum_t_AUTOMATON_STATE1))
                                      (set1
                                      (tuple21 enum_t_AUTOMATON_STATE1
                                      enum_t_AUTOMATON_STATE1)) (t2tb12 r)
                                      (t2tb t)))))))

;; image_union
  (assert
  (forall ((r (set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (s (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (t (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))))
  (= (tb2t1
     (image (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb15 r) (t2tb (union3 s t)))) (union2
                                      (tb2t1
                                      (image
                                      (tuple21 enum_t_AUTOMATON_STATE1
                                      enum_t_AUTOMATON_STATE1)
                                      (set1
                                      (tuple21 enum_t_AUTOMATON_STATE1
                                      enum_t_AUTOMATON_STATE1)) (t2tb15 r)
                                      (t2tb s)))
                                      (tb2t1
                                      (image
                                      (tuple21 enum_t_AUTOMATON_STATE1
                                      enum_t_AUTOMATON_STATE1)
                                      (set1
                                      (tuple21 enum_t_AUTOMATON_STATE1
                                      enum_t_AUTOMATON_STATE1)) (t2tb15 r)
                                      (t2tb t)))))))

;; image_union
  (assert
  (forall ((r (set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) enum_t_AUTOMATON_STATE)))
  (s (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (t (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))))
  (= (tb2t2
     (image enum_t_AUTOMATON_STATE1
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb18 r) (t2tb (union3 s t)))) (union1
                                      (tb2t2
                                      (image enum_t_AUTOMATON_STATE1
                                      (set1
                                      (tuple21 enum_t_AUTOMATON_STATE1
                                      enum_t_AUTOMATON_STATE1)) (t2tb18 r)
                                      (t2tb s)))
                                      (tb2t2
                                      (image enum_t_AUTOMATON_STATE1
                                      (set1
                                      (tuple21 enum_t_AUTOMATON_STATE1
                                      enum_t_AUTOMATON_STATE1)) (t2tb18 r)
                                      (t2tb t)))))))

;; image_union
  (assert
  (forall ((b ty))
  (forall ((r uni) (s (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (t (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))))
  (= (image b
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) r
     (t2tb (union3 s t))) (union b
                          (image b
                          (set1
                          (tuple21 enum_t_AUTOMATON_STATE1
                          enum_t_AUTOMATON_STATE1)) r (t2tb s))
                          (image b
                          (set1
                          (tuple21 enum_t_AUTOMATON_STATE1
                          enum_t_AUTOMATON_STATE1)) r (t2tb t)))))))

;; image_union
  (assert
  (forall ((r (set (tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))) (s (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (t (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (= (tb2t
     (image (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb20 r)
     (t2tb1 (union2 s t)))) (union3
                            (tb2t
                            (image
                            (set1
                            (tuple21 enum_t_AUTOMATON_STATE1
                            enum_t_AUTOMATON_STATE1))
                            (tuple21 enum_t_AUTOMATON_STATE1
                            enum_t_AUTOMATON_STATE1) (t2tb20 r) (t2tb1 s)))
                            (tb2t
                            (image
                            (set1
                            (tuple21 enum_t_AUTOMATON_STATE1
                            enum_t_AUTOMATON_STATE1))
                            (tuple21 enum_t_AUTOMATON_STATE1
                            enum_t_AUTOMATON_STATE1) (t2tb20 r) (t2tb1 t)))))))

;; image_union
  (assert
  (forall ((r (set (tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (s (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (t (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (= (tb2t1
     (image (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb24 r)
     (t2tb1 (union2 s t)))) (union2
                            (tb2t1
                            (image
                            (tuple21 enum_t_AUTOMATON_STATE1
                            enum_t_AUTOMATON_STATE1)
                            (tuple21 enum_t_AUTOMATON_STATE1
                            enum_t_AUTOMATON_STATE1) (t2tb24 r) (t2tb1 s)))
                            (tb2t1
                            (image
                            (tuple21 enum_t_AUTOMATON_STATE1
                            enum_t_AUTOMATON_STATE1)
                            (tuple21 enum_t_AUTOMATON_STATE1
                            enum_t_AUTOMATON_STATE1) (t2tb24 r) (t2tb1 t)))))))

;; image_union
  (assert
  (forall ((r (set (tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) enum_t_AUTOMATON_STATE)))
  (s (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (t (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (= (tb2t2
     (image enum_t_AUTOMATON_STATE1
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb27 r)
     (t2tb1 (union2 s t)))) (union1
                            (tb2t2
                            (image enum_t_AUTOMATON_STATE1
                            (tuple21 enum_t_AUTOMATON_STATE1
                            enum_t_AUTOMATON_STATE1) (t2tb27 r) (t2tb1 s)))
                            (tb2t2
                            (image enum_t_AUTOMATON_STATE1
                            (tuple21 enum_t_AUTOMATON_STATE1
                            enum_t_AUTOMATON_STATE1) (t2tb27 r) (t2tb1 t)))))))

;; image_union
  (assert
  (forall ((b ty))
  (forall ((r uni) (s (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (t (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (= (image b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) r
     (t2tb1 (union2 s t))) (union b
                           (image b
                           (tuple21 enum_t_AUTOMATON_STATE1
                           enum_t_AUTOMATON_STATE1) r (t2tb1 s))
                           (image b
                           (tuple21 enum_t_AUTOMATON_STATE1
                           enum_t_AUTOMATON_STATE1) r (t2tb1 t)))))))

;; image_union
  (assert
  (forall ((r (set (tuple2 enum_t_AUTOMATON_STATE
  (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))))
  (s (set enum_t_AUTOMATON_STATE)) (t (set enum_t_AUTOMATON_STATE)))
  (= (tb2t
     (image (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     enum_t_AUTOMATON_STATE1 (t2tb30 r) (t2tb2 (union1 s t)))) (union3
                                                               (tb2t
                                                               (image
                                                               (set1
                                                               (tuple21
                                                               enum_t_AUTOMATON_STATE1
                                                               enum_t_AUTOMATON_STATE1))
                                                               enum_t_AUTOMATON_STATE1
                                                               (t2tb30 r)
                                                               (t2tb2 s)))
                                                               (tb2t
                                                               (image
                                                               (set1
                                                               (tuple21
                                                               enum_t_AUTOMATON_STATE1
                                                               enum_t_AUTOMATON_STATE1))
                                                               enum_t_AUTOMATON_STATE1
                                                               (t2tb30 r)
                                                               (t2tb2 t)))))))

;; image_union
  (assert
  (forall ((r (set (tuple2 enum_t_AUTOMATON_STATE
  (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (s (set enum_t_AUTOMATON_STATE)) (t (set enum_t_AUTOMATON_STATE)))
  (= (tb2t1
     (image (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     enum_t_AUTOMATON_STATE1 (t2tb34 r) (t2tb2 (union1 s t)))) (union2
                                                               (tb2t1
                                                               (image
                                                               (tuple21
                                                               enum_t_AUTOMATON_STATE1
                                                               enum_t_AUTOMATON_STATE1)
                                                               enum_t_AUTOMATON_STATE1
                                                               (t2tb34 r)
                                                               (t2tb2 s)))
                                                               (tb2t1
                                                               (image
                                                               (tuple21
                                                               enum_t_AUTOMATON_STATE1
                                                               enum_t_AUTOMATON_STATE1)
                                                               enum_t_AUTOMATON_STATE1
                                                               (t2tb34 r)
                                                               (t2tb2 t)))))))

;; image_union
  (assert
  (forall ((r (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s (set enum_t_AUTOMATON_STATE)) (t (set enum_t_AUTOMATON_STATE)))
  (= (tb2t2
     (image enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb1 r)
     (t2tb2 (union1 s t)))) (union1
                            (tb2t2
                            (image enum_t_AUTOMATON_STATE1
                            enum_t_AUTOMATON_STATE1 (t2tb1 r) (t2tb2 s)))
                            (tb2t2
                            (image enum_t_AUTOMATON_STATE1
                            enum_t_AUTOMATON_STATE1 (t2tb1 r) (t2tb2 t)))))))

;; image_union
  (assert
  (forall ((b ty))
  (forall ((r uni) (s (set enum_t_AUTOMATON_STATE))
  (t (set enum_t_AUTOMATON_STATE)))
  (= (image b enum_t_AUTOMATON_STATE1 r (t2tb2 (union1 s t))) (union b
                                                              (image b
                                                              enum_t_AUTOMATON_STATE1
                                                              r (t2tb2 s))
                                                              (image b
                                                              enum_t_AUTOMATON_STATE1
                                                              r (t2tb2 t)))))))

;; image_union
  (assert
  (forall ((a ty) (b ty))
  (forall ((r uni) (s uni) (t uni))
  (= (image b a r (union a s t)) (union b (image b a r s) (image b a r t))))))

;; image_add
  (assert
  (forall ((a ty))
  (forall ((r uni) (dom uni) (x uni))
  (= (tb2t
     (image (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     a r (add a x dom))) (union3
                         (tb2t
                         (image
                         (set1
                         (tuple21 enum_t_AUTOMATON_STATE1
                         enum_t_AUTOMATON_STATE1)) a r (add a x (empty a))))
                         (tb2t
                         (image
                         (set1
                         (tuple21 enum_t_AUTOMATON_STATE1
                         enum_t_AUTOMATON_STATE1)) a r dom)))))))

;; image_add
  (assert
  (forall ((a ty))
  (forall ((r uni) (dom uni) (x uni))
  (= (tb2t1
     (image (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) a r
     (add a x dom))) (union2
                     (tb2t1
                     (image
                     (tuple21 enum_t_AUTOMATON_STATE1
                     enum_t_AUTOMATON_STATE1) a r (add a x (empty a))))
                     (tb2t1
                     (image
                     (tuple21 enum_t_AUTOMATON_STATE1
                     enum_t_AUTOMATON_STATE1) a r dom)))))))

;; image_add
  (assert
  (forall ((a ty))
  (forall ((r uni) (dom uni) (x uni))
  (= (tb2t2 (image enum_t_AUTOMATON_STATE1 a r (add a x dom))) (union1
                                                               (tb2t2
                                                               (image
                                                               enum_t_AUTOMATON_STATE1
                                                               a r
                                                               (add a x
                                                               (empty a))))
                                                               (tb2t2
                                                               (image
                                                               enum_t_AUTOMATON_STATE1
                                                               a r dom)))))))

;; image_add
  (assert
  (forall ((r (set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))) (dom (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (x (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (= (tb2t
     (image (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb12 r) (t2tb (add3 x dom)))) (union3
                                      (tb2t
                                      (image
                                      (set1
                                      (tuple21 enum_t_AUTOMATON_STATE1
                                      enum_t_AUTOMATON_STATE1))
                                      (set1
                                      (tuple21 enum_t_AUTOMATON_STATE1
                                      enum_t_AUTOMATON_STATE1)) (t2tb12 r)
                                      (t2tb (add3 x empty3))))
                                      (tb2t
                                      (image
                                      (set1
                                      (tuple21 enum_t_AUTOMATON_STATE1
                                      enum_t_AUTOMATON_STATE1))
                                      (set1
                                      (tuple21 enum_t_AUTOMATON_STATE1
                                      enum_t_AUTOMATON_STATE1)) (t2tb12 r)
                                      (t2tb dom)))))))

;; image_add
  (assert
  (forall ((r (set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (dom (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (x (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (= (tb2t1
     (image (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb15 r) (t2tb (add3 x dom)))) (union2
                                      (tb2t1
                                      (image
                                      (tuple21 enum_t_AUTOMATON_STATE1
                                      enum_t_AUTOMATON_STATE1)
                                      (set1
                                      (tuple21 enum_t_AUTOMATON_STATE1
                                      enum_t_AUTOMATON_STATE1)) (t2tb15 r)
                                      (t2tb (add3 x empty3))))
                                      (tb2t1
                                      (image
                                      (tuple21 enum_t_AUTOMATON_STATE1
                                      enum_t_AUTOMATON_STATE1)
                                      (set1
                                      (tuple21 enum_t_AUTOMATON_STATE1
                                      enum_t_AUTOMATON_STATE1)) (t2tb15 r)
                                      (t2tb dom)))))))

;; image_add
  (assert
  (forall ((r (set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) enum_t_AUTOMATON_STATE)))
  (dom (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (= (tb2t2
     (image enum_t_AUTOMATON_STATE1
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb18 r) (t2tb (add3 x dom)))) (union1
                                      (tb2t2
                                      (image enum_t_AUTOMATON_STATE1
                                      (set1
                                      (tuple21 enum_t_AUTOMATON_STATE1
                                      enum_t_AUTOMATON_STATE1)) (t2tb18 r)
                                      (t2tb (add3 x empty3))))
                                      (tb2t2
                                      (image enum_t_AUTOMATON_STATE1
                                      (set1
                                      (tuple21 enum_t_AUTOMATON_STATE1
                                      enum_t_AUTOMATON_STATE1)) (t2tb18 r)
                                      (t2tb dom)))))))

;; image_add
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (x (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (= (image b
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) r
     (t2tb (add3 x dom))) (union b
                          (image b
                          (set1
                          (tuple21 enum_t_AUTOMATON_STATE1
                          enum_t_AUTOMATON_STATE1)) r (t2tb (add3 x empty3)))
                          (image b
                          (set1
                          (tuple21 enum_t_AUTOMATON_STATE1
                          enum_t_AUTOMATON_STATE1)) r (t2tb dom)))))))

;; image_add
  (assert
  (forall ((r (set (tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))) (dom (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (x (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))
  (= (tb2t
     (image (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb20 r)
     (t2tb1 (add2 x dom)))) (union3
                            (tb2t
                            (image
                            (set1
                            (tuple21 enum_t_AUTOMATON_STATE1
                            enum_t_AUTOMATON_STATE1))
                            (tuple21 enum_t_AUTOMATON_STATE1
                            enum_t_AUTOMATON_STATE1) (t2tb20 r)
                            (t2tb1 (add2 x empty2))))
                            (tb2t
                            (image
                            (set1
                            (tuple21 enum_t_AUTOMATON_STATE1
                            enum_t_AUTOMATON_STATE1))
                            (tuple21 enum_t_AUTOMATON_STATE1
                            enum_t_AUTOMATON_STATE1) (t2tb20 r) (t2tb1 dom)))))))

;; image_add
  (assert
  (forall ((r (set (tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (dom (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (x (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))
  (= (tb2t1
     (image (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb24 r)
     (t2tb1 (add2 x dom)))) (union2
                            (tb2t1
                            (image
                            (tuple21 enum_t_AUTOMATON_STATE1
                            enum_t_AUTOMATON_STATE1)
                            (tuple21 enum_t_AUTOMATON_STATE1
                            enum_t_AUTOMATON_STATE1) (t2tb24 r)
                            (t2tb1 (add2 x empty2))))
                            (tb2t1
                            (image
                            (tuple21 enum_t_AUTOMATON_STATE1
                            enum_t_AUTOMATON_STATE1)
                            (tuple21 enum_t_AUTOMATON_STATE1
                            enum_t_AUTOMATON_STATE1) (t2tb24 r) (t2tb1 dom)))))))

;; image_add
  (assert
  (forall ((r (set (tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) enum_t_AUTOMATON_STATE)))
  (dom (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (= (tb2t2
     (image enum_t_AUTOMATON_STATE1
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb27 r)
     (t2tb1 (add2 x dom)))) (union1
                            (tb2t2
                            (image enum_t_AUTOMATON_STATE1
                            (tuple21 enum_t_AUTOMATON_STATE1
                            enum_t_AUTOMATON_STATE1) (t2tb27 r)
                            (t2tb1 (add2 x empty2))))
                            (tb2t2
                            (image enum_t_AUTOMATON_STATE1
                            (tuple21 enum_t_AUTOMATON_STATE1
                            enum_t_AUTOMATON_STATE1) (t2tb27 r) (t2tb1 dom)))))))

;; image_add
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (x (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))
  (= (image b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) r
     (t2tb1 (add2 x dom))) (union b
                           (image b
                           (tuple21 enum_t_AUTOMATON_STATE1
                           enum_t_AUTOMATON_STATE1) r
                           (t2tb1 (add2 x empty2)))
                           (image b
                           (tuple21 enum_t_AUTOMATON_STATE1
                           enum_t_AUTOMATON_STATE1) r (t2tb1 dom)))))))

;; image_add
  (assert
  (forall ((r (set (tuple2 enum_t_AUTOMATON_STATE
  (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))))
  (dom (set enum_t_AUTOMATON_STATE)) (x enum_t_AUTOMATON_STATE))
  (= (tb2t
     (image (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     enum_t_AUTOMATON_STATE1 (t2tb30 r) (t2tb2 (add1 x dom)))) (union3
                                                               (tb2t
                                                               (image
                                                               (set1
                                                               (tuple21
                                                               enum_t_AUTOMATON_STATE1
                                                               enum_t_AUTOMATON_STATE1))
                                                               enum_t_AUTOMATON_STATE1
                                                               (t2tb30 r)
                                                               (t2tb2
                                                               (add1 x
                                                               empty1))))
                                                               (tb2t
                                                               (image
                                                               (set1
                                                               (tuple21
                                                               enum_t_AUTOMATON_STATE1
                                                               enum_t_AUTOMATON_STATE1))
                                                               enum_t_AUTOMATON_STATE1
                                                               (t2tb30 r)
                                                               (t2tb2 dom)))))))

;; image_add
  (assert
  (forall ((r (set (tuple2 enum_t_AUTOMATON_STATE
  (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (dom (set enum_t_AUTOMATON_STATE)) (x enum_t_AUTOMATON_STATE))
  (= (tb2t1
     (image (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     enum_t_AUTOMATON_STATE1 (t2tb34 r) (t2tb2 (add1 x dom)))) (union2
                                                               (tb2t1
                                                               (image
                                                               (tuple21
                                                               enum_t_AUTOMATON_STATE1
                                                               enum_t_AUTOMATON_STATE1)
                                                               enum_t_AUTOMATON_STATE1
                                                               (t2tb34 r)
                                                               (t2tb2
                                                               (add1 x
                                                               empty1))))
                                                               (tb2t1
                                                               (image
                                                               (tuple21
                                                               enum_t_AUTOMATON_STATE1
                                                               enum_t_AUTOMATON_STATE1)
                                                               enum_t_AUTOMATON_STATE1
                                                               (t2tb34 r)
                                                               (t2tb2 dom)))))))

;; image_add
  (assert
  (forall ((r (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (dom (set enum_t_AUTOMATON_STATE)) (x enum_t_AUTOMATON_STATE))
  (= (tb2t2
     (image enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb1 r)
     (t2tb2 (add1 x dom)))) (union1
                            (tb2t2
                            (image enum_t_AUTOMATON_STATE1
                            enum_t_AUTOMATON_STATE1 (t2tb1 r)
                            (t2tb2 (add1 x empty1))))
                            (tb2t2
                            (image enum_t_AUTOMATON_STATE1
                            enum_t_AUTOMATON_STATE1 (t2tb1 r) (t2tb2 dom)))))))

;; image_add
  (assert
  (forall ((b ty))
  (forall ((r uni) (dom (set enum_t_AUTOMATON_STATE))
  (x enum_t_AUTOMATON_STATE))
  (= (image b enum_t_AUTOMATON_STATE1 r (t2tb2 (add1 x dom))) (union b
                                                              (image b
                                                              enum_t_AUTOMATON_STATE1
                                                              r
                                                              (t2tb2
                                                              (add1 x empty1)))
                                                              (image b
                                                              enum_t_AUTOMATON_STATE1
                                                              r (t2tb2 dom)))))))

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
  (forall ((f uni) (s uni) (t (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))))
  (and
  (=> (mem
  (set1
  (tuple21 a
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))) f
  (infix_plmngt
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) a s
  (t2tb t)))
  (and
  (forall ((x uni) (y (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (=> (mem
  (tuple21 a
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 a (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  x (t2tb1 y)) f) (and (mem a x s) (mem3 y t))))
  (forall ((x uni) (y1 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (y2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (=>
  (and (mem
  (tuple21 a
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 a (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  x (t2tb1 y1)) f) (mem
  (tuple21 a
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 a (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  x (t2tb1 y2)) f)) (= y1 y2)))))
  (=>
  (and
  (forall ((x uni) (y (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (=> (sort a x)
  (=> (mem
  (tuple21 a
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 a (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  x (t2tb1 y)) f) (and (mem a x s) (mem3 y t)))))
  (forall ((x uni) (y1 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (y2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (=> (sort a x)
  (=>
  (and (mem
  (tuple21 a
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 a (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  x (t2tb1 y1)) f) (mem
  (tuple21 a
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 a (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  x (t2tb1 y2)) f)) (= y1 y2))))) (mem
  (set1
  (tuple21 a
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))) f
  (infix_plmngt
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) a s
  (t2tb t))))))))

;; mem_function
  (assert
  (forall ((a ty))
  (forall ((f uni) (s uni) (t (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (and
  (=> (mem
  (set1
  (tuple21 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))) f
  (infix_plmngt (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) a s
  (t2tb1 t)))
  (and
  (forall ((x uni) (y (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))
  (=> (mem
  (tuple21 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) x
  (t2tb3 y)) f) (and (mem a x s) (mem2 y t))))
  (forall ((x uni) (y1 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (y2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))
  (=>
  (and (mem
  (tuple21 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) x
  (t2tb3 y1)) f) (mem
  (tuple21 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) x
  (t2tb3 y2)) f)) (= y1 y2)))))
  (=>
  (and
  (forall ((x uni) (y (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))
  (=> (sort a x)
  (=> (mem
  (tuple21 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) x
  (t2tb3 y)) f) (and (mem a x s) (mem2 y t)))))
  (forall ((x uni) (y1 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (y2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))
  (=> (sort a x)
  (=>
  (and (mem
  (tuple21 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) x
  (t2tb3 y1)) f) (mem
  (tuple21 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) x
  (t2tb3 y2)) f)) (= y1 y2))))) (mem
  (set1
  (tuple21 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))) f
  (infix_plmngt (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) a s
  (t2tb1 t))))))))

;; mem_function
  (assert
  (forall ((a ty))
  (forall ((f uni) (s uni) (t (set enum_t_AUTOMATON_STATE)))
  (and
  (=> (mem (set1 (tuple21 a enum_t_AUTOMATON_STATE1)) f
  (infix_plmngt enum_t_AUTOMATON_STATE1 a s (t2tb2 t)))
  (and
  (forall ((x uni) (y enum_t_AUTOMATON_STATE))
  (=> (mem (tuple21 a enum_t_AUTOMATON_STATE1)
  (Tuple2 a enum_t_AUTOMATON_STATE1 x (t2tb4 y)) f)
  (and (mem a x s) (mem1 y t))))
  (forall ((x uni) (y1 enum_t_AUTOMATON_STATE) (y2 enum_t_AUTOMATON_STATE))
  (=>
  (and (mem (tuple21 a enum_t_AUTOMATON_STATE1)
  (Tuple2 a enum_t_AUTOMATON_STATE1 x (t2tb4 y1)) f) (mem
  (tuple21 a enum_t_AUTOMATON_STATE1)
  (Tuple2 a enum_t_AUTOMATON_STATE1 x (t2tb4 y2)) f)) (= y1 y2)))))
  (=>
  (and
  (forall ((x uni) (y enum_t_AUTOMATON_STATE))
  (=> (sort a x)
  (=> (mem (tuple21 a enum_t_AUTOMATON_STATE1)
  (Tuple2 a enum_t_AUTOMATON_STATE1 x (t2tb4 y)) f)
  (and (mem a x s) (mem1 y t)))))
  (forall ((x uni) (y1 enum_t_AUTOMATON_STATE) (y2 enum_t_AUTOMATON_STATE))
  (=> (sort a x)
  (=>
  (and (mem (tuple21 a enum_t_AUTOMATON_STATE1)
  (Tuple2 a enum_t_AUTOMATON_STATE1 x (t2tb4 y1)) f) (mem
  (tuple21 a enum_t_AUTOMATON_STATE1)
  (Tuple2 a enum_t_AUTOMATON_STATE1 x (t2tb4 y2)) f)) (= y1 y2))))) (mem
  (set1 (tuple21 a enum_t_AUTOMATON_STATE1)) f
  (infix_plmngt enum_t_AUTOMATON_STATE1 a s (t2tb2 t))))))))

;; mem_function
  (assert
  (forall ((f (set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))) (s (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (t (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))))
  (= (mem
  (set1
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))))
  (t2tb12 f)
  (infix_plmngt
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s)
  (t2tb t)))
  (and
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (y (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (=> (mem
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb1 x)
  (t2tb1 y)) (t2tb12 f)) (and (mem3 x s) (mem3 y t))))
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (y1 (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (y2 (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (=>
  (and (mem
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb1 x)
  (t2tb1 y1)) (t2tb12 f)) (mem
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb1 x)
  (t2tb1 y2)) (t2tb12 f))) (= y1 y2)))))))

;; mem_function
  (assert
  (forall ((f (set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (s (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (t (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (= (mem
  (set1
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))) (t2tb15 f)
  (infix_plmngt (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s)
  (t2tb1 t)))
  (and
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (y (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (=> (mem
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 x)
  (t2tb3 y)) (t2tb15 f)) (and (mem3 x s) (mem2 y t))))
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (y1 (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (y2 (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (=>
  (and (mem
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 x)
  (t2tb3 y1)) (t2tb15 f)) (mem
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 x)
  (t2tb3 y2)) (t2tb15 f))) (= y1 y2)))))))

;; mem_function
  (assert
  (forall ((f (set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) enum_t_AUTOMATON_STATE)))
  (s (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (t (set enum_t_AUTOMATON_STATE)))
  (= (mem
  (set1
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  enum_t_AUTOMATON_STATE1)) (t2tb18 f)
  (infix_plmngt enum_t_AUTOMATON_STATE1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s)
  (t2tb2 t)))
  (and
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (y enum_t_AUTOMATON_STATE))
  (=> (mem
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  enum_t_AUTOMATON_STATE1)
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  enum_t_AUTOMATON_STATE1 (t2tb1 x) (t2tb4 y)) (t2tb18 f))
  (and (mem3 x s) (mem1 y t))))
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (y1 enum_t_AUTOMATON_STATE) (y2 enum_t_AUTOMATON_STATE))
  (=>
  (and (mem
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  enum_t_AUTOMATON_STATE1)
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  enum_t_AUTOMATON_STATE1 (t2tb1 x) (t2tb4 y1)) (t2tb18 f)) (mem
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  enum_t_AUTOMATON_STATE1)
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  enum_t_AUTOMATON_STATE1 (t2tb1 x) (t2tb4 y2)) (t2tb18 f))) (= y1 y2)))))))

;; mem_function
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (t uni))
  (and
  (=> (mem
  (set1
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  b)) f
  (infix_plmngt b
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s)
  t))
  (and
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (y uni))
  (=> (mem
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  b)
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) b
  (t2tb1 x) y) f) (and (mem3 x s) (mem b y t))))
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (y1 uni) (y2 uni))
  (=> (sort b y1)
  (=> (sort b y2)
  (=>
  (and (mem
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  b)
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) b
  (t2tb1 x) y1) f) (mem
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  b)
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) b
  (t2tb1 x) y2) f)) (= y1 y2)))))))
  (=>
  (and
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (y uni))
  (=> (sort b y)
  (=> (mem
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  b)
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) b
  (t2tb1 x) y) f) (and (mem3 x s) (mem b y t)))))
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (y1 uni) (y2 uni))
  (=> (sort b y1)
  (=> (sort b y2)
  (=>
  (and (mem
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  b)
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) b
  (t2tb1 x) y1) f) (mem
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  b)
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) b
  (t2tb1 x) y2) f)) (= y1 y2)))))) (mem
  (set1
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  b)) f
  (infix_plmngt b
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s)
  t)))))))

;; mem_function
  (assert
  (forall ((f (set (tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))) (s (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (t (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))))
  (= (mem
  (set1
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))))
  (t2tb20 f)
  (infix_plmngt
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 s)
  (t2tb t)))
  (and
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (y (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (=> (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb3 x)
  (t2tb1 y)) (t2tb20 f)) (and (mem2 x s) (mem3 y t))))
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (y1 (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (y2 (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (=>
  (and (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb3 x)
  (t2tb1 y1)) (t2tb20 f)) (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb3 x)
  (t2tb1 y2)) (t2tb20 f))) (= y1 y2)))))))

;; mem_function
  (assert
  (forall ((f (set (tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (s (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (t (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (= (mem
  (set1
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))) (t2tb24 f)
  (infix_plmngt (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 s)
  (t2tb1 t)))
  (and
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (y (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (=> (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb3 x)
  (t2tb3 y)) (t2tb24 f)) (and (mem2 x s) (mem2 y t))))
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (y1 (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (y2 (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (=>
  (and (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb3 x)
  (t2tb3 y1)) (t2tb24 f)) (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb3 x)
  (t2tb3 y2)) (t2tb24 f))) (= y1 y2)))))))

;; mem_function
  (assert
  (forall ((f (set (tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) enum_t_AUTOMATON_STATE)))
  (s (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (t (set enum_t_AUTOMATON_STATE)))
  (= (mem
  (set1
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  enum_t_AUTOMATON_STATE1)) (t2tb27 f)
  (infix_plmngt enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 s)
  (t2tb2 t)))
  (and
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (y enum_t_AUTOMATON_STATE))
  (=> (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  enum_t_AUTOMATON_STATE1)
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  enum_t_AUTOMATON_STATE1 (t2tb3 x) (t2tb4 y)) (t2tb27 f))
  (and (mem2 x s) (mem1 y t))))
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (y1 enum_t_AUTOMATON_STATE) (y2 enum_t_AUTOMATON_STATE))
  (=>
  (and (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  enum_t_AUTOMATON_STATE1)
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  enum_t_AUTOMATON_STATE1 (t2tb3 x) (t2tb4 y1)) (t2tb27 f)) (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  enum_t_AUTOMATON_STATE1)
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  enum_t_AUTOMATON_STATE1 (t2tb3 x) (t2tb4 y2)) (t2tb27 f))) (= y1 y2)))))))

;; mem_function
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (t uni))
  (and
  (=> (mem
  (set1
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)) f
  (infix_plmngt b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 s) t))
  (and
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (y uni))
  (=> (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b
  (t2tb3 x) y) f) (and (mem2 x s) (mem b y t))))
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (y1 uni) (y2 uni))
  (=> (sort b y1)
  (=> (sort b y2)
  (=>
  (and (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b
  (t2tb3 x) y1) f) (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b
  (t2tb3 x) y2) f)) (= y1 y2)))))))
  (=>
  (and
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (y uni))
  (=> (sort b y)
  (=> (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b
  (t2tb3 x) y) f) (and (mem2 x s) (mem b y t)))))
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (y1 uni) (y2 uni))
  (=> (sort b y1)
  (=> (sort b y2)
  (=>
  (and (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b
  (t2tb3 x) y1) f) (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b
  (t2tb3 x) y2) f)) (= y1 y2)))))) (mem
  (set1
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)) f
  (infix_plmngt b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 s) t)))))))

;; mem_function
  (assert
  (forall ((f (set (tuple2 enum_t_AUTOMATON_STATE
  (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))))
  (s (set enum_t_AUTOMATON_STATE))
  (t (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))))
  (= (mem
  (set1
  (tuple21 enum_t_AUTOMATON_STATE1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))))
  (t2tb30 f)
  (infix_plmngt
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  enum_t_AUTOMATON_STATE1 (t2tb2 s) (t2tb t)))
  (and
  (forall ((x enum_t_AUTOMATON_STATE) (y (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (=> (mem
  (tuple21 enum_t_AUTOMATON_STATE1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 enum_t_AUTOMATON_STATE1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb4 x)
  (t2tb1 y)) (t2tb30 f)) (and (mem1 x s) (mem3 y t))))
  (forall ((x enum_t_AUTOMATON_STATE) (y1 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (y2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (=>
  (and (mem
  (tuple21 enum_t_AUTOMATON_STATE1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 enum_t_AUTOMATON_STATE1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb4 x)
  (t2tb1 y1)) (t2tb30 f)) (mem
  (tuple21 enum_t_AUTOMATON_STATE1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 enum_t_AUTOMATON_STATE1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb4 x)
  (t2tb1 y2)) (t2tb30 f))) (= y1 y2)))))))

;; mem_function
  (assert
  (forall ((f (set (tuple2 enum_t_AUTOMATON_STATE
  (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (s (set enum_t_AUTOMATON_STATE)) (t (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (= (mem
  (set1
  (tuple21 enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))) (t2tb34 f)
  (infix_plmngt (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  enum_t_AUTOMATON_STATE1 (t2tb2 s) (t2tb1 t)))
  (and
  (forall ((x enum_t_AUTOMATON_STATE) (y (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))
  (=> (mem
  (tuple21 enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb4 x)
  (t2tb3 y)) (t2tb34 f)) (and (mem1 x s) (mem2 y t))))
  (forall ((x enum_t_AUTOMATON_STATE) (y1 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (y2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))
  (=>
  (and (mem
  (tuple21 enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb4 x)
  (t2tb3 y1)) (t2tb34 f)) (mem
  (tuple21 enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb4 x)
  (t2tb3 y2)) (t2tb34 f))) (= y1 y2)))))))

;; mem_function
  (assert
  (forall ((f (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s (set enum_t_AUTOMATON_STATE)) (t (set enum_t_AUTOMATON_STATE)))
  (= (mem3 f
  (tb2t
  (infix_plmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 t))))
  (and
  (forall ((x enum_t_AUTOMATON_STATE) (y enum_t_AUTOMATON_STATE))
  (=> (mem2 (Tuple21 x y) f) (and (mem1 x s) (mem1 y t))))
  (forall ((x enum_t_AUTOMATON_STATE) (y1 enum_t_AUTOMATON_STATE)
  (y2 enum_t_AUTOMATON_STATE))
  (=> (and (mem2 (Tuple21 x y1) f) (mem2 (Tuple21 x y2) f)) (= y1 y2)))))))

;; mem_function
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set enum_t_AUTOMATON_STATE)) (t uni))
  (and
  (=> (mem (set1 (tuple21 enum_t_AUTOMATON_STATE1 b)) f
  (infix_plmngt b enum_t_AUTOMATON_STATE1 (t2tb2 s) t))
  (and
  (forall ((x enum_t_AUTOMATON_STATE) (y uni))
  (=> (mem (tuple21 enum_t_AUTOMATON_STATE1 b)
  (Tuple2 enum_t_AUTOMATON_STATE1 b (t2tb4 x) y) f)
  (and (mem1 x s) (mem b y t))))
  (forall ((x enum_t_AUTOMATON_STATE) (y1 uni) (y2 uni))
  (=> (sort b y1)
  (=> (sort b y2)
  (=>
  (and (mem (tuple21 enum_t_AUTOMATON_STATE1 b)
  (Tuple2 enum_t_AUTOMATON_STATE1 b (t2tb4 x) y1) f) (mem
  (tuple21 enum_t_AUTOMATON_STATE1 b)
  (Tuple2 enum_t_AUTOMATON_STATE1 b (t2tb4 x) y2) f)) (= y1 y2)))))))
  (=>
  (and
  (forall ((x enum_t_AUTOMATON_STATE) (y uni))
  (=> (sort b y)
  (=> (mem (tuple21 enum_t_AUTOMATON_STATE1 b)
  (Tuple2 enum_t_AUTOMATON_STATE1 b (t2tb4 x) y) f)
  (and (mem1 x s) (mem b y t)))))
  (forall ((x enum_t_AUTOMATON_STATE) (y1 uni) (y2 uni))
  (=> (sort b y1)
  (=> (sort b y2)
  (=>
  (and (mem (tuple21 enum_t_AUTOMATON_STATE1 b)
  (Tuple2 enum_t_AUTOMATON_STATE1 b (t2tb4 x) y1) f) (mem
  (tuple21 enum_t_AUTOMATON_STATE1 b)
  (Tuple2 enum_t_AUTOMATON_STATE1 b (t2tb4 x) y2) f)) (= y1 y2)))))) (mem
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 b)) f
  (infix_plmngt b enum_t_AUTOMATON_STATE1 (t2tb2 s) t)))))))

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
  (forall ((f uni) (s (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (t uni) (x (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (y uni))
  (=> (mem
  (set1
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  b)) f
  (infix_plmngt b
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s)
  t))
  (=> (mem
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  b)
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) b
  (t2tb1 x) y) f) (mem3 x s))))))

;; domain_function
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (t uni) (x (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (y uni))
  (=> (mem
  (set1
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)) f
  (infix_plmngt b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 s) t))
  (=> (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b
  (t2tb3 x) y) f) (mem2 x s))))))

;; domain_function
  (assert
  (forall ((f (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s (set enum_t_AUTOMATON_STATE)) (t (set enum_t_AUTOMATON_STATE))
  (x enum_t_AUTOMATON_STATE) (y enum_t_AUTOMATON_STATE))
  (=> (mem3 f
  (tb2t
  (infix_plmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 t)))) (=> (mem2 (Tuple21 x y) f) (mem1 x s)))))

;; domain_function
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set enum_t_AUTOMATON_STATE)) (t uni)
  (x enum_t_AUTOMATON_STATE) (y uni))
  (=> (mem (set1 (tuple21 enum_t_AUTOMATON_STATE1 b)) f
  (infix_plmngt b enum_t_AUTOMATON_STATE1 (t2tb2 s) t))
  (=> (mem (tuple21 enum_t_AUTOMATON_STATE1 b)
  (Tuple2 enum_t_AUTOMATON_STATE1 b (t2tb4 x) y) f) (mem1 x s))))))

;; domain_function
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni) (x uni) (y uni))
  (=> (mem (set1 (tuple21 a b)) f (infix_plmngt b a s t))
  (=> (mem (tuple21 a b) (Tuple2 a b x y) f) (mem a x s))))))

;; range_function
  (assert
  (forall ((a ty))
  (forall ((f uni) (s uni) (t (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (x uni) (y (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (=> (mem
  (set1
  (tuple21 a
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))) f
  (infix_plmngt
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) a s
  (t2tb t)))
  (=> (mem
  (tuple21 a
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 a (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  x (t2tb1 y)) f) (mem3 y t))))))

;; range_function
  (assert
  (forall ((a ty))
  (forall ((f uni) (s uni) (t (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (x uni) (y (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))
  (=> (mem
  (set1
  (tuple21 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))) f
  (infix_plmngt (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) a s
  (t2tb1 t)))
  (=> (mem
  (tuple21 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) x
  (t2tb3 y)) f) (mem2 y t))))))

;; range_function
  (assert
  (forall ((a ty))
  (forall ((f uni) (s uni) (t (set enum_t_AUTOMATON_STATE)) (x uni)
  (y enum_t_AUTOMATON_STATE))
  (=> (mem (set1 (tuple21 a enum_t_AUTOMATON_STATE1)) f
  (infix_plmngt enum_t_AUTOMATON_STATE1 a s (t2tb2 t)))
  (=> (mem (tuple21 a enum_t_AUTOMATON_STATE1)
  (Tuple2 a enum_t_AUTOMATON_STATE1 x (t2tb4 y)) f) (mem1 y t))))))

;; range_function
  (assert
  (forall ((f (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s (set enum_t_AUTOMATON_STATE)) (t (set enum_t_AUTOMATON_STATE))
  (x enum_t_AUTOMATON_STATE) (y enum_t_AUTOMATON_STATE))
  (=> (mem3 f
  (tb2t
  (infix_plmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 t)))) (=> (mem2 (Tuple21 x y) f) (mem1 y t)))))

;; range_function
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni) (x uni) (y uni))
  (=> (mem (set1 (tuple21 a b)) f (infix_plmngt b a s t))
  (=> (mem (tuple21 a b) (Tuple2 a b x y) f) (mem b y t))))))

;; function_extend_range
  (assert
  (forall ((f (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s (set enum_t_AUTOMATON_STATE)) (t (set enum_t_AUTOMATON_STATE))
  (u (set enum_t_AUTOMATON_STATE)))
  (=> (subset enum_t_AUTOMATON_STATE1 (t2tb2 t) (t2tb2 u))
  (=> (mem3 f
  (tb2t
  (infix_plmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 t)))) (mem3 f
  (tb2t
  (infix_plmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 u))))))))

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
  (forall ((f uni) (s uni) (t (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (u (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))))
  (=> (subset
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb u)
  (t2tb t))
  (=> (mem
  (set1
  (tuple21 a
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))) f
  (infix_plmngt
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) a s
  (t2tb t)))
  (=>
  (forall ((x uni) (y (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (=> (sort a x)
  (=> (mem
  (tuple21 a
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 a (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  x (t2tb1 y)) f) (mem3 y u)))) (mem
  (set1
  (tuple21 a
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))) f
  (infix_plmngt
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) a s
  (t2tb u)))))))))

;; function_reduce_range
  (assert
  (forall ((a ty))
  (forall ((f uni) (s uni) (t (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (u (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (=> (subset (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 u) (t2tb1 t))
  (=> (mem
  (set1
  (tuple21 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))) f
  (infix_plmngt (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) a s
  (t2tb1 t)))
  (=>
  (forall ((x uni) (y (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))
  (=> (sort a x)
  (=> (mem
  (tuple21 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) x
  (t2tb3 y)) f) (mem2 y u)))) (mem
  (set1
  (tuple21 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))) f
  (infix_plmngt (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) a s
  (t2tb1 u)))))))))

;; function_reduce_range
  (assert
  (forall ((a ty))
  (forall ((f uni) (s uni) (t (set enum_t_AUTOMATON_STATE))
  (u (set enum_t_AUTOMATON_STATE)))
  (=> (subset enum_t_AUTOMATON_STATE1 (t2tb2 u) (t2tb2 t))
  (=> (mem (set1 (tuple21 a enum_t_AUTOMATON_STATE1)) f
  (infix_plmngt enum_t_AUTOMATON_STATE1 a s (t2tb2 t)))
  (=>
  (forall ((x uni) (y enum_t_AUTOMATON_STATE))
  (=> (sort a x)
  (=> (mem (tuple21 a enum_t_AUTOMATON_STATE1)
  (Tuple2 a enum_t_AUTOMATON_STATE1 x (t2tb4 y)) f) (mem1 y u)))) (mem
  (set1 (tuple21 a enum_t_AUTOMATON_STATE1)) f
  (infix_plmngt enum_t_AUTOMATON_STATE1 a s (t2tb2 u)))))))))

;; function_reduce_range
  (assert
  (forall ((f (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s (set enum_t_AUTOMATON_STATE)) (t (set enum_t_AUTOMATON_STATE))
  (u (set enum_t_AUTOMATON_STATE)))
  (=> (subset enum_t_AUTOMATON_STATE1 (t2tb2 u) (t2tb2 t))
  (=> (mem3 f
  (tb2t
  (infix_plmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 t))))
  (=>
  (forall ((x enum_t_AUTOMATON_STATE) (y enum_t_AUTOMATON_STATE))
  (=> (mem2 (Tuple21 x y) f) (mem1 y u))) (mem3 f
  (tb2t
  (infix_plmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 u)))))))))

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
  (forall ((r (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (forall ((x enum_t_AUTOMATON_STATE) (y enum_t_AUTOMATON_STATE))
  (= (mem2 (Tuple21 y x)
  (tb2t1 (inverse enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb1 r))))
  (mem2 (Tuple21 x y) r)))))

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
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (and
  (=> (mem3 x
  (tb2t
  (dom b (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) r)))
  (exists ((y uni))
  (and (sort b y) (mem
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  b)
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) b
  (t2tb1 x) y) r))))
  (=>
  (exists ((y uni)) (mem
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  b)
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) b
  (t2tb1 x) y) r)) (mem3 x
  (tb2t
  (dom b (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) r)))))))))

;; dom_def
  (assert
  (forall ((b ty))
  (forall ((r uni))
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (and
  (=> (mem2 x
  (tb2t1 (dom b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) r)))
  (exists ((y uni))
  (and (sort b y) (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b
  (t2tb3 x) y) r))))
  (=>
  (exists ((y uni)) (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b
  (t2tb3 x) y) r)) (mem2 x
  (tb2t1 (dom b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) r)))))))))

;; dom_def
  (assert
  (forall ((r (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (forall ((x enum_t_AUTOMATON_STATE))
  (= (mem1 x
  (tb2t2 (dom enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb1 r))))
  (exists ((y enum_t_AUTOMATON_STATE)) (mem2 (Tuple21 x y) r))))))

;; dom_def
  (assert
  (forall ((b ty))
  (forall ((r uni))
  (forall ((x enum_t_AUTOMATON_STATE))
  (and
  (=> (mem1 x (tb2t2 (dom b enum_t_AUTOMATON_STATE1 r)))
  (exists ((y uni))
  (and (sort b y) (mem (tuple21 enum_t_AUTOMATON_STATE1 b)
  (Tuple2 enum_t_AUTOMATON_STATE1 b (t2tb4 x) y) r))))
  (=>
  (exists ((y uni)) (mem (tuple21 enum_t_AUTOMATON_STATE1 b)
  (Tuple2 enum_t_AUTOMATON_STATE1 b (t2tb4 x) y) r)) (mem1 x
  (tb2t2 (dom b enum_t_AUTOMATON_STATE1 r)))))))))

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
  (forall ((y (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (and
  (=> (mem3 y
  (tb2t
  (ran (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) a r)))
  (exists ((x uni))
  (and (sort a x) (mem
  (tuple21 a
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 a (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  x (t2tb1 y)) r))))
  (=>
  (exists ((x uni)) (mem
  (tuple21 a
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 a (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  x (t2tb1 y)) r)) (mem3 y
  (tb2t
  (ran (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) a r)))))))))

;; ran_def
  (assert
  (forall ((a ty))
  (forall ((r uni))
  (forall ((y (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (and
  (=> (mem2 y
  (tb2t1 (ran (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) a r)))
  (exists ((x uni))
  (and (sort a x) (mem
  (tuple21 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) x
  (t2tb3 y)) r))))
  (=>
  (exists ((x uni)) (mem
  (tuple21 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) x
  (t2tb3 y)) r)) (mem2 y
  (tb2t1 (ran (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) a r)))))))))

;; ran_def
  (assert
  (forall ((a ty))
  (forall ((r uni))
  (forall ((y enum_t_AUTOMATON_STATE))
  (and
  (=> (mem1 y (tb2t2 (ran enum_t_AUTOMATON_STATE1 a r)))
  (exists ((x uni))
  (and (sort a x) (mem (tuple21 a enum_t_AUTOMATON_STATE1)
  (Tuple2 a enum_t_AUTOMATON_STATE1 x (t2tb4 y)) r))))
  (=>
  (exists ((x uni)) (mem (tuple21 a enum_t_AUTOMATON_STATE1)
  (Tuple2 a enum_t_AUTOMATON_STATE1 x (t2tb4 y)) r)) (mem1 y
  (tb2t2 (ran enum_t_AUTOMATON_STATE1 a r)))))))))

;; ran_def
  (assert
  (forall ((r (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (forall ((y enum_t_AUTOMATON_STATE))
  (= (mem1 y
  (tb2t2 (ran enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb1 r))))
  (exists ((x enum_t_AUTOMATON_STATE)) (mem2 (Tuple21 x y) r))))))

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
     (dom b (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (empty
     (tuple21
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) b)))) 
  empty3)))

;; dom_empty
  (assert
  (forall ((b ty))
  (= (tb2t1
     (dom b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (empty
     (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)))) 
  empty2)))

;; dom_empty
  (assert
  (= (tb2t2
     (dom enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb1 empty2))) 
  empty1))

;; dom_empty
  (assert
  (forall ((b ty))
  (= (tb2t2
     (dom b enum_t_AUTOMATON_STATE1
     (empty (tuple21 enum_t_AUTOMATON_STATE1 b)))) empty1)))

;; dom_empty
  (assert
  (forall ((a ty) (b ty)) (= (dom b a (empty (tuple21 a b))) (empty a))))

;; dom_add
  (assert
  (forall ((b ty))
  (forall ((f uni) (x (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (y uni))
  (= (tb2t
     (dom b (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (add
     (tuple21
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) b)
     (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     b (t2tb1 x) y) f))) (add3 x
                         (tb2t
                         (dom b
                         (set1
                         (tuple21 enum_t_AUTOMATON_STATE1
                         enum_t_AUTOMATON_STATE1)) f)))))))

;; dom_add
  (assert
  (forall ((b ty))
  (forall ((f uni) (x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (y uni))
  (= (tb2t1
     (dom b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (add
     (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)
     (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b
     (t2tb3 x) y) f))) (add2 x
                       (tb2t1
                       (dom b
                       (tuple21 enum_t_AUTOMATON_STATE1
                       enum_t_AUTOMATON_STATE1) f)))))))

;; dom_add
  (assert
  (forall ((f (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (x enum_t_AUTOMATON_STATE) (y enum_t_AUTOMATON_STATE))
  (= (tb2t2
     (dom enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
     (t2tb1 (add2 (Tuple21 x y) f)))) (add1 x
                                      (tb2t2
                                      (dom enum_t_AUTOMATON_STATE1
                                      enum_t_AUTOMATON_STATE1 (t2tb1 f)))))))

;; dom_add
  (assert
  (forall ((b ty))
  (forall ((f uni) (x enum_t_AUTOMATON_STATE) (y uni))
  (= (tb2t2
     (dom b enum_t_AUTOMATON_STATE1
     (add (tuple21 enum_t_AUTOMATON_STATE1 b)
     (Tuple2 enum_t_AUTOMATON_STATE1 b (t2tb4 x) y) f))) (add1 x
                                                         (tb2t2
                                                         (dom b
                                                         enum_t_AUTOMATON_STATE1
                                                         f)))))))

;; dom_add
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (x uni) (y uni))
  (= (dom b a (add (tuple21 a b) (Tuple2 a b x y) f)) (add a x (dom b a f))))))

;; dom_singleton
  (assert
  (forall ((b ty))
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (y uni))
  (= (tb2t
     (dom b (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (add
     (tuple21
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) b)
     (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     b (t2tb1 x) y)
     (empty
     (tuple21
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) b))))) 
  (add3 x empty3)))))

;; dom_singleton
  (assert
  (forall ((b ty))
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (y uni))
  (= (tb2t1
     (dom b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (add
     (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)
     (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b
     (t2tb3 x) y)
     (empty
     (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b))))) 
  (add2 x empty2)))))

;; dom_singleton
  (assert
  (forall ((x enum_t_AUTOMATON_STATE) (y enum_t_AUTOMATON_STATE))
  (= (tb2t2
     (dom enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
     (t2tb1 (add2 (Tuple21 x y) empty2)))) (add1 x empty1))))

;; dom_singleton
  (assert
  (forall ((b ty))
  (forall ((x enum_t_AUTOMATON_STATE) (y uni))
  (= (tb2t2
     (dom b enum_t_AUTOMATON_STATE1
     (add (tuple21 enum_t_AUTOMATON_STATE1 b)
     (Tuple2 enum_t_AUTOMATON_STATE1 b (t2tb4 x) y)
     (empty (tuple21 enum_t_AUTOMATON_STATE1 b))))) (add1 x empty1)))))

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
  (forall ((f (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s (set enum_t_AUTOMATON_STATE)) (t (set enum_t_AUTOMATON_STATE)))
  (= (mem3 f
  (tb2t
  (infix_mnmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 t))))
  (and (mem3 f
  (tb2t
  (infix_plmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 t))))
  (= (tb2t2 (dom enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb1 f))) s)))))

;; mem_total_functions
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni))
  (=> (sort (set1 a) s)
  (= (mem (set1 (tuple21 a b)) f (infix_mnmngt b a s t))
  (and (mem (set1 (tuple21 a b)) f (infix_plmngt b a s t)) (= (dom b a f) s)))))))

;; total_function_is_function
  (assert
  (forall ((f (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s (set enum_t_AUTOMATON_STATE)) (t (set enum_t_AUTOMATON_STATE)))
  (! (=> (mem3 f
     (tb2t
     (infix_mnmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
     (t2tb2 t)))) (mem3 f
     (tb2t
     (infix_plmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
     (t2tb2 t))))) :pattern ((mem3
  f
  (tb2t
  (infix_mnmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 t))))) )))

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
  (forall ((s uni) (t (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (x uni) (y (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (=> (and (mem a x s) (mem3 y t)) (mem
  (set1
  (tuple21 a
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))))
  (add
  (tuple21 a
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 a (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  x (t2tb1 y))
  (empty
  (tuple21 a
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))))
  (infix_plmngt
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) a s
  (t2tb t)))))))

;; singleton_is_partial_function
  (assert
  (forall ((a ty))
  (forall ((s uni) (t (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (x uni) (y (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))
  (=> (and (mem a x s) (mem2 y t)) (mem
  (set1
  (tuple21 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (add (tuple21 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) x
  (t2tb3 y))
  (empty
  (tuple21 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))))
  (infix_plmngt (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) a s
  (t2tb1 t)))))))

;; singleton_is_partial_function
  (assert
  (forall ((a ty))
  (forall ((s uni) (t (set enum_t_AUTOMATON_STATE)) (x uni)
  (y enum_t_AUTOMATON_STATE))
  (=> (and (mem a x s) (mem1 y t)) (mem
  (set1 (tuple21 a enum_t_AUTOMATON_STATE1))
  (add (tuple21 a enum_t_AUTOMATON_STATE1)
  (Tuple2 a enum_t_AUTOMATON_STATE1 x (t2tb4 y))
  (empty (tuple21 a enum_t_AUTOMATON_STATE1)))
  (infix_plmngt enum_t_AUTOMATON_STATE1 a s (t2tb2 t)))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (t (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (x (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (y (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (=> (and (mem3 x s) (mem3 y t)) (mem
  (set1
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))))
  (add
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb1 x)
  (t2tb1 y))
  (empty
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))))
  (infix_plmngt
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s)
  (t2tb t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (t (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (x (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (y (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))
  (=> (and (mem3 x s) (mem2 y t)) (mem
  (set1
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (add
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 x)
  (t2tb3 y))
  (empty
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))))
  (infix_plmngt (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s)
  (t2tb1 t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (t (set enum_t_AUTOMATON_STATE))
  (x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (y enum_t_AUTOMATON_STATE))
  (=> (and (mem3 x s) (mem1 y t)) (mem
  (set1
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  enum_t_AUTOMATON_STATE1))
  (add
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  enum_t_AUTOMATON_STATE1)
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  enum_t_AUTOMATON_STATE1 (t2tb1 x) (t2tb4 y))
  (empty
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  enum_t_AUTOMATON_STATE1)))
  (infix_plmngt enum_t_AUTOMATON_STATE1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s)
  (t2tb2 t))))))

;; singleton_is_partial_function
  (assert
  (forall ((b ty))
  (forall ((s (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (t uni) (x (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (y uni))
  (=> (and (mem3 x s) (mem b y t)) (mem
  (set1
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  b))
  (add
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  b)
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) b
  (t2tb1 x) y)
  (empty
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  b)))
  (infix_plmngt b
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s)
  t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (t (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (y (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (=> (and (mem2 x s) (mem3 y t)) (mem
  (set1
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))))
  (add
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb3 x)
  (t2tb1 y))
  (empty
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))))
  (infix_plmngt
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 s)
  (t2tb t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (t (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (y (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (=> (and (mem2 x s) (mem2 y t)) (mem
  (set1
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (add
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb3 x)
  (t2tb3 y))
  (empty
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))))
  (infix_plmngt (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 s)
  (t2tb1 t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (t (set enum_t_AUTOMATON_STATE)) (x (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (y enum_t_AUTOMATON_STATE))
  (=> (and (mem2 x s) (mem1 y t)) (mem
  (set1
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  enum_t_AUTOMATON_STATE1))
  (add
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  enum_t_AUTOMATON_STATE1)
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  enum_t_AUTOMATON_STATE1 (t2tb3 x) (t2tb4 y))
  (empty
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  enum_t_AUTOMATON_STATE1)))
  (infix_plmngt enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 s)
  (t2tb2 t))))))

;; singleton_is_partial_function
  (assert
  (forall ((b ty))
  (forall ((s (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (t uni) (x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)) (y uni))
  (=> (and (mem2 x s) (mem b y t)) (mem
  (set1
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b))
  (add (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b
  (t2tb3 x) y)
  (empty
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)))
  (infix_plmngt b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 s) t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set enum_t_AUTOMATON_STATE))
  (t (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (x enum_t_AUTOMATON_STATE) (y (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (=> (and (mem1 x s) (mem3 y t)) (mem
  (set1
  (tuple21 enum_t_AUTOMATON_STATE1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))))
  (add
  (tuple21 enum_t_AUTOMATON_STATE1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 enum_t_AUTOMATON_STATE1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb4 x)
  (t2tb1 y))
  (empty
  (tuple21 enum_t_AUTOMATON_STATE1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))))
  (infix_plmngt
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  enum_t_AUTOMATON_STATE1 (t2tb2 s) (t2tb t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set enum_t_AUTOMATON_STATE))
  (t (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (x enum_t_AUTOMATON_STATE) (y (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))
  (=> (and (mem1 x s) (mem2 y t)) (mem
  (set1
  (tuple21 enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (add
  (tuple21 enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb4 x)
  (t2tb3 y))
  (empty
  (tuple21 enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))))
  (infix_plmngt (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  enum_t_AUTOMATON_STATE1 (t2tb2 s) (t2tb1 t))))))

;; singleton_is_partial_function
  (assert
  (forall ((s (set enum_t_AUTOMATON_STATE)) (t (set enum_t_AUTOMATON_STATE))
  (x enum_t_AUTOMATON_STATE) (y enum_t_AUTOMATON_STATE))
  (=> (and (mem1 x s) (mem1 y t)) (mem3 (add2 (Tuple21 x y) empty2)
  (tb2t
  (infix_plmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 t)))))))

;; singleton_is_partial_function
  (assert
  (forall ((b ty))
  (forall ((s (set enum_t_AUTOMATON_STATE)) (t uni)
  (x enum_t_AUTOMATON_STATE) (y uni))
  (=> (and (mem1 x s) (mem b y t)) (mem
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 b))
  (add (tuple21 enum_t_AUTOMATON_STATE1 b)
  (Tuple2 enum_t_AUTOMATON_STATE1 b (t2tb4 x) y)
  (empty (tuple21 enum_t_AUTOMATON_STATE1 b)))
  (infix_plmngt b enum_t_AUTOMATON_STATE1 (t2tb2 s) t))))))

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
  (forall ((x uni) (y (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (! (mem
  (set1
  (tuple21 a
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))))
  (add
  (tuple21 a
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 a (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  x (t2tb1 y))
  (empty
  (tuple21 a
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))))
  (infix_mnmngt
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) a
  (add a x (empty a)) (t2tb (add3 y empty3)))) :pattern ((add
                                                         (tuple21 a
                                                         (set1
                                                         (tuple21
                                                         enum_t_AUTOMATON_STATE1
                                                         enum_t_AUTOMATON_STATE1)))
                                                         (Tuple2 a
                                                         (set1
                                                         (tuple21
                                                         enum_t_AUTOMATON_STATE1
                                                         enum_t_AUTOMATON_STATE1))
                                                         x (t2tb1 y))
                                                         (empty
                                                         (tuple21 a
                                                         (set1
                                                         (tuple21
                                                         enum_t_AUTOMATON_STATE1
                                                         enum_t_AUTOMATON_STATE1)))))) ))))

;; singleton_is_function
  (assert
  (forall ((a ty))
  (forall ((x uni) (y (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (! (mem
  (set1
  (tuple21 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (add (tuple21 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) x
  (t2tb3 y))
  (empty
  (tuple21 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))))
  (infix_mnmngt (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) a
  (add a x (empty a)) (t2tb1 (add2 y empty2)))) :pattern ((add
                                                          (tuple21 a
                                                          (tuple21
                                                          enum_t_AUTOMATON_STATE1
                                                          enum_t_AUTOMATON_STATE1))
                                                          (Tuple2 a
                                                          (tuple21
                                                          enum_t_AUTOMATON_STATE1
                                                          enum_t_AUTOMATON_STATE1)
                                                          x (t2tb3 y))
                                                          (empty
                                                          (tuple21 a
                                                          (tuple21
                                                          enum_t_AUTOMATON_STATE1
                                                          enum_t_AUTOMATON_STATE1))))) ))))

;; singleton_is_function
  (assert
  (forall ((a ty))
  (forall ((x uni) (y enum_t_AUTOMATON_STATE)) (! (mem
  (set1 (tuple21 a enum_t_AUTOMATON_STATE1))
  (add (tuple21 a enum_t_AUTOMATON_STATE1)
  (Tuple2 a enum_t_AUTOMATON_STATE1 x (t2tb4 y))
  (empty (tuple21 a enum_t_AUTOMATON_STATE1)))
  (infix_mnmngt enum_t_AUTOMATON_STATE1 a (add a x (empty a))
  (t2tb2 (add1 y empty1)))) :pattern ((add
                                      (tuple21 a enum_t_AUTOMATON_STATE1)
                                      (Tuple2 a enum_t_AUTOMATON_STATE1 x
                                      (t2tb4 y))
                                      (empty
                                      (tuple21 a enum_t_AUTOMATON_STATE1)))) ))))

;; singleton_is_function
  (assert
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (y (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))) (! (mem
  (set1
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))))
  (add
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb1 x)
  (t2tb1 y))
  (empty
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))))
  (infix_mnmngt
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (t2tb (add3 x empty3)) (t2tb (add3 y empty3)))) :pattern ((tb2t12
                                                            (add
                                                            (tuple21
                                                            (set1
                                                            (tuple21
                                                            enum_t_AUTOMATON_STATE1
                                                            enum_t_AUTOMATON_STATE1))
                                                            (set1
                                                            (tuple21
                                                            enum_t_AUTOMATON_STATE1
                                                            enum_t_AUTOMATON_STATE1)))
                                                            (Tuple2
                                                            (set1
                                                            (tuple21
                                                            enum_t_AUTOMATON_STATE1
                                                            enum_t_AUTOMATON_STATE1))
                                                            (set1
                                                            (tuple21
                                                            enum_t_AUTOMATON_STATE1
                                                            enum_t_AUTOMATON_STATE1))
                                                            (t2tb1 x)
                                                            (t2tb1 y))
                                                            (empty
                                                            (tuple21
                                                            (set1
                                                            (tuple21
                                                            enum_t_AUTOMATON_STATE1
                                                            enum_t_AUTOMATON_STATE1))
                                                            (set1
                                                            (tuple21
                                                            enum_t_AUTOMATON_STATE1
                                                            enum_t_AUTOMATON_STATE1))))))) )))

;; singleton_is_function
  (assert
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (y (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))) (! (mem
  (set1
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (add
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 x)
  (t2tb3 y))
  (empty
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))))
  (infix_mnmngt (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (t2tb (add3 x empty3)) (t2tb1 (add2 y empty2)))) :pattern ((tb2t15
                                                             (add
                                                             (tuple21
                                                             (set1
                                                             (tuple21
                                                             enum_t_AUTOMATON_STATE1
                                                             enum_t_AUTOMATON_STATE1))
                                                             (tuple21
                                                             enum_t_AUTOMATON_STATE1
                                                             enum_t_AUTOMATON_STATE1))
                                                             (Tuple2
                                                             (set1
                                                             (tuple21
                                                             enum_t_AUTOMATON_STATE1
                                                             enum_t_AUTOMATON_STATE1))
                                                             (tuple21
                                                             enum_t_AUTOMATON_STATE1
                                                             enum_t_AUTOMATON_STATE1)
                                                             (t2tb1 x)
                                                             (t2tb3 y))
                                                             (empty
                                                             (tuple21
                                                             (set1
                                                             (tuple21
                                                             enum_t_AUTOMATON_STATE1
                                                             enum_t_AUTOMATON_STATE1))
                                                             (tuple21
                                                             enum_t_AUTOMATON_STATE1
                                                             enum_t_AUTOMATON_STATE1)))))) )))

;; singleton_is_function
  (assert
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (y enum_t_AUTOMATON_STATE)) (! (mem
  (set1
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  enum_t_AUTOMATON_STATE1))
  (add
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  enum_t_AUTOMATON_STATE1)
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  enum_t_AUTOMATON_STATE1 (t2tb1 x) (t2tb4 y))
  (empty
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  enum_t_AUTOMATON_STATE1)))
  (infix_mnmngt enum_t_AUTOMATON_STATE1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (t2tb (add3 x empty3)) (t2tb2 (add1 y empty1)))) :pattern ((tb2t18
                                                             (add
                                                             (tuple21
                                                             (set1
                                                             (tuple21
                                                             enum_t_AUTOMATON_STATE1
                                                             enum_t_AUTOMATON_STATE1))
                                                             enum_t_AUTOMATON_STATE1)
                                                             (Tuple2
                                                             (set1
                                                             (tuple21
                                                             enum_t_AUTOMATON_STATE1
                                                             enum_t_AUTOMATON_STATE1))
                                                             enum_t_AUTOMATON_STATE1
                                                             (t2tb1 x)
                                                             (t2tb4 y))
                                                             (empty
                                                             (tuple21
                                                             (set1
                                                             (tuple21
                                                             enum_t_AUTOMATON_STATE1
                                                             enum_t_AUTOMATON_STATE1))
                                                             enum_t_AUTOMATON_STATE1))))) )))

;; singleton_is_function
  (assert
  (forall ((b ty))
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (y uni)) (! (mem
  (set1
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  b))
  (add
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  b)
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) b
  (t2tb1 x) y)
  (empty
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  b)))
  (infix_mnmngt b
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (t2tb (add3 x empty3)) (add b y (empty b)))) :pattern ((add
                                                         (tuple21
                                                         (set1
                                                         (tuple21
                                                         enum_t_AUTOMATON_STATE1
                                                         enum_t_AUTOMATON_STATE1))
                                                         b)
                                                         (Tuple2
                                                         (set1
                                                         (tuple21
                                                         enum_t_AUTOMATON_STATE1
                                                         enum_t_AUTOMATON_STATE1))
                                                         b (t2tb1 x) y)
                                                         (empty
                                                         (tuple21
                                                         (set1
                                                         (tuple21
                                                         enum_t_AUTOMATON_STATE1
                                                         enum_t_AUTOMATON_STATE1))
                                                         b)))) ))))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (y (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))) (! (mem
  (set1
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))))
  (add
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb3 x)
  (t2tb1 y))
  (empty
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))))
  (infix_mnmngt
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 (add2 x empty2)) (t2tb (add3 y empty3)))) :pattern ((tb2t20
                                                             (add
                                                             (tuple21
                                                             (tuple21
                                                             enum_t_AUTOMATON_STATE1
                                                             enum_t_AUTOMATON_STATE1)
                                                             (set1
                                                             (tuple21
                                                             enum_t_AUTOMATON_STATE1
                                                             enum_t_AUTOMATON_STATE1)))
                                                             (Tuple2
                                                             (tuple21
                                                             enum_t_AUTOMATON_STATE1
                                                             enum_t_AUTOMATON_STATE1)
                                                             (set1
                                                             (tuple21
                                                             enum_t_AUTOMATON_STATE1
                                                             enum_t_AUTOMATON_STATE1))
                                                             (t2tb3 x)
                                                             (t2tb1 y))
                                                             (empty
                                                             (tuple21
                                                             (tuple21
                                                             enum_t_AUTOMATON_STATE1
                                                             enum_t_AUTOMATON_STATE1)
                                                             (set1
                                                             (tuple21
                                                             enum_t_AUTOMATON_STATE1
                                                             enum_t_AUTOMATON_STATE1))))))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (y (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))) (! (mem
  (set1
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (add
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb3 x)
  (t2tb3 y))
  (empty
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))))
  (infix_mnmngt (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 (add2 x empty2)) (t2tb1 (add2 y empty2)))) :pattern ((tb2t24
                                                              (add
                                                              (tuple21
                                                              (tuple21
                                                              enum_t_AUTOMATON_STATE1
                                                              enum_t_AUTOMATON_STATE1)
                                                              (tuple21
                                                              enum_t_AUTOMATON_STATE1
                                                              enum_t_AUTOMATON_STATE1))
                                                              (Tuple2
                                                              (tuple21
                                                              enum_t_AUTOMATON_STATE1
                                                              enum_t_AUTOMATON_STATE1)
                                                              (tuple21
                                                              enum_t_AUTOMATON_STATE1
                                                              enum_t_AUTOMATON_STATE1)
                                                              (t2tb3 x)
                                                              (t2tb3 y))
                                                              (empty
                                                              (tuple21
                                                              (tuple21
                                                              enum_t_AUTOMATON_STATE1
                                                              enum_t_AUTOMATON_STATE1)
                                                              (tuple21
                                                              enum_t_AUTOMATON_STATE1
                                                              enum_t_AUTOMATON_STATE1)))))) )))

;; singleton_is_function
  (assert
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (y enum_t_AUTOMATON_STATE)) (! (mem
  (set1
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  enum_t_AUTOMATON_STATE1))
  (add
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  enum_t_AUTOMATON_STATE1)
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  enum_t_AUTOMATON_STATE1 (t2tb3 x) (t2tb4 y))
  (empty
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  enum_t_AUTOMATON_STATE1)))
  (infix_mnmngt enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 (add2 x empty2)) (t2tb2 (add1 y empty1)))) :pattern ((tb2t27
                                                              (add
                                                              (tuple21
                                                              (tuple21
                                                              enum_t_AUTOMATON_STATE1
                                                              enum_t_AUTOMATON_STATE1)
                                                              enum_t_AUTOMATON_STATE1)
                                                              (Tuple2
                                                              (tuple21
                                                              enum_t_AUTOMATON_STATE1
                                                              enum_t_AUTOMATON_STATE1)
                                                              enum_t_AUTOMATON_STATE1
                                                              (t2tb3 x)
                                                              (t2tb4 y))
                                                              (empty
                                                              (tuple21
                                                              (tuple21
                                                              enum_t_AUTOMATON_STATE1
                                                              enum_t_AUTOMATON_STATE1)
                                                              enum_t_AUTOMATON_STATE1))))) )))

;; singleton_is_function
  (assert
  (forall ((b ty))
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (y uni)) (! (mem
  (set1
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b))
  (add (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b
  (t2tb3 x) y)
  (empty
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)))
  (infix_mnmngt b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 (add2 x empty2)) (add b y (empty b)))) :pattern ((add
                                                          (tuple21
                                                          (tuple21
                                                          enum_t_AUTOMATON_STATE1
                                                          enum_t_AUTOMATON_STATE1)
                                                          b)
                                                          (Tuple2
                                                          (tuple21
                                                          enum_t_AUTOMATON_STATE1
                                                          enum_t_AUTOMATON_STATE1)
                                                          b (t2tb3 x) y)
                                                          (empty
                                                          (tuple21
                                                          (tuple21
                                                          enum_t_AUTOMATON_STATE1
                                                          enum_t_AUTOMATON_STATE1)
                                                          b)))) ))))

;; singleton_is_function
  (assert
  (forall ((x enum_t_AUTOMATON_STATE) (y (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (! (mem
  (set1
  (tuple21 enum_t_AUTOMATON_STATE1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))))
  (add
  (tuple21 enum_t_AUTOMATON_STATE1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 enum_t_AUTOMATON_STATE1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb4 x)
  (t2tb1 y))
  (empty
  (tuple21 enum_t_AUTOMATON_STATE1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))))
  (infix_mnmngt
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  enum_t_AUTOMATON_STATE1 (t2tb2 (add1 x empty1)) (t2tb (add3 y empty3)))) :pattern (
  (tb2t30
  (add
  (tuple21 enum_t_AUTOMATON_STATE1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 enum_t_AUTOMATON_STATE1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb4 x)
  (t2tb1 y))
  (empty
  (tuple21 enum_t_AUTOMATON_STATE1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))))))) )))

;; singleton_is_function
  (assert
  (forall ((x enum_t_AUTOMATON_STATE) (y (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (! (mem
  (set1
  (tuple21 enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (add
  (tuple21 enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb4 x)
  (t2tb3 y))
  (empty
  (tuple21 enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))))
  (infix_mnmngt (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  enum_t_AUTOMATON_STATE1 (t2tb2 (add1 x empty1)) (t2tb1 (add2 y empty2)))) :pattern (
  (tb2t34
  (add
  (tuple21 enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb4 x)
  (t2tb3 y))
  (empty
  (tuple21 enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))))) )))

;; singleton_is_function
  (assert
  (forall ((x enum_t_AUTOMATON_STATE) (y enum_t_AUTOMATON_STATE)) (! (mem3
  (add2 (Tuple21 x y) empty2)
  (tb2t
  (infix_mnmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
  (t2tb2 (add1 x empty1)) (t2tb2 (add1 y empty1))))) :pattern ((add2
                                                               (Tuple21 x y)
                                                               empty2)) )))

;; singleton_is_function
  (assert
  (forall ((b ty))
  (forall ((x enum_t_AUTOMATON_STATE) (y uni)) (! (mem
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 b))
  (add (tuple21 enum_t_AUTOMATON_STATE1 b)
  (Tuple2 enum_t_AUTOMATON_STATE1 b (t2tb4 x) y)
  (empty (tuple21 enum_t_AUTOMATON_STATE1 b)))
  (infix_mnmngt b enum_t_AUTOMATON_STATE1 (t2tb2 (add1 x empty1))
  (add b y (empty b)))) :pattern ((add (tuple21 enum_t_AUTOMATON_STATE1 b)
                                  (Tuple2 enum_t_AUTOMATON_STATE1 b (t2tb4 x)
                                  y)
                                  (empty (tuple21 enum_t_AUTOMATON_STATE1 b)))) ))))

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
  (forall ((f uni) (s (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (t uni) (a (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (=>
  (and (mem
  (set1
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  b)) f
  (infix_plmngt b
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s)
  t)) (mem3 a
  (tb2t
  (dom b (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) f))))
  (mem
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  b)
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) b
  (t2tb1 a)
  (apply b (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) f
  (t2tb1 a))) f)))))

;; apply_def0
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (t uni) (a (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))
  (=>
  (and (mem
  (set1
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)) f
  (infix_plmngt b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 s) t)) (mem2 a
  (tb2t1 (dom b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) f))))
  (mem (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b
  (t2tb3 a)
  (apply b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) f
  (t2tb3 a))) f)))))

;; apply_def0
  (assert
  (forall ((f (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s (set enum_t_AUTOMATON_STATE)) (t (set enum_t_AUTOMATON_STATE))
  (a enum_t_AUTOMATON_STATE))
  (=>
  (and (mem3 f
  (tb2t
  (infix_plmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 t)))) (mem1 a
  (tb2t2 (dom enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb1 f)))))
  (mem2
  (Tuple21 a
  (tb2t4
  (apply enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb1 f) (t2tb4 a))))
  f))))

;; apply_def0
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set enum_t_AUTOMATON_STATE)) (t uni)
  (a enum_t_AUTOMATON_STATE))
  (=>
  (and (mem (set1 (tuple21 enum_t_AUTOMATON_STATE1 b)) f
  (infix_plmngt b enum_t_AUTOMATON_STATE1 (t2tb2 s) t)) (mem1 a
  (tb2t2 (dom b enum_t_AUTOMATON_STATE1 f)))) (mem
  (tuple21 enum_t_AUTOMATON_STATE1 b)
  (Tuple2 enum_t_AUTOMATON_STATE1 b (t2tb4 a)
  (apply b enum_t_AUTOMATON_STATE1 f (t2tb4 a))) f)))))

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
  (forall ((f uni) (s (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (t uni) (a (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (=>
  (and (mem
  (set1
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  b)) f
  (infix_mnmngt b
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s)
  t)) (mem3 a s)) (mem
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  b)
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) b
  (t2tb1 a)
  (apply b (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) f
  (t2tb1 a))) f)))))

;; apply_def1
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (t uni) (a (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))
  (=>
  (and (mem
  (set1
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)) f
  (infix_mnmngt b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 s) t)) (mem2 a s)) (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b
  (t2tb3 a)
  (apply b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) f
  (t2tb3 a))) f)))))

;; apply_def1
  (assert
  (forall ((f (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s (set enum_t_AUTOMATON_STATE)) (t (set enum_t_AUTOMATON_STATE))
  (a enum_t_AUTOMATON_STATE))
  (=>
  (and (mem3 f
  (tb2t
  (infix_mnmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 t)))) (mem1 a s)) (mem2
  (Tuple21 a
  (tb2t4
  (apply enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb1 f) (t2tb4 a))))
  f))))

;; apply_def1
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set enum_t_AUTOMATON_STATE)) (t uni)
  (a enum_t_AUTOMATON_STATE))
  (=>
  (and (mem (set1 (tuple21 enum_t_AUTOMATON_STATE1 b)) f
  (infix_mnmngt b enum_t_AUTOMATON_STATE1 (t2tb2 s) t)) (mem1 a s)) (mem
  (tuple21 enum_t_AUTOMATON_STATE1 b)
  (Tuple2 enum_t_AUTOMATON_STATE1 b (t2tb4 a)
  (apply b enum_t_AUTOMATON_STATE1 f (t2tb4 a))) f)))))

;; apply_def1
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni) (a1 uni))
  (=> (and (mem (set1 (tuple21 a b)) f (infix_mnmngt b a s t)) (mem a a1 s))
  (mem (tuple21 a b) (Tuple2 a b a1 (apply b a f a1)) f)))))

;; apply_def2
  (assert
  (forall ((f (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s (set enum_t_AUTOMATON_STATE)) (t (set enum_t_AUTOMATON_STATE))
  (a enum_t_AUTOMATON_STATE) (b enum_t_AUTOMATON_STATE))
  (=>
  (and (mem3 f
  (tb2t
  (infix_plmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 t)))) (mem2 (Tuple21 a b) f))
  (= (tb2t4
     (apply enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb1 f)
     (t2tb4 a))) b))))

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
  (forall ((x enum_t_AUTOMATON_STATE) (y enum_t_AUTOMATON_STATE))
  (= (tb2t4
     (apply enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
     (t2tb1 (add2 (Tuple21 x y) empty2)) (t2tb4 x))) y)))

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
  (t (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))))
  (! (=>
     (and (mem
     (set1
     (tuple21 a
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))) f
     (infix_plmngt
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) a s
     (t2tb t))) (mem a x
     (dom (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) a
     f))) (mem3
     (tb2t1
     (apply (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     a f x)) t)) :pattern ((mem
  (set1
  (tuple21 a
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))) f
  (infix_plmngt
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) a s
  (t2tb t)))
  (tb2t1
  (apply (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) a f
  x))) ))))

;; apply_range
  (assert
  (forall ((a ty))
  (forall ((x uni) (f uni) (s uni) (t (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (! (=>
     (and (mem
     (set1
     (tuple21 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))) f
     (infix_plmngt (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     a s (t2tb1 t))) (mem a x
     (dom (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) a f)))
     (mem2
     (tb2t3
     (apply (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) a f x))
     t)) :pattern ((mem
  (set1
  (tuple21 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))) f
  (infix_plmngt (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) a s
  (t2tb1 t)))
  (tb2t3
  (apply (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) a f x))) ))))

;; apply_range
  (assert
  (forall ((a ty))
  (forall ((x uni) (f uni) (s uni) (t (set enum_t_AUTOMATON_STATE)))
  (! (=>
     (and (mem (set1 (tuple21 a enum_t_AUTOMATON_STATE1)) f
     (infix_plmngt enum_t_AUTOMATON_STATE1 a s (t2tb2 t))) (mem a x
     (dom enum_t_AUTOMATON_STATE1 a f))) (mem1
     (tb2t4 (apply enum_t_AUTOMATON_STATE1 a f x)) t)) :pattern ((mem
  (set1 (tuple21 a enum_t_AUTOMATON_STATE1)) f
  (infix_plmngt enum_t_AUTOMATON_STATE1 a s (t2tb2 t)))
  (tb2t4 (apply enum_t_AUTOMATON_STATE1 a f x))) ))))

;; apply_range
  (assert
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (f (set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))) (s (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (t (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))))
  (! (=>
     (and (mem
     (set1
     (tuple21
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))))
     (t2tb12 f)
     (infix_plmngt
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb s) (t2tb t))) (mem3 x
     (tb2t
     (dom (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb12 f))))) (mem3
     (tb2t1
     (apply (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb12 f) (t2tb1 x))) t)) :pattern ((mem
  (set1
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))))
  (t2tb12 f)
  (infix_plmngt
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s)
  (t2tb t)))
  (tb2t1
  (apply (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb12 f)
  (t2tb1 x)))) )))

;; apply_range
  (assert
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (f (set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (s (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (t (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (! (=>
     (and (mem
     (set1
     (tuple21
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))) (t2tb15 f)
     (infix_plmngt (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb s) (t2tb1 t))) (mem3 x
     (tb2t
     (dom (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb15 f))))) (mem2
     (tb2t3
     (apply (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb15 f) (t2tb1 x))) t)) :pattern ((mem
  (set1
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))) (t2tb15 f)
  (infix_plmngt (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s)
  (t2tb1 t)))
  (tb2t3
  (apply (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb15 f)
  (t2tb1 x)))) )))

;; apply_range
  (assert
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (f (set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) enum_t_AUTOMATON_STATE)))
  (s (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (t (set enum_t_AUTOMATON_STATE)))
  (! (=>
     (and (mem
     (set1
     (tuple21
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     enum_t_AUTOMATON_STATE1)) (t2tb18 f)
     (infix_plmngt enum_t_AUTOMATON_STATE1
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb s) (t2tb2 t))) (mem3 x
     (tb2t
     (dom enum_t_AUTOMATON_STATE1
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb18 f))))) (mem1
     (tb2t4
     (apply enum_t_AUTOMATON_STATE1
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb18 f) (t2tb1 x))) t)) :pattern ((mem
  (set1
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  enum_t_AUTOMATON_STATE1)) (t2tb18 f)
  (infix_plmngt enum_t_AUTOMATON_STATE1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s)
  (t2tb2 t)))
  (tb2t4
  (apply enum_t_AUTOMATON_STATE1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb18 f)
  (t2tb1 x)))) )))

;; apply_range
  (assert
  (forall ((b ty))
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (f uni) (s (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (t uni))
  (! (=>
     (and (mem
     (set1
     (tuple21
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) b)) f
     (infix_plmngt b
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb s) t)) (mem3 x
     (tb2t
     (dom b (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     f)))) (mem b
     (apply b
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) f
     (t2tb1 x)) t)) :pattern ((mem
  (set1
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  b)) f
  (infix_plmngt b
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s)
  t))
  (apply b (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) f
  (t2tb1 x))) ))))

;; apply_range
  (assert
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (f (set (tuple2 (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)
  (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))))
  (s (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (t (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))))
  (! (=>
     (and (mem
     (set1
     (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))))
     (t2tb20 f)
     (infix_plmngt
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 s)
     (t2tb t))) (mem2 x
     (tb2t1
     (dom (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb20 f)))))
     (mem3
     (tb2t1
     (apply (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb20 f)
     (t2tb3 x))) t)) :pattern ((mem
  (set1
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))))
  (t2tb20 f)
  (infix_plmngt
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 s)
  (t2tb t)))
  (tb2t1
  (apply (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb20 f)
  (t2tb3 x)))) )))

;; apply_range
  (assert
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (f (set (tuple2 (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)
  (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (s (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (t (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (! (=>
     (and (mem
     (set1
     (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))) (t2tb24 f)
     (infix_plmngt (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 s)
     (t2tb1 t))) (mem2 x
     (tb2t1
     (dom (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb24 f)))))
     (mem2
     (tb2t3
     (apply (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb24 f)
     (t2tb3 x))) t)) :pattern ((mem
  (set1
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))) (t2tb24 f)
  (infix_plmngt (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 s)
  (t2tb1 t)))
  (tb2t3
  (apply (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb24 f)
  (t2tb3 x)))) )))

;; apply_range
  (assert
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (f (set (tuple2 (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)
  enum_t_AUTOMATON_STATE))) (s (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (t (set enum_t_AUTOMATON_STATE)))
  (! (=>
     (and (mem
     (set1
     (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     enum_t_AUTOMATON_STATE1)) (t2tb27 f)
     (infix_plmngt enum_t_AUTOMATON_STATE1
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 s)
     (t2tb2 t))) (mem2 x
     (tb2t1
     (dom enum_t_AUTOMATON_STATE1
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb27 f)))))
     (mem1
     (tb2t4
     (apply enum_t_AUTOMATON_STATE1
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb27 f)
     (t2tb3 x))) t)) :pattern ((mem
  (set1
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  enum_t_AUTOMATON_STATE1)) (t2tb27 f)
  (infix_plmngt enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 s)
  (t2tb2 t)))
  (tb2t4
  (apply enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb27 f)
  (t2tb3 x)))) )))

;; apply_range
  (assert
  (forall ((b ty))
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)) (f uni)
  (s (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))) (t uni))
  (! (=>
     (and (mem
     (set1
     (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)) f
     (infix_plmngt b
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 s) t))
     (mem2 x
     (tb2t1
     (dom b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) f))))
     (mem b
     (apply b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) f
     (t2tb3 x)) t)) :pattern ((mem
  (set1
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)) f
  (infix_plmngt b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 s) t))
  (apply b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) f
  (t2tb3 x))) ))))

;; apply_range
  (assert
  (forall ((x enum_t_AUTOMATON_STATE) (f (set (tuple2 enum_t_AUTOMATON_STATE
  (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))))
  (s (set enum_t_AUTOMATON_STATE))
  (t (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))))
  (! (=>
     (and (mem
     (set1
     (tuple21 enum_t_AUTOMATON_STATE1
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))))
     (t2tb30 f)
     (infix_plmngt
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     enum_t_AUTOMATON_STATE1 (t2tb2 s) (t2tb t))) (mem1 x
     (tb2t2
     (dom (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     enum_t_AUTOMATON_STATE1 (t2tb30 f))))) (mem3
     (tb2t1
     (apply (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     enum_t_AUTOMATON_STATE1 (t2tb30 f) (t2tb4 x))) t)) :pattern ((mem
  (set1
  (tuple21 enum_t_AUTOMATON_STATE1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))))
  (t2tb30 f)
  (infix_plmngt
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  enum_t_AUTOMATON_STATE1 (t2tb2 s) (t2tb t)))
  (tb2t1
  (apply (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  enum_t_AUTOMATON_STATE1 (t2tb30 f) (t2tb4 x)))) )))

;; apply_range
  (assert
  (forall ((x enum_t_AUTOMATON_STATE) (f (set (tuple2 enum_t_AUTOMATON_STATE
  (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (s (set enum_t_AUTOMATON_STATE)) (t (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (! (=>
     (and (mem
     (set1
     (tuple21 enum_t_AUTOMATON_STATE1
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))) (t2tb34 f)
     (infix_plmngt (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     enum_t_AUTOMATON_STATE1 (t2tb2 s) (t2tb1 t))) (mem1 x
     (tb2t2
     (dom (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     enum_t_AUTOMATON_STATE1 (t2tb34 f))))) (mem2
     (tb2t3
     (apply (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     enum_t_AUTOMATON_STATE1 (t2tb34 f) (t2tb4 x))) t)) :pattern ((mem
  (set1
  (tuple21 enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))) (t2tb34 f)
  (infix_plmngt (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  enum_t_AUTOMATON_STATE1 (t2tb2 s) (t2tb1 t)))
  (tb2t3
  (apply (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  enum_t_AUTOMATON_STATE1 (t2tb34 f) (t2tb4 x)))) )))

;; apply_range
  (assert
  (forall ((x enum_t_AUTOMATON_STATE) (f (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (s (set enum_t_AUTOMATON_STATE))
  (t (set enum_t_AUTOMATON_STATE)))
  (! (=>
     (and (mem3 f
     (tb2t
     (infix_plmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
     (t2tb2 t)))) (mem1 x
     (tb2t2 (dom enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb1 f)))))
     (mem1
     (tb2t4
     (apply enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb1 f)
     (t2tb4 x))) t)) :pattern ((mem3
  f
  (tb2t
  (infix_plmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 t))))
  (tb2t4
  (apply enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb1 f) (t2tb4 x)))) )))

;; apply_range
  (assert
  (forall ((b ty))
  (forall ((x enum_t_AUTOMATON_STATE) (f uni)
  (s (set enum_t_AUTOMATON_STATE)) (t uni))
  (! (=>
     (and (mem (set1 (tuple21 enum_t_AUTOMATON_STATE1 b)) f
     (infix_plmngt b enum_t_AUTOMATON_STATE1 (t2tb2 s) t)) (mem1 x
     (tb2t2 (dom b enum_t_AUTOMATON_STATE1 f)))) (mem b
     (apply b enum_t_AUTOMATON_STATE1 f (t2tb4 x)) t)) :pattern ((mem
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 b)) f
  (infix_plmngt b enum_t_AUTOMATON_STATE1 (t2tb2 s) t))
  (apply b enum_t_AUTOMATON_STATE1 f (t2tb4 x))) ))))

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
  (forall ((x uni) (z enum_t_AUTOMATON_STATE) (p uni)
  (q (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (= (mem (tuple21 a enum_t_AUTOMATON_STATE1)
  (Tuple2 a enum_t_AUTOMATON_STATE1 x (t2tb4 z))
  (semicolon enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 a p (t2tb1 q)))
  (exists ((y enum_t_AUTOMATON_STATE))
  (and (mem (tuple21 a enum_t_AUTOMATON_STATE1)
  (Tuple2 a enum_t_AUTOMATON_STATE1 x (t2tb4 y)) p) (mem2 (Tuple21 y z) q)))))))

;; semicolon_def
  (assert
  (forall ((b ty))
  (forall ((x enum_t_AUTOMATON_STATE) (z enum_t_AUTOMATON_STATE) (p uni)
  (q uni))
  (and
  (=> (mem2 (Tuple21 x z)
  (tb2t1 (semicolon enum_t_AUTOMATON_STATE1 b enum_t_AUTOMATON_STATE1 p q)))
  (exists ((y uni))
  (and (sort b y)
  (and (mem (tuple21 enum_t_AUTOMATON_STATE1 b)
  (Tuple2 enum_t_AUTOMATON_STATE1 b (t2tb4 x) y) p) (mem
  (tuple21 b enum_t_AUTOMATON_STATE1)
  (Tuple2 b enum_t_AUTOMATON_STATE1 y (t2tb4 z)) q)))))
  (=>
  (exists ((y uni))
  (and (mem (tuple21 enum_t_AUTOMATON_STATE1 b)
  (Tuple2 enum_t_AUTOMATON_STATE1 b (t2tb4 x) y) p) (mem
  (tuple21 b enum_t_AUTOMATON_STATE1)
  (Tuple2 b enum_t_AUTOMATON_STATE1 y (t2tb4 z)) q))) (mem2 (Tuple21 x z)
  (tb2t1 (semicolon enum_t_AUTOMATON_STATE1 b enum_t_AUTOMATON_STATE1 p q))))))))

;; semicolon_def
  (assert
  (forall ((x enum_t_AUTOMATON_STATE) (z enum_t_AUTOMATON_STATE)
  (p (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (q (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (= (mem2 (Tuple21 x z)
  (tb2t1
  (semicolon enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
  enum_t_AUTOMATON_STATE1 (t2tb1 p) (t2tb1 q))))
  (exists ((y enum_t_AUTOMATON_STATE))
  (and (mem2 (Tuple21 x y) p) (mem2 (Tuple21 y z) q))))))

;; semicolon_def
  (assert
  (forall ((c ty))
  (forall ((x enum_t_AUTOMATON_STATE) (z uni)
  (p (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))) (q uni))
  (= (mem (tuple21 enum_t_AUTOMATON_STATE1 c)
  (Tuple2 enum_t_AUTOMATON_STATE1 c (t2tb4 x) z)
  (semicolon c enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb1 p) q))
  (exists ((y enum_t_AUTOMATON_STATE))
  (and (mem2 (Tuple21 x y) p) (mem (tuple21 enum_t_AUTOMATON_STATE1 c)
  (Tuple2 enum_t_AUTOMATON_STATE1 c (t2tb4 y) z) q)))))))

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
  (! (=> (sort
     (tuple21 t (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) e)
     (and
     (=> (mem
     (tuple21 t (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) e
     (direct_product enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 t r1 r2))
     (exists ((x uni) (y enum_t_AUTOMATON_STATE) (z enum_t_AUTOMATON_STATE))
     (and (sort t x)
     (and
     (= (Tuple2 t (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) x
        (t2tb3 (Tuple21 y z))) e)
     (and (mem (tuple21 t enum_t_AUTOMATON_STATE1)
     (Tuple2 t enum_t_AUTOMATON_STATE1 x (t2tb4 y)) r1) (mem
     (tuple21 t enum_t_AUTOMATON_STATE1)
     (Tuple2 t enum_t_AUTOMATON_STATE1 x (t2tb4 z)) r2))))))
     (=>
     (exists ((x uni) (y enum_t_AUTOMATON_STATE) (z enum_t_AUTOMATON_STATE))
     (and
     (= (Tuple2 t (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) x
        (t2tb3 (Tuple21 y z))) e)
     (and (mem (tuple21 t enum_t_AUTOMATON_STATE1)
     (Tuple2 t enum_t_AUTOMATON_STATE1 x (t2tb4 y)) r1) (mem
     (tuple21 t enum_t_AUTOMATON_STATE1)
     (Tuple2 t enum_t_AUTOMATON_STATE1 x (t2tb4 z)) r2)))) (mem
     (tuple21 t (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) e
     (direct_product enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 t r1 r2))))) :pattern ((mem
  (tuple21 t (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) e
  (direct_product enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 t r1 r2))) ))))

;; direct_product_def
  (assert
  (forall ((u ty))
  (forall ((e uni) (r1 uni) (r2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (! (=> (sort
     (tuple21 enum_t_AUTOMATON_STATE1 (tuple21 u enum_t_AUTOMATON_STATE1)) e)
     (and
     (=> (mem
     (tuple21 enum_t_AUTOMATON_STATE1 (tuple21 u enum_t_AUTOMATON_STATE1)) e
     (direct_product enum_t_AUTOMATON_STATE1 u enum_t_AUTOMATON_STATE1 r1
     (t2tb1 r2)))
     (exists ((x enum_t_AUTOMATON_STATE) (y uni) (z enum_t_AUTOMATON_STATE))
     (and (sort u y)
     (and
     (= (Tuple2 enum_t_AUTOMATON_STATE1 (tuple21 u enum_t_AUTOMATON_STATE1)
        (t2tb4 x) (Tuple2 u enum_t_AUTOMATON_STATE1 y (t2tb4 z))) e)
     (and (mem (tuple21 enum_t_AUTOMATON_STATE1 u)
     (Tuple2 enum_t_AUTOMATON_STATE1 u (t2tb4 x) y) r1) (mem2 (Tuple21 x z)
     r2))))))
     (=>
     (exists ((x enum_t_AUTOMATON_STATE) (y uni) (z enum_t_AUTOMATON_STATE))
     (and
     (= (Tuple2 enum_t_AUTOMATON_STATE1 (tuple21 u enum_t_AUTOMATON_STATE1)
        (t2tb4 x) (Tuple2 u enum_t_AUTOMATON_STATE1 y (t2tb4 z))) e)
     (and (mem (tuple21 enum_t_AUTOMATON_STATE1 u)
     (Tuple2 enum_t_AUTOMATON_STATE1 u (t2tb4 x) y) r1) (mem2 (Tuple21 x z)
     r2)))) (mem
     (tuple21 enum_t_AUTOMATON_STATE1 (tuple21 u enum_t_AUTOMATON_STATE1)) e
     (direct_product enum_t_AUTOMATON_STATE1 u enum_t_AUTOMATON_STATE1 r1
     (t2tb1 r2)))))) :pattern ((mem
  (tuple21 enum_t_AUTOMATON_STATE1 (tuple21 u enum_t_AUTOMATON_STATE1)) e
  (direct_product enum_t_AUTOMATON_STATE1 u enum_t_AUTOMATON_STATE1 r1
  (t2tb1 r2)))) ))))

;; direct_product_def
  (assert
  (forall ((e (tuple2 enum_t_AUTOMATON_STATE (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (r1 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (r2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (! (= (mem
     (tuple21 enum_t_AUTOMATON_STATE1
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb32 e)
     (direct_product enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
     enum_t_AUTOMATON_STATE1 (t2tb1 r1) (t2tb1 r2)))
     (exists ((x enum_t_AUTOMATON_STATE) (y enum_t_AUTOMATON_STATE)
     (z enum_t_AUTOMATON_STATE))
     (and
     (= (tb2t32
        (Tuple2 enum_t_AUTOMATON_STATE1
        (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb4 x)
        (t2tb3 (Tuple21 y z)))) e)
     (and (mem2 (Tuple21 x y) r1) (mem2 (Tuple21 x z) r2))))) :pattern ((mem
  (tuple21 enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb32 e)
  (direct_product enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
  enum_t_AUTOMATON_STATE1 (t2tb1 r1) (t2tb1 r2)))) )))

;; direct_product_def
  (assert
  (forall ((v ty))
  (forall ((e uni) (r1 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (r2 uni))
  (! (=> (sort
     (tuple21 enum_t_AUTOMATON_STATE1 (tuple21 enum_t_AUTOMATON_STATE1 v)) e)
     (and
     (=> (mem
     (tuple21 enum_t_AUTOMATON_STATE1 (tuple21 enum_t_AUTOMATON_STATE1 v)) e
     (direct_product v enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
     (t2tb1 r1) r2))
     (exists ((x enum_t_AUTOMATON_STATE) (y enum_t_AUTOMATON_STATE) (z uni))
     (and (sort v z)
     (and
     (= (Tuple2 enum_t_AUTOMATON_STATE1 (tuple21 enum_t_AUTOMATON_STATE1 v)
        (t2tb4 x) (Tuple2 enum_t_AUTOMATON_STATE1 v (t2tb4 y) z)) e)
     (and (mem2 (Tuple21 x y) r1) (mem (tuple21 enum_t_AUTOMATON_STATE1 v)
     (Tuple2 enum_t_AUTOMATON_STATE1 v (t2tb4 x) z) r2))))))
     (=>
     (exists ((x enum_t_AUTOMATON_STATE) (y enum_t_AUTOMATON_STATE) (z uni))
     (and
     (= (Tuple2 enum_t_AUTOMATON_STATE1 (tuple21 enum_t_AUTOMATON_STATE1 v)
        (t2tb4 x) (Tuple2 enum_t_AUTOMATON_STATE1 v (t2tb4 y) z)) e)
     (and (mem2 (Tuple21 x y) r1) (mem (tuple21 enum_t_AUTOMATON_STATE1 v)
     (Tuple2 enum_t_AUTOMATON_STATE1 v (t2tb4 x) z) r2)))) (mem
     (tuple21 enum_t_AUTOMATON_STATE1 (tuple21 enum_t_AUTOMATON_STATE1 v)) e
     (direct_product v enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
     (t2tb1 r1) r2))))) :pattern ((mem
  (tuple21 enum_t_AUTOMATON_STATE1 (tuple21 enum_t_AUTOMATON_STATE1 v)) e
  (direct_product v enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
  (t2tb1 r1) r2))) ))))

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
  (forall ((e uni) (r1 uni) (r2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (=> (sort
  (tuple21 (tuple21 t enum_t_AUTOMATON_STATE1)
  (tuple21 u enum_t_AUTOMATON_STATE1)) e)
  (and
  (=> (mem
  (tuple21 (tuple21 t enum_t_AUTOMATON_STATE1)
  (tuple21 u enum_t_AUTOMATON_STATE1)) e
  (parallel_product enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 u t r1
  (t2tb1 r2)))
  (exists ((x uni) (y enum_t_AUTOMATON_STATE) (z uni)
  (a enum_t_AUTOMATON_STATE))
  (and (sort t x)
  (and (sort u z)
  (and
  (= (Tuple2 (tuple21 t enum_t_AUTOMATON_STATE1)
     (tuple21 u enum_t_AUTOMATON_STATE1)
     (Tuple2 t enum_t_AUTOMATON_STATE1 x (t2tb4 y))
     (Tuple2 u enum_t_AUTOMATON_STATE1 z (t2tb4 a))) e)
  (and (mem (tuple21 t u) (Tuple2 t u x z) r1) (mem2 (Tuple21 y a) r2)))))))
  (=>
  (exists ((x uni) (y enum_t_AUTOMATON_STATE) (z uni)
  (a enum_t_AUTOMATON_STATE))
  (and
  (= (Tuple2 (tuple21 t enum_t_AUTOMATON_STATE1)
     (tuple21 u enum_t_AUTOMATON_STATE1)
     (Tuple2 t enum_t_AUTOMATON_STATE1 x (t2tb4 y))
     (Tuple2 u enum_t_AUTOMATON_STATE1 z (t2tb4 a))) e)
  (and (mem (tuple21 t u) (Tuple2 t u x z) r1) (mem2 (Tuple21 y a) r2))))
  (mem
  (tuple21 (tuple21 t enum_t_AUTOMATON_STATE1)
  (tuple21 u enum_t_AUTOMATON_STATE1)) e
  (parallel_product enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 u t r1
  (t2tb1 r2)))))))))

;; parallel_product_def
  (assert
  (forall ((t ty) (v ty))
  (forall ((e uni) (r1 uni) (r2 uni))
  (=> (sort
  (tuple21 (tuple21 t v)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) e)
  (and
  (=> (mem
  (tuple21 (tuple21 t v)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) e
  (parallel_product enum_t_AUTOMATON_STATE1 v enum_t_AUTOMATON_STATE1 t r1
  r2))
  (exists ((x uni) (y uni) (z enum_t_AUTOMATON_STATE)
  (a enum_t_AUTOMATON_STATE))
  (and (sort t x)
  (and (sort v y)
  (and
  (= (Tuple2 (tuple21 t v)
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (Tuple2 t v x y) (t2tb3 (Tuple21 z a))) e)
  (and (mem (tuple21 t enum_t_AUTOMATON_STATE1)
  (Tuple2 t enum_t_AUTOMATON_STATE1 x (t2tb4 z)) r1) (mem
  (tuple21 v enum_t_AUTOMATON_STATE1)
  (Tuple2 v enum_t_AUTOMATON_STATE1 y (t2tb4 a)) r2)))))))
  (=>
  (exists ((x uni) (y uni) (z enum_t_AUTOMATON_STATE)
  (a enum_t_AUTOMATON_STATE))
  (and
  (= (Tuple2 (tuple21 t v)
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (Tuple2 t v x y) (t2tb3 (Tuple21 z a))) e)
  (and (mem (tuple21 t enum_t_AUTOMATON_STATE1)
  (Tuple2 t enum_t_AUTOMATON_STATE1 x (t2tb4 z)) r1) (mem
  (tuple21 v enum_t_AUTOMATON_STATE1)
  (Tuple2 v enum_t_AUTOMATON_STATE1 y (t2tb4 a)) r2)))) (mem
  (tuple21 (tuple21 t v)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) e
  (parallel_product enum_t_AUTOMATON_STATE1 v enum_t_AUTOMATON_STATE1 t r1
  r2))))))))

;; parallel_product_def
  (assert
  (forall ((t ty))
  (forall ((e uni) (r1 uni) (r2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (=> (sort
  (tuple21 (tuple21 t enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) e)
  (and
  (=> (mem
  (tuple21 (tuple21 t enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) e
  (parallel_product enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
  enum_t_AUTOMATON_STATE1 t r1 (t2tb1 r2)))
  (exists ((x uni) (y enum_t_AUTOMATON_STATE) (z enum_t_AUTOMATON_STATE)
  (a enum_t_AUTOMATON_STATE))
  (and (sort t x)
  (and
  (= (Tuple2 (tuple21 t enum_t_AUTOMATON_STATE1)
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (Tuple2 t enum_t_AUTOMATON_STATE1 x (t2tb4 y)) (t2tb3 (Tuple21 z a))) e)
  (and (mem (tuple21 t enum_t_AUTOMATON_STATE1)
  (Tuple2 t enum_t_AUTOMATON_STATE1 x (t2tb4 z)) r1) (mem2 (Tuple21 y a) r2))))))
  (=>
  (exists ((x uni) (y enum_t_AUTOMATON_STATE) (z enum_t_AUTOMATON_STATE)
  (a enum_t_AUTOMATON_STATE))
  (and
  (= (Tuple2 (tuple21 t enum_t_AUTOMATON_STATE1)
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (Tuple2 t enum_t_AUTOMATON_STATE1 x (t2tb4 y)) (t2tb3 (Tuple21 z a))) e)
  (and (mem (tuple21 t enum_t_AUTOMATON_STATE1)
  (Tuple2 t enum_t_AUTOMATON_STATE1 x (t2tb4 z)) r1) (mem2 (Tuple21 y a) r2))))
  (mem
  (tuple21 (tuple21 t enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) e
  (parallel_product enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
  enum_t_AUTOMATON_STATE1 t r1 (t2tb1 r2)))))))))

;; parallel_product_def
  (assert
  (forall ((u ty))
  (forall ((e uni) (r1 uni) (r2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (=> (sort
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 u enum_t_AUTOMATON_STATE1)) e)
  (and
  (=> (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 u enum_t_AUTOMATON_STATE1)) e
  (parallel_product enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 u
  enum_t_AUTOMATON_STATE1 r1 (t2tb1 r2)))
  (exists ((x enum_t_AUTOMATON_STATE) (y enum_t_AUTOMATON_STATE) (z uni)
  (a enum_t_AUTOMATON_STATE))
  (and (sort u z)
  (and
  (= (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (tuple21 u enum_t_AUTOMATON_STATE1) (t2tb3 (Tuple21 x y))
     (Tuple2 u enum_t_AUTOMATON_STATE1 z (t2tb4 a))) e)
  (and (mem (tuple21 enum_t_AUTOMATON_STATE1 u)
  (Tuple2 enum_t_AUTOMATON_STATE1 u (t2tb4 x) z) r1) (mem2 (Tuple21 y a) r2))))))
  (=>
  (exists ((x enum_t_AUTOMATON_STATE) (y enum_t_AUTOMATON_STATE) (z uni)
  (a enum_t_AUTOMATON_STATE))
  (and
  (= (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (tuple21 u enum_t_AUTOMATON_STATE1) (t2tb3 (Tuple21 x y))
     (Tuple2 u enum_t_AUTOMATON_STATE1 z (t2tb4 a))) e)
  (and (mem (tuple21 enum_t_AUTOMATON_STATE1 u)
  (Tuple2 enum_t_AUTOMATON_STATE1 u (t2tb4 x) z) r1) (mem2 (Tuple21 y a) r2))))
  (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 u enum_t_AUTOMATON_STATE1)) e
  (parallel_product enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 u
  enum_t_AUTOMATON_STATE1 r1 (t2tb1 r2)))))))))

;; parallel_product_def
  (assert
  (forall ((u ty) (w ty))
  (forall ((e uni) (r1 uni) (r2 uni))
  (=> (sort
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 u w)) e)
  (and
  (=> (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 u w)) e
  (parallel_product w enum_t_AUTOMATON_STATE1 u enum_t_AUTOMATON_STATE1 r1
  r2))
  (exists ((x enum_t_AUTOMATON_STATE) (y enum_t_AUTOMATON_STATE) (z uni)
  (a uni))
  (and (sort u z)
  (and (sort w a)
  (and
  (= (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (tuple21 u w) (t2tb3 (Tuple21 x y)) (Tuple2 u w z a)) e)
  (and (mem (tuple21 enum_t_AUTOMATON_STATE1 u)
  (Tuple2 enum_t_AUTOMATON_STATE1 u (t2tb4 x) z) r1) (mem
  (tuple21 enum_t_AUTOMATON_STATE1 w)
  (Tuple2 enum_t_AUTOMATON_STATE1 w (t2tb4 y) a) r2)))))))
  (=>
  (exists ((x enum_t_AUTOMATON_STATE) (y enum_t_AUTOMATON_STATE) (z uni)
  (a uni))
  (and
  (= (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (tuple21 u w) (t2tb3 (Tuple21 x y)) (Tuple2 u w z a)) e)
  (and (mem (tuple21 enum_t_AUTOMATON_STATE1 u)
  (Tuple2 enum_t_AUTOMATON_STATE1 u (t2tb4 x) z) r1) (mem
  (tuple21 enum_t_AUTOMATON_STATE1 w)
  (Tuple2 enum_t_AUTOMATON_STATE1 w (t2tb4 y) a) r2)))) (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 u w)) e
  (parallel_product w enum_t_AUTOMATON_STATE1 u enum_t_AUTOMATON_STATE1 r1
  r2))))))))

;; parallel_product_def
  (assert
  (forall ((v ty))
  (forall ((e uni) (r1 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (r2 uni))
  (=> (sort
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 v)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) e)
  (and
  (=> (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 v)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) e
  (parallel_product enum_t_AUTOMATON_STATE1 v enum_t_AUTOMATON_STATE1
  enum_t_AUTOMATON_STATE1 (t2tb1 r1) r2))
  (exists ((x enum_t_AUTOMATON_STATE) (y uni) (z enum_t_AUTOMATON_STATE)
  (a enum_t_AUTOMATON_STATE))
  (and (sort v y)
  (and
  (= (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 v)
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (Tuple2 enum_t_AUTOMATON_STATE1 v (t2tb4 x) y) (t2tb3 (Tuple21 z a))) e)
  (and (mem2 (Tuple21 x z) r1) (mem (tuple21 v enum_t_AUTOMATON_STATE1)
  (Tuple2 v enum_t_AUTOMATON_STATE1 y (t2tb4 a)) r2))))))
  (=>
  (exists ((x enum_t_AUTOMATON_STATE) (y uni) (z enum_t_AUTOMATON_STATE)
  (a enum_t_AUTOMATON_STATE))
  (and
  (= (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 v)
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (Tuple2 enum_t_AUTOMATON_STATE1 v (t2tb4 x) y) (t2tb3 (Tuple21 z a))) e)
  (and (mem2 (Tuple21 x z) r1) (mem (tuple21 v enum_t_AUTOMATON_STATE1)
  (Tuple2 v enum_t_AUTOMATON_STATE1 y (t2tb4 a)) r2)))) (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 v)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) e
  (parallel_product enum_t_AUTOMATON_STATE1 v enum_t_AUTOMATON_STATE1
  enum_t_AUTOMATON_STATE1 (t2tb1 r1) r2))))))))

;; parallel_product_def
  (assert
  (forall ((e (tuple2 (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)
  (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (r1 (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (r2 (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (= (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb25 e)
  (parallel_product enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
  enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb1 r1) (t2tb1 r2)))
  (exists ((x enum_t_AUTOMATON_STATE) (y enum_t_AUTOMATON_STATE)
  (z enum_t_AUTOMATON_STATE) (a enum_t_AUTOMATON_STATE))
  (and
  (= (tb2t25
     (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (t2tb3 (Tuple21 x y)) (t2tb3 (Tuple21 z a)))) e)
  (and (mem2 (Tuple21 x z) r1) (mem2 (Tuple21 y a) r2)))))))

;; parallel_product_def
  (assert
  (forall ((w ty))
  (forall ((e uni) (r1 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (r2 uni))
  (=> (sort
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 w)) e)
  (and
  (=> (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 w)) e
  (parallel_product w enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
  enum_t_AUTOMATON_STATE1 (t2tb1 r1) r2))
  (exists ((x enum_t_AUTOMATON_STATE) (y enum_t_AUTOMATON_STATE)
  (z enum_t_AUTOMATON_STATE) (a uni))
  (and (sort w a)
  (and
  (= (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (tuple21 enum_t_AUTOMATON_STATE1 w) (t2tb3 (Tuple21 x y))
     (Tuple2 enum_t_AUTOMATON_STATE1 w (t2tb4 z) a)) e)
  (and (mem2 (Tuple21 x z) r1) (mem (tuple21 enum_t_AUTOMATON_STATE1 w)
  (Tuple2 enum_t_AUTOMATON_STATE1 w (t2tb4 y) a) r2))))))
  (=>
  (exists ((x enum_t_AUTOMATON_STATE) (y enum_t_AUTOMATON_STATE)
  (z enum_t_AUTOMATON_STATE) (a uni))
  (and
  (= (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (tuple21 enum_t_AUTOMATON_STATE1 w) (t2tb3 (Tuple21 x y))
     (Tuple2 enum_t_AUTOMATON_STATE1 w (t2tb4 z) a)) e)
  (and (mem2 (Tuple21 x z) r1) (mem (tuple21 enum_t_AUTOMATON_STATE1 w)
  (Tuple2 enum_t_AUTOMATON_STATE1 w (t2tb4 y) a) r2)))) (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 w)) e
  (parallel_product w enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
  enum_t_AUTOMATON_STATE1 (t2tb1 r1) r2))))))))

;; parallel_product_def
  (assert
  (forall ((v ty) (w ty))
  (forall ((e uni) (r1 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (r2 uni))
  (=> (sort
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 v)
  (tuple21 enum_t_AUTOMATON_STATE1 w)) e)
  (and
  (=> (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 v)
  (tuple21 enum_t_AUTOMATON_STATE1 w)) e
  (parallel_product w v enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
  (t2tb1 r1) r2))
  (exists ((x enum_t_AUTOMATON_STATE) (y uni) (z enum_t_AUTOMATON_STATE)
  (a uni))
  (and (sort v y)
  (and (sort w a)
  (and
  (= (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 v)
     (tuple21 enum_t_AUTOMATON_STATE1 w)
     (Tuple2 enum_t_AUTOMATON_STATE1 v (t2tb4 x) y)
     (Tuple2 enum_t_AUTOMATON_STATE1 w (t2tb4 z) a)) e)
  (and (mem2 (Tuple21 x z) r1) (mem (tuple21 v w) (Tuple2 v w y a) r2)))))))
  (=>
  (exists ((x enum_t_AUTOMATON_STATE) (y uni) (z enum_t_AUTOMATON_STATE)
  (a uni))
  (and
  (= (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 v)
     (tuple21 enum_t_AUTOMATON_STATE1 w)
     (Tuple2 enum_t_AUTOMATON_STATE1 v (t2tb4 x) y)
     (Tuple2 enum_t_AUTOMATON_STATE1 w (t2tb4 z) a)) e)
  (and (mem2 (Tuple21 x z) r1) (mem (tuple21 v w) (Tuple2 v w y a) r2))))
  (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 v)
  (tuple21 enum_t_AUTOMATON_STATE1 w)) e
  (parallel_product w v enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
  (t2tb1 r1) r2))))))))

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
  (forall ((f uni) (g (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (s uni) (t (set enum_t_AUTOMATON_STATE))
  (u (set enum_t_AUTOMATON_STATE)))
  (=>
  (and (mem (set1 (tuple21 a enum_t_AUTOMATON_STATE1)) f
  (infix_plmngt enum_t_AUTOMATON_STATE1 a s (t2tb2 t))) (mem3 g
  (tb2t
  (infix_plmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 t)
  (t2tb2 u))))) (mem (set1 (tuple21 a enum_t_AUTOMATON_STATE1))
  (semicolon enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 a f (t2tb1 g))
  (infix_plmngt enum_t_AUTOMATON_STATE1 a s (t2tb2 u)))))))

;; semicolon_is_function
  (assert
  (forall ((b ty))
  (forall ((f uni) (g uni) (s (set enum_t_AUTOMATON_STATE)) (t uni)
  (u (set enum_t_AUTOMATON_STATE)))
  (=>
  (and (mem (set1 (tuple21 enum_t_AUTOMATON_STATE1 b)) f
  (infix_plmngt b enum_t_AUTOMATON_STATE1 (t2tb2 s) t)) (mem
  (set1 (tuple21 b enum_t_AUTOMATON_STATE1)) g
  (infix_plmngt enum_t_AUTOMATON_STATE1 b t (t2tb2 u)))) (mem3
  (tb2t1 (semicolon enum_t_AUTOMATON_STATE1 b enum_t_AUTOMATON_STATE1 f g))
  (tb2t
  (infix_plmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 u))))))))

;; semicolon_is_function
  (assert
  (forall ((f (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (g (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s (set enum_t_AUTOMATON_STATE)) (t (set enum_t_AUTOMATON_STATE))
  (u (set enum_t_AUTOMATON_STATE)))
  (=>
  (and (mem3 f
  (tb2t
  (infix_plmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 t)))) (mem3 g
  (tb2t
  (infix_plmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 t)
  (t2tb2 u))))) (mem3
  (tb2t1
  (semicolon enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
  enum_t_AUTOMATON_STATE1 (t2tb1 f) (t2tb1 g)))
  (tb2t
  (infix_plmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 u)))))))

;; semicolon_is_function
  (assert
  (forall ((c ty))
  (forall ((f (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (g uni) (s (set enum_t_AUTOMATON_STATE)) (t (set enum_t_AUTOMATON_STATE))
  (u uni))
  (=>
  (and (mem3 f
  (tb2t
  (infix_plmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 t)))) (mem (set1 (tuple21 enum_t_AUTOMATON_STATE1 c)) g
  (infix_plmngt c enum_t_AUTOMATON_STATE1 (t2tb2 t) u))) (mem
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 c))
  (semicolon c enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb1 f) g)
  (infix_plmngt c enum_t_AUTOMATON_STATE1 (t2tb2 s) u))))))

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
  (t (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (u uni))
  (=>
  (and (mem
  (set1
  (tuple21 a
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))) f
  (infix_plmngt
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) a s
  (t2tb t)))
  (and (mem
  (set1
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  c)) g
  (infix_plmngt c
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb t)
  u))
  (and (mem a x
  (dom (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) a f))
  (mem3
  (tb2t1
  (apply (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) a f
  x))
  (tb2t
  (dom c (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) g))))))
  (= (apply c a
     (semicolon c
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) a f g)
     x) (apply c
        (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) g
        (apply
        (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) a f
        x)))))))

;; apply_compose
  (assert
  (forall ((a ty) (c ty))
  (forall ((x uni) (f uni) (g uni) (s uni)
  (t (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))) (u uni))
  (=>
  (and (mem
  (set1
  (tuple21 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))) f
  (infix_plmngt (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) a s
  (t2tb1 t)))
  (and (mem
  (set1
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) c)) g
  (infix_plmngt c (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 t) u))
  (and (mem a x
  (dom (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) a f)) (mem2
  (tb2t3
  (apply (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) a f x))
  (tb2t1 (dom c (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) g))))))
  (= (apply c a
     (semicolon c (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) a
     f g) x) (apply c
             (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) g
             (apply (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
             a f x)))))))

;; apply_compose
  (assert
  (forall ((a ty))
  (forall ((x uni) (f uni) (g (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (s uni) (t (set enum_t_AUTOMATON_STATE))
  (u (set enum_t_AUTOMATON_STATE)))
  (=>
  (and (mem (set1 (tuple21 a enum_t_AUTOMATON_STATE1)) f
  (infix_plmngt enum_t_AUTOMATON_STATE1 a s (t2tb2 t)))
  (and (mem3 g
  (tb2t
  (infix_plmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 t)
  (t2tb2 u))))
  (and (mem a x (dom enum_t_AUTOMATON_STATE1 a f)) (mem1
  (tb2t4 (apply enum_t_AUTOMATON_STATE1 a f x))
  (tb2t2 (dom enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb1 g)))))))
  (= (tb2t4
     (apply enum_t_AUTOMATON_STATE1 a
     (semicolon enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 a f
     (t2tb1 g)) x)) (tb2t4
                    (apply enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
                    (t2tb1 g) (apply enum_t_AUTOMATON_STATE1 a f x))))))))

;; apply_compose
  (assert
  (forall ((a ty) (c ty))
  (forall ((x uni) (f uni) (g uni) (s uni) (t (set enum_t_AUTOMATON_STATE))
  (u uni))
  (=>
  (and (mem (set1 (tuple21 a enum_t_AUTOMATON_STATE1)) f
  (infix_plmngt enum_t_AUTOMATON_STATE1 a s (t2tb2 t)))
  (and (mem (set1 (tuple21 enum_t_AUTOMATON_STATE1 c)) g
  (infix_plmngt c enum_t_AUTOMATON_STATE1 (t2tb2 t) u))
  (and (mem a x (dom enum_t_AUTOMATON_STATE1 a f)) (mem1
  (tb2t4 (apply enum_t_AUTOMATON_STATE1 a f x))
  (tb2t2 (dom c enum_t_AUTOMATON_STATE1 g))))))
  (= (apply c a (semicolon c enum_t_AUTOMATON_STATE1 a f g) x) (apply c
                                                               enum_t_AUTOMATON_STATE1
                                                               g
                                                               (apply
                                                               enum_t_AUTOMATON_STATE1
                                                               a f x)))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (f (set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))) (g uni)
  (s (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (t (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (u uni))
  (=>
  (and (mem
  (set1
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))))
  (t2tb12 f)
  (infix_plmngt
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s)
  (t2tb t)))
  (and (mem
  (set1
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  c)) g
  (infix_plmngt c
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb t)
  u))
  (and (mem3 x
  (tb2t
  (dom (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (t2tb12 f)))) (mem3
  (tb2t1
  (apply (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb12 f)
  (t2tb1 x)))
  (tb2t
  (dom c (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) g))))))
  (= (apply c
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (semicolon c
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb12 f) g) (t2tb1 x)) (apply c
                              (set1
                              (tuple21 enum_t_AUTOMATON_STATE1
                              enum_t_AUTOMATON_STATE1)) g
                              (apply
                              (set1
                              (tuple21 enum_t_AUTOMATON_STATE1
                              enum_t_AUTOMATON_STATE1))
                              (set1
                              (tuple21 enum_t_AUTOMATON_STATE1
                              enum_t_AUTOMATON_STATE1)) (t2tb12 f) (t2tb1 x))))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (f (set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (g uni)
  (s (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (t (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))) (u uni))
  (=>
  (and (mem
  (set1
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))) (t2tb15 f)
  (infix_plmngt (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s)
  (t2tb1 t)))
  (and (mem
  (set1
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) c)) g
  (infix_plmngt c (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 t) u))
  (and (mem3 x
  (tb2t
  (dom (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (t2tb15 f)))) (mem2
  (tb2t3
  (apply (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb15 f)
  (t2tb1 x)))
  (tb2t1 (dom c (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) g))))))
  (= (apply c
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (semicolon c (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb15 f) g) (t2tb1 x)) (apply c
                              (tuple21 enum_t_AUTOMATON_STATE1
                              enum_t_AUTOMATON_STATE1) g
                              (apply
                              (tuple21 enum_t_AUTOMATON_STATE1
                              enum_t_AUTOMATON_STATE1)
                              (set1
                              (tuple21 enum_t_AUTOMATON_STATE1
                              enum_t_AUTOMATON_STATE1)) (t2tb15 f) (t2tb1 x))))))))

;; apply_compose
  (assert
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (f (set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) enum_t_AUTOMATON_STATE)))
  (g (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (t (set enum_t_AUTOMATON_STATE)) (u (set enum_t_AUTOMATON_STATE)))
  (=>
  (and (mem
  (set1
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  enum_t_AUTOMATON_STATE1)) (t2tb18 f)
  (infix_plmngt enum_t_AUTOMATON_STATE1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s)
  (t2tb2 t)))
  (and (mem3 g
  (tb2t
  (infix_plmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 t)
  (t2tb2 u))))
  (and (mem3 x
  (tb2t
  (dom enum_t_AUTOMATON_STATE1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (t2tb18 f)))) (mem1
  (tb2t4
  (apply enum_t_AUTOMATON_STATE1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb18 f)
  (t2tb1 x)))
  (tb2t2 (dom enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb1 g)))))))
  (= (tb2t4
     (apply enum_t_AUTOMATON_STATE1
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (semicolon enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb18 f) (t2tb1 g)) (t2tb1 x))) (tb2t4
                                       (apply enum_t_AUTOMATON_STATE1
                                       enum_t_AUTOMATON_STATE1 (t2tb1 g)
                                       (apply enum_t_AUTOMATON_STATE1
                                       (set1
                                       (tuple21 enum_t_AUTOMATON_STATE1
                                       enum_t_AUTOMATON_STATE1)) (t2tb18 f)
                                       (t2tb1 x))))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (f (set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) enum_t_AUTOMATON_STATE))) (g uni)
  (s (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (t (set enum_t_AUTOMATON_STATE)) (u uni))
  (=>
  (and (mem
  (set1
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  enum_t_AUTOMATON_STATE1)) (t2tb18 f)
  (infix_plmngt enum_t_AUTOMATON_STATE1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s)
  (t2tb2 t)))
  (and (mem (set1 (tuple21 enum_t_AUTOMATON_STATE1 c)) g
  (infix_plmngt c enum_t_AUTOMATON_STATE1 (t2tb2 t) u))
  (and (mem3 x
  (tb2t
  (dom enum_t_AUTOMATON_STATE1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (t2tb18 f)))) (mem1
  (tb2t4
  (apply enum_t_AUTOMATON_STATE1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb18 f)
  (t2tb1 x))) (tb2t2 (dom c enum_t_AUTOMATON_STATE1 g))))))
  (= (apply c
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (semicolon c enum_t_AUTOMATON_STATE1
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb18 f) g) (t2tb1 x)) (apply c enum_t_AUTOMATON_STATE1 g
                              (apply enum_t_AUTOMATON_STATE1
                              (set1
                              (tuple21 enum_t_AUTOMATON_STATE1
                              enum_t_AUTOMATON_STATE1)) (t2tb18 f) (t2tb1 x))))))))

;; apply_compose
  (assert
  (forall ((b ty) (c ty))
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (f uni) (g uni) (s (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (t uni) (u uni))
  (=>
  (and (mem
  (set1
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  b)) f
  (infix_plmngt b
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s)
  t))
  (and (mem (set1 (tuple21 b c)) g (infix_plmngt c b t u))
  (and (mem3 x
  (tb2t
  (dom b (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) f)))
  (mem b
  (apply b (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) f
  (t2tb1 x)) (dom c b g)))))
  (= (apply c
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (semicolon c b
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) f g)
     (t2tb1 x)) (apply c b g
                (apply b
                (set1
                (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) f
                (t2tb1 x))))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (f (set (tuple2 (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)
  (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))) (g uni)
  (s (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (t (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (u uni))
  (=>
  (and (mem
  (set1
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))))
  (t2tb20 f)
  (infix_plmngt
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 s)
  (t2tb t)))
  (and (mem
  (set1
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  c)) g
  (infix_plmngt c
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb t)
  u))
  (and (mem2 x
  (tb2t1
  (dom (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb20 f))))
  (mem3
  (tb2t1
  (apply (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb20 f)
  (t2tb3 x)))
  (tb2t
  (dom c (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) g))))))
  (= (apply c (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (semicolon c
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb20 f) g)
     (t2tb3 x)) (apply c
                (set1
                (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) g
                (apply
                (set1
                (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
                (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
                (t2tb20 f) (t2tb3 x))))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (f (set (tuple2 (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)
  (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))) (g uni)
  (s (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (t (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))) (u uni))
  (=>
  (and (mem
  (set1
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))) (t2tb24 f)
  (infix_plmngt (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 s)
  (t2tb1 t)))
  (and (mem
  (set1
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) c)) g
  (infix_plmngt c (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 t) u))
  (and (mem2 x
  (tb2t1
  (dom (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb24 f))))
  (mem2
  (tb2t3
  (apply (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb24 f)
  (t2tb3 x)))
  (tb2t1 (dom c (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) g))))))
  (= (apply c (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (semicolon c (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb24 f) g)
     (t2tb3 x)) (apply c
                (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) g
                (apply
                (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
                (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
                (t2tb24 f) (t2tb3 x))))))))

;; apply_compose
  (assert
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (f (set (tuple2 (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)
  enum_t_AUTOMATON_STATE))) (g (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (s (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (t (set enum_t_AUTOMATON_STATE))
  (u (set enum_t_AUTOMATON_STATE)))
  (=>
  (and (mem
  (set1
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  enum_t_AUTOMATON_STATE1)) (t2tb27 f)
  (infix_plmngt enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 s)
  (t2tb2 t)))
  (and (mem3 g
  (tb2t
  (infix_plmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 t)
  (t2tb2 u))))
  (and (mem2 x
  (tb2t1
  (dom enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb27 f))))
  (mem1
  (tb2t4
  (apply enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb27 f)
  (t2tb3 x)))
  (tb2t2 (dom enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb1 g)))))))
  (= (tb2t4
     (apply enum_t_AUTOMATON_STATE1
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (semicolon enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb27 f)
     (t2tb1 g)) (t2tb3 x))) (tb2t4
                            (apply enum_t_AUTOMATON_STATE1
                            enum_t_AUTOMATON_STATE1 (t2tb1 g)
                            (apply enum_t_AUTOMATON_STATE1
                            (tuple21 enum_t_AUTOMATON_STATE1
                            enum_t_AUTOMATON_STATE1) (t2tb27 f) (t2tb3 x))))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (f (set (tuple2 (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)
  enum_t_AUTOMATON_STATE))) (g uni) (s (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (t (set enum_t_AUTOMATON_STATE)) (u uni))
  (=>
  (and (mem
  (set1
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  enum_t_AUTOMATON_STATE1)) (t2tb27 f)
  (infix_plmngt enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 s)
  (t2tb2 t)))
  (and (mem (set1 (tuple21 enum_t_AUTOMATON_STATE1 c)) g
  (infix_plmngt c enum_t_AUTOMATON_STATE1 (t2tb2 t) u))
  (and (mem2 x
  (tb2t1
  (dom enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb27 f))))
  (mem1
  (tb2t4
  (apply enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb27 f)
  (t2tb3 x))) (tb2t2 (dom c enum_t_AUTOMATON_STATE1 g))))))
  (= (apply c (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (semicolon c enum_t_AUTOMATON_STATE1
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb27 f) g)
     (t2tb3 x)) (apply c enum_t_AUTOMATON_STATE1 g
                (apply enum_t_AUTOMATON_STATE1
                (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
                (t2tb27 f) (t2tb3 x))))))))

;; apply_compose
  (assert
  (forall ((b ty) (c ty))
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)) (f uni)
  (g uni) (s (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (t uni) (u uni))
  (=>
  (and (mem
  (set1
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)) f
  (infix_plmngt b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 s) t))
  (and (mem (set1 (tuple21 b c)) g (infix_plmngt c b t u))
  (and (mem2 x
  (tb2t1 (dom b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) f)))
  (mem b
  (apply b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) f
  (t2tb3 x)) (dom c b g)))))
  (= (apply c (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (semicolon c b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     f g) (t2tb3 x)) (apply c b g
                     (apply b
                     (tuple21 enum_t_AUTOMATON_STATE1
                     enum_t_AUTOMATON_STATE1) f (t2tb3 x))))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x enum_t_AUTOMATON_STATE) (f (set (tuple2 enum_t_AUTOMATON_STATE
  (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))) (g uni)
  (s (set enum_t_AUTOMATON_STATE))
  (t (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (u uni))
  (=>
  (and (mem
  (set1
  (tuple21 enum_t_AUTOMATON_STATE1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))))
  (t2tb30 f)
  (infix_plmngt
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  enum_t_AUTOMATON_STATE1 (t2tb2 s) (t2tb t)))
  (and (mem
  (set1
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  c)) g
  (infix_plmngt c
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb t)
  u))
  (and (mem1 x
  (tb2t2
  (dom (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  enum_t_AUTOMATON_STATE1 (t2tb30 f)))) (mem3
  (tb2t1
  (apply (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  enum_t_AUTOMATON_STATE1 (t2tb30 f) (t2tb4 x)))
  (tb2t
  (dom c (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) g))))))
  (= (apply c enum_t_AUTOMATON_STATE1
     (semicolon c
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     enum_t_AUTOMATON_STATE1 (t2tb30 f) g) (t2tb4 x)) (apply c
                                                      (set1
                                                      (tuple21
                                                      enum_t_AUTOMATON_STATE1
                                                      enum_t_AUTOMATON_STATE1))
                                                      g
                                                      (apply
                                                      (set1
                                                      (tuple21
                                                      enum_t_AUTOMATON_STATE1
                                                      enum_t_AUTOMATON_STATE1))
                                                      enum_t_AUTOMATON_STATE1
                                                      (t2tb30 f) (t2tb4 x))))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x enum_t_AUTOMATON_STATE) (f (set (tuple2 enum_t_AUTOMATON_STATE
  (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))) (g uni)
  (s (set enum_t_AUTOMATON_STATE)) (t (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (u uni))
  (=>
  (and (mem
  (set1
  (tuple21 enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))) (t2tb34 f)
  (infix_plmngt (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  enum_t_AUTOMATON_STATE1 (t2tb2 s) (t2tb1 t)))
  (and (mem
  (set1
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) c)) g
  (infix_plmngt c (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 t) u))
  (and (mem1 x
  (tb2t2
  (dom (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  enum_t_AUTOMATON_STATE1 (t2tb34 f)))) (mem2
  (tb2t3
  (apply (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  enum_t_AUTOMATON_STATE1 (t2tb34 f) (t2tb4 x)))
  (tb2t1 (dom c (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) g))))))
  (= (apply c enum_t_AUTOMATON_STATE1
     (semicolon c (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     enum_t_AUTOMATON_STATE1 (t2tb34 f) g) (t2tb4 x)) (apply c
                                                      (tuple21
                                                      enum_t_AUTOMATON_STATE1
                                                      enum_t_AUTOMATON_STATE1)
                                                      g
                                                      (apply
                                                      (tuple21
                                                      enum_t_AUTOMATON_STATE1
                                                      enum_t_AUTOMATON_STATE1)
                                                      enum_t_AUTOMATON_STATE1
                                                      (t2tb34 f) (t2tb4 x))))))))

;; apply_compose
  (assert
  (forall ((x enum_t_AUTOMATON_STATE) (f (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (g (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (s (set enum_t_AUTOMATON_STATE))
  (t (set enum_t_AUTOMATON_STATE)) (u (set enum_t_AUTOMATON_STATE)))
  (=>
  (and (mem3 f
  (tb2t
  (infix_plmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 t))))
  (and (mem3 g
  (tb2t
  (infix_plmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 t)
  (t2tb2 u))))
  (and (mem1 x
  (tb2t2 (dom enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb1 f))))
  (mem1
  (tb2t4
  (apply enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb1 f) (t2tb4 x)))
  (tb2t2 (dom enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb1 g)))))))
  (= (tb2t4
     (apply enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
     (semicolon enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
     enum_t_AUTOMATON_STATE1 (t2tb1 f) (t2tb1 g)) (t2tb4 x))) (tb2t4
                                                              (apply
                                                              enum_t_AUTOMATON_STATE1
                                                              enum_t_AUTOMATON_STATE1
                                                              (t2tb1 g)
                                                              (apply
                                                              enum_t_AUTOMATON_STATE1
                                                              enum_t_AUTOMATON_STATE1
                                                              (t2tb1 f)
                                                              (t2tb4 x))))))))

;; apply_compose
  (assert
  (forall ((c ty))
  (forall ((x enum_t_AUTOMATON_STATE) (f (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (g uni) (s (set enum_t_AUTOMATON_STATE))
  (t (set enum_t_AUTOMATON_STATE)) (u uni))
  (=>
  (and (mem3 f
  (tb2t
  (infix_plmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 t))))
  (and (mem (set1 (tuple21 enum_t_AUTOMATON_STATE1 c)) g
  (infix_plmngt c enum_t_AUTOMATON_STATE1 (t2tb2 t) u))
  (and (mem1 x
  (tb2t2 (dom enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb1 f))))
  (mem1
  (tb2t4
  (apply enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb1 f) (t2tb4 x)))
  (tb2t2 (dom c enum_t_AUTOMATON_STATE1 g))))))
  (= (apply c enum_t_AUTOMATON_STATE1
     (semicolon c enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb1 f)
     g) (t2tb4 x)) (apply c enum_t_AUTOMATON_STATE1 g
                   (apply enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
                   (t2tb1 f) (t2tb4 x))))))))

;; apply_compose
  (assert
  (forall ((b ty) (c ty))
  (forall ((x enum_t_AUTOMATON_STATE) (f uni) (g uni)
  (s (set enum_t_AUTOMATON_STATE)) (t uni) (u uni))
  (=>
  (and (mem (set1 (tuple21 enum_t_AUTOMATON_STATE1 b)) f
  (infix_plmngt b enum_t_AUTOMATON_STATE1 (t2tb2 s) t))
  (and (mem (set1 (tuple21 b c)) g (infix_plmngt c b t u))
  (and (mem1 x (tb2t2 (dom b enum_t_AUTOMATON_STATE1 f))) (mem b
  (apply b enum_t_AUTOMATON_STATE1 f (t2tb4 x)) (dom c b g)))))
  (= (apply c enum_t_AUTOMATON_STATE1
     (semicolon c b enum_t_AUTOMATON_STATE1 f g) (t2tb4 x)) (apply c b g
                                                            (apply b
                                                            enum_t_AUTOMATON_STATE1
                                                            f (t2tb4 x))))))))

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
  (forall ((f (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s (set enum_t_AUTOMATON_STATE)) (t (set enum_t_AUTOMATON_STATE)))
  (= (mem3 f
  (tb2t
  (infix_gtplgt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 t))))
  (and (mem3 f
  (tb2t
  (infix_plmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 t)))) (mem3
  (tb2t1 (inverse enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb1 f)))
  (tb2t
  (infix_plmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 t)
  (t2tb2 s))))))))

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
  (forall ((f (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s (set enum_t_AUTOMATON_STATE)) (t (set enum_t_AUTOMATON_STATE)))
  (= (mem3 f
  (tb2t
  (infix_gtmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 t))))
  (and (mem3 f
  (tb2t
  (infix_gtplgt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 t)))) (mem3 f
  (tb2t
  (infix_mnmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 t))))))))

;; mem_total_injection
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni))
  (= (mem (set1 (tuple21 a b)) f (infix_gtmngt b a s t))
  (and (mem (set1 (tuple21 a b)) f (infix_gtplgt b a s t)) (mem
  (set1 (tuple21 a b)) f (infix_mnmngt b a s t)))))))

;; mem_total_injection_alt
  (assert
  (forall ((f (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s (set enum_t_AUTOMATON_STATE)) (t (set enum_t_AUTOMATON_STATE)))
  (= (mem3 f
  (tb2t
  (infix_gtmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 t))))
  (and (mem3 f
  (tb2t
  (infix_mnmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 t)))) (mem3
  (tb2t1 (inverse enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb1 f)))
  (tb2t
  (infix_plmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 t)
  (t2tb2 s))))))))

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
  (forall ((f uni) (s (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (t uni))
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (y (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (=> (mem
  (set1
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  b)) f
  (infix_gtmngt b
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s)
  t))
  (=> (mem3 x s)
  (=> (mem3 y s)
  (=>
  (= (apply b
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) f
     (t2tb1 x)) (apply b
                (set1
                (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) f
                (t2tb1 y)))
  (= x y)))))))))

;; injection
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (t uni))
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (y (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (=> (mem
  (set1
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)) f
  (infix_gtmngt b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 s) t))
  (=> (mem2 x s)
  (=> (mem2 y s)
  (=>
  (= (apply b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) f
     (t2tb3 x)) (apply b
                (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) f
                (t2tb3 y)))
  (= x y)))))))))

;; injection
  (assert
  (forall ((f (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s (set enum_t_AUTOMATON_STATE)) (t (set enum_t_AUTOMATON_STATE)))
  (forall ((x enum_t_AUTOMATON_STATE) (y enum_t_AUTOMATON_STATE))
  (=> (mem3 f
  (tb2t
  (infix_gtmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 t))))
  (=> (mem1 x s)
  (=> (mem1 y s)
  (=>
  (= (tb2t4
     (apply enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb1 f)
     (t2tb4 x))) (tb2t4
                 (apply enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
                 (t2tb1 f) (t2tb4 y))))
  (= x y))))))))

;; injection
  (assert
  (forall ((b ty))
  (forall ((f uni) (s (set enum_t_AUTOMATON_STATE)) (t uni))
  (forall ((x enum_t_AUTOMATON_STATE) (y enum_t_AUTOMATON_STATE))
  (=> (mem (set1 (tuple21 enum_t_AUTOMATON_STATE1 b)) f
  (infix_gtmngt b enum_t_AUTOMATON_STATE1 (t2tb2 s) t))
  (=> (mem1 x s)
  (=> (mem1 y s)
  (=>
  (= (apply b enum_t_AUTOMATON_STATE1 f (t2tb4 x)) (apply b
                                                   enum_t_AUTOMATON_STATE1 f
                                                   (t2tb4 y)))
  (= x y)))))))))

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
  (forall ((f (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s (set enum_t_AUTOMATON_STATE)) (t (set enum_t_AUTOMATON_STATE)))
  (= (mem3 f
  (tb2t
  (infix_plmngtgt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 t))))
  (and (mem3 f
  (tb2t
  (infix_plmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 t))))
  (= (tb2t2 (ran enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb1 f))) t)))))

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
  (forall ((f (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s (set enum_t_AUTOMATON_STATE)) (t (set enum_t_AUTOMATON_STATE)))
  (= (mem3 f
  (tb2t
  (infix_mnmngtgt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 t))))
  (and (mem3 f
  (tb2t
  (infix_plmngtgt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 t)))) (mem3 f
  (tb2t
  (infix_mnmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 t))))))))

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
  (forall ((f (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s (set enum_t_AUTOMATON_STATE)) (t (set enum_t_AUTOMATON_STATE)))
  (= (mem3 f
  (tb2t
  (infix_gtplgtgt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 t))))
  (and (mem3 f
  (tb2t
  (infix_gtplgt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 t)))) (mem3 f
  (tb2t
  (infix_plmngtgt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 t))))))))

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
  (forall ((f (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s (set enum_t_AUTOMATON_STATE)) (t (set enum_t_AUTOMATON_STATE)))
  (= (mem3 f
  (tb2t
  (infix_gtmngtgt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 t))))
  (and (mem3 f
  (tb2t
  (infix_gtmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 t)))) (mem3 f
  (tb2t
  (infix_mnmngtgt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 t))))))))

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
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (y (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))))
  (= (mem
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb1 x)
  (t2tb1 y))
  (id (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (t2tb s))) (and (mem3 x s) (= x y)))))

;; id_def
  (assert
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (y (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (s (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (= (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb3 x)
  (t2tb3 y))
  (id (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 s)))
  (and (mem2 x s) (= x y)))))

;; id_def
  (assert
  (forall ((x enum_t_AUTOMATON_STATE) (y enum_t_AUTOMATON_STATE)
  (s (set enum_t_AUTOMATON_STATE)))
  (= (mem2 (Tuple21 x y) (tb2t1 (id enum_t_AUTOMATON_STATE1 (t2tb2 s))))
  (and (mem1 x s) (= x y)))))

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
  (forall ((s (set enum_t_AUTOMATON_STATE))) (mem3
  (tb2t1 (id enum_t_AUTOMATON_STATE1 (t2tb2 s)))
  (tb2t
  (infix_plmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 s))))))

;; id_fun
  (assert
  (forall ((a ty))
  (forall ((s uni)) (mem (set1 (tuple21 a a)) (id a s)
  (infix_plmngt a a s s)))))

;; id_total_fun
  (assert
  (forall ((s (set enum_t_AUTOMATON_STATE))) (mem3
  (tb2t1 (id enum_t_AUTOMATON_STATE1 (t2tb2 s)))
  (tb2t
  (infix_mnmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 s))))))

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
  (= (seq_length a n s) (infix_mnmngt a int (t2tb7 (mk 1 n)) s)))))

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
  (infix_mnmngt a int (t2tb7 (mk 1 (size a r))) s))))))

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
  (forall ((s (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))) (is_finite_subset
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (t2tb empty3) (t2tb s) 0)))

;; Empty
  (assert
  (forall ((s (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (is_finite_subset (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 empty2) (t2tb1 s) 0)))

;; Empty
  (assert
  (forall ((s (set enum_t_AUTOMATON_STATE))) (is_finite_subset
  enum_t_AUTOMATON_STATE1 (t2tb2 empty1) (t2tb2 s) 0)))

;; Empty
  (assert
  (forall ((a ty)) (forall ((s uni)) (is_finite_subset a (empty a) s 0))))

;; Add_mem
  (assert
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s1 (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (s2 (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (c Int))
  (=> (is_finite_subset
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s1)
  (t2tb s2) c)
  (=> (mem3 x s2)
  (=> (mem3 x s1) (is_finite_subset
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (t2tb (add3 x s1)) (t2tb s2) c))))))

;; Add_mem
  (assert
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (s1 (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s2 (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))) (c Int))
  (=> (is_finite_subset
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 s1)
  (t2tb1 s2) c)
  (=> (mem2 x s2)
  (=> (mem2 x s1) (is_finite_subset
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 (add2 x s1)) (t2tb1 s2) c))))))

;; Add_mem
  (assert
  (forall ((x enum_t_AUTOMATON_STATE) (s1 (set enum_t_AUTOMATON_STATE))
  (s2 (set enum_t_AUTOMATON_STATE)) (c Int))
  (=> (is_finite_subset enum_t_AUTOMATON_STATE1 (t2tb2 s1) (t2tb2 s2) c)
  (=> (mem1 x s2)
  (=> (mem1 x s1) (is_finite_subset enum_t_AUTOMATON_STATE1
  (t2tb2 (add1 x s1)) (t2tb2 s2) c))))))

;; Add_mem
  (assert
  (forall ((a ty))
  (forall ((x uni) (s1 uni) (s2 uni) (c Int))
  (=> (is_finite_subset a s1 s2 c)
  (=> (mem a x s2) (=> (mem a x s1) (is_finite_subset a (add a x s1) s2 c)))))))

;; Add_notmem
  (assert
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s1 (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (s2 (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (c Int))
  (=> (is_finite_subset
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s1)
  (t2tb s2) c)
  (=> (mem3 x s2)
  (=> (not (mem3 x s1)) (is_finite_subset
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (t2tb (add3 x s1)) (t2tb s2) (+ c 1)))))))

;; Add_notmem
  (assert
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (s1 (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s2 (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))) (c Int))
  (=> (is_finite_subset
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 s1)
  (t2tb1 s2) c)
  (=> (mem2 x s2)
  (=> (not (mem2 x s1)) (is_finite_subset
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 (add2 x s1)) (t2tb1 s2) (+ c 1)))))))

;; Add_notmem
  (assert
  (forall ((x enum_t_AUTOMATON_STATE) (s1 (set enum_t_AUTOMATON_STATE))
  (s2 (set enum_t_AUTOMATON_STATE)) (c Int))
  (=> (is_finite_subset enum_t_AUTOMATON_STATE1 (t2tb2 s1) (t2tb2 s2) c)
  (=> (mem1 x s2)
  (=> (not (mem1 x s1)) (is_finite_subset enum_t_AUTOMATON_STATE1
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
  (forall ((z (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (z1 (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (z2 Int))
  (=> (is_finite_subset
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb z)
  (t2tb z1) z2)
  (or
  (or
  (exists ((s (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))) (and (and (= z empty3) (= z1 s)) (= z2 0)))
  (exists ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s1 (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (s2 (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (c Int))
  (and (is_finite_subset
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s1)
  (t2tb s2) c)
  (and (mem3 x s2)
  (and (mem3 x s1) (and (and (= z (add3 x s1)) (= z1 s2)) (= z2 c)))))))
  (exists ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s1 (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (s2 (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (c Int))
  (and (is_finite_subset
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s1)
  (t2tb s2) c)
  (and (mem3 x s2)
  (and (not (mem3 x s1))
  (and (and (= z (add3 x s1)) (= z1 s2)) (= z2 (+ c 1)))))))))))

;; is_finite_subset_inversion
  (assert
  (forall ((z (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (z1 (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))) (z2 Int))
  (=> (is_finite_subset
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 z)
  (t2tb1 z1) z2)
  (or
  (or
  (exists ((s (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (and (and (= z empty2) (= z1 s)) (= z2 0)))
  (exists ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (s1 (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s2 (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))) (c Int))
  (and (is_finite_subset
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 s1)
  (t2tb1 s2) c)
  (and (mem2 x s2)
  (and (mem2 x s1) (and (and (= z (add2 x s1)) (= z1 s2)) (= z2 c)))))))
  (exists ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (s1 (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s2 (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))) (c Int))
  (and (is_finite_subset
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 s1)
  (t2tb1 s2) c)
  (and (mem2 x s2)
  (and (not (mem2 x s1))
  (and (and (= z (add2 x s1)) (= z1 s2)) (= z2 (+ c 1)))))))))))

;; is_finite_subset_inversion
  (assert
  (forall ((z (set enum_t_AUTOMATON_STATE)) (z1 (set enum_t_AUTOMATON_STATE))
  (z2 Int))
  (=> (is_finite_subset enum_t_AUTOMATON_STATE1 (t2tb2 z) (t2tb2 z1) z2)
  (or
  (or
  (exists ((s (set enum_t_AUTOMATON_STATE)))
  (and (and (= z empty1) (= z1 s)) (= z2 0)))
  (exists ((x enum_t_AUTOMATON_STATE) (s1 (set enum_t_AUTOMATON_STATE))
  (s2 (set enum_t_AUTOMATON_STATE)) (c Int))
  (and (is_finite_subset enum_t_AUTOMATON_STATE1 (t2tb2 s1) (t2tb2 s2) c)
  (and (mem1 x s2)
  (and (mem1 x s1) (and (and (= z (add1 x s1)) (= z1 s2)) (= z2 c)))))))
  (exists ((x enum_t_AUTOMATON_STATE) (s1 (set enum_t_AUTOMATON_STATE))
  (s2 (set enum_t_AUTOMATON_STATE)) (c Int))
  (and (is_finite_subset enum_t_AUTOMATON_STATE1 (t2tb2 s1) (t2tb2 s2) c)
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
  (=> (<= a b) (is_finite_subset int (t2tb7 (mk a b)) (t2tb7 integer)
  (+ (- b a) 1)))))

;; finite_interval_empty
  (assert
  (forall ((a Int) (b Int))
  (=> (< b a) (is_finite_subset int (t2tb7 (mk a b)) (t2tb7 integer) 0))))

(declare-fun finite_subsets (ty uni) uni)

;; finite_subsets_sort
  (assert
  (forall ((a ty))
  (forall ((x uni)) (sort (set1 (set1 a)) (finite_subsets a x)))))

;; finite_subsets_def
  (assert
  (forall ((s (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (= (mem3 x
  (tb2t
  (finite_subsets (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 s))))
  (exists ((c Int)) (is_finite_subset
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 x)
  (t2tb1 s) c)))))

;; finite_subsets_def
  (assert
  (forall ((a ty))
  (forall ((s uni) (x uni))
  (= (mem (set1 a) x (finite_subsets a s))
  (exists ((c Int)) (is_finite_subset a x s c))))))

;; finite_Empty
  (assert
  (forall ((s (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))) (mem
  (set1 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (t2tb empty3)
  (finite_subsets
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s)))))

;; finite_Empty
  (assert
  (forall ((s (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (mem3 empty2
  (tb2t
  (finite_subsets (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 s))))))

;; finite_Empty
  (assert
  (forall ((s (set enum_t_AUTOMATON_STATE))) (mem
  (set1 enum_t_AUTOMATON_STATE1) (t2tb2 empty1)
  (finite_subsets enum_t_AUTOMATON_STATE1 (t2tb2 s)))))

;; finite_Empty
  (assert
  (forall ((a ty))
  (forall ((s uni)) (mem (set1 a) (empty a) (finite_subsets a s)))))

;; finite_Add
  (assert
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s1 (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (s2 (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))))
  (=> (mem
  (set1 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (t2tb s1)
  (finite_subsets
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s2)))
  (=> (mem3 x s2) (mem
  (set1 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (t2tb (add3 x s1))
  (finite_subsets
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s2)))))))

;; finite_Add
  (assert
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (s1 (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s2 (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (=> (mem3 s1
  (tb2t
  (finite_subsets (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 s2))))
  (=> (mem2 x s2) (mem3 (add2 x s1)
  (tb2t
  (finite_subsets (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 s2))))))))

;; finite_Add
  (assert
  (forall ((x enum_t_AUTOMATON_STATE) (s1 (set enum_t_AUTOMATON_STATE))
  (s2 (set enum_t_AUTOMATON_STATE)))
  (=> (mem (set1 enum_t_AUTOMATON_STATE1) (t2tb2 s1)
  (finite_subsets enum_t_AUTOMATON_STATE1 (t2tb2 s2)))
  (=> (mem1 x s2) (mem (set1 enum_t_AUTOMATON_STATE1) (t2tb2 (add1 x s1))
  (finite_subsets enum_t_AUTOMATON_STATE1 (t2tb2 s2)))))))

;; finite_Add
  (assert
  (forall ((a ty))
  (forall ((x uni) (s1 uni) (s2 uni))
  (=> (mem (set1 a) s1 (finite_subsets a s2))
  (=> (mem a x s2) (mem (set1 a) (add a x s1) (finite_subsets a s2)))))))

;; finite_Union
  (assert
  (forall ((s1 (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (s2 (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (s3 (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))))
  (=> (mem
  (set1 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (t2tb s1)
  (finite_subsets
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s3)))
  (=> (mem
  (set1 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (t2tb s2)
  (finite_subsets
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s3)))
  (mem
  (set1 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (t2tb (union3 s1 s2))
  (finite_subsets
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s3)))))))

;; finite_Union
  (assert
  (forall ((s1 (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s2 (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s3 (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (=> (mem3 s1
  (tb2t
  (finite_subsets (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 s3))))
  (=> (mem3 s2
  (tb2t
  (finite_subsets (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 s3)))) (mem3 (union2 s1 s2)
  (tb2t
  (finite_subsets (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 s3))))))))

;; finite_Union
  (assert
  (forall ((s1 (set enum_t_AUTOMATON_STATE))
  (s2 (set enum_t_AUTOMATON_STATE)) (s3 (set enum_t_AUTOMATON_STATE)))
  (=> (mem (set1 enum_t_AUTOMATON_STATE1) (t2tb2 s1)
  (finite_subsets enum_t_AUTOMATON_STATE1 (t2tb2 s3)))
  (=> (mem (set1 enum_t_AUTOMATON_STATE1) (t2tb2 s2)
  (finite_subsets enum_t_AUTOMATON_STATE1 (t2tb2 s3))) (mem
  (set1 enum_t_AUTOMATON_STATE1) (t2tb2 (union1 s1 s2))
  (finite_subsets enum_t_AUTOMATON_STATE1 (t2tb2 s3)))))))

;; finite_Union
  (assert
  (forall ((a ty))
  (forall ((s1 uni) (s2 uni) (s3 uni))
  (=> (mem (set1 a) s1 (finite_subsets a s3))
  (=> (mem (set1 a) s2 (finite_subsets a s3)) (mem (set1 a) (union a s1 s2)
  (finite_subsets a s3)))))))

;; finite_inversion
  (assert
  (forall ((s1 (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (s2 (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))))
  (=> (mem
  (set1 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (t2tb s1)
  (finite_subsets
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s2)))
  (or (= s1 empty3)
  (exists ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s3 (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))))
  (and (= s1 (add3 x s3)) (mem
  (set1 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (t2tb s3)
  (finite_subsets
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s2)))))))))

;; finite_inversion
  (assert
  (forall ((s1 (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s2 (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (=> (mem3 s1
  (tb2t
  (finite_subsets (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 s2))))
  (or (= s1 empty2)
  (exists ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (s3 (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (and (= s1 (add2 x s3)) (mem3 s3
  (tb2t
  (finite_subsets (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 s2))))))))))

;; finite_inversion
  (assert
  (forall ((s1 (set enum_t_AUTOMATON_STATE))
  (s2 (set enum_t_AUTOMATON_STATE)))
  (=> (mem (set1 enum_t_AUTOMATON_STATE1) (t2tb2 s1)
  (finite_subsets enum_t_AUTOMATON_STATE1 (t2tb2 s2)))
  (or (= s1 empty1)
  (exists ((x enum_t_AUTOMATON_STATE) (s3 (set enum_t_AUTOMATON_STATE)))
  (and (= s1 (add1 x s3)) (mem (set1 enum_t_AUTOMATON_STATE1) (t2tb2 s3)
  (finite_subsets enum_t_AUTOMATON_STATE1 (t2tb2 s2)))))))))

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
  (forall ((s (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (x (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))))
  (= (mem
  (set1 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (t2tb x)
  (non_empty_finite_subsets
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s)))
  (exists ((c Int))
  (and (is_finite_subset
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb x)
  (t2tb s) c) (not (= x empty3)))))))

;; non_empty_finite_subsets_def
  (assert
  (forall ((s (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (= (mem3 x
  (tb2t
  (non_empty_finite_subsets
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 s))))
  (exists ((c Int))
  (and (is_finite_subset
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 x)
  (t2tb1 s) c) (not (= x empty2)))))))

;; non_empty_finite_subsets_def
  (assert
  (forall ((s (set enum_t_AUTOMATON_STATE)) (x (set enum_t_AUTOMATON_STATE)))
  (= (mem (set1 enum_t_AUTOMATON_STATE1) (t2tb2 x)
  (non_empty_finite_subsets enum_t_AUTOMATON_STATE1 (t2tb2 s)))
  (exists ((c Int))
  (and (is_finite_subset enum_t_AUTOMATON_STATE1 (t2tb2 x) (t2tb2 s) c)
  (not (= x empty1)))))))

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
  (= (card (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb empty3)) 0))

;; card_Empty
  (assert
  (= (card (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (t2tb1 empty2)) 0))

;; card_Empty
  (assert (= (card enum_t_AUTOMATON_STATE1 (t2tb2 empty1)) 0))

;; card_Empty
  (assert (forall ((a ty)) (= (card a (empty a)) 0)))

;; card_Add_not_mem
  (assert
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s1 (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (s2 (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))))
  (! (=> (mem
     (set1 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
     (t2tb s1)
     (finite_subsets
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb s2)))
     (=> (not (mem3 x s1))
     (= (card
        (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
        (t2tb (add3 x s1))) (+ (card
                               (set1
                               (tuple21 enum_t_AUTOMATON_STATE1
                               enum_t_AUTOMATON_STATE1)) (t2tb s1)) 1)))) :pattern ((mem
  (set1 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (t2tb s1)
  (finite_subsets
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s2)))
  (card (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (t2tb (add3 x s1)))) )))

;; card_Add_not_mem
  (assert
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (s1 (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s2 (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (! (=> (mem3 s1
     (tb2t
     (finite_subsets
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 s2))))
     (=> (not (mem2 x s1))
     (= (card (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
        (t2tb1 (add2 x s1))) (+ (card
                                (tuple21 enum_t_AUTOMATON_STATE1
                                enum_t_AUTOMATON_STATE1) (t2tb1 s1)) 1)))) :pattern ((mem3
  s1
  (tb2t
  (finite_subsets (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 s2))))
  (card (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 (add2 x s1)))) )))

;; card_Add_not_mem
  (assert
  (forall ((x enum_t_AUTOMATON_STATE) (s1 (set enum_t_AUTOMATON_STATE))
  (s2 (set enum_t_AUTOMATON_STATE)))
  (! (=> (mem (set1 enum_t_AUTOMATON_STATE1) (t2tb2 s1)
     (finite_subsets enum_t_AUTOMATON_STATE1 (t2tb2 s2)))
     (=> (not (mem1 x s1))
     (= (card enum_t_AUTOMATON_STATE1 (t2tb2 (add1 x s1))) (+ (card
                                                              enum_t_AUTOMATON_STATE1
                                                              (t2tb2 s1)) 1)))) :pattern ((mem
  (set1 enum_t_AUTOMATON_STATE1) (t2tb2 s1)
  (finite_subsets enum_t_AUTOMATON_STATE1 (t2tb2 s2)))
  (card enum_t_AUTOMATON_STATE1 (t2tb2 (add1 x s1)))) )))

;; card_Add_not_mem
  (assert
  (forall ((a ty))
  (forall ((x uni) (s1 uni) (s2 uni))
  (! (=> (mem (set1 a) s1 (finite_subsets a s2))
     (=> (not (mem a x s1)) (= (card a (add a x s1)) (+ (card a s1) 1)))) :pattern ((mem
  (set1 a) s1 (finite_subsets a s2)) (card a (add a x s1))) ))))

;; card_Add_mem
  (assert
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s1 (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (s2 (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))))
  (! (=> (mem
     (set1 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
     (t2tb s1)
     (finite_subsets
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb s2)))
     (=> (mem3 x s1)
     (= (card
        (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
        (t2tb (add3 x s1))) (card
                            (set1
                            (tuple21 enum_t_AUTOMATON_STATE1
                            enum_t_AUTOMATON_STATE1)) (t2tb s1))))) :pattern ((mem
  (set1 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (t2tb s1)
  (finite_subsets
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s2)))
  (card (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (t2tb (add3 x s1)))) )))

;; card_Add_mem
  (assert
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (s1 (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s2 (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (! (=> (mem3 s1
     (tb2t
     (finite_subsets
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 s2))))
     (=> (mem2 x s1)
     (= (card (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
        (t2tb1 (add2 x s1))) (card
                             (tuple21 enum_t_AUTOMATON_STATE1
                             enum_t_AUTOMATON_STATE1) (t2tb1 s1))))) :pattern ((mem3
  s1
  (tb2t
  (finite_subsets (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 s2))))
  (card (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 (add2 x s1)))) )))

;; card_Add_mem
  (assert
  (forall ((x enum_t_AUTOMATON_STATE) (s1 (set enum_t_AUTOMATON_STATE))
  (s2 (set enum_t_AUTOMATON_STATE)))
  (! (=> (mem (set1 enum_t_AUTOMATON_STATE1) (t2tb2 s1)
     (finite_subsets enum_t_AUTOMATON_STATE1 (t2tb2 s2)))
     (=> (mem1 x s1)
     (= (card enum_t_AUTOMATON_STATE1 (t2tb2 (add1 x s1))) (card
                                                           enum_t_AUTOMATON_STATE1
                                                           (t2tb2 s1))))) :pattern ((mem
  (set1 enum_t_AUTOMATON_STATE1) (t2tb2 s1)
  (finite_subsets enum_t_AUTOMATON_STATE1 (t2tb2 s2)))
  (card enum_t_AUTOMATON_STATE1 (t2tb2 (add1 x s1)))) )))

;; card_Add_mem
  (assert
  (forall ((a ty))
  (forall ((x uni) (s1 uni) (s2 uni))
  (! (=> (mem (set1 a) s1 (finite_subsets a s2))
     (=> (mem a x s1) (= (card a (add a x s1)) (card a s1)))) :pattern ((mem
  (set1 a) s1 (finite_subsets a s2)) (card a (add a x s1))) ))))

;; card_Union
  (assert
  (forall ((s1 (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (s2 (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (s3 (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))))
  (! (=> (mem
     (set1 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
     (t2tb s1)
     (finite_subsets
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb s3)))
     (=> (mem
     (set1 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
     (t2tb s2)
     (finite_subsets
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb s3)))
     (=> (is_empty
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (inter (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb s1) (t2tb s2)))
     (= (card
        (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
        (t2tb (union3 s1 s2))) (+ (card
                                  (set1
                                  (tuple21 enum_t_AUTOMATON_STATE1
                                  enum_t_AUTOMATON_STATE1)) (t2tb s1)) 
     (card (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb s2))))))) :pattern ((mem
  (set1 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (t2tb s1)
  (finite_subsets
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s3)))
  (mem
  (set1 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (t2tb s2)
  (finite_subsets
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s3)))
  (card (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (t2tb (union3 s1 s2)))) )))

;; card_Union
  (assert
  (forall ((s1 (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s2 (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (s3 (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (! (=> (mem3 s1
     (tb2t
     (finite_subsets
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 s3))))
     (=> (mem3 s2
     (tb2t
     (finite_subsets
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 s3))))
     (=> (is_empty (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (inter (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (t2tb1 s1) (t2tb1 s2)))
     (= (card (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
        (t2tb1 (union2 s1 s2))) (+ (card
                                   (tuple21 enum_t_AUTOMATON_STATE1
                                   enum_t_AUTOMATON_STATE1) (t2tb1 s1)) 
     (card (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (t2tb1 s2))))))) :pattern ((mem3
  s1
  (tb2t
  (finite_subsets (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 s3)))) (mem3 s2
  (tb2t
  (finite_subsets (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 s3))))
  (card (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 (union2 s1 s2)))) )))

;; card_Union
  (assert
  (forall ((s1 (set enum_t_AUTOMATON_STATE))
  (s2 (set enum_t_AUTOMATON_STATE)) (s3 (set enum_t_AUTOMATON_STATE)))
  (! (=> (mem (set1 enum_t_AUTOMATON_STATE1) (t2tb2 s1)
     (finite_subsets enum_t_AUTOMATON_STATE1 (t2tb2 s3)))
     (=> (mem (set1 enum_t_AUTOMATON_STATE1) (t2tb2 s2)
     (finite_subsets enum_t_AUTOMATON_STATE1 (t2tb2 s3)))
     (=> (is_empty enum_t_AUTOMATON_STATE1
     (inter enum_t_AUTOMATON_STATE1 (t2tb2 s1) (t2tb2 s2)))
     (= (card enum_t_AUTOMATON_STATE1 (t2tb2 (union1 s1 s2))) (+ (card
                                                                 enum_t_AUTOMATON_STATE1
                                                                 (t2tb2 s1)) 
     (card enum_t_AUTOMATON_STATE1 (t2tb2 s2))))))) :pattern ((mem
  (set1 enum_t_AUTOMATON_STATE1) (t2tb2 s1)
  (finite_subsets enum_t_AUTOMATON_STATE1 (t2tb2 s3))) (mem
  (set1 enum_t_AUTOMATON_STATE1) (t2tb2 s2)
  (finite_subsets enum_t_AUTOMATON_STATE1 (t2tb2 s3)))
  (card enum_t_AUTOMATON_STATE1 (t2tb2 (union1 s1 s2)))) )))

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
  (forall ((a1 uni) (b (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (x uni) (y (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (! (= (mem
     (tuple21 a
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
     (Tuple2 a
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) x
     (t2tb1 y))
     (times (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     a a1 (t2tb b))) (and (mem a x a1) (mem3 y b))) :pattern ((mem
  (tuple21 a
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 a (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  x (t2tb1 y))
  (times (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) a
  a1 (t2tb b)))) ))))

;; times_def
  (assert
  (forall ((a ty))
  (forall ((a1 uni) (b (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (x uni) (y (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))
  (! (= (mem
     (tuple21 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (Tuple2 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) x
     (t2tb3 y))
     (times (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) a a1
     (t2tb1 b))) (and (mem a x a1) (mem2 y b))) :pattern ((mem
  (tuple21 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) x
  (t2tb3 y))
  (times (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) a a1
  (t2tb1 b)))) ))))

;; times_def
  (assert
  (forall ((a ty))
  (forall ((a1 uni) (b (set enum_t_AUTOMATON_STATE)) (x uni)
  (y enum_t_AUTOMATON_STATE))
  (! (= (mem (tuple21 a enum_t_AUTOMATON_STATE1)
     (Tuple2 a enum_t_AUTOMATON_STATE1 x (t2tb4 y))
     (times enum_t_AUTOMATON_STATE1 a a1 (t2tb2 b)))
     (and (mem a x a1) (mem1 y b))) :pattern ((mem
  (tuple21 a enum_t_AUTOMATON_STATE1)
  (Tuple2 a enum_t_AUTOMATON_STATE1 x (t2tb4 y))
  (times enum_t_AUTOMATON_STATE1 a a1 (t2tb2 b)))) ))))

;; times_def
  (assert
  (forall ((a (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (b (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (x (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (y (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (! (= (mem
     (tuple21
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
     (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb1 x) (t2tb1 y))
     (times (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb a) (t2tb b))) (and (mem3 x a) (mem3 y b))) :pattern ((mem
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb1 x)
  (t2tb1 y))
  (times (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb a)
  (t2tb b)))) )))

;; times_def
  (assert
  (forall ((a (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (b (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (x (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (y (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))
  (! (= (mem
     (tuple21
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 x)
     (t2tb3 y))
     (times (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb a) (t2tb1 b))) (and (mem3 x a) (mem2 y b))) :pattern ((mem
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 x)
  (t2tb3 y))
  (times (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb a)
  (t2tb1 b)))) )))

;; times_def
  (assert
  (forall ((a (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (b (set enum_t_AUTOMATON_STATE))
  (x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (y enum_t_AUTOMATON_STATE))
  (! (= (mem
     (tuple21
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     enum_t_AUTOMATON_STATE1)
     (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     enum_t_AUTOMATON_STATE1 (t2tb1 x) (t2tb4 y))
     (times enum_t_AUTOMATON_STATE1
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb a) (t2tb2 b))) (and (mem3 x a) (mem1 y b))) :pattern ((mem
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  enum_t_AUTOMATON_STATE1)
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  enum_t_AUTOMATON_STATE1 (t2tb1 x) (t2tb4 y))
  (times enum_t_AUTOMATON_STATE1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb a)
  (t2tb2 b)))) )))

;; times_def
  (assert
  (forall ((b ty))
  (forall ((a (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (b1 uni) (x (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (y uni))
  (! (= (mem
     (tuple21
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) b)
     (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     b (t2tb1 x) y)
     (times b
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb a) b1)) (and (mem3 x a) (mem b y b1))) :pattern ((mem
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  b)
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) b
  (t2tb1 x) y)
  (times b (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (t2tb a) b1))) ))))

;; times_def
  (assert
  (forall ((a (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (b (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (y (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (! (= (mem
     (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
     (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb3 x) (t2tb1 y))
     (times (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 a)
     (t2tb b))) (and (mem2 x a) (mem3 y b))) :pattern ((mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb3 x)
  (t2tb1 y))
  (times (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 a)
  (t2tb b)))) )))

;; times_def
  (assert
  (forall ((a (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (b (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (y (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (! (= (mem
     (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb3 x)
     (t2tb3 y))
     (times (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 a)
     (t2tb1 b))) (and (mem2 x a) (mem2 y b))) :pattern ((mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb3 x)
  (t2tb3 y))
  (times (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 a)
  (t2tb1 b)))) )))

;; times_def
  (assert
  (forall ((a (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (b (set enum_t_AUTOMATON_STATE)) (x (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (y enum_t_AUTOMATON_STATE))
  (! (= (mem
     (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     enum_t_AUTOMATON_STATE1)
     (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     enum_t_AUTOMATON_STATE1 (t2tb3 x) (t2tb4 y))
     (times enum_t_AUTOMATON_STATE1
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 a)
     (t2tb2 b))) (and (mem2 x a) (mem1 y b))) :pattern ((mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  enum_t_AUTOMATON_STATE1)
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  enum_t_AUTOMATON_STATE1 (t2tb3 x) (t2tb4 y))
  (times enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 a)
  (t2tb2 b)))) )))

;; times_def
  (assert
  (forall ((b ty))
  (forall ((a (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (b1 uni) (x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (y uni))
  (! (= (mem
     (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)
     (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b
     (t2tb3 x) y)
     (times b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     (t2tb1 a) b1)) (and (mem2 x a) (mem b y b1))) :pattern ((mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b
  (t2tb3 x) y)
  (times b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 a) b1))) ))))

;; times_def
  (assert
  (forall ((a (set enum_t_AUTOMATON_STATE))
  (b (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (x enum_t_AUTOMATON_STATE) (y (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (! (= (mem
     (tuple21 enum_t_AUTOMATON_STATE1
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
     (Tuple2 enum_t_AUTOMATON_STATE1
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb4 x) (t2tb1 y))
     (times (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     enum_t_AUTOMATON_STATE1 (t2tb2 a) (t2tb b)))
     (and (mem1 x a) (mem3 y b))) :pattern ((mem
  (tuple21 enum_t_AUTOMATON_STATE1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 enum_t_AUTOMATON_STATE1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb4 x)
  (t2tb1 y))
  (times (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  enum_t_AUTOMATON_STATE1 (t2tb2 a) (t2tb b)))) )))

;; times_def
  (assert
  (forall ((a (set enum_t_AUTOMATON_STATE))
  (b (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (x enum_t_AUTOMATON_STATE) (y (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))
  (! (= (mem
     (tuple21 enum_t_AUTOMATON_STATE1
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (Tuple2 enum_t_AUTOMATON_STATE1
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb4 x)
     (t2tb3 y))
     (times (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
     enum_t_AUTOMATON_STATE1 (t2tb2 a) (t2tb1 b)))
     (and (mem1 x a) (mem2 y b))) :pattern ((mem
  (tuple21 enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb4 x)
  (t2tb3 y))
  (times (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  enum_t_AUTOMATON_STATE1 (t2tb2 a) (t2tb1 b)))) )))

;; times_def
  (assert
  (forall ((a (set enum_t_AUTOMATON_STATE)) (b (set enum_t_AUTOMATON_STATE))
  (x enum_t_AUTOMATON_STATE) (y enum_t_AUTOMATON_STATE))
  (! (= (mem2 (Tuple21 x y)
     (tb2t1
     (times enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 a)
     (t2tb2 b)))) (and (mem1 x a) (mem1 y b))) :pattern ((mem2
  (Tuple21 x y)
  (tb2t1
  (times enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 a) (t2tb2 b))))) )))

;; times_def
  (assert
  (forall ((b ty))
  (forall ((a (set enum_t_AUTOMATON_STATE)) (b1 uni)
  (x enum_t_AUTOMATON_STATE) (y uni))
  (! (= (mem (tuple21 enum_t_AUTOMATON_STATE1 b)
     (Tuple2 enum_t_AUTOMATON_STATE1 b (t2tb4 x) y)
     (times b enum_t_AUTOMATON_STATE1 (t2tb2 a) b1))
     (and (mem1 x a) (mem b y b1))) :pattern ((mem
  (tuple21 enum_t_AUTOMATON_STATE1 b)
  (Tuple2 enum_t_AUTOMATON_STATE1 b (t2tb4 x) y)
  (times b enum_t_AUTOMATON_STATE1 (t2tb2 a) b1))) ))))

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
  (forall ((c (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (s (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (x enum_t_AUTOMATON_STATE) (y enum_t_AUTOMATON_STATE))
  (= (mem2 c (add2 (Tuple21 x y) s)) (or (= c (Tuple21 x y)) (mem2 c s)))))

;; break_mem_in_add
  (assert
  (forall ((a ty) (b ty))
  (forall ((c uni) (s uni) (x uni) (y uni))
  (=> (sort (tuple21 a b) c)
  (= (mem (tuple21 a b) c (add (tuple21 a b) (Tuple2 a b x y) s))
  (or (= c (Tuple2 a b x y)) (mem (tuple21 a b) c s)))))))

;; break_power_times
  (assert
  (forall ((r (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (u (set enum_t_AUTOMATON_STATE)) (v (set enum_t_AUTOMATON_STATE)))
  (= (mem3 r
  (tb2t
  (power1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (times enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 u) (t2tb2 v)))))
  (subset (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 r)
  (times enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 u) (t2tb2 v))))))

;; break_power_times
  (assert
  (forall ((a ty) (b ty))
  (forall ((r uni) (u uni) (v uni))
  (= (mem (set1 (tuple21 a b)) r (power1 (tuple21 a b) (times b a u v)))
  (subset (tuple21 a b) r (times b a u v))))))

;; subset_of_times
  (assert
  (forall ((a ty))
  (forall ((r uni) (u uni) (v (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))))
  (and
  (=> (subset
  (tuple21 a
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))) r
  (times (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) a u
  (t2tb v)))
  (forall ((x uni) (y (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (=> (mem
  (tuple21 a
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 a (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  x (t2tb1 y)) r) (and (mem a x u) (mem3 y v)))))
  (=>
  (forall ((x uni) (y (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (=> (sort a x)
  (=> (mem
  (tuple21 a
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 a (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  x (t2tb1 y)) r) (and (mem a x u) (mem3 y v))))) (subset
  (tuple21 a
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))) r
  (times (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) a u
  (t2tb v))))))))

;; subset_of_times
  (assert
  (forall ((a ty))
  (forall ((r uni) (u uni) (v (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (and
  (=> (subset
  (tuple21 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) r
  (times (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) a u
  (t2tb1 v)))
  (forall ((x uni) (y (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))
  (=> (mem
  (tuple21 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) x
  (t2tb3 y)) r) (and (mem a x u) (mem2 y v)))))
  (=>
  (forall ((x uni) (y (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))
  (=> (sort a x)
  (=> (mem
  (tuple21 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) x
  (t2tb3 y)) r) (and (mem a x u) (mem2 y v))))) (subset
  (tuple21 a (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) r
  (times (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) a u
  (t2tb1 v))))))))

;; subset_of_times
  (assert
  (forall ((a ty))
  (forall ((r uni) (u uni) (v (set enum_t_AUTOMATON_STATE)))
  (and
  (=> (subset (tuple21 a enum_t_AUTOMATON_STATE1) r
  (times enum_t_AUTOMATON_STATE1 a u (t2tb2 v)))
  (forall ((x uni) (y enum_t_AUTOMATON_STATE))
  (=> (mem (tuple21 a enum_t_AUTOMATON_STATE1)
  (Tuple2 a enum_t_AUTOMATON_STATE1 x (t2tb4 y)) r)
  (and (mem a x u) (mem1 y v)))))
  (=>
  (forall ((x uni) (y enum_t_AUTOMATON_STATE))
  (=> (sort a x)
  (=> (mem (tuple21 a enum_t_AUTOMATON_STATE1)
  (Tuple2 a enum_t_AUTOMATON_STATE1 x (t2tb4 y)) r)
  (and (mem a x u) (mem1 y v))))) (subset (tuple21 a enum_t_AUTOMATON_STATE1)
  r (times enum_t_AUTOMATON_STATE1 a u (t2tb2 v))))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))) (u (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (v (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))))
  (= (subset
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (t2tb12 r)
  (times (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb u)
  (t2tb v)))
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (y (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (=> (mem
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb1 x)
  (t2tb1 y)) (t2tb12 r)) (and (mem3 x u) (mem3 y v)))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (u (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (v (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (= (subset
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb15 r)
  (times (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb u)
  (t2tb1 v)))
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (y (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (=> (mem
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 x)
  (t2tb3 y)) (t2tb15 r)) (and (mem3 x u) (mem2 y v)))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) enum_t_AUTOMATON_STATE)))
  (u (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (v (set enum_t_AUTOMATON_STATE)))
  (= (subset
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  enum_t_AUTOMATON_STATE1) (t2tb18 r)
  (times enum_t_AUTOMATON_STATE1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb u)
  (t2tb2 v)))
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (y enum_t_AUTOMATON_STATE))
  (=> (mem
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  enum_t_AUTOMATON_STATE1)
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  enum_t_AUTOMATON_STATE1 (t2tb1 x) (t2tb4 y)) (t2tb18 r))
  (and (mem3 x u) (mem1 y v)))))))

;; subset_of_times
  (assert
  (forall ((b ty))
  (forall ((r uni) (u (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (v uni))
  (and
  (=> (subset
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  b) r
  (times b (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (t2tb u) v))
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (y uni))
  (=> (mem
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  b)
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) b
  (t2tb1 x) y) r) (and (mem3 x u) (mem b y v)))))
  (=>
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (y uni))
  (=> (sort b y)
  (=> (mem
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  b)
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) b
  (t2tb1 x) y) r) (and (mem3 x u) (mem b y v))))) (subset
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  b) r
  (times b (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (t2tb u) v)))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))) (u (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))))
  (= (subset
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (t2tb20 r)
  (times (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 u)
  (t2tb v)))
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (y (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (=> (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb3 x)
  (t2tb1 y)) (t2tb20 r)) (and (mem2 x u) (mem3 y v)))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (u (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (= (subset
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb24 r)
  (times (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 u)
  (t2tb1 v)))
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (y (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (=> (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb3 x)
  (t2tb3 y)) (t2tb24 r)) (and (mem2 x u) (mem2 y v)))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE) enum_t_AUTOMATON_STATE)))
  (u (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (v (set enum_t_AUTOMATON_STATE)))
  (= (subset
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  enum_t_AUTOMATON_STATE1) (t2tb27 r)
  (times enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 u)
  (t2tb2 v)))
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (y enum_t_AUTOMATON_STATE))
  (=> (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  enum_t_AUTOMATON_STATE1)
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  enum_t_AUTOMATON_STATE1 (t2tb3 x) (t2tb4 y)) (t2tb27 r))
  (and (mem2 x u) (mem1 y v)))))))

;; subset_of_times
  (assert
  (forall ((b ty))
  (forall ((r uni) (u (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v uni))
  (and
  (=> (subset
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b) r
  (times b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 u) v))
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (y uni))
  (=> (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b
  (t2tb3 x) y) r) (and (mem2 x u) (mem b y v)))))
  (=>
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (y uni))
  (=> (sort b y)
  (=> (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b
  (t2tb3 x) y) r) (and (mem2 x u) (mem b y v))))) (subset
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b) r
  (times b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 u) v)))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 enum_t_AUTOMATON_STATE
  (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))))
  (u (set enum_t_AUTOMATON_STATE))
  (v (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))))
  (= (subset
  (tuple21 enum_t_AUTOMATON_STATE1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (t2tb30 r)
  (times (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  enum_t_AUTOMATON_STATE1 (t2tb2 u) (t2tb v)))
  (forall ((x enum_t_AUTOMATON_STATE) (y (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (=> (mem
  (tuple21 enum_t_AUTOMATON_STATE1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 enum_t_AUTOMATON_STATE1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb4 x)
  (t2tb1 y)) (t2tb30 r)) (and (mem1 x u) (mem3 y v)))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 enum_t_AUTOMATON_STATE
  (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (u (set enum_t_AUTOMATON_STATE)) (v (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (= (subset
  (tuple21 enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb34 r)
  (times (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  enum_t_AUTOMATON_STATE1 (t2tb2 u) (t2tb1 v)))
  (forall ((x enum_t_AUTOMATON_STATE) (y (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))
  (=> (mem
  (tuple21 enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 enum_t_AUTOMATON_STATE1
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb4 x)
  (t2tb3 y)) (t2tb34 r)) (and (mem1 x u) (mem2 y v)))))))

;; subset_of_times
  (assert
  (forall ((r (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (u (set enum_t_AUTOMATON_STATE)) (v (set enum_t_AUTOMATON_STATE)))
  (= (subset (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 r)
  (times enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 u) (t2tb2 v)))
  (forall ((x enum_t_AUTOMATON_STATE) (y enum_t_AUTOMATON_STATE))
  (=> (mem2 (Tuple21 x y) r) (and (mem1 x u) (mem1 y v)))))))

;; subset_of_times
  (assert
  (forall ((b ty))
  (forall ((r uni) (u (set enum_t_AUTOMATON_STATE)) (v uni))
  (and
  (=> (subset (tuple21 enum_t_AUTOMATON_STATE1 b) r
  (times b enum_t_AUTOMATON_STATE1 (t2tb2 u) v))
  (forall ((x enum_t_AUTOMATON_STATE) (y uni))
  (=> (mem (tuple21 enum_t_AUTOMATON_STATE1 b)
  (Tuple2 enum_t_AUTOMATON_STATE1 b (t2tb4 x) y) r)
  (and (mem1 x u) (mem b y v)))))
  (=>
  (forall ((x enum_t_AUTOMATON_STATE) (y uni))
  (=> (sort b y)
  (=> (mem (tuple21 enum_t_AUTOMATON_STATE1 b)
  (Tuple2 enum_t_AUTOMATON_STATE1 b (t2tb4 x) y) r)
  (and (mem1 x u) (mem b y v))))) (subset (tuple21 enum_t_AUTOMATON_STATE1 b)
  r (times b enum_t_AUTOMATON_STATE1 (t2tb2 u) v)))))))

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
  (forall ((s uni) (x uni) (y (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (! (=> (mem a x s)
     (= (tb2t1
        (apply
        (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) a
        (times
        (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) a s
        (t2tb (add3 y empty3))) x)) y)) :pattern ((tb2t1
                                                  (apply
                                                  (set1
                                                  (tuple21
                                                  enum_t_AUTOMATON_STATE1
                                                  enum_t_AUTOMATON_STATE1)) a
                                                  (times
                                                  (set1
                                                  (tuple21
                                                  enum_t_AUTOMATON_STATE1
                                                  enum_t_AUTOMATON_STATE1)) a
                                                  s (t2tb (add3 y empty3)))
                                                  x))) ))))

;; apply_times
  (assert
  (forall ((a ty))
  (forall ((s uni) (x uni) (y (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))
  (! (=> (mem a x s)
     (= (tb2t3
        (apply (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) a
        (times (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) a s
        (t2tb1 (add2 y empty2))) x)) y)) :pattern ((tb2t3
                                                   (apply
                                                   (tuple21
                                                   enum_t_AUTOMATON_STATE1
                                                   enum_t_AUTOMATON_STATE1) a
                                                   (times
                                                   (tuple21
                                                   enum_t_AUTOMATON_STATE1
                                                   enum_t_AUTOMATON_STATE1) a
                                                   s (t2tb1 (add2 y empty2)))
                                                   x))) ))))

;; apply_times
  (assert
  (forall ((a ty))
  (forall ((s uni) (x uni) (y enum_t_AUTOMATON_STATE))
  (! (=> (mem a x s)
     (= (tb2t4
        (apply enum_t_AUTOMATON_STATE1 a
        (times enum_t_AUTOMATON_STATE1 a s (t2tb2 (add1 y empty1))) x)) y)) :pattern (
  (tb2t4
  (apply enum_t_AUTOMATON_STATE1 a
  (times enum_t_AUTOMATON_STATE1 a s (t2tb2 (add1 y empty1))) x))) ))))

;; apply_times
  (assert
  (forall ((s (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (x (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (y (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))
  (! (=> (mem3 x s)
     (= (tb2t1
        (apply
        (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
        (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
        (times
        (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
        (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
        (t2tb s) (t2tb (add3 y empty3))) (t2tb1 x))) y)) :pattern ((tb2t1
                                                                   (apply
                                                                   (set1
                                                                   (tuple21
                                                                   enum_t_AUTOMATON_STATE1
                                                                   enum_t_AUTOMATON_STATE1))
                                                                   (set1
                                                                   (tuple21
                                                                   enum_t_AUTOMATON_STATE1
                                                                   enum_t_AUTOMATON_STATE1))
                                                                   (times
                                                                   (set1
                                                                   (tuple21
                                                                   enum_t_AUTOMATON_STATE1
                                                                   enum_t_AUTOMATON_STATE1))
                                                                   (set1
                                                                   (tuple21
                                                                   enum_t_AUTOMATON_STATE1
                                                                   enum_t_AUTOMATON_STATE1))
                                                                   (t2tb s)
                                                                   (t2tb
                                                                   (add3 y
                                                                   empty3)))
                                                                   (t2tb1 x)))) )))

;; apply_times
  (assert
  (forall ((s (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (x (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (y (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))
  (! (=> (mem3 x s)
     (= (tb2t3
        (apply (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
        (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
        (times (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
        (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
        (t2tb s) (t2tb1 (add2 y empty2))) (t2tb1 x))) y)) :pattern ((tb2t3
                                                                    (apply
                                                                    (tuple21
                                                                    enum_t_AUTOMATON_STATE1
                                                                    enum_t_AUTOMATON_STATE1)
                                                                    (set1
                                                                    (tuple21
                                                                    enum_t_AUTOMATON_STATE1
                                                                    enum_t_AUTOMATON_STATE1))
                                                                    (times
                                                                    (tuple21
                                                                    enum_t_AUTOMATON_STATE1
                                                                    enum_t_AUTOMATON_STATE1)
                                                                    (set1
                                                                    (tuple21
                                                                    enum_t_AUTOMATON_STATE1
                                                                    enum_t_AUTOMATON_STATE1))
                                                                    (t2tb s)
                                                                    (t2tb1
                                                                    (add2 y
                                                                    empty2)))
                                                                    (t2tb1 x)))) )))

;; apply_times
  (assert
  (forall ((s (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (x (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (y enum_t_AUTOMATON_STATE))
  (! (=> (mem3 x s)
     (= (tb2t4
        (apply enum_t_AUTOMATON_STATE1
        (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
        (times enum_t_AUTOMATON_STATE1
        (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
        (t2tb s) (t2tb2 (add1 y empty1))) (t2tb1 x))) y)) :pattern ((tb2t4
                                                                    (apply
                                                                    enum_t_AUTOMATON_STATE1
                                                                    (set1
                                                                    (tuple21
                                                                    enum_t_AUTOMATON_STATE1
                                                                    enum_t_AUTOMATON_STATE1))
                                                                    (times
                                                                    enum_t_AUTOMATON_STATE1
                                                                    (set1
                                                                    (tuple21
                                                                    enum_t_AUTOMATON_STATE1
                                                                    enum_t_AUTOMATON_STATE1))
                                                                    (t2tb s)
                                                                    (t2tb2
                                                                    (add1 y
                                                                    empty1)))
                                                                    (t2tb1 x)))) )))

;; apply_times
  (assert
  (forall ((b ty))
  (forall ((s (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (x (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (y uni))
  (! (=> (sort b y)
     (=> (mem3 x s)
     (= (apply b
        (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
        (times b
        (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
        (t2tb s) (add b y (empty b))) (t2tb1 x)) y))) :pattern ((apply b
                                                                (set1
                                                                (tuple21
                                                                enum_t_AUTOMATON_STATE1
                                                                enum_t_AUTOMATON_STATE1))
                                                                (times b
                                                                (set1
                                                                (tuple21
                                                                enum_t_AUTOMATON_STATE1
                                                                enum_t_AUTOMATON_STATE1))
                                                                (t2tb s)
                                                                (add b y
                                                                (empty b)))
                                                                (t2tb1 x))) ))))

;; apply_times
  (assert
  (forall ((s (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (y (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (! (=> (mem2 x s)
     (= (tb2t1
        (apply
        (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
        (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
        (times
        (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
        (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 s)
        (t2tb (add3 y empty3))) (t2tb3 x))) y)) :pattern ((tb2t1
                                                          (apply
                                                          (set1
                                                          (tuple21
                                                          enum_t_AUTOMATON_STATE1
                                                          enum_t_AUTOMATON_STATE1))
                                                          (tuple21
                                                          enum_t_AUTOMATON_STATE1
                                                          enum_t_AUTOMATON_STATE1)
                                                          (times
                                                          (set1
                                                          (tuple21
                                                          enum_t_AUTOMATON_STATE1
                                                          enum_t_AUTOMATON_STATE1))
                                                          (tuple21
                                                          enum_t_AUTOMATON_STATE1
                                                          enum_t_AUTOMATON_STATE1)
                                                          (t2tb1 s)
                                                          (t2tb
                                                          (add3 y empty3)))
                                                          (t2tb3 x)))) )))

;; apply_times
  (assert
  (forall ((s (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (y (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (! (=> (mem2 x s)
     (= (tb2t3
        (apply (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
        (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
        (times (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
        (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 s)
        (t2tb1 (add2 y empty2))) (t2tb3 x))) y)) :pattern ((tb2t3
                                                           (apply
                                                           (tuple21
                                                           enum_t_AUTOMATON_STATE1
                                                           enum_t_AUTOMATON_STATE1)
                                                           (tuple21
                                                           enum_t_AUTOMATON_STATE1
                                                           enum_t_AUTOMATON_STATE1)
                                                           (times
                                                           (tuple21
                                                           enum_t_AUTOMATON_STATE1
                                                           enum_t_AUTOMATON_STATE1)
                                                           (tuple21
                                                           enum_t_AUTOMATON_STATE1
                                                           enum_t_AUTOMATON_STATE1)
                                                           (t2tb1 s)
                                                           (t2tb1
                                                           (add2 y empty2)))
                                                           (t2tb3 x)))) )))

;; apply_times
  (assert
  (forall ((s (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (y enum_t_AUTOMATON_STATE))
  (! (=> (mem2 x s)
     (= (tb2t4
        (apply enum_t_AUTOMATON_STATE1
        (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
        (times enum_t_AUTOMATON_STATE1
        (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 s)
        (t2tb2 (add1 y empty1))) (t2tb3 x))) y)) :pattern ((tb2t4
                                                           (apply
                                                           enum_t_AUTOMATON_STATE1
                                                           (tuple21
                                                           enum_t_AUTOMATON_STATE1
                                                           enum_t_AUTOMATON_STATE1)
                                                           (times
                                                           enum_t_AUTOMATON_STATE1
                                                           (tuple21
                                                           enum_t_AUTOMATON_STATE1
                                                           enum_t_AUTOMATON_STATE1)
                                                           (t2tb1 s)
                                                           (t2tb2
                                                           (add1 y empty1)))
                                                           (t2tb3 x)))) )))

;; apply_times
  (assert
  (forall ((b ty))
  (forall ((s (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)) (y uni))
  (! (=> (sort b y)
     (=> (mem2 x s)
     (= (apply b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
        (times b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
        (t2tb1 s) (add b y (empty b))) (t2tb3 x)) y))) :pattern ((apply b
                                                                 (tuple21
                                                                 enum_t_AUTOMATON_STATE1
                                                                 enum_t_AUTOMATON_STATE1)
                                                                 (times b
                                                                 (tuple21
                                                                 enum_t_AUTOMATON_STATE1
                                                                 enum_t_AUTOMATON_STATE1)
                                                                 (t2tb1 s)
                                                                 (add b y
                                                                 (empty b)))
                                                                 (t2tb3 x))) ))))

;; apply_times
  (assert
  (forall ((s (set enum_t_AUTOMATON_STATE)) (x enum_t_AUTOMATON_STATE)
  (y (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (! (=> (mem1 x s)
     (= (tb2t1
        (apply
        (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
        enum_t_AUTOMATON_STATE1
        (times
        (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
        enum_t_AUTOMATON_STATE1 (t2tb2 s) (t2tb (add3 y empty3))) (t2tb4 x))) y)) :pattern (
  (tb2t1
  (apply (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  enum_t_AUTOMATON_STATE1
  (times (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  enum_t_AUTOMATON_STATE1 (t2tb2 s) (t2tb (add3 y empty3))) (t2tb4 x)))) )))

;; apply_times
  (assert
  (forall ((s (set enum_t_AUTOMATON_STATE)) (x enum_t_AUTOMATON_STATE)
  (y (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (! (=> (mem1 x s)
     (= (tb2t3
        (apply (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
        enum_t_AUTOMATON_STATE1
        (times (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
        enum_t_AUTOMATON_STATE1 (t2tb2 s) (t2tb1 (add2 y empty2))) (t2tb4 x))) y)) :pattern (
  (tb2t3
  (apply (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  enum_t_AUTOMATON_STATE1
  (times (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  enum_t_AUTOMATON_STATE1 (t2tb2 s) (t2tb1 (add2 y empty2))) (t2tb4 x)))) )))

;; apply_times
  (assert
  (forall ((s (set enum_t_AUTOMATON_STATE)) (x enum_t_AUTOMATON_STATE)
  (y enum_t_AUTOMATON_STATE))
  (! (=> (mem1 x s)
     (= (tb2t4
        (apply enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
        (times enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
        (t2tb2 (add1 y empty1))) (t2tb4 x))) y)) :pattern ((tb2t4
                                                           (apply
                                                           enum_t_AUTOMATON_STATE1
                                                           enum_t_AUTOMATON_STATE1
                                                           (times
                                                           enum_t_AUTOMATON_STATE1
                                                           enum_t_AUTOMATON_STATE1
                                                           (t2tb2 s)
                                                           (t2tb2
                                                           (add1 y empty1)))
                                                           (t2tb4 x)))) )))

;; apply_times
  (assert
  (forall ((b ty))
  (forall ((s (set enum_t_AUTOMATON_STATE)) (x enum_t_AUTOMATON_STATE)
  (y uni))
  (! (=> (sort b y)
     (=> (mem1 x s)
     (= (apply b enum_t_AUTOMATON_STATE1
        (times b enum_t_AUTOMATON_STATE1 (t2tb2 s) (add b y (empty b)))
        (t2tb4 x)) y))) :pattern ((apply b enum_t_AUTOMATON_STATE1
                                  (times b enum_t_AUTOMATON_STATE1 (t2tb2 s)
                                  (add b y (empty b))) (t2tb4 x))) ))))

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
  (forall ((x uni) (y (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (r uni)
  (f (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))))
  (=> (subset
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb f)
  (ran (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) e1 r))
  (= (mem
  (tuple21 e1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 e1 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  x (t2tb1 y))
  (range_restriction
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) e1 r
  (t2tb f)))
  (and (mem
  (tuple21 e1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 e1 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  x (t2tb1 y)) r) (mem3 y f)))))))

;; range_restriction_def
  (assert
  (forall ((e1 ty))
  (forall ((x uni) (y (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (r uni) (f (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (=> (subset (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 f)
  (ran (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) e1 r))
  (= (mem
  (tuple21 e1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 e1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) x
  (t2tb3 y))
  (range_restriction
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) e1 r (t2tb1 f)))
  (and (mem
  (tuple21 e1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 e1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) x
  (t2tb3 y)) r) (mem2 y f)))))))

;; range_restriction_def
  (assert
  (forall ((e1 ty))
  (forall ((x uni) (y enum_t_AUTOMATON_STATE) (r uni)
  (f (set enum_t_AUTOMATON_STATE)))
  (=> (subset enum_t_AUTOMATON_STATE1 (t2tb2 f)
  (ran enum_t_AUTOMATON_STATE1 e1 r))
  (= (mem (tuple21 e1 enum_t_AUTOMATON_STATE1)
  (Tuple2 e1 enum_t_AUTOMATON_STATE1 x (t2tb4 y))
  (range_restriction enum_t_AUTOMATON_STATE1 e1 r (t2tb2 f)))
  (and (mem (tuple21 e1 enum_t_AUTOMATON_STATE1)
  (Tuple2 e1 enum_t_AUTOMATON_STATE1 x (t2tb4 y)) r) (mem1 y f)))))))

;; range_restriction_def
  (assert
  (forall ((x enum_t_AUTOMATON_STATE) (y enum_t_AUTOMATON_STATE)
  (r (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (f (set enum_t_AUTOMATON_STATE)))
  (=> (subset enum_t_AUTOMATON_STATE1 (t2tb2 f)
  (ran enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb1 r)))
  (= (mem2 (Tuple21 x y)
  (tb2t1
  (range_restriction enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
  (t2tb1 r) (t2tb2 f)))) (and (mem2 (Tuple21 x y) r) (mem1 y f))))))

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
  (forall ((x uni) (y (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (r uni)
  (f (set (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))))
  (= (mem
  (tuple21 e1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 e1 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  x (t2tb1 y))
  (range_substraction
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) e1 r
  (t2tb f)))
  (and (mem
  (tuple21 e1
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (Tuple2 e1 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  x (t2tb1 y)) r) (not (mem3 y f)))))))

;; range_substraction_def
  (assert
  (forall ((e1 ty))
  (forall ((x uni) (y (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))
  (r uni) (f (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (= (mem
  (tuple21 e1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 e1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) x
  (t2tb3 y))
  (range_substraction
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) e1 r (t2tb1 f)))
  (and (mem
  (tuple21 e1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (Tuple2 e1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) x
  (t2tb3 y)) r) (not (mem2 y f)))))))

;; range_substraction_def
  (assert
  (forall ((e1 ty))
  (forall ((x uni) (y enum_t_AUTOMATON_STATE) (r uni)
  (f (set enum_t_AUTOMATON_STATE)))
  (= (mem (tuple21 e1 enum_t_AUTOMATON_STATE1)
  (Tuple2 e1 enum_t_AUTOMATON_STATE1 x (t2tb4 y))
  (range_substraction enum_t_AUTOMATON_STATE1 e1 r (t2tb2 f)))
  (and (mem (tuple21 e1 enum_t_AUTOMATON_STATE1)
  (Tuple2 e1 enum_t_AUTOMATON_STATE1 x (t2tb4 y)) r) (not (mem1 y f)))))))

;; range_substraction_def
  (assert
  (forall ((x enum_t_AUTOMATON_STATE) (y enum_t_AUTOMATON_STATE)
  (r (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (f (set enum_t_AUTOMATON_STATE)))
  (= (mem2 (Tuple21 x y)
  (tb2t1
  (range_substraction enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
  (t2tb1 r) (t2tb2 f)))) (and (mem2 (Tuple21 x y) r) (not (mem1 y f))))))

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
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (y uni) (r uni) (f (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))))
  (= (mem
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  e2)
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) e2
  (t2tb1 x) y)
  (domain_restriction e2
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb f)
  r))
  (and (mem
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  e2)
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) e2
  (t2tb1 x) y) r) (mem3 x f))))))

;; domain_restriction_def
  (assert
  (forall ((e2 ty))
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)) (y uni)
  (r uni) (f (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (= (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) e2)
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) e2
  (t2tb3 x) y)
  (domain_restriction e2
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 f) r))
  (and (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) e2)
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) e2
  (t2tb3 x) y) r) (mem2 x f))))))

;; domain_restriction_def
  (assert
  (forall ((x enum_t_AUTOMATON_STATE) (y enum_t_AUTOMATON_STATE)
  (r (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (f (set enum_t_AUTOMATON_STATE)))
  (= (mem2 (Tuple21 x y)
  (tb2t1
  (domain_restriction enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
  (t2tb2 f) (t2tb1 r)))) (and (mem2 (Tuple21 x y) r) (mem1 x f)))))

;; domain_restriction_def
  (assert
  (forall ((e2 ty))
  (forall ((x enum_t_AUTOMATON_STATE) (y uni) (r uni)
  (f (set enum_t_AUTOMATON_STATE)))
  (= (mem (tuple21 enum_t_AUTOMATON_STATE1 e2)
  (Tuple2 enum_t_AUTOMATON_STATE1 e2 (t2tb4 x) y)
  (domain_restriction e2 enum_t_AUTOMATON_STATE1 (t2tb2 f) r))
  (and (mem (tuple21 enum_t_AUTOMATON_STATE1 e2)
  (Tuple2 enum_t_AUTOMATON_STATE1 e2 (t2tb4 x) y) r) (mem1 x f))))))

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
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (y uni) (r uni) (f (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))))
  (=> (subset
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb f)
  (dom e2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) r))
  (= (mem
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  e2)
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) e2
  (t2tb1 x) y)
  (domain_substraction e2
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb f)
  r))
  (and (mem
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  e2)
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) e2
  (t2tb1 x) y) r) (not (mem3 x f))))))))

;; domain_substraction_def
  (assert
  (forall ((e2 ty))
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)) (y uni)
  (r uni) (f (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (=> (subset (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 f)
  (dom e2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) r))
  (= (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) e2)
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) e2
  (t2tb3 x) y)
  (domain_substraction e2
  (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 f) r))
  (and (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) e2)
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) e2
  (t2tb3 x) y) r) (not (mem2 x f))))))))

;; domain_substraction_def
  (assert
  (forall ((x enum_t_AUTOMATON_STATE) (y enum_t_AUTOMATON_STATE)
  (r (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (f (set enum_t_AUTOMATON_STATE)))
  (=> (subset enum_t_AUTOMATON_STATE1 (t2tb2 f)
  (dom enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb1 r)))
  (= (mem2 (Tuple21 x y)
  (tb2t1
  (domain_substraction enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
  (t2tb2 f) (t2tb1 r)))) (and (mem2 (Tuple21 x y) r) (not (mem1 x f)))))))

;; domain_substraction_def
  (assert
  (forall ((e2 ty))
  (forall ((x enum_t_AUTOMATON_STATE) (y uni) (r uni)
  (f (set enum_t_AUTOMATON_STATE)))
  (=> (subset enum_t_AUTOMATON_STATE1 (t2tb2 f)
  (dom e2 enum_t_AUTOMATON_STATE1 r))
  (= (mem (tuple21 enum_t_AUTOMATON_STATE1 e2)
  (Tuple2 enum_t_AUTOMATON_STATE1 e2 (t2tb4 x) y)
  (domain_substraction e2 enum_t_AUTOMATON_STATE1 (t2tb2 f) r))
  (and (mem (tuple21 enum_t_AUTOMATON_STATE1 e2)
  (Tuple2 enum_t_AUTOMATON_STATE1 e2 (t2tb4 x) y) r) (not (mem1 x f))))))))

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
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (y uni) (q uni) (r uni))
  (= (mem
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  b)
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) b
  (t2tb1 x) y)
  (infix_lspl b
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) q r))
  (ite (mem3 x
  (tb2t
  (dom b (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) r)))
  (mem
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  b)
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) b
  (t2tb1 x) y) r) (mem
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  b)
  (Tuple2 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) b
  (t2tb1 x) y) q))))))

;; overriding_def
  (assert
  (forall ((b ty))
  (forall ((x (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)) (y uni)
  (q uni) (r uni))
  (= (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b
  (t2tb3 x) y)
  (infix_lspl b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) q
  r))
  (ite (mem2 x
  (tb2t1 (dom b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) r)))
  (mem (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b
  (t2tb3 x) y) r) (mem
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)
  (Tuple2 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b
  (t2tb3 x) y) q))))))

;; overriding_def
  (assert
  (forall ((x enum_t_AUTOMATON_STATE) (y enum_t_AUTOMATON_STATE)
  (q (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (r (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (= (mem2 (Tuple21 x y)
  (tb2t1
  (infix_lspl enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb1 q)
  (t2tb1 r))))
  (ite (mem1 x
  (tb2t2 (dom enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb1 r))))
  (mem2 (Tuple21 x y) r) (mem2 (Tuple21 x y) q)))))

;; overriding_def
  (assert
  (forall ((b ty))
  (forall ((x enum_t_AUTOMATON_STATE) (y uni) (q uni) (r uni))
  (= (mem (tuple21 enum_t_AUTOMATON_STATE1 b)
  (Tuple2 enum_t_AUTOMATON_STATE1 b (t2tb4 x) y)
  (infix_lspl b enum_t_AUTOMATON_STATE1 q r))
  (ite (mem1 x (tb2t2 (dom b enum_t_AUTOMATON_STATE1 r))) (mem
  (tuple21 enum_t_AUTOMATON_STATE1 b)
  (Tuple2 enum_t_AUTOMATON_STATE1 b (t2tb4 x) y) r) (mem
  (tuple21 enum_t_AUTOMATON_STATE1 b)
  (Tuple2 enum_t_AUTOMATON_STATE1 b (t2tb4 x) y) q))))))

;; overriding_def
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (y uni) (q uni) (r uni))
  (= (mem (tuple21 a b) (Tuple2 a b x y) (infix_lspl b a q r))
  (ite (mem a x (dom b a r)) (mem (tuple21 a b) (Tuple2 a b x y) r) (mem
  (tuple21 a b) (Tuple2 a b x y) q))))))

;; function_overriding
  (assert
  (forall ((s (set enum_t_AUTOMATON_STATE)) (t (set enum_t_AUTOMATON_STATE))
  (f (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (g (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (=>
  (and (mem3 f
  (tb2t
  (infix_plmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 t)))) (mem3 g
  (tb2t
  (infix_plmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 t))))) (mem3
  (tb2t1
  (infix_lspl enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb1 f)
  (t2tb1 g)))
  (tb2t
  (infix_plmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 t)))))))

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
  (! (= (tb2t
        (dom b
        (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
        (infix_lspl b
        (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) f g))) 
  (union3
  (tb2t
  (dom b (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) f))
  (tb2t
  (dom b (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) g)))) :pattern (
  (tb2t
  (dom b (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (infix_lspl b
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) f g)))) ))))

;; dom_overriding
  (assert
  (forall ((b ty))
  (forall ((f uni) (g uni))
  (! (= (tb2t1
        (dom b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
        (infix_lspl b
        (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) f g))) 
  (union2
  (tb2t1 (dom b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) f))
  (tb2t1 (dom b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) g)))) :pattern (
  (tb2t1
  (dom b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (infix_lspl b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) f
  g)))) ))))

;; dom_overriding
  (assert
  (forall ((b ty))
  (forall ((f uni) (g uni))
  (! (= (tb2t2
        (dom b enum_t_AUTOMATON_STATE1
        (infix_lspl b enum_t_AUTOMATON_STATE1 f g))) (union1
                                                     (tb2t2
                                                     (dom b
                                                     enum_t_AUTOMATON_STATE1
                                                     f))
                                                     (tb2t2
                                                     (dom b
                                                     enum_t_AUTOMATON_STATE1
                                                     g)))) :pattern (
  (tb2t2
  (dom b enum_t_AUTOMATON_STATE1 (infix_lspl b enum_t_AUTOMATON_STATE1 f g)))) ))))

;; dom_overriding
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (g uni))
  (! (= (dom b a (infix_lspl b a f g)) (union a (dom b a f) (dom b a g))) :pattern (
  (dom b a (infix_lspl b a f g))) ))))

;; apply_overriding_1
  (assert
  (forall ((b ty))
  (forall ((s (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (t uni) (f uni) (g uni)
  (x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (! (=>
     (and (mem
     (set1
     (tuple21
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) b)) f
     (infix_plmngt b
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb s) t)) (mem
     (set1
     (tuple21
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) b)) g
     (infix_plmngt b
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb s) t)))
     (=> (mem3 x
     (tb2t
     (dom b (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     g)))
     (= (apply b
        (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
        (infix_lspl b
        (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) f g)
        (t2tb1 x)) (apply b
                   (set1
                   (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
                   g (t2tb1 x))))) :pattern ((mem
  (set1
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  b)) f
  (infix_plmngt b
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s)
  t)) (mem
  (set1
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  b)) g
  (infix_plmngt b
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s)
  t))
  (apply b (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (infix_lspl b
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) f g)
  (t2tb1 x))) ))))

;; apply_overriding_1
  (assert
  (forall ((b ty))
  (forall ((s (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (t uni) (f uni) (g uni) (x (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))
  (! (=>
     (and (mem
     (set1
     (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)) f
     (infix_plmngt b
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 s) t))
     (mem
     (set1
     (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)) g
     (infix_plmngt b
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 s) t)))
     (=> (mem2 x
     (tb2t1
     (dom b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) g)))
     (= (apply b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
        (infix_lspl b
        (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) f g)
        (t2tb3 x)) (apply b
                   (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
                   g (t2tb3 x))))) :pattern ((mem
  (set1
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)) f
  (infix_plmngt b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 s) t)) (mem
  (set1
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)) g
  (infix_plmngt b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 s) t))
  (apply b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (infix_lspl b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) f
  g) (t2tb3 x))) ))))

;; apply_overriding_1
  (assert
  (forall ((s (set enum_t_AUTOMATON_STATE)) (t (set enum_t_AUTOMATON_STATE))
  (f (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (g (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (x enum_t_AUTOMATON_STATE))
  (! (=>
     (and (mem3 f
     (tb2t
     (infix_plmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
     (t2tb2 t)))) (mem3 g
     (tb2t
     (infix_plmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
     (t2tb2 t)))))
     (=> (mem1 x
     (tb2t2 (dom enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb1 g))))
     (= (tb2t4
        (apply enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
        (infix_lspl enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb1 f)
        (t2tb1 g)) (t2tb4 x))) (tb2t4
                               (apply enum_t_AUTOMATON_STATE1
                               enum_t_AUTOMATON_STATE1 (t2tb1 g) (t2tb4 x)))))) :pattern ((mem3
  f
  (tb2t
  (infix_plmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 t)))) (mem3 g
  (tb2t
  (infix_plmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 t))))
  (tb2t4
  (apply enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
  (infix_lspl enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb1 f)
  (t2tb1 g)) (t2tb4 x)))) )))

;; apply_overriding_1
  (assert
  (forall ((b ty))
  (forall ((s (set enum_t_AUTOMATON_STATE)) (t uni) (f uni) (g uni)
  (x enum_t_AUTOMATON_STATE))
  (! (=>
     (and (mem (set1 (tuple21 enum_t_AUTOMATON_STATE1 b)) f
     (infix_plmngt b enum_t_AUTOMATON_STATE1 (t2tb2 s) t)) (mem
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 b)) g
     (infix_plmngt b enum_t_AUTOMATON_STATE1 (t2tb2 s) t)))
     (=> (mem1 x (tb2t2 (dom b enum_t_AUTOMATON_STATE1 g)))
     (= (apply b enum_t_AUTOMATON_STATE1
        (infix_lspl b enum_t_AUTOMATON_STATE1 f g) (t2tb4 x)) (apply b
                                                              enum_t_AUTOMATON_STATE1
                                                              g (t2tb4 x))))) :pattern ((mem
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 b)) f
  (infix_plmngt b enum_t_AUTOMATON_STATE1 (t2tb2 s) t)) (mem
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 b)) g
  (infix_plmngt b enum_t_AUTOMATON_STATE1 (t2tb2 s) t))
  (apply b enum_t_AUTOMATON_STATE1 (infix_lspl b enum_t_AUTOMATON_STATE1 f g)
  (t2tb4 x))) ))))

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
  (forall ((s (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) (t uni) (f uni) (g uni)
  (x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (! (=>
     (and (mem
     (set1
     (tuple21
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) b)) f
     (infix_plmngt b
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb s) t)) (mem
     (set1
     (tuple21
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) b)) g
     (infix_plmngt b
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     (t2tb s) t)))
     (=>
     (not (mem3 x
     (tb2t
     (dom b (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     g))))
     (=> (mem3 x
     (tb2t
     (dom b (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
     f)))
     (= (apply b
        (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
        (infix_lspl b
        (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) f g)
        (t2tb1 x)) (apply b
                   (set1
                   (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
                   f (t2tb1 x)))))) :pattern ((mem
  (set1
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  b)) f
  (infix_plmngt b
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s)
  t))
  (apply b (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (infix_lspl b
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) f g)
  (t2tb1 x))) :pattern ((mem
  (set1
  (tuple21 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  b)) g
  (infix_plmngt b
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) (t2tb s)
  t))
  (apply b (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (infix_lspl b
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) f g)
  (t2tb1 x))) ))))

;; apply_overriding_2
  (assert
  (forall ((b ty))
  (forall ((s (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (t uni) (f uni) (g uni) (x (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))
  (! (=>
     (and (mem
     (set1
     (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)) f
     (infix_plmngt b
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 s) t))
     (mem
     (set1
     (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)) g
     (infix_plmngt b
     (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) (t2tb1 s) t)))
     (=>
     (not (mem2 x
     (tb2t1
     (dom b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) g))))
     (=> (mem2 x
     (tb2t1
     (dom b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) f)))
     (= (apply b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
        (infix_lspl b
        (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) f g)
        (t2tb3 x)) (apply b
                   (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
                   f (t2tb3 x)))))) :pattern ((mem
  (set1
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)) f
  (infix_plmngt b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 s) t))
  (apply b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (infix_lspl b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) f
  g) (t2tb3 x))) :pattern ((mem
  (set1
  (tuple21 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) b)) g
  (infix_plmngt b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (t2tb1 s) t))
  (apply b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)
  (infix_lspl b (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1) f
  g) (t2tb3 x))) ))))

;; apply_overriding_2
  (assert
  (forall ((s (set enum_t_AUTOMATON_STATE)) (t (set enum_t_AUTOMATON_STATE))
  (f (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (g (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE)))
  (x enum_t_AUTOMATON_STATE))
  (! (=>
     (and (mem3 f
     (tb2t
     (infix_plmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
     (t2tb2 t)))) (mem3 g
     (tb2t
     (infix_plmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
     (t2tb2 t)))))
     (=>
     (not (mem1 x
     (tb2t2 (dom enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb1 g)))))
     (=> (mem1 x
     (tb2t2 (dom enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb1 f))))
     (= (tb2t4
        (apply enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
        (infix_lspl enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb1 f)
        (t2tb1 g)) (t2tb4 x))) (tb2t4
                               (apply enum_t_AUTOMATON_STATE1
                               enum_t_AUTOMATON_STATE1 (t2tb1 f) (t2tb4 x))))))) :pattern ((mem3
  f
  (tb2t
  (infix_plmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 t))))
  (tb2t4
  (apply enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
  (infix_lspl enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb1 f)
  (t2tb1 g)) (t2tb4 x)))) :pattern ((mem3 g
  (tb2t
  (infix_plmngt enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb2 s)
  (t2tb2 t))))
  (tb2t4
  (apply enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
  (infix_lspl enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1 (t2tb1 f)
  (t2tb1 g)) (t2tb4 x)))) )))

;; apply_overriding_2
  (assert
  (forall ((b ty))
  (forall ((s (set enum_t_AUTOMATON_STATE)) (t uni) (f uni) (g uni)
  (x enum_t_AUTOMATON_STATE))
  (! (=>
     (and (mem (set1 (tuple21 enum_t_AUTOMATON_STATE1 b)) f
     (infix_plmngt b enum_t_AUTOMATON_STATE1 (t2tb2 s) t)) (mem
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 b)) g
     (infix_plmngt b enum_t_AUTOMATON_STATE1 (t2tb2 s) t)))
     (=> (not (mem1 x (tb2t2 (dom b enum_t_AUTOMATON_STATE1 g))))
     (=> (mem1 x (tb2t2 (dom b enum_t_AUTOMATON_STATE1 f)))
     (= (apply b enum_t_AUTOMATON_STATE1
        (infix_lspl b enum_t_AUTOMATON_STATE1 f g) (t2tb4 x)) (apply b
                                                              enum_t_AUTOMATON_STATE1
                                                              f (t2tb4 x)))))) :pattern ((mem
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 b)) f
  (infix_plmngt b enum_t_AUTOMATON_STATE1 (t2tb2 s) t))
  (apply b enum_t_AUTOMATON_STATE1 (infix_lspl b enum_t_AUTOMATON_STATE1 f g)
  (t2tb4 x))) :pattern ((mem (set1 (tuple21 enum_t_AUTOMATON_STATE1 b)) g
  (infix_plmngt b enum_t_AUTOMATON_STATE1 (t2tb2 s) t))
  (apply b enum_t_AUTOMATON_STATE1 (infix_lspl b enum_t_AUTOMATON_STATE1 f g)
  (t2tb4 x))) ))))

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

(declare-fun E_empty_open () enum_t_AUTOMATON_STATE)

(declare-fun E_train_open () enum_t_AUTOMATON_STATE)

(declare-fun E_train_primary_closing () enum_t_AUTOMATON_STATE)

(declare-fun E_train_secondary_wait () enum_t_AUTOMATON_STATE)

(declare-fun E_train_secondary_closing () enum_t_AUTOMATON_STATE)

(declare-fun E_train_closed () enum_t_AUTOMATON_STATE)

(declare-fun E_empty_closed () enum_t_AUTOMATON_STATE)

(declare-fun E_empty_opening () enum_t_AUTOMATON_STATE)

(declare-fun E_failure () enum_t_AUTOMATON_STATE)

(declare-fun match_enum_t_AUTOMATON_STATE (ty enum_t_AUTOMATON_STATE uni uni
  uni uni uni uni uni uni uni) uni)

;; match_enum_t_AUTOMATON_STATE_sort
  (assert
  (forall ((a ty))
  (forall ((x enum_t_AUTOMATON_STATE) (x1 uni) (x2 uni) (x3 uni) (x4 uni)
  (x5 uni) (x6 uni) (x7 uni) (x8 uni) (x9 uni)) (sort a
  (match_enum_t_AUTOMATON_STATE a x x1 x2 x3 x4 x5 x6 x7 x8 x9)))))

;; match_enum_t_AUTOMATON_STATE_E_empty_open
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni))
  (=> (sort a z)
  (= (match_enum_t_AUTOMATON_STATE a E_empty_open z z1 z2 z3 z4 z5 z6 z7 z8) z)))))

;; match_enum_t_AUTOMATON_STATE_E_train_open
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni))
  (=> (sort a z1)
  (= (match_enum_t_AUTOMATON_STATE a E_train_open z z1 z2 z3 z4 z5 z6 z7 z8) z1)))))

;; match_enum_t_AUTOMATON_STATE_E_train_primary_closing
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni))
  (=> (sort a z2)
  (= (match_enum_t_AUTOMATON_STATE a E_train_primary_closing z z1 z2 z3 z4 z5
     z6 z7 z8) z2)))))

;; match_enum_t_AUTOMATON_STATE_E_train_secondary_wait
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni))
  (=> (sort a z3)
  (= (match_enum_t_AUTOMATON_STATE a E_train_secondary_wait z z1 z2 z3 z4 z5
     z6 z7 z8) z3)))))

;; match_enum_t_AUTOMATON_STATE_E_train_secondary_closing
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni))
  (=> (sort a z4)
  (= (match_enum_t_AUTOMATON_STATE a E_train_secondary_closing z z1 z2 z3 z4
     z5 z6 z7 z8) z4)))))

;; match_enum_t_AUTOMATON_STATE_E_train_closed
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni))
  (=> (sort a z5)
  (= (match_enum_t_AUTOMATON_STATE a E_train_closed z z1 z2 z3 z4 z5 z6 z7
     z8) z5)))))

;; match_enum_t_AUTOMATON_STATE_E_empty_closed
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni))
  (=> (sort a z6)
  (= (match_enum_t_AUTOMATON_STATE a E_empty_closed z z1 z2 z3 z4 z5 z6 z7
     z8) z6)))))

;; match_enum_t_AUTOMATON_STATE_E_empty_opening
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni))
  (=> (sort a z7)
  (= (match_enum_t_AUTOMATON_STATE a E_empty_opening z z1 z2 z3 z4 z5 z6 z7
     z8) z7)))))

;; match_enum_t_AUTOMATON_STATE_E_failure
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni) (z2 uni) (z3 uni) (z4 uni) (z5 uni) (z6 uni)
  (z7 uni) (z8 uni))
  (=> (sort a z8)
  (= (match_enum_t_AUTOMATON_STATE a E_failure z z1 z2 z3 z4 z5 z6 z7 z8) z8)))))

(declare-fun index_enum_t_AUTOMATON_STATE (enum_t_AUTOMATON_STATE) Int)

;; index_enum_t_AUTOMATON_STATE_E_empty_open
  (assert (= (index_enum_t_AUTOMATON_STATE E_empty_open) 0))

;; index_enum_t_AUTOMATON_STATE_E_train_open
  (assert (= (index_enum_t_AUTOMATON_STATE E_train_open) 1))

;; index_enum_t_AUTOMATON_STATE_E_train_primary_closing
  (assert (= (index_enum_t_AUTOMATON_STATE E_train_primary_closing) 2))

;; index_enum_t_AUTOMATON_STATE_E_train_secondary_wait
  (assert (= (index_enum_t_AUTOMATON_STATE E_train_secondary_wait) 3))

;; index_enum_t_AUTOMATON_STATE_E_train_secondary_closing
  (assert (= (index_enum_t_AUTOMATON_STATE E_train_secondary_closing) 4))

;; index_enum_t_AUTOMATON_STATE_E_train_closed
  (assert (= (index_enum_t_AUTOMATON_STATE E_train_closed) 5))

;; index_enum_t_AUTOMATON_STATE_E_empty_closed
  (assert (= (index_enum_t_AUTOMATON_STATE E_empty_closed) 6))

;; index_enum_t_AUTOMATON_STATE_E_empty_opening
  (assert (= (index_enum_t_AUTOMATON_STATE E_empty_opening) 7))

;; index_enum_t_AUTOMATON_STATE_E_failure
  (assert (= (index_enum_t_AUTOMATON_STATE E_failure) 8))

;; enum_t_AUTOMATON_STATE_inversion
  (assert
  (forall ((u enum_t_AUTOMATON_STATE))
  (or
  (or
  (or
  (or
  (or
  (or
  (or (or (= u E_empty_open) (= u E_train_open))
  (= u E_train_primary_closing)) (= u E_train_secondary_wait))
  (= u E_train_secondary_closing)) (= u E_train_closed))
  (= u E_empty_closed)) (= u E_empty_opening)) (= u E_failure))))

(declare-fun set_enum_t_AUTOMATON_STATE () (set enum_t_AUTOMATON_STATE))

;; set_enum_t_AUTOMATON_STATE_axiom
  (assert
  (forall ((x enum_t_AUTOMATON_STATE)) (mem1 x set_enum_t_AUTOMATON_STATE)))

(assert
;; ValuesLemmas_1
 ;; File "POwhy_bpo2why/RCS3/Automaton_context_i.why", line 1007, characters 7-21
  (not (mem3
  (union2
  (union2
  (union2
  (union2
  (union2
  (union2
  (union2
  (union2
  (union2
  (union2
  (union2
  (union2
  (union2
  (union2
  (union2
  (union2
  (union2
  (union2
  (union2
  (union2
  (union2
  (union2
  (union2
  (union2
  (union2
  (union2
  (union2 (add2 (Tuple21 E_empty_open E_empty_open) empty2)
  (add2 (Tuple21 E_empty_open E_train_open) empty2))
  (add2 (Tuple21 E_empty_open E_failure) empty2))
  (add2 (Tuple21 E_train_open E_train_open) empty2))
  (add2 (Tuple21 E_train_open E_train_primary_closing) empty2))
  (add2 (Tuple21 E_train_open E_failure) empty2))
  (add2 (Tuple21 E_train_primary_closing E_train_primary_closing) empty2))
  (add2 (Tuple21 E_train_primary_closing E_train_closed) empty2))
  (add2 (Tuple21 E_train_primary_closing E_train_secondary_wait) empty2))
  (add2 (Tuple21 E_train_primary_closing E_failure) empty2))
  (add2 (Tuple21 E_train_secondary_wait E_train_secondary_wait) empty2))
  (add2 (Tuple21 E_train_secondary_wait E_train_secondary_closing) empty2))
  (add2 (Tuple21 E_train_secondary_wait E_failure) empty2))
  (add2 (Tuple21 E_train_secondary_closing E_train_secondary_closing) empty2))
  (add2 (Tuple21 E_train_secondary_closing E_train_closed) empty2))
  (add2 (Tuple21 E_train_secondary_closing E_failure) empty2))
  (add2 (Tuple21 E_train_closed E_train_closed) empty2))
  (add2 (Tuple21 E_train_closed E_empty_closed) empty2))
  (add2 (Tuple21 E_train_closed E_failure) empty2))
  (add2 (Tuple21 E_empty_closed E_empty_closed) empty2))
  (add2 (Tuple21 E_empty_closed E_empty_opening) empty2))
  (add2 (Tuple21 E_empty_closed E_train_closed) empty2))
  (add2 (Tuple21 E_empty_closed E_failure) empty2))
  (add2 (Tuple21 E_empty_opening E_empty_opening) empty2))
  (add2 (Tuple21 E_empty_opening E_empty_open) empty2))
  (add2 (Tuple21 E_empty_opening E_train_open) empty2))
  (add2 (Tuple21 E_empty_opening E_failure) empty2))
  (add2 (Tuple21 E_failure E_failure) empty2))
  (relation1 set_enum_t_AUTOMATON_STATE set_enum_t_AUTOMATON_STATE))))
(check-sat)
