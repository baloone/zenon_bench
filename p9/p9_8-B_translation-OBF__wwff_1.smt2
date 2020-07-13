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

(declare-fun infix_eqeq (ty uni uni) Bool)

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
  (forall ((a ty))
  (forall ((s uni))
  (and (=> (is_empty a s) (forall ((x uni)) (not (mem a x s))))
  (=> (forall ((x uni)) (=> (sort a x) (not (mem a x s)))) (is_empty a s))))))

;; empty_def1
  (assert (forall ((a ty)) (is_empty a (empty a))))

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
  (assert
  (forall ((a Int) (b Int)) (=> (< b a) (= (mk a b) (tb2t1 (empty int))))))

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
  (infix_eqeq (tuple21 int int) (t2tb6 v_OBF__yyee)
  (image (tuple21 int int) int
  (ran (tuple21 int (tuple21 int int)) int
  (domain_restriction (tuple21 int (tuple21 int int)) int (t2tb1 v_OBF__xxee)
  (direct_product (tuple21 int int) int int (t2tb6 v_OBF__wwee)
  (direct_product int int int (t2tb6 v_OBF__ttee) (t2tb6 v_OBF__vvee)))))
  (add int (t2tb12 v_OBF__rrbb) (empty int))))) (infix_eqeq (tuple21 int int)
  (t2tb6 v_OBF__zzee)
  (image (tuple21 int int) int
  (ran (tuple21 int (tuple21 int int)) int
  (domain_restriction (tuple21 int (tuple21 int int)) int (t2tb1 v_OBF__xxee)
  (direct_product (tuple21 int int) int int (t2tb6 v_OBF__wwee)
  (direct_product int int int (t2tb6 v_OBF__ttee) (t2tb6 v_OBF__vvee)))))
  (add int (t2tb12 v_OBF__mmbb) (empty int))))) (infix_eqeq (tuple21 int int)
  (t2tb6 v_OBF__oodd)
  (image (tuple21 int int) int
  (ran (tuple21 int (tuple21 int int)) int
  (domain_restriction (tuple21 int (tuple21 int int)) int (t2tb1 v_OBF__xxee)
  (direct_product (tuple21 int int) int int (t2tb6 v_OBF__wwee)
  (direct_product int int int (t2tb6 v_OBF__ttee) (t2tb6 v_OBF__vvee)))))
  (add int (t2tb12 v_OBF__ffbb) (empty int))))) (infix_eqeq (tuple21 int int)
  (t2tb6 v_OBF__nndd)
  (image (tuple21 int int) int
  (ran (tuple21 int (tuple21 int int)) int
  (domain_restriction (tuple21 int (tuple21 int int)) int (t2tb1 v_OBF__xxee)
  (direct_product (tuple21 int int) int int (t2tb6 v_OBF__wwee)
  (direct_product int int int (t2tb6 v_OBF__uuee) (t2tb6 v_OBF__vvee)))))
  (add int (t2tb12 v_OBF__ffbb) (empty int))))) (mem (set1 (tuple21 int int))
  (t2tb6 v_OBF__uuee) (power (tuple21 int int) (t2tb6 v_OBF__ttee)))) (mem
  (set1 (tuple21 int int)) (t2tb6 v_OBF__vvee)
  (infix_plmngt int int (t2tb1 v_OBF__ddcc) (t2tb1 v_OBF__bbbb))))
  (infix_eqeq int (dom int int (t2tb6 v_OBF__vvee)) (t2tb1 v_OBF__ddcc)))
  (mem (set1 int) (ran int int (t2tb6 v_OBF__wwee))
  (power int
  (union int
  (union int (add int (t2tb12 v_OBF__rrbb) (empty int))
  (add int (t2tb12 v_OBF__mmbb) (empty int)))
  (add int (t2tb12 v_OBF__ffbb) (empty int)))))) (mem (set1 int)
  (t2tb1 v_OBF__ddcc) (finite_subsets int (t2tb1 integer))))
  (not (infix_eqeq int (t2tb1 v_OBF__ddcc) (empty int)))) (mem
  (set1 (tuple21 int int)) (t2tb6 v_OBF__oodd)
  (relation int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb)))) (mem
  (set1 (tuple21 int int)) (t2tb6 v_OBF__nndd)
  (relation int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb)))) (mem
  (set1 int) (t2tb1 v_OBF__ppdd) (power int (t2tb1 v_OBF__bbbb))))
  (infix_eqeq (tuple21 int int) (t2tb6 v_OBF__aaff)
  (times int int
  (diff int (dom int int (t2tb6 v_OBF__oodd))
  (dom (tuple21 int int) int
  (range_substraction (tuple21 int int) int
  (direct_product int int int (t2tb6 v_OBF__oodd) (t2tb6 v_OBF__oodd))
  (id int (t2tb1 v_OBF__bbbb))))) (t2tb1 v_OBF__bbbb)))) (mem
  (set1 (tuple21 int int)) (t2tb6 v_OBF__nndd)
  (power (tuple21 int int) (t2tb6 v_OBF__oodd)))) (mem int
  (t2tb12 v_OBF__xxbb) (t2tb1 v_OBF__bbbb))) (mem (set1 (tuple21 int int))
  (t2tb6 v_OBF__yyee)
  (power (tuple21 int int)
  (times int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb))))) (mem
  (set1 (tuple21 int int)) (t2tb6 v_OBF__zzee)
  (power (tuple21 int int)
  (times int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb)))))
  (not (= v_OBF__xxbb v_OBF__sscc))) (infix_eqeq (tuple21 int int)
  (t2tb6 v_OBF__bbff)
  (union (tuple21 int int) (t2tb6 v_OBF__yyee)
  (semicolon int int int (t2tb6 v_OBF__yyee)
  (times int int (add int (t2tb12 v_OBF__xxbb) (empty int))
  (t2tb1 v_OBF__bbbb)))))) (infix_eqeq (tuple21 int int) (t2tb6 v_OBF__ccff)
  (union (tuple21 int int) (t2tb6 v_OBF__zzee)
  (semicolon int int int (t2tb6 v_OBF__zzee)
  (times int int (add int (t2tb12 v_OBF__xxbb) (empty int))
  (t2tb1 v_OBF__bbbb)))))) (mem int (t2tb12 v_OBF__oobb)
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
  (not (= v_OBF__uucc v_OBF__ttcc))) (infix_eqeq int (t2tb1 v_OBF__eecc)
  (union int
  (union int (union int (t2tb1 v_OBF__uu) (t2tb1 v_OBF__rrcc))
  (t2tb1 v_OBF__qqcc))
  (union int
  (union int
  (union int (add int (t2tb12 v_OBF__iibb) (empty int))
  (add int (t2tb12 v_OBF__jjbb) (empty int)))
  (add int (t2tb12 v_OBF__ttcc) (empty int)))
  (add int (t2tb12 v_OBF__uucc) (empty int)))))) (infix_eqeq
  (tuple21 int int) (t2tb6 v_OBF__eeff)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (domain_restriction int int (t2tb1 v_OBF__uu) (t2tb6 v_OBF__bbff))
  (times int int (t2tb1 v_OBF__qqcc) (t2tb1 v_OBF__ddff)))
  (times int int
  (union int (add int (t2tb12 v_OBF__iibb) (empty int))
  (add int (t2tb12 v_OBF__jjbb) (empty int))) (t2tb1 v_OBF__ddff)))
  (times int int (t2tb1 v_OBF__rrcc)
  (add int (t2tb12 v_OBF__sscc) (empty int))))
  (times int int (t2tb1 v_OBF__qqbb) (t2tb1 v_OBF__bbbb)))
  (times int int (add int (t2tb12 v_OBF__ttcc) (empty int))
  (t2tb1 v_OBF__bbbb)))
  (add (tuple21 int int)
  (Tuple2 int int (t2tb12 v_OBF__uucc) (t2tb12 v_OBF__sscc))
  (empty (tuple21 int int)))))) (infix_eqeq (tuple21 (tuple21 int int) int)
  (t2tb4 v_OBF__ffff)
  (union (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (domain_restriction int int (t2tb1 v_OBF__uu) (t2tb6 v_OBF__ccff))
  (times int int (t2tb1 v_OBF__qqcc) (t2tb1 v_OBF__ddff)))
  (add (tuple21 int int)
  (Tuple2 int int (t2tb12 v_OBF__uucc) (t2tb12 v_OBF__sscc))
  (empty (tuple21 int int)))) (t2tb1 v_OBF__wwcc))
  (times int (tuple21 int int)
  (times int int
  (union int (add int (t2tb12 v_OBF__iibb) (empty int))
  (add int (t2tb12 v_OBF__jjbb) (empty int))) (t2tb1 v_OBF__ddff))
  (add int (t2tb12 v_OBF__oobb) (empty int)))))) (infix_eqeq
  (tuple21 int int) (t2tb6 v_OBF__ggff)
  (domain_restriction int int (t2tb1 v_OBF__uu) (t2tb6 v_OBF__aaff)))) (mem
  int (t2tb12 v_OBF__dddd) (t2tb1 integer))) (infix_eqeq (tuple21 int int)
  (t2tb6 v_OBF__hhff)
  (times int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb)))) (infix_eqeq
  (tuple21 int int) (t2tb6 v_OBF__iiff)
  (times int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb))))
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
  (t2tb1 integer))))) (infix_eqeq (tuple21 (tuple21 int enum_OBF__aa1) int)
  (t2tb2 v_OBF__jjff)
  (times int (tuple21 int enum_OBF__aa1)
  (times enum_OBF__aa1 int (add int (t2tb12 0) (empty int))
  (union enum_OBF__aa1
  (union enum_OBF__aa1
  (union enum_OBF__aa1
  (union enum_OBF__aa1
  (add enum_OBF__aa1 (t2tb162 E_OBF__bb) (empty enum_OBF__aa1))
  (add enum_OBF__aa1 (t2tb162 E_OBF__ff) (empty enum_OBF__aa1)))
  (add enum_OBF__aa1 (t2tb162 E_OBF__gg) (empty enum_OBF__aa1)))
  (add enum_OBF__aa1 (t2tb162 E_OBF__ee) (empty enum_OBF__aa1)))
  (add enum_OBF__aa1 (t2tb162 E_OBF__cc) (empty enum_OBF__aa1))))
  (add int (t2tb12 0) (empty int))))) (infix_eqeq
  (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 v_OBF__kkff)
  (times int (tuple21 int enum_OBF__aa1)
  (times enum_OBF__aa1 int (add int (t2tb12 0) (empty int))
  (union enum_OBF__aa1
  (add enum_OBF__aa1 (t2tb162 E_OBF__hh) (empty enum_OBF__aa1))
  (add enum_OBF__aa1 (t2tb162 E_OBF__dd) (empty enum_OBF__aa1))))
  (add int (t2tb12 1) (empty int))))) (infix_eqeq
  (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 v_OBF__llff)
  (times int (tuple21 int enum_OBF__aa1)
  (times enum_OBF__aa1 int (add int (t2tb12 1) (empty int))
  (add enum_OBF__aa1 (t2tb162 E_OBF__cc) (empty enum_OBF__aa1)))
  (add int (t2tb12 0) (empty int))))) (infix_eqeq
  (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 v_OBF__mmff)
  (times int (tuple21 int enum_OBF__aa1)
  (times enum_OBF__aa1 int (add int (t2tb12 1) (empty int))
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
  (add int (t2tb12 1) (empty int))))) (infix_eqeq
  (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 v_OBF__hhdd)
  (union (tuple21 (tuple21 int enum_OBF__aa1) int)
  (union (tuple21 (tuple21 int enum_OBF__aa1) int)
  (union (tuple21 (tuple21 int enum_OBF__aa1) int) (t2tb2 v_OBF__jjff)
  (t2tb2 v_OBF__kkff)) (t2tb2 v_OBF__llff)) (t2tb2 v_OBF__mmff)))) (mem
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
  (times int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb))))) (infix_eqeq
  (tuple21 (tuple21 (tuple21 int int) int) int) (t2tb3 v_OBF__nnff)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int) (t2tb6 v_OBF__eeff) (t2tb1 v_OBF__wwcc))
  (add int (t2tb12 v_OBF__rrbb) (empty int)))
  (times int (tuple21 (tuple21 int int) int) (t2tb4 v_OBF__ffff)
  (add int (t2tb12 v_OBF__mmbb) (empty int))))
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int) (t2tb6 v_OBF__ggff) (t2tb1 v_OBF__wwcc))
  (add int (t2tb12 v_OBF__ffbb) (empty int))))
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int) (t2tb6 v_OBF__hhff) (t2tb1 v_OBF__wwcc))
  (add int (t2tb12 v_OBF__jjdd) (empty int))))
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int) (t2tb6 v_OBF__iiff) (t2tb1 v_OBF__wwcc))
  (add int (t2tb12 v_OBF__kkdd) (empty int))))
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int)
  (times int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb))
  (t2tb1 v_OBF__wwcc)) (add int (t2tb12 v_OBF__lldd) (empty int)))))) (mem
  (set1 (tuple21 (tuple21 (tuple21 int int) int) int)) (t2tb3 v_OBF__nnff)
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
  (not (infix_eqeq int (t2tb1 v_OBF__eecc) (empty int)))) (mem (set1 int)
  (t2tb1 v_OBF__bbbb) (finite_subsets int (t2tb1 integer))))
  (not (infix_eqeq int (t2tb1 v_OBF__bbbb) (empty int)))) (mem (set1 int)
  (t2tb1 v_OBF__wwcc) (finite_subsets int (t2tb1 integer))))
  (not (infix_eqeq int (t2tb1 v_OBF__wwcc) (empty int)))) (mem (set1 int)
  (t2tb1 v_OBF__ffcc) (finite_subsets int (t2tb1 integer))))
  (not (infix_eqeq int (t2tb1 v_OBF__ffcc) (empty int)))))))

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
  (infix_eqeq int (dom int int (t2tb6 v_OBF__rree))
  (t2tb1 (mk 1 v_OBF__dddd)))) (mem (set1 (tuple21 int int))
  (t2tb6 v_OBF__ssee)
  (infix_plmngt int int (t2tb1 (mk 1 v_OBF__dddd)) (t2tb1 v_OBF__bbbb))))
  (infix_eqeq int (dom int int (t2tb6 v_OBF__ssee))
  (t2tb1 (mk 1 v_OBF__dddd)))) (mem (set1 int) (t2tb1 v_OBF__aacc)
  (power int (t2tb1 v_OBF__ddcc)))) (mem (set1 int) (t2tb1 v_OBF__zzbb)
  (power int (t2tb1 v_OBF__ddcc)))) (mem (set1 int) (t2tb1 v_OBF__yybb)
  (power int (t2tb1 v_OBF__bbbb)))) (mem (set1 int) (t2tb1 v_OBF__bbcc)
  (power int (t2tb1 v_OBF__ddcc)))) (mem (set1 int) (t2tb1 v_OBF__ssbb)
  (power int (t2tb1 v_OBF__ddcc)))))))

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
  (infix_eqeq (tuple21 int int) (t2tb6 v_OBF__hhcc)
  (image (tuple21 int int) int
  (ran (tuple21 int (tuple21 int int)) int
  (domain_restriction (tuple21 int (tuple21 int int)) int (t2tb1 v_OBF__ttbb)
  (direct_product (tuple21 int int) int int (t2tb6 v_OBF__vvbb)
  (direct_product int int int (t2tb6 v_OBF__uubb) (t2tb6 v_OBF__wwbb)))))
  (add int (t2tb12 v_OBF__rrbb) (empty int))))) (infix_eqeq (tuple21 int int)
  (t2tb6 v_OBF__iicc)
  (image (tuple21 int int) int
  (ran (tuple21 int (tuple21 int int)) int
  (domain_restriction (tuple21 int (tuple21 int int)) int (t2tb1 v_OBF__ttbb)
  (direct_product (tuple21 int int) int int (t2tb6 v_OBF__vvbb)
  (direct_product int int int (t2tb6 v_OBF__uubb) (t2tb6 v_OBF__wwbb)))))
  (add int (t2tb12 v_OBF__mmbb) (empty int))))) (infix_eqeq (tuple21 int int)
  (t2tb6 v_OBF__jjcc)
  (image (tuple21 int int) int
  (ran (tuple21 int (tuple21 int int)) int
  (domain_restriction (tuple21 int (tuple21 int int)) int (t2tb1 v_OBF__ttbb)
  (direct_product (tuple21 int int) int int (t2tb6 v_OBF__vvbb)
  (direct_product int int int (t2tb6 v_OBF__uubb) (t2tb6 v_OBF__wwbb)))))
  (add int (t2tb12 v_OBF__ffbb) (empty int))))) (infix_eqeq (tuple21 int int)
  (t2tb6 v_OBF__kkcc)
  (image (tuple21 int int) int
  (ran (tuple21 int (tuple21 int int)) int
  (domain_restriction (tuple21 int (tuple21 int int)) int (t2tb1 v_OBF__ttbb)
  (direct_product (tuple21 int int) int int (t2tb6 v_OBF__vvbb)
  (direct_product int int int (t2tb6 v_OBF__cccc) (t2tb6 v_OBF__wwbb)))))
  (add int (t2tb12 v_OBF__ffbb) (empty int))))) (mem (set1 (tuple21 int int))
  (t2tb6 v_OBF__cccc) (power (tuple21 int int) (t2tb6 v_OBF__uubb)))) (mem
  (set1 (tuple21 int int)) (t2tb6 v_OBF__wwbb)
  (infix_plmngt int int (t2tb1 v_OBF__ddcc) (t2tb1 v_OBF__bbbb))))
  (infix_eqeq int (dom int int (t2tb6 v_OBF__wwbb)) (t2tb1 v_OBF__ddcc)))
  (mem (set1 int) (ran int int (t2tb6 v_OBF__vvbb))
  (power int
  (union int
  (union int (add int (t2tb12 v_OBF__rrbb) (empty int))
  (add int (t2tb12 v_OBF__mmbb) (empty int)))
  (add int (t2tb12 v_OBF__ffbb) (empty int))))))
  (=> (= v_OBF__ddbb 2) (infix_eqeq int (t2tb1 v_OBF__ggbb)
  (inter int (t2tb1 v_OBF__ttbb)
  (image int int (inverse int int (t2tb6 v_OBF__uubb))
  (add int (t2tb12 v_OBF__tt) (empty int)))))))
  (=> (= v_OBF__ddbb 2) (infix_eqeq int (t2tb1 v_OBF__ggcc)
  (inter int
  (inter int (t2tb1 v_OBF__ttbb)
  (image int int (inverse int int (t2tb6 v_OBF__uubb))
  (add int (t2tb12 v_OBF__tt) (empty int))))
  (image int int (inverse int int (t2tb6 v_OBF__vvbb))
  (add int (t2tb12 v_OBF__eebb) (empty int)))))))
  (=> (= v_OBF__ddbb 2) (infix_eqeq int (t2tb1 v_OBF__ww)
  (image int int (t2tb6 v_OBF__wwbb) (t2tb1 v_OBF__ggcc)))))
  (=> (= v_OBF__ddbb 2) (infix_eqeq int (t2tb1 v_OBF__zz)
  (inter int
  (inter int (t2tb1 v_OBF__ttbb)
  (image int int (inverse int int (t2tb6 v_OBF__cccc))
  (add int (t2tb12 v_OBF__tt) (empty int))))
  (image int int (inverse int int (t2tb6 v_OBF__vvbb))
  (add int (t2tb12 v_OBF__eebb) (empty int)))))))
  (=> (= v_OBF__ddbb 2) (infix_eqeq int (t2tb1 v_OBF__ppbb)
  (inter int
  (inter int
  (inter int (t2tb1 v_OBF__ttbb)
  (image int int (inverse int int (t2tb6 v_OBF__uubb))
  (add int (t2tb12 v_OBF__tt) (empty int))))
  (image int int (inverse int int (t2tb6 v_OBF__vvbb))
  (add int (t2tb12 v_OBF__eebb) (empty int))))
  (image int int (inverse int int (t2tb6 v_OBF__wwbb))
  (union int (add int (t2tb12 v_OBF__vv) (empty int))
  (add int (t2tb12 v_OBF__xxbb) (empty int)))))))) (mem
  (set1 (tuple21 int int)) (t2tb6 v_OBF__jjcc)
  (relation int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb)))) (mem
  (set1 (tuple21 int int)) (t2tb6 v_OBF__kkcc)
  (relation int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb)))) (mem
  (set1 int) (t2tb1 v_OBF__yy) (power int (t2tb1 v_OBF__bbbb)))) (infix_eqeq
  (tuple21 int int) (t2tb6 v_OBF__llcc)
  (times int int
  (diff int
  (dom int int
  (union (tuple21 int int) (t2tb6 v_OBF__kkcc)
  (range_substraction int int (t2tb6 v_OBF__jjcc)
  (image int int
  (times int int (add int (t2tb12 0) (empty int))
  (diff int (t2tb1 v_OBF__yy) (add int (t2tb12 v_OBF__vv) (empty int))))
  (add int (t2tb12 v_OBF__xx) (empty int))))))
  (dom (tuple21 int int) int
  (range_substraction (tuple21 int int) int
  (direct_product int int int (t2tb6 v_OBF__jjcc) (t2tb6 v_OBF__jjcc))
  (id int (t2tb1 v_OBF__bbbb))))) (t2tb1 v_OBF__bbbb)))) (mem
  (set1 (tuple21 int int)) (t2tb6 v_OBF__kkcc)
  (power (tuple21 int int) (t2tb6 v_OBF__jjcc)))) (mem
  (set1 (tuple21 int int)) (t2tb6 v_OBF__hhcc)
  (power (tuple21 int int)
  (times int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb))))) (mem
  (set1 (tuple21 int int)) (t2tb6 v_OBF__iicc)
  (power (tuple21 int int)
  (times int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb))))) (infix_eqeq
  (tuple21 int int) (t2tb6 v_OBF__mmcc)
  (union (tuple21 int int) (t2tb6 v_OBF__hhcc)
  (semicolon int int int (t2tb6 v_OBF__hhcc)
  (times int int (add int (t2tb12 v_OBF__xxbb) (empty int))
  (t2tb1 v_OBF__bbbb)))))) (infix_eqeq (tuple21 int int) (t2tb6 v_OBF__nncc)
  (union (tuple21 int int) (t2tb6 v_OBF__iicc)
  (semicolon int int int (t2tb6 v_OBF__iicc)
  (times int int (add int (t2tb12 v_OBF__xxbb) (empty int))
  (t2tb1 v_OBF__bbbb)))))) (mem (set1 (tuple21 int int)) (t2tb6 v_OBF__mmcc)
  (power (tuple21 int int)
  (times int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb))))) (mem
  (set1 (tuple21 int int)) (t2tb6 v_OBF__nncc)
  (power (tuple21 int int)
  (times int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb))))) (mem
  (set1 (tuple21 int int)) (t2tb6 v_OBF__llcc)
  (power (tuple21 int int)
  (times int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb))))) (mem (set1 int)
  (t2tb1 v_OBF__kkbb) (power int (t2tb1 v_OBF__bbbb)))) (infix_eqeq
  (tuple21 int int) (t2tb6 v_OBF__ppcc)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (union (tuple21 int int)
  (domain_restriction int int (t2tb1 v_OBF__uu) (t2tb6 v_OBF__mmcc))
  (times int int (t2tb1 v_OBF__qqcc) (t2tb1 v_OBF__kkbb)))
  (times int int
  (union int (add int (t2tb12 v_OBF__iibb) (empty int))
  (add int (t2tb12 v_OBF__jjbb) (empty int))) (t2tb1 v_OBF__kkbb)))
  (times int int (t2tb1 v_OBF__rrcc)
  (add int (t2tb12 v_OBF__sscc) (empty int))))
  (dom int (tuple21 int int)
  (range_restriction int (tuple21 int int)
  (times int (tuple21 int int)
  (times int int (t2tb1 v_OBF__qqbb) (t2tb1 v_OBF__bbbb))
  (add int (t2tb12 1) (empty int))) (add int (t2tb12 v_OBF__xx) (empty int)))))
  (times int int (add int (t2tb12 v_OBF__ttcc) (empty int))
  (t2tb1 v_OBF__bbbb)))
  (add (tuple21 int int)
  (Tuple2 int int (t2tb12 v_OBF__uucc) (t2tb12 v_OBF__sscc))
  (empty (tuple21 int int)))))) (infix_eqeq (tuple21 (tuple21 int int) int)
  (t2tb4 v_OBF__vvcc)
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
  (add int (t2tb12 v_OBF__sscc) (empty int)))
  (add bool (t2tb13 false) (empty bool)))
  (add bool (t2tb13 v_OBF__oocc) (empty bool)))))
  (add (tuple21 int int)
  (Tuple2 int int (t2tb12 v_OBF__uucc) (t2tb12 v_OBF__sscc))
  (empty (tuple21 int int)))) (t2tb1 v_OBF__wwcc))
  (times int (tuple21 int int)
  (times int int
  (union int (add int (t2tb12 v_OBF__iibb) (empty int))
  (add int (t2tb12 v_OBF__jjbb) (empty int))) (t2tb1 v_OBF__kkbb))
  (add int (t2tb12 v_OBF__oobb) (empty int)))))) (infix_eqeq
  (tuple21 int int) (t2tb6 v_OBF__xxcc)
  (domain_restriction int int (t2tb1 v_OBF__uu) (t2tb6 v_OBF__llcc)))) (mem
  int (t2tb12 v_OBF__yycc) (t2tb1 v_OBF__bbbb))) (mem int
  (t2tb12 v_OBF__zzcc) (t2tb1 integer))) (mem (set1 (tuple21 int int))
  (t2tb6 v_OBF__aadd)
  (relation int int (t2tb1 integer) (t2tb1 v_OBF__bbbb)))) (mem
  (set1 (tuple21 int int)) (t2tb6 v_OBF__bbdd)
  (relation int int (t2tb1 integer) (t2tb1 v_OBF__bbbb)))) (infix_eqeq
  (tuple21 int int) (t2tb6 v_OBF__ccdd)
  (dom (tuple21 int int) (tuple21 int int)
  (range_substraction (tuple21 int int) (tuple21 int int)
  (times (tuple21 int int) (tuple21 int int)
  (times int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb))
  (add (tuple21 int int) (Tuple2 int int (t2tb12 v_OBF__dddd) (t2tb12 0))
  (empty (tuple21 int int))))
  (add (tuple21 int int)
  (Tuple2 int int (t2tb12 v_OBF__zzcc) (t2tb12 v_OBF__xx))
  (empty (tuple21 int int))))))) (infix_eqeq (tuple21 int int)
  (t2tb6 v_OBF__eedd)
  (dom (tuple21 int int) (tuple21 int int)
  (range_substraction (tuple21 int int) (tuple21 int int)
  (times (tuple21 int int) (tuple21 int int)
  (times int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb))
  (add (tuple21 int int) (Tuple2 int int (t2tb12 0) (t2tb12 0))
  (empty (tuple21 int int))))
  (add (tuple21 int int)
  (Tuple2 int int (t2tb12 v_OBF__zzcc) (t2tb12 v_OBF__xx))
  (empty (tuple21 int int))))))) (mem int (t2tb12 v_OBF__zzcc)
  (t2tb1 (mk 0 v_OBF__dddd)))) (mem (set1 (tuple21 int int))
  (t2tb6 v_OBF__aadd)
  (infix_plmngt int int (t2tb1 (mk 1 v_OBF__dddd)) (t2tb1 v_OBF__bbbb))))
  (infix_eqeq int (dom int int (t2tb6 v_OBF__aadd))
  (t2tb1 (mk 1 v_OBF__dddd)))) (mem (set1 (tuple21 int int))
  (t2tb6 v_OBF__bbdd)
  (infix_plmngt int int (t2tb1 (mk 1 v_OBF__dddd)) (t2tb1 v_OBF__bbbb))))
  (infix_eqeq int (dom int int (t2tb6 v_OBF__bbdd))
  (t2tb1 (mk 1 v_OBF__dddd)))) (mem int (t2tb12 v_OBF__ffdd)
  (t2tb1 integer))) (mem int (t2tb12 v_OBF__xx) (t2tb1 integer))) (mem
  (tuple21 (tuple21 int enum_OBF__aa1) int)
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
  (times int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb))))) (infix_eqeq
  (tuple21 (tuple21 (tuple21 int int) int) int) (t2tb3 v_OBF__iidd)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (union (tuple21 (tuple21 (tuple21 int int) int) int)
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int) (t2tb6 v_OBF__ppcc) (t2tb1 v_OBF__wwcc))
  (add int (t2tb12 v_OBF__rrbb) (empty int)))
  (times int (tuple21 (tuple21 int int) int) (t2tb4 v_OBF__vvcc)
  (add int (t2tb12 v_OBF__mmbb) (empty int))))
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int) (t2tb6 v_OBF__xxcc) (t2tb1 v_OBF__wwcc))
  (add int (t2tb12 v_OBF__ffbb) (empty int))))
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int) (t2tb6 v_OBF__ccdd) (t2tb1 v_OBF__wwcc))
  (add int (t2tb12 v_OBF__jjdd) (empty int))))
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int) (t2tb6 v_OBF__eedd) (t2tb1 v_OBF__wwcc))
  (add int (t2tb12 v_OBF__kkdd) (empty int))))
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int)
  (times int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb))
  (t2tb1 v_OBF__wwcc)) (add int (t2tb12 v_OBF__lldd) (empty int)))))) (mem
  int (t2tb12 v_OBF__ddbb) (t2tb1 integer))) (mem int (t2tb12 v_OBF__tt)
  (t2tb1 v_OBF__eecc))) (mem int (t2tb12 v_OBF__vv) (t2tb1 v_OBF__bbbb)))
  (mem int (t2tb12 v_OBF__nnbb) (t2tb1 v_OBF__wwcc))) (mem int
  (t2tb12 v_OBF__eebb) (t2tb1 v_OBF__ffcc))) (mem
  (set1 (tuple21 (tuple21 (tuple21 int int) int) int)) (t2tb3 v_OBF__iidd)
  (power (tuple21 (tuple21 (tuple21 int int) int) int)
  (times int (tuple21 (tuple21 int int) int)
  (times int (tuple21 int int)
  (times int int (t2tb1 v_OBF__eecc) (t2tb1 v_OBF__bbbb))
  (t2tb1 v_OBF__wwcc)) (t2tb1 v_OBF__ffcc)))))
  (=> (= v_OBF__ddbb 2) (infix_eqeq int (t2tb1 v_OBF__ggcc)
  (inter int (t2tb1 v_OBF__ggbb)
  (image int int (inverse int int (t2tb6 v_OBF__vvbb))
  (add int (t2tb12 v_OBF__eebb) (empty int)))))))
  (=> (and (= v_OBF__ddbb 2) (= v_OBF__eebb v_OBF__ffbb)) (infix_eqeq 
  int (image int int (t2tb6 v_OBF__wwbb) (t2tb1 v_OBF__zz))
  (image int int (t2tb6 v_OBF__kkcc)
  (add int (t2tb12 v_OBF__tt) (empty int))))))
  (=> (and (= v_OBF__ddbb 2) (= v_OBF__eebb v_OBF__ffbb)) (infix_eqeq 
  int (t2tb1 v_OBF__ww)
  (image int int (t2tb6 v_OBF__jjcc)
  (add int (t2tb12 v_OBF__tt) (empty int)))))) (infix_eqeq (tuple21 int int)
  (union (tuple21 int int) (t2tb6 v_OBF__kkcc)
  (range_substraction int int (t2tb6 v_OBF__jjcc)
  (image int int
  (times int int (add int (t2tb12 0) (empty int))
  (diff int (t2tb1 v_OBF__yy) (add int (t2tb12 v_OBF__vv) (empty int))))
  (add int (t2tb12 1) (empty int))))) (t2tb6 v_OBF__jjcc))) (infix_eqeq
  (tuple21 int int)
  (union (tuple21 int int) (t2tb6 v_OBF__kkcc)
  (range_substraction int int (t2tb6 v_OBF__jjcc)
  (image int int
  (times int int (add int (t2tb12 0) (empty int))
  (diff int (t2tb1 v_OBF__yy) (add int (t2tb12 v_OBF__vv) (empty int))))
  (add int (t2tb12 0) (empty int)))))
  (union (tuple21 int int) (t2tb6 v_OBF__kkcc)
  (range_substraction int int (t2tb6 v_OBF__jjcc)
  (diff int (t2tb1 v_OBF__yy) (add int (t2tb12 v_OBF__vv) (empty int)))))))
  (infix_eqeq (tuple21 int int)
  (union (tuple21 int int) (t2tb6 v_OBF__nndd)
  (range_substraction int int (t2tb6 v_OBF__oodd)
  (image int int
  (times int int (add int (t2tb12 0) (empty int))
  (diff int (t2tb1 v_OBF__ppdd) (add int (t2tb12 v_OBF__sscc) (empty int))))
  (add int (t2tb12 1) (empty int))))) (t2tb6 v_OBF__oodd))) (mem int
  (t2tb12 v_OBF__xx)
  (union int (add int (t2tb12 0) (empty int))
  (add int (t2tb12 1) (empty int))))) (mem
  (set1 (tuple21 (tuple21 int enum_OBF__aa1) int)) (t2tb2 v_OBF__hhdd)
  (infix_plmngt int (tuple21 int enum_OBF__aa1)
  (times enum_OBF__aa1 int
  (union int (add int (t2tb12 0) (empty int))
  (add int (t2tb12 1) (empty int))) (t2tb161 set_enum_OBF__aa))
  (union int (add int (t2tb12 0) (empty int))
  (add int (t2tb12 1) (empty int)))))) (infix_eqeq
  (tuple21 int enum_OBF__aa1)
  (dom int (tuple21 int enum_OBF__aa1) (t2tb2 v_OBF__hhdd))
  (times enum_OBF__aa1 int
  (union int (add int (t2tb12 0) (empty int))
  (add int (t2tb12 1) (empty int))) (t2tb161 set_enum_OBF__aa)))) (mem
  (set1 enum_OBF__ii1) (t2tb5 v_OBF__llbb)
  (power enum_OBF__ii1 (t2tb5 set_enum_OBF__ii))))
  (= v_OBF__qqdd v_OBF__ddbb)) (= v_OBF__rrdd v_OBF__tt))
  (= v_OBF__ssdd v_OBF__vv)) (= v_OBF__ttdd v_OBF__nnbb))
  (= v_OBF__uudd v_OBF__eebb)) (= v_OBF__vvdd v_OBF__mmdd))
  (= v_OBF__wwdd v_OBF__xx)) (= v_OBF__xxdd v_OBF__yycc))
  (= v_OBF__yydd v_OBF__zzcc)) (infix_eqeq (tuple21 int int)
  (t2tb6 v_OBF__zzdd) (t2tb6 v_OBF__aadd))) (infix_eqeq (tuple21 int int)
  (t2tb6 v_OBF__aaee) (t2tb6 v_OBF__bbdd))) (= v_OBF__bbee v_OBF__oocc))
  (infix_eqeq int (t2tb1 v_OBF__ccee) (t2tb1 v_OBF__kkbb))) (infix_eqeq 
  int (t2tb1 v_OBF__ddee) (t2tb1 v_OBF__yy))) (infix_eqeq (tuple21 int int)
  (t2tb6 v_OBF__eeee) (t2tb6 v_OBF__uubb))) (infix_eqeq (tuple21 int int)
  (t2tb6 v_OBF__ffee) (t2tb6 v_OBF__cccc))) (infix_eqeq (tuple21 int int)
  (t2tb6 v_OBF__ggee) (t2tb6 v_OBF__wwbb))) (infix_eqeq (tuple21 int int)
  (t2tb6 v_OBF__hhee) (t2tb6 v_OBF__vvbb))) (infix_eqeq int
  (t2tb1 v_OBF__iiee) (t2tb1 v_OBF__ttbb))) (infix_eqeq int
  (t2tb1 v_OBF__jjee) (t2tb1 v_OBF__ggbb))) (infix_eqeq int
  (t2tb1 v_OBF__kkee) (t2tb1 v_OBF__ggcc))) (infix_eqeq int
  (t2tb1 v_OBF__llee) (t2tb1 v_OBF__ww))) (infix_eqeq int (t2tb1 v_OBF__mmee)
  (t2tb1 v_OBF__zz))) (infix_eqeq int (t2tb1 v_OBF__nnee)
  (t2tb1 v_OBF__ppbb))))))

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
  (and (infix_eqeq int (t2tb1 v_OBF__ssbb)
  (inter int (t2tb1 v_OBF__zzbb)
  (image int int (inverse int int (t2tb6 v_OBF__wwbb))
  (union int (add int (t2tb12 v_OBF__vv) (empty int))
  (add int (t2tb12 v_OBF__xxbb) (empty int)))))) (= v_OBF__ddbb 1))
  (infix_eqeq int (t2tb1 v_OBF__aacc)
  (inter int (t2tb1 v_OBF__ttbb)
  (image int int (inverse int int (t2tb6 v_OBF__uubb))
  (add int (t2tb12 v_OBF__tt) (empty int)))))) (infix_eqeq int
  (t2tb1 v_OBF__zzbb)
  (inter int (t2tb1 v_OBF__aacc)
  (image int int (inverse int int (t2tb6 v_OBF__vvbb))
  (add int (t2tb12 v_OBF__eebb) (empty int)))))) (infix_eqeq int
  (t2tb1 v_OBF__yybb)
  (image int int (t2tb6 v_OBF__wwbb) (t2tb1 v_OBF__zzbb)))) (infix_eqeq 
  int (t2tb1 v_OBF__bbcc)
  (inter int
  (inter int (t2tb1 v_OBF__ttbb)
  (image int int (inverse int int (t2tb6 v_OBF__cccc))
  (add int (t2tb12 v_OBF__tt) (empty int))))
  (image int int (inverse int int (t2tb6 v_OBF__vvbb))
  (add int (t2tb12 v_OBF__eebb) (empty int)))))))))

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
  (infix_eqeq int (t2tb1 v_OBF__zzbb)
  (inter int
  (inter int (t2tb1 v_OBF__ttbb)
  (image int int (inverse int int (t2tb6 v_OBF__uubb))
  (add int (t2tb12 v_OBF__tt) (empty int))))
  (image int int (inverse int int (t2tb6 v_OBF__vvbb))
  (add int (t2tb12 v_OBF__eebb) (empty int))))))))

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
  (infix_eqeq int (t2tb1 v_OBF__yybb)
  (image int int (t2tb6 v_OBF__wwbb)
  (inter int
  (inter int (t2tb1 v_OBF__ttbb)
  (image int int (inverse int int (t2tb6 v_OBF__uubb))
  (add int (t2tb12 v_OBF__tt) (empty int))))
  (image int int (inverse int int (t2tb6 v_OBF__vvbb))
  (add int (t2tb12 v_OBF__eebb) (empty int)))))))))

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
  (infix_eqeq int (t2tb1 v_OBF__ssbb)
  (inter int
  (inter int
  (inter int (t2tb1 v_OBF__ttbb)
  (image int int (inverse int int (t2tb6 v_OBF__uubb))
  (add int (t2tb12 v_OBF__tt) (empty int))))
  (image int int (inverse int int (t2tb6 v_OBF__vvbb))
  (add int (t2tb12 v_OBF__eebb) (empty int))))
  (image int int (inverse int int (t2tb6 v_OBF__wwbb))
  (union int (add int (t2tb12 v_OBF__vv) (empty int))
  (add int (t2tb12 v_OBF__xxbb) (empty int)))))))))

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
  (union int (add int (t2tb12 v_OBF__iibb) (empty int))
  (add int (t2tb12 v_OBF__jjbb) (empty int)))) (mem int (t2tb12 v_OBF__vv)
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
  (and (not (infix_eqeq int (t2tb1 v_OBF__ggbb) (empty int))) (infix_eqeq 
  int (t2tb1 v_OBF__ww) (empty int)))) (= v_OBF__ddbb 2))
  (= v_OBF__eebb v_OBF__ffbb)) (mem int (t2tb12 v_OBF__tt)
  (t2tb1 v_OBF__uu))) (mem int (t2tb12 v_OBF__aabb) (t2tb1 v_OBF__bbbb)))
  (infix_eqeq int (t2tb1 v_OBF__ww)
  (add int (t2tb12 v_OBF__aabb) (empty int)))))))

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
  (not (infix_eqeq int (t2tb1 v_OBF__ww) (empty int))))
  (forall ((v_OBF__aabb1 Int))
  (=> (mem int (t2tb12 v_OBF__aabb1) (t2tb1 v_OBF__bbbb))
  (not (infix_eqeq int (t2tb1 v_OBF__ww)
  (add int (t2tb12 v_OBF__aabb1) (empty int))))))) (= v_OBF__ddbb 2))
  (= v_OBF__eebb v_OBF__ffbb)) (mem int (t2tb12 v_OBF__aabb)
  (t2tb1 v_OBF__bbbb))) (infix_eqeq int (t2tb1 v_OBF__ww)
  (add int (t2tb12 v_OBF__aabb) (empty int)))))))

(assert
;; OBF__wwff_1
 ;; File "POwhy_bpo2why/p9/p9_8.why", line 3299, characters 7-18
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
  (f26 v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb v_OBF__zz v_OBF__yyee
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
  v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb))) (f21
  v_OBF__zzee v_OBF__zzdd v_OBF__zzcc v_OBF__zzbb v_OBF__zz v_OBF__yyee
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
  v_OBF__aaff v_OBF__aaee v_OBF__aadd v_OBF__aacc v_OBF__aabb)))))
(check-sat)
