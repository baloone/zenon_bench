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

;; mem_integer
  (assert (forall ((x Int)) (mem int (t2tb3 x) (t2tb2 integer))))

(declare-fun natural () (set Int))

;; mem_natural
  (assert
  (forall ((x Int)) (= (mem int (t2tb3 x) (t2tb2 natural)) (<= 0 x))))

(declare-fun natural1 () (set Int))

;; mem_natural1
  (assert
  (forall ((x Int)) (= (mem int (t2tb3 x) (t2tb2 natural1)) (< 0 x))))

(declare-fun nat () (set Int))

;; mem_nat
  (assert
  (forall ((x Int))
  (= (mem int (t2tb3 x) (t2tb2 nat)) (and (<= 0 x) (<= x 2147483647)))))

(declare-fun nat1 () (set Int))

;; mem_nat1
  (assert
  (forall ((x Int))
  (= (mem int (t2tb3 x) (t2tb2 nat1)) (and (< 0 x) (<= x 2147483647)))))

(declare-fun bounded_int () (set Int))

;; mem_bounded_int
  (assert
  (forall ((x Int))
  (= (mem int (t2tb3 x) (t2tb2 bounded_int))
  (and (<= (- 2147483647) x) (<= x 2147483647)))))

(declare-fun mk (Int Int) (set Int))

;; mem_interval
  (assert
  (forall ((x Int) (a Int) (b Int))
  (! (= (mem int (t2tb3 x) (t2tb2 (mk a b))) (and (<= a x) (<= x b))) :pattern ((mem
  int (t2tb3 x) (t2tb2 (mk a b)))) )))

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

(declare-fun t2tb4 ((set enum_ETAT_AUTOMATE)) uni)

;; t2tb_sort
  (assert
  (forall ((x (set enum_ETAT_AUTOMATE))) (sort (set1 enum_ETAT_AUTOMATE1)
  (t2tb4 x))))

(declare-fun tb2t4 (uni) (set enum_ETAT_AUTOMATE))

;; BridgeL
  (assert
  (forall ((i (set enum_ETAT_AUTOMATE)))
  (! (= (tb2t4 (t2tb4 i)) i) :pattern ((t2tb4 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 enum_ETAT_AUTOMATE1) j) (= (t2tb4 (tb2t4 j)) j)) :pattern (
  (t2tb4 (tb2t4 j))) )))

(declare-fun t2tb5 (enum_ETAT_AUTOMATE) uni)

;; t2tb_sort
  (assert
  (forall ((x enum_ETAT_AUTOMATE)) (sort enum_ETAT_AUTOMATE1 (t2tb5 x))))

(declare-fun tb2t5 (uni) enum_ETAT_AUTOMATE)

;; BridgeL
  (assert
  (forall ((i enum_ETAT_AUTOMATE))
  (! (= (tb2t5 (t2tb5 i)) i) :pattern ((t2tb5 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort enum_ETAT_AUTOMATE1 j) (= (t2tb5 (tb2t5 j)) j)) :pattern (
  (t2tb5 (tb2t5 j))) )))

;; set_enum_ETAT_AUTOMATE_axiom
  (assert
  (forall ((x enum_ETAT_AUTOMATE)) (mem enum_ETAT_AUTOMATE1 (t2tb5 x)
  (t2tb4 set_enum_ETAT_AUTOMATE))))

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

(declare-fun t2tb6 ((set enum_ETAT_DAB)) uni)

;; t2tb_sort
  (assert
  (forall ((x (set enum_ETAT_DAB))) (sort (set1 enum_ETAT_DAB1) (t2tb6 x))))

(declare-fun tb2t6 (uni) (set enum_ETAT_DAB))

;; BridgeL
  (assert
  (forall ((i (set enum_ETAT_DAB)))
  (! (= (tb2t6 (t2tb6 i)) i) :pattern ((t2tb6 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 enum_ETAT_DAB1) j) (= (t2tb6 (tb2t6 j)) j)) :pattern (
  (t2tb6 (tb2t6 j))) )))

(declare-fun t2tb7 (enum_ETAT_DAB) uni)

;; t2tb_sort
  (assert (forall ((x enum_ETAT_DAB)) (sort enum_ETAT_DAB1 (t2tb7 x))))

(declare-fun tb2t7 (uni) enum_ETAT_DAB)

;; BridgeL
  (assert
  (forall ((i enum_ETAT_DAB))
  (! (= (tb2t7 (t2tb7 i)) i) :pattern ((t2tb7 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort enum_ETAT_DAB1 j) (= (t2tb7 (tb2t7 j)) j)) :pattern ((t2tb7
                                                                    (tb2t7 j))) )))

;; set_enum_ETAT_DAB_axiom
  (assert
  (forall ((x enum_ETAT_DAB)) (mem enum_ETAT_DAB1 (t2tb7 x)
  (t2tb6 set_enum_ETAT_DAB))))

(declare-sort enum_ORDRE_OPERATEUR 0)

(declare-fun enum_ORDRE_OPERATEUR1 () ty)

(declare-fun E_Marche () enum_ORDRE_OPERATEUR)

(declare-fun E_Arret () enum_ORDRE_OPERATEUR)

(declare-fun match_enum_ORDRE_OPERATEUR (ty enum_ORDRE_OPERATEUR uni
  uni) uni)

;; match_enum_ORDRE_OPERATEUR_sort
  (assert
  (forall ((a ty))
  (forall ((x enum_ORDRE_OPERATEUR) (x1 uni) (x2 uni)) (sort a
  (match_enum_ORDRE_OPERATEUR a x x1 x2)))))

;; match_enum_ORDRE_OPERATEUR_E_Marche
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni))
  (=> (sort a z) (= (match_enum_ORDRE_OPERATEUR a E_Marche z z1) z)))))

;; match_enum_ORDRE_OPERATEUR_E_Arret
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni))
  (=> (sort a z1) (= (match_enum_ORDRE_OPERATEUR a E_Arret z z1) z1)))))

(declare-fun index_enum_ORDRE_OPERATEUR (enum_ORDRE_OPERATEUR) Int)

;; index_enum_ORDRE_OPERATEUR_E_Marche
  (assert (= (index_enum_ORDRE_OPERATEUR E_Marche) 0))

;; index_enum_ORDRE_OPERATEUR_E_Arret
  (assert (= (index_enum_ORDRE_OPERATEUR E_Arret) 1))

;; enum_ORDRE_OPERATEUR_inversion
  (assert
  (forall ((u enum_ORDRE_OPERATEUR)) (or (= u E_Marche) (= u E_Arret))))

(declare-fun set_enum_ORDRE_OPERATEUR () (set enum_ORDRE_OPERATEUR))

(declare-fun t2tb8 ((set enum_ORDRE_OPERATEUR)) uni)

;; t2tb_sort
  (assert
  (forall ((x (set enum_ORDRE_OPERATEUR))) (sort (set1 enum_ORDRE_OPERATEUR1)
  (t2tb8 x))))

(declare-fun tb2t8 (uni) (set enum_ORDRE_OPERATEUR))

;; BridgeL
  (assert
  (forall ((i (set enum_ORDRE_OPERATEUR)))
  (! (= (tb2t8 (t2tb8 i)) i) :pattern ((t2tb8 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 enum_ORDRE_OPERATEUR1) j) (= (t2tb8 (tb2t8 j)) j)) :pattern (
  (t2tb8 (tb2t8 j))) )))

(declare-fun t2tb9 (enum_ORDRE_OPERATEUR) uni)

;; t2tb_sort
  (assert
  (forall ((x enum_ORDRE_OPERATEUR)) (sort enum_ORDRE_OPERATEUR1 (t2tb9 x))))

(declare-fun tb2t9 (uni) enum_ORDRE_OPERATEUR)

;; BridgeL
  (assert
  (forall ((i enum_ORDRE_OPERATEUR))
  (! (= (tb2t9 (t2tb9 i)) i) :pattern ((t2tb9 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort enum_ORDRE_OPERATEUR1 j) (= (t2tb9 (tb2t9 j)) j)) :pattern (
  (t2tb9 (tb2t9 j))) )))

;; set_enum_ORDRE_OPERATEUR_axiom
  (assert
  (forall ((x enum_ORDRE_OPERATEUR)) (mem enum_ORDRE_OPERATEUR1 (t2tb9 x)
  (t2tb8 set_enum_ORDRE_OPERATEUR))))

(declare-sort enum_STATUT 0)

(declare-fun enum_STATUT1 () ty)

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

(declare-fun t2tb10 ((set enum_STATUT)) uni)

;; t2tb_sort
  (assert
  (forall ((x (set enum_STATUT))) (sort (set1 enum_STATUT1) (t2tb10 x))))

(declare-fun tb2t10 (uni) (set enum_STATUT))

;; BridgeL
  (assert
  (forall ((i (set enum_STATUT)))
  (! (= (tb2t10 (t2tb10 i)) i) :pattern ((t2tb10 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 enum_STATUT1) j) (= (t2tb10 (tb2t10 j)) j)) :pattern (
  (t2tb10 (tb2t10 j))) )))

(declare-fun t2tb11 (enum_STATUT) uni)

;; t2tb_sort
  (assert (forall ((x enum_STATUT)) (sort enum_STATUT1 (t2tb11 x))))

(declare-fun tb2t11 (uni) enum_STATUT)

;; BridgeL
  (assert
  (forall ((i enum_STATUT))
  (! (= (tb2t11 (t2tb11 i)) i) :pattern ((t2tb11 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort enum_STATUT1 j) (= (t2tb11 (tb2t11 j)) j)) :pattern ((t2tb11
                                                                    (tb2t11
                                                                    j))) )))

;; set_enum_STATUT_axiom
  (assert
  (forall ((x enum_STATUT)) (mem enum_STATUT1 (t2tb11 x)
  (t2tb10 set_enum_STATUT))))

(declare-fun f2 (Int Int Int Int Int Int Int Int Int Int Int Int Bool Bool
  Bool Bool Bool Bool enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR (set Int) (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_DAB enum_ETAT_DAB enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_DAB enum_ETAT_DAB Int Int
  Int Int (set Int) Int (set (tuple2 Int Int)) Int Int Int Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set Int) (set Int) Int Int Int Int Int
  Int Int Int Int Int Int Int Int Int (set Int) (set Int)) Bool)

;; f2_def
  (assert
  (forall ((v_tedaz_7777 Int) (v_teda_2 Int) (v_teda_1 Int) (v_teda_0 Int)
  (v_teda Int) (v_som_0 Int) (v_som Int) (v_rjt Int) (v_retraitsz_7777 Int)
  (v_retraits_2 Int) (v_retraits_1 Int) (v_retraits Int)
  (v_panne_dabz_7777 Bool) (v_panne_dab_2 Bool) (v_panne_dab_1 Bool)
  (v_panne_dab Bool) (v_pan_dab_1 Bool) (v_pan_dab_0 Bool)
  (v_ordrez_7777 enum_ORDRE_OPERATEUR) (v_ordre_2 enum_ORDRE_OPERATEUR)
  (v_ordre_1 enum_ORDRE_OPERATEUR) (v_ordre enum_ORDRE_OPERATEUR)
  (v_oo_0 enum_ORDRE_OPERATEUR) (v_oo enum_ORDRE_OPERATEUR)
  (v_interdits_1 (set Int)) (v_interdits (set Int))
  (v_etat_dabz_7777 enum_ETAT_DAB) (v_etat_dab_2 enum_ETAT_DAB)
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_autz_7778 enum_ETAT_AUTOMATE) (v_etat_aut_1 enum_ETAT_AUTOMATE)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat_1 enum_ETAT_DAB) (v_etat_0 enum_ETAT_DAB) (v_datez_7777 Int)
  (v_date_1 Int) (v_date_0 Int) (v_date Int) (v_crt_int (set Int))
  (v_crt Int) (v_cpt_crt (set (tuple2 Int Int))) (v_corbeillez_7777 Int)
  (v_corbeille_2 Int) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptesz_7777 (set (tuple2 Int Int))) (v_comptes_2 (set (tuple2 Int
  Int))) (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int
  Int))) (v_clts (set Int)) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cartez_7778 Int) (v_carte_1 Int) (v_carte_0 Int) (v_carte Int)
  (v_caissez_7777 Int) (v_caisse_2 Int) (v_caisse_1 Int) (v_caisse Int)
  (v_avance_1 Int) (v_avance Int) (v_K0 Int) (v_HS Int) (v_D_min Int)
  (v_D_max Int) (v_DATE (set Int)) (v_CARTE (set Int))) (f2 v_tedaz_7777
  v_teda_2 v_teda_1 v_teda_0 v_teda v_som_0 v_som v_rjt v_retraitsz_7777
  v_retraits_2 v_retraits_1 v_retraits v_panne_dabz_7777 v_panne_dab_2
  v_panne_dab_1 v_panne_dab v_pan_dab_1 v_pan_dab_0 v_ordrez_7777 v_ordre_2
  v_ordre_1 v_ordre v_oo_0 v_oo v_interdits_1 v_interdits v_etat_dabz_7777
  v_etat_dab_2 v_etat_dab_1 v_etat_dab v_etat_autz_7778 v_etat_aut_1
  v_etat_aut_0 v_etat_aut v_etat_1 v_etat_0 v_datez_7777 v_date_1 v_date_0
  v_date v_crt_int v_crt v_cpt_crt v_corbeillez_7777 v_corbeille_2
  v_corbeille_1 v_corbeille v_comptesz_7777 v_comptes_2 v_comptes_1 v_comptes
  v_clts v_clients_1 v_clients v_cartez_7778 v_carte_1 v_carte_0 v_carte
  v_caissez_7777 v_caisse_2 v_caisse_1 v_caisse v_avance_1 v_avance v_K0 v_HS
  v_D_min v_D_max v_DATE v_CARTE)))

(declare-fun f3 (Int Int Int Int Int Int Int Int Int Int Int Int Bool Bool
  Bool Bool Bool Bool enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR (set Int) (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_DAB enum_ETAT_DAB enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_DAB enum_ETAT_DAB Int Int
  Int Int (set Int) Int (set (tuple2 Int Int)) Int Int Int Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set Int) (set Int) Int Int Int Int Int
  Int Int Int Int Int Int Int Int Int (set Int) (set Int)) Bool)

(declare-fun t2tb12 ((set (set Int))) uni)

;; t2tb_sort
  (assert (forall ((x (set (set Int)))) (sort (set1 (set1 int)) (t2tb12 x))))

(declare-fun tb2t12 (uni) (set (set Int)))

;; BridgeL
  (assert
  (forall ((i (set (set Int))))
  (! (= (tb2t12 (t2tb12 i)) i) :pattern ((t2tb12 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb12 (tb2t12 j)) j) :pattern ((t2tb12 (tb2t12 j))) )))

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

(declare-fun t2tb14 ((set (tuple2 Int Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int Int)))) (sort (set1 (tuple21 int int))
  (t2tb14 x))))

(declare-fun tb2t14 (uni) (set (tuple2 Int Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int Int))))
  (! (= (tb2t14 (t2tb14 i)) i) :pattern ((t2tb14 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb14 (tb2t14 j)) j) :pattern ((t2tb14 (tb2t14 j))) )))

;; f3_def
  (assert
  (forall ((v_tedaz_7777 Int) (v_teda_2 Int) (v_teda_1 Int) (v_teda_0 Int)
  (v_teda Int) (v_som_0 Int) (v_som Int) (v_rjt Int) (v_retraitsz_7777 Int)
  (v_retraits_2 Int) (v_retraits_1 Int) (v_retraits Int)
  (v_panne_dabz_7777 Bool) (v_panne_dab_2 Bool) (v_panne_dab_1 Bool)
  (v_panne_dab Bool) (v_pan_dab_1 Bool) (v_pan_dab_0 Bool)
  (v_ordrez_7777 enum_ORDRE_OPERATEUR) (v_ordre_2 enum_ORDRE_OPERATEUR)
  (v_ordre_1 enum_ORDRE_OPERATEUR) (v_ordre enum_ORDRE_OPERATEUR)
  (v_oo_0 enum_ORDRE_OPERATEUR) (v_oo enum_ORDRE_OPERATEUR)
  (v_interdits_1 (set Int)) (v_interdits (set Int))
  (v_etat_dabz_7777 enum_ETAT_DAB) (v_etat_dab_2 enum_ETAT_DAB)
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_autz_7778 enum_ETAT_AUTOMATE) (v_etat_aut_1 enum_ETAT_AUTOMATE)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat_1 enum_ETAT_DAB) (v_etat_0 enum_ETAT_DAB) (v_datez_7777 Int)
  (v_date_1 Int) (v_date_0 Int) (v_date Int) (v_crt_int (set Int))
  (v_crt Int) (v_cpt_crt (set (tuple2 Int Int))) (v_corbeillez_7777 Int)
  (v_corbeille_2 Int) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptesz_7777 (set (tuple2 Int Int))) (v_comptes_2 (set (tuple2 Int
  Int))) (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int
  Int))) (v_clts (set Int)) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cartez_7778 Int) (v_carte_1 Int) (v_carte_0 Int) (v_carte Int)
  (v_caissez_7777 Int) (v_caisse_2 Int) (v_caisse_1 Int) (v_caisse Int)
  (v_avance_1 Int) (v_avance Int) (v_K0 Int) (v_HS Int) (v_D_min Int)
  (v_D_max Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f3 v_tedaz_7777 v_teda_2 v_teda_1 v_teda_0 v_teda v_som_0 v_som v_rjt
  v_retraitsz_7777 v_retraits_2 v_retraits_1 v_retraits v_panne_dabz_7777
  v_panne_dab_2 v_panne_dab_1 v_panne_dab v_pan_dab_1 v_pan_dab_0
  v_ordrez_7777 v_ordre_2 v_ordre_1 v_ordre v_oo_0 v_oo v_interdits_1
  v_interdits v_etat_dabz_7777 v_etat_dab_2 v_etat_dab_1 v_etat_dab
  v_etat_autz_7778 v_etat_aut_1 v_etat_aut_0 v_etat_aut v_etat_1 v_etat_0
  v_datez_7777 v_date_1 v_date_0 v_date v_crt_int v_crt v_cpt_crt
  v_corbeillez_7777 v_corbeille_2 v_corbeille_1 v_corbeille v_comptesz_7777
  v_comptes_2 v_comptes_1 v_comptes v_clts v_clients_1 v_clients
  v_cartez_7778 v_carte_1 v_carte_0 v_carte v_caissez_7777 v_caisse_2
  v_caisse_1 v_caisse v_avance_1 v_avance v_K0 v_HS v_D_min v_D_max v_DATE
  v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (mem int (t2tb3 v_K0) (t2tb2 v_CARTE)) (mem int (t2tb3 v_HS)
  (t2tb2 v_CARTE))) (not (= v_K0 v_HS))) (mem (set1 int) (t2tb2 v_CARTE)
  (finite_subsets int (t2tb2 integer))))
  (not (infix_eqeq int (t2tb2 v_CARTE) (empty int)))) (mem int
  (t2tb3 v_D_min) (t2tb2 integer))) (<= 0 v_D_min)) (<= v_D_min 2147483647))
  (mem int (t2tb3 v_D_max) (t2tb2 integer))) (<= 0 v_D_max))
  (<= v_D_max 2147483647)) (<= (+ v_D_min 1) v_D_max)) (infix_eqeq int
  (t2tb2 v_DATE) (t2tb2 (mk v_D_min v_D_max)))) (mem (set1 int)
  (t2tb2 v_clients_1)
  (power int
  (diff int (t2tb2 v_CARTE)
  (union int (add int (t2tb3 v_K0) (empty int))
  (add int (t2tb3 v_HS) (empty int))))))) (mem (set1 (tuple21 int int))
  (t2tb14 v_comptes_1)
  (infix_plmngt int int (t2tb2 v_clients_1) (t2tb2 nat)))) (infix_eqeq 
  int (dom int int (t2tb14 v_comptes_1)) (t2tb2 v_clients_1))) (mem
  (set1 int) (t2tb2 v_interdits_1) (power int (t2tb2 v_clients_1)))) (mem 
  int (t2tb3 v_caisse_1) (t2tb2 integer))) (<= 0 v_caisse_1))
  (<= v_caisse_1 2147483647)) (mem int (t2tb3 v_corbeille_1)
  (t2tb2 integer))) (<= 0 v_corbeille_1)) (<= v_corbeille_1 2147483647)) (mem
  int (t2tb3 v_retraits_1) (t2tb2 integer))) (<= 0 v_retraits_1))
  (<= v_retraits_1 2147483647)) (mem int (t2tb3 v_carte_1) (t2tb2 v_CARTE)))
  (mem int (t2tb3 (+ (+ v_caisse_1 v_corbeille_1) v_retraits_1))
  (t2tb2 integer))) (<= 0 (+ (+ v_caisse_1 v_corbeille_1) v_retraits_1)))
  (<= (+ (+ v_caisse_1 v_corbeille_1) v_retraits_1) 2147483647)) (mem 
  int (t2tb3 v_teda_1) (t2tb2 integer))) (<= 0 v_teda_1))
  (<= v_teda_1 2147483647)) (mem int (t2tb3 v_avance_1) (t2tb2 integer)))
  (<= 0 v_avance_1)) (<= v_avance_1 2147483647))
  (=> (= v_ordre_1 E_Marche) (<= 1 v_teda_1)))
  (=> (<= 1 v_teda_1) (= v_ordre_1 E_Marche))) (mem int (t2tb3 v_date_1)
  (t2tb2 v_DATE))))))

(declare-fun f4 (Int Int Int Int Int Int Int Int Int Int Int Int Bool Bool
  Bool Bool Bool Bool enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR (set Int) (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_DAB enum_ETAT_DAB enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_DAB enum_ETAT_DAB Int Int
  Int Int (set Int) Int (set (tuple2 Int Int)) Int Int Int Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set Int) (set Int) Int Int Int Int Int
  Int Int Int Int Int Int Int Int Int (set Int) (set Int)) Bool)

;; f4_def
  (assert
  (forall ((v_tedaz_7777 Int) (v_teda_2 Int) (v_teda_1 Int) (v_teda_0 Int)
  (v_teda Int) (v_som_0 Int) (v_som Int) (v_rjt Int) (v_retraitsz_7777 Int)
  (v_retraits_2 Int) (v_retraits_1 Int) (v_retraits Int)
  (v_panne_dabz_7777 Bool) (v_panne_dab_2 Bool) (v_panne_dab_1 Bool)
  (v_panne_dab Bool) (v_pan_dab_1 Bool) (v_pan_dab_0 Bool)
  (v_ordrez_7777 enum_ORDRE_OPERATEUR) (v_ordre_2 enum_ORDRE_OPERATEUR)
  (v_ordre_1 enum_ORDRE_OPERATEUR) (v_ordre enum_ORDRE_OPERATEUR)
  (v_oo_0 enum_ORDRE_OPERATEUR) (v_oo enum_ORDRE_OPERATEUR)
  (v_interdits_1 (set Int)) (v_interdits (set Int))
  (v_etat_dabz_7777 enum_ETAT_DAB) (v_etat_dab_2 enum_ETAT_DAB)
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_autz_7778 enum_ETAT_AUTOMATE) (v_etat_aut_1 enum_ETAT_AUTOMATE)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat_1 enum_ETAT_DAB) (v_etat_0 enum_ETAT_DAB) (v_datez_7777 Int)
  (v_date_1 Int) (v_date_0 Int) (v_date Int) (v_crt_int (set Int))
  (v_crt Int) (v_cpt_crt (set (tuple2 Int Int))) (v_corbeillez_7777 Int)
  (v_corbeille_2 Int) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptesz_7777 (set (tuple2 Int Int))) (v_comptes_2 (set (tuple2 Int
  Int))) (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int
  Int))) (v_clts (set Int)) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cartez_7778 Int) (v_carte_1 Int) (v_carte_0 Int) (v_carte Int)
  (v_caissez_7777 Int) (v_caisse_2 Int) (v_caisse_1 Int) (v_caisse Int)
  (v_avance_1 Int) (v_avance Int) (v_K0 Int) (v_HS Int) (v_D_min Int)
  (v_D_max Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f4 v_tedaz_7777 v_teda_2 v_teda_1 v_teda_0 v_teda v_som_0 v_som v_rjt
  v_retraitsz_7777 v_retraits_2 v_retraits_1 v_retraits v_panne_dabz_7777
  v_panne_dab_2 v_panne_dab_1 v_panne_dab v_pan_dab_1 v_pan_dab_0
  v_ordrez_7777 v_ordre_2 v_ordre_1 v_ordre v_oo_0 v_oo v_interdits_1
  v_interdits v_etat_dabz_7777 v_etat_dab_2 v_etat_dab_1 v_etat_dab
  v_etat_autz_7778 v_etat_aut_1 v_etat_aut_0 v_etat_aut v_etat_1 v_etat_0
  v_datez_7777 v_date_1 v_date_0 v_date v_crt_int v_crt v_cpt_crt
  v_corbeillez_7777 v_corbeille_2 v_corbeille_1 v_corbeille v_comptesz_7777
  v_comptes_2 v_comptes_1 v_comptes v_clts v_clients_1 v_clients
  v_cartez_7778 v_carte_1 v_carte_0 v_carte v_caissez_7777 v_caisse_2
  v_caisse_1 v_caisse v_avance_1 v_avance v_K0 v_HS v_D_min v_D_max v_DATE
  v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (mem int (t2tb3 v_caisse_1) (t2tb2 integer)) (<= 0 v_caisse_1))
  (<= v_caisse_1 2147483647)) (mem int (t2tb3 v_corbeille_1)
  (t2tb2 integer))) (<= 0 v_corbeille_1)) (<= v_corbeille_1 2147483647)) (mem
  int (t2tb3 v_retraits_1) (t2tb2 integer))) (<= 0 v_retraits_1))
  (<= v_retraits_1 2147483647)) (mem int (t2tb3 v_avance_1) (t2tb2 integer)))
  (<= 0 v_avance_1)) (<= v_avance_1 2147483647))
  (= (+ (+ v_caisse_1 v_corbeille_1) v_retraits_1) v_avance_1))
  (=> (or (= v_panne_dab_1 true) (<= (+ v_caisse_1 1) 900))
  (= v_etat_dab_1 E_Hors_service)))
  (=> (= v_etat_dab_1 E_Hors_service)
  (or (= v_panne_dab_1 true) (<= (+ v_caisse_1 1) 900))))
  (= v_caisse v_caisse_1)) (= v_corbeille v_corbeille_1))
  (= v_retraits v_retraits_1)) (= v_avance v_avance_1))
  (= v_etat_dab v_etat_dab_1)) (= v_panne_dab v_panne_dab_1)))))

(declare-fun f5 (Int Int Int Int Int Int Int Int Int Int Int Int Bool Bool
  Bool Bool Bool Bool enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR (set Int) (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_DAB enum_ETAT_DAB enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_DAB enum_ETAT_DAB Int Int
  Int Int (set Int) Int (set (tuple2 Int Int)) Int Int Int Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set Int) (set Int) Int Int Int Int Int
  Int Int Int Int Int Int Int Int Int (set Int) (set Int)) Bool)

;; f5_def
  (assert
  (forall ((v_tedaz_7777 Int) (v_teda_2 Int) (v_teda_1 Int) (v_teda_0 Int)
  (v_teda Int) (v_som_0 Int) (v_som Int) (v_rjt Int) (v_retraitsz_7777 Int)
  (v_retraits_2 Int) (v_retraits_1 Int) (v_retraits Int)
  (v_panne_dabz_7777 Bool) (v_panne_dab_2 Bool) (v_panne_dab_1 Bool)
  (v_panne_dab Bool) (v_pan_dab_1 Bool) (v_pan_dab_0 Bool)
  (v_ordrez_7777 enum_ORDRE_OPERATEUR) (v_ordre_2 enum_ORDRE_OPERATEUR)
  (v_ordre_1 enum_ORDRE_OPERATEUR) (v_ordre enum_ORDRE_OPERATEUR)
  (v_oo_0 enum_ORDRE_OPERATEUR) (v_oo enum_ORDRE_OPERATEUR)
  (v_interdits_1 (set Int)) (v_interdits (set Int))
  (v_etat_dabz_7777 enum_ETAT_DAB) (v_etat_dab_2 enum_ETAT_DAB)
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_autz_7778 enum_ETAT_AUTOMATE) (v_etat_aut_1 enum_ETAT_AUTOMATE)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat_1 enum_ETAT_DAB) (v_etat_0 enum_ETAT_DAB) (v_datez_7777 Int)
  (v_date_1 Int) (v_date_0 Int) (v_date Int) (v_crt_int (set Int))
  (v_crt Int) (v_cpt_crt (set (tuple2 Int Int))) (v_corbeillez_7777 Int)
  (v_corbeille_2 Int) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptesz_7777 (set (tuple2 Int Int))) (v_comptes_2 (set (tuple2 Int
  Int))) (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int
  Int))) (v_clts (set Int)) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cartez_7778 Int) (v_carte_1 Int) (v_carte_0 Int) (v_carte Int)
  (v_caissez_7777 Int) (v_caisse_2 Int) (v_caisse_1 Int) (v_caisse Int)
  (v_avance_1 Int) (v_avance Int) (v_K0 Int) (v_HS Int) (v_D_min Int)
  (v_D_max Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f5 v_tedaz_7777 v_teda_2 v_teda_1 v_teda_0 v_teda v_som_0 v_som v_rjt
  v_retraitsz_7777 v_retraits_2 v_retraits_1 v_retraits v_panne_dabz_7777
  v_panne_dab_2 v_panne_dab_1 v_panne_dab v_pan_dab_1 v_pan_dab_0
  v_ordrez_7777 v_ordre_2 v_ordre_1 v_ordre v_oo_0 v_oo v_interdits_1
  v_interdits v_etat_dabz_7777 v_etat_dab_2 v_etat_dab_1 v_etat_dab
  v_etat_autz_7778 v_etat_aut_1 v_etat_aut_0 v_etat_aut v_etat_1 v_etat_0
  v_datez_7777 v_date_1 v_date_0 v_date v_crt_int v_crt v_cpt_crt
  v_corbeillez_7777 v_corbeille_2 v_corbeille_1 v_corbeille v_comptesz_7777
  v_comptes_2 v_comptes_1 v_comptes v_clts v_clients_1 v_clients
  v_cartez_7778 v_carte_1 v_carte_0 v_carte v_caissez_7777 v_caisse_2
  v_caisse_1 v_caisse v_avance_1 v_avance v_K0 v_HS v_D_min v_D_max v_DATE
  v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and (and (mem int (t2tb3 v_som) (t2tb2 integer)) (<= 0 v_som))
  (<= v_som 2147483647)) (<= 901 v_som)) (mem int (t2tb3 v_teda_0)
  (t2tb2 integer))) (<= 0 v_teda_0)) (<= v_teda_0 2147483647))
  (not (= v_teda_0 0))))))

(declare-fun f8 (Int Int Int Int Int Int Int Int Int Int Int Int Bool Bool
  Bool Bool Bool Bool enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR (set Int) (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_DAB enum_ETAT_DAB enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_DAB enum_ETAT_DAB Int Int
  Int Int (set Int) Int (set (tuple2 Int Int)) Int Int Int Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set Int) (set Int) Int Int Int Int Int
  Int Int Int Int Int Int Int Int Int (set Int) (set Int)) Bool)

;; f8_def
  (assert
  (forall ((v_tedaz_7777 Int) (v_teda_2 Int) (v_teda_1 Int) (v_teda_0 Int)
  (v_teda Int) (v_som_0 Int) (v_som Int) (v_rjt Int) (v_retraitsz_7777 Int)
  (v_retraits_2 Int) (v_retraits_1 Int) (v_retraits Int)
  (v_panne_dabz_7777 Bool) (v_panne_dab_2 Bool) (v_panne_dab_1 Bool)
  (v_panne_dab Bool) (v_pan_dab_1 Bool) (v_pan_dab_0 Bool)
  (v_ordrez_7777 enum_ORDRE_OPERATEUR) (v_ordre_2 enum_ORDRE_OPERATEUR)
  (v_ordre_1 enum_ORDRE_OPERATEUR) (v_ordre enum_ORDRE_OPERATEUR)
  (v_oo_0 enum_ORDRE_OPERATEUR) (v_oo enum_ORDRE_OPERATEUR)
  (v_interdits_1 (set Int)) (v_interdits (set Int))
  (v_etat_dabz_7777 enum_ETAT_DAB) (v_etat_dab_2 enum_ETAT_DAB)
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_autz_7778 enum_ETAT_AUTOMATE) (v_etat_aut_1 enum_ETAT_AUTOMATE)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat_1 enum_ETAT_DAB) (v_etat_0 enum_ETAT_DAB) (v_datez_7777 Int)
  (v_date_1 Int) (v_date_0 Int) (v_date Int) (v_crt_int (set Int))
  (v_crt Int) (v_cpt_crt (set (tuple2 Int Int))) (v_corbeillez_7777 Int)
  (v_corbeille_2 Int) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptesz_7777 (set (tuple2 Int Int))) (v_comptes_2 (set (tuple2 Int
  Int))) (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int
  Int))) (v_clts (set Int)) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cartez_7778 Int) (v_carte_1 Int) (v_carte_0 Int) (v_carte Int)
  (v_caissez_7777 Int) (v_caisse_2 Int) (v_caisse_1 Int) (v_caisse Int)
  (v_avance_1 Int) (v_avance Int) (v_K0 Int) (v_HS Int) (v_D_min Int)
  (v_D_max Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f8 v_tedaz_7777 v_teda_2 v_teda_1 v_teda_0 v_teda v_som_0 v_som v_rjt
  v_retraitsz_7777 v_retraits_2 v_retraits_1 v_retraits v_panne_dabz_7777
  v_panne_dab_2 v_panne_dab_1 v_panne_dab v_pan_dab_1 v_pan_dab_0
  v_ordrez_7777 v_ordre_2 v_ordre_1 v_ordre v_oo_0 v_oo v_interdits_1
  v_interdits v_etat_dabz_7777 v_etat_dab_2 v_etat_dab_1 v_etat_dab
  v_etat_autz_7778 v_etat_aut_1 v_etat_aut_0 v_etat_aut v_etat_1 v_etat_0
  v_datez_7777 v_date_1 v_date_0 v_date v_crt_int v_crt v_cpt_crt
  v_corbeillez_7777 v_corbeille_2 v_corbeille_1 v_corbeille v_comptesz_7777
  v_comptes_2 v_comptes_1 v_comptes v_clts v_clients_1 v_clients
  v_cartez_7778 v_carte_1 v_carte_0 v_carte v_caissez_7777 v_caisse_2
  v_caisse_1 v_caisse v_avance_1 v_avance v_K0 v_HS v_D_min v_D_max v_DATE
  v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (mem int (t2tb3 v_som) (t2tb2 integer)) (<= 0 v_som))
  (<= v_som 2147483647)) (<= 901 v_som)) (mem (set1 int) (t2tb2 v_clts)
  (power int
  (diff int (t2tb2 v_CARTE)
  (union int (add int (t2tb3 v_K0) (empty int))
  (add int (t2tb3 v_HS) (empty int))))))) (mem (set1 (tuple21 int int))
  (t2tb14 v_cpt_crt) (infix_plmngt int int (t2tb2 v_clts) (t2tb2 nat))))
  (infix_eqeq int (dom int int (t2tb14 v_cpt_crt)) (t2tb2 v_clts))) (mem
  (set1 int) (t2tb2 v_crt_int) (power int (t2tb2 v_clts))))
  (=> (= v_etat_0 E_Hors_service)
  (or (= v_pan_dab_0 true) (<= (+ v_som 1) 900))))
  (=> (or (= v_pan_dab_0 true) (<= (+ v_som 1) 900))
  (= v_etat_0 E_Hors_service))) (mem int (t2tb3 v_teda_0) (t2tb2 integer)))
  (<= 0 v_teda_0)) (<= v_teda_0 2147483647)) (not (= v_teda_0 0))))))

(declare-fun f10 (Int Int Int Int Int Int Int Int Int Int Int Int Bool Bool
  Bool Bool Bool Bool enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR (set Int) (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_DAB enum_ETAT_DAB enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_DAB enum_ETAT_DAB Int Int
  Int Int (set Int) Int (set (tuple2 Int Int)) Int Int Int Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set Int) (set Int) Int Int Int Int Int
  Int Int Int Int Int Int Int Int Int (set Int) (set Int)) Bool)

;; f10_def
  (assert
  (forall ((v_tedaz_7777 Int) (v_teda_2 Int) (v_teda_1 Int) (v_teda_0 Int)
  (v_teda Int) (v_som_0 Int) (v_som Int) (v_rjt Int) (v_retraitsz_7777 Int)
  (v_retraits_2 Int) (v_retraits_1 Int) (v_retraits Int)
  (v_panne_dabz_7777 Bool) (v_panne_dab_2 Bool) (v_panne_dab_1 Bool)
  (v_panne_dab Bool) (v_pan_dab_1 Bool) (v_pan_dab_0 Bool)
  (v_ordrez_7777 enum_ORDRE_OPERATEUR) (v_ordre_2 enum_ORDRE_OPERATEUR)
  (v_ordre_1 enum_ORDRE_OPERATEUR) (v_ordre enum_ORDRE_OPERATEUR)
  (v_oo_0 enum_ORDRE_OPERATEUR) (v_oo enum_ORDRE_OPERATEUR)
  (v_interdits_1 (set Int)) (v_interdits (set Int))
  (v_etat_dabz_7777 enum_ETAT_DAB) (v_etat_dab_2 enum_ETAT_DAB)
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_autz_7778 enum_ETAT_AUTOMATE) (v_etat_aut_1 enum_ETAT_AUTOMATE)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat_1 enum_ETAT_DAB) (v_etat_0 enum_ETAT_DAB) (v_datez_7777 Int)
  (v_date_1 Int) (v_date_0 Int) (v_date Int) (v_crt_int (set Int))
  (v_crt Int) (v_cpt_crt (set (tuple2 Int Int))) (v_corbeillez_7777 Int)
  (v_corbeille_2 Int) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptesz_7777 (set (tuple2 Int Int))) (v_comptes_2 (set (tuple2 Int
  Int))) (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int
  Int))) (v_clts (set Int)) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cartez_7778 Int) (v_carte_1 Int) (v_carte_0 Int) (v_carte Int)
  (v_caissez_7777 Int) (v_caisse_2 Int) (v_caisse_1 Int) (v_caisse Int)
  (v_avance_1 Int) (v_avance Int) (v_K0 Int) (v_HS Int) (v_D_min Int)
  (v_D_max Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f10 v_tedaz_7777 v_teda_2 v_teda_1 v_teda_0 v_teda v_som_0 v_som v_rjt
  v_retraitsz_7777 v_retraits_2 v_retraits_1 v_retraits v_panne_dabz_7777
  v_panne_dab_2 v_panne_dab_1 v_panne_dab v_pan_dab_1 v_pan_dab_0
  v_ordrez_7777 v_ordre_2 v_ordre_1 v_ordre v_oo_0 v_oo v_interdits_1
  v_interdits v_etat_dabz_7777 v_etat_dab_2 v_etat_dab_1 v_etat_dab
  v_etat_autz_7778 v_etat_aut_1 v_etat_aut_0 v_etat_aut v_etat_1 v_etat_0
  v_datez_7777 v_date_1 v_date_0 v_date v_crt_int v_crt v_cpt_crt
  v_corbeillez_7777 v_corbeille_2 v_corbeille_1 v_corbeille v_comptesz_7777
  v_comptes_2 v_comptes_1 v_comptes v_clts v_clients_1 v_clients
  v_cartez_7778 v_carte_1 v_carte_0 v_carte v_caissez_7777 v_caisse_2
  v_caisse_1 v_caisse v_avance_1 v_avance v_K0 v_HS v_D_min v_D_max v_DATE
  v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (=> (= v_oo E_Marche) (<= 2 v_teda_0))
  (=> (<= 2 v_teda_0) (= v_oo E_Marche))) (mem int (t2tb3 v_som)
  (t2tb2 integer))) (<= 0 v_som)) (<= v_som 2147483647)) (<= 901 v_som)) (mem
  (set1 int) (t2tb2 v_clts)
  (power int
  (diff int (t2tb2 v_CARTE)
  (union int (add int (t2tb3 v_K0) (empty int))
  (add int (t2tb3 v_HS) (empty int))))))) (mem (set1 (tuple21 int int))
  (t2tb14 v_cpt_crt) (infix_plmngt int int (t2tb2 v_clts) (t2tb2 nat))))
  (infix_eqeq int (dom int int (t2tb14 v_cpt_crt)) (t2tb2 v_clts))) (mem
  (set1 int) (t2tb2 v_crt_int) (power int (t2tb2 v_clts))))
  (=> (= v_etat_0 E_Hors_service)
  (or (= v_pan_dab_0 true) (<= (+ v_som 1) 900))))
  (=> (or (= v_pan_dab_0 true) (<= (+ v_som 1) 900))
  (= v_etat_0 E_Hors_service))) (mem int (t2tb3 v_teda_0) (t2tb2 integer)))
  (<= 0 v_teda_0)) (<= v_teda_0 2147483647)) (not (= v_teda_0 0))))))

(declare-fun f11 (Int Int Int Int Int Int Int Int Int Int Int Int Bool Bool
  Bool Bool Bool Bool enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR (set Int) (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_DAB enum_ETAT_DAB enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_DAB enum_ETAT_DAB Int Int
  Int Int (set Int) Int (set (tuple2 Int Int)) Int Int Int Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set Int) (set Int) Int Int Int Int Int
  Int Int Int Int Int Int Int Int Int (set Int) (set Int)) Bool)

;; f11_def
  (assert
  (forall ((v_tedaz_7777 Int) (v_teda_2 Int) (v_teda_1 Int) (v_teda_0 Int)
  (v_teda Int) (v_som_0 Int) (v_som Int) (v_rjt Int) (v_retraitsz_7777 Int)
  (v_retraits_2 Int) (v_retraits_1 Int) (v_retraits Int)
  (v_panne_dabz_7777 Bool) (v_panne_dab_2 Bool) (v_panne_dab_1 Bool)
  (v_panne_dab Bool) (v_pan_dab_1 Bool) (v_pan_dab_0 Bool)
  (v_ordrez_7777 enum_ORDRE_OPERATEUR) (v_ordre_2 enum_ORDRE_OPERATEUR)
  (v_ordre_1 enum_ORDRE_OPERATEUR) (v_ordre enum_ORDRE_OPERATEUR)
  (v_oo_0 enum_ORDRE_OPERATEUR) (v_oo enum_ORDRE_OPERATEUR)
  (v_interdits_1 (set Int)) (v_interdits (set Int))
  (v_etat_dabz_7777 enum_ETAT_DAB) (v_etat_dab_2 enum_ETAT_DAB)
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_autz_7778 enum_ETAT_AUTOMATE) (v_etat_aut_1 enum_ETAT_AUTOMATE)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat_1 enum_ETAT_DAB) (v_etat_0 enum_ETAT_DAB) (v_datez_7777 Int)
  (v_date_1 Int) (v_date_0 Int) (v_date Int) (v_crt_int (set Int))
  (v_crt Int) (v_cpt_crt (set (tuple2 Int Int))) (v_corbeillez_7777 Int)
  (v_corbeille_2 Int) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptesz_7777 (set (tuple2 Int Int))) (v_comptes_2 (set (tuple2 Int
  Int))) (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int
  Int))) (v_clts (set Int)) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cartez_7778 Int) (v_carte_1 Int) (v_carte_0 Int) (v_carte Int)
  (v_caissez_7777 Int) (v_caisse_2 Int) (v_caisse_1 Int) (v_caisse Int)
  (v_avance_1 Int) (v_avance Int) (v_K0 Int) (v_HS Int) (v_D_min Int)
  (v_D_max Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f11 v_tedaz_7777 v_teda_2 v_teda_1 v_teda_0 v_teda v_som_0 v_som v_rjt
  v_retraitsz_7777 v_retraits_2 v_retraits_1 v_retraits v_panne_dabz_7777
  v_panne_dab_2 v_panne_dab_1 v_panne_dab v_pan_dab_1 v_pan_dab_0
  v_ordrez_7777 v_ordre_2 v_ordre_1 v_ordre v_oo_0 v_oo v_interdits_1
  v_interdits v_etat_dabz_7777 v_etat_dab_2 v_etat_dab_1 v_etat_dab
  v_etat_autz_7778 v_etat_aut_1 v_etat_aut_0 v_etat_aut v_etat_1 v_etat_0
  v_datez_7777 v_date_1 v_date_0 v_date v_crt_int v_crt v_cpt_crt
  v_corbeillez_7777 v_corbeille_2 v_corbeille_1 v_corbeille v_comptesz_7777
  v_comptes_2 v_comptes_1 v_comptes v_clts v_clients_1 v_clients
  v_cartez_7778 v_carte_1 v_carte_0 v_carte v_caissez_7777 v_caisse_2
  v_caisse_1 v_caisse v_avance_1 v_avance v_K0 v_HS v_D_min v_D_max v_DATE
  v_CARTE) (mem int (t2tb3 (- v_teda_0 1)) (t2tb2 integer)))))

(declare-fun f12 (Int Int Int Int Int Int Int Int Int Int Int Int Bool Bool
  Bool Bool Bool Bool enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR (set Int) (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_DAB enum_ETAT_DAB enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_DAB enum_ETAT_DAB Int Int
  Int Int (set Int) Int (set (tuple2 Int Int)) Int Int Int Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set Int) (set Int) Int Int Int Int Int
  Int Int Int Int Int Int Int Int Int (set Int) (set Int)) Bool)

;; f12_def
  (assert
  (forall ((v_tedaz_7777 Int) (v_teda_2 Int) (v_teda_1 Int) (v_teda_0 Int)
  (v_teda Int) (v_som_0 Int) (v_som Int) (v_rjt Int) (v_retraitsz_7777 Int)
  (v_retraits_2 Int) (v_retraits_1 Int) (v_retraits Int)
  (v_panne_dabz_7777 Bool) (v_panne_dab_2 Bool) (v_panne_dab_1 Bool)
  (v_panne_dab Bool) (v_pan_dab_1 Bool) (v_pan_dab_0 Bool)
  (v_ordrez_7777 enum_ORDRE_OPERATEUR) (v_ordre_2 enum_ORDRE_OPERATEUR)
  (v_ordre_1 enum_ORDRE_OPERATEUR) (v_ordre enum_ORDRE_OPERATEUR)
  (v_oo_0 enum_ORDRE_OPERATEUR) (v_oo enum_ORDRE_OPERATEUR)
  (v_interdits_1 (set Int)) (v_interdits (set Int))
  (v_etat_dabz_7777 enum_ETAT_DAB) (v_etat_dab_2 enum_ETAT_DAB)
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_autz_7778 enum_ETAT_AUTOMATE) (v_etat_aut_1 enum_ETAT_AUTOMATE)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat_1 enum_ETAT_DAB) (v_etat_0 enum_ETAT_DAB) (v_datez_7777 Int)
  (v_date_1 Int) (v_date_0 Int) (v_date Int) (v_crt_int (set Int))
  (v_crt Int) (v_cpt_crt (set (tuple2 Int Int))) (v_corbeillez_7777 Int)
  (v_corbeille_2 Int) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptesz_7777 (set (tuple2 Int Int))) (v_comptes_2 (set (tuple2 Int
  Int))) (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int
  Int))) (v_clts (set Int)) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cartez_7778 Int) (v_carte_1 Int) (v_carte_0 Int) (v_carte Int)
  (v_caissez_7777 Int) (v_caisse_2 Int) (v_caisse_1 Int) (v_caisse Int)
  (v_avance_1 Int) (v_avance Int) (v_K0 Int) (v_HS Int) (v_D_min Int)
  (v_D_max Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f12 v_tedaz_7777 v_teda_2 v_teda_1 v_teda_0 v_teda v_som_0 v_som v_rjt
  v_retraitsz_7777 v_retraits_2 v_retraits_1 v_retraits v_panne_dabz_7777
  v_panne_dab_2 v_panne_dab_1 v_panne_dab v_pan_dab_1 v_pan_dab_0
  v_ordrez_7777 v_ordre_2 v_ordre_1 v_ordre v_oo_0 v_oo v_interdits_1
  v_interdits v_etat_dabz_7777 v_etat_dab_2 v_etat_dab_1 v_etat_dab
  v_etat_autz_7778 v_etat_aut_1 v_etat_aut_0 v_etat_aut v_etat_1 v_etat_0
  v_datez_7777 v_date_1 v_date_0 v_date v_crt_int v_crt v_cpt_crt
  v_corbeillez_7777 v_corbeille_2 v_corbeille_1 v_corbeille v_comptesz_7777
  v_comptes_2 v_comptes_1 v_comptes v_clts v_clients_1 v_clients
  v_cartez_7778 v_carte_1 v_carte_0 v_carte v_caissez_7777 v_caisse_2
  v_caisse_1 v_caisse v_avance_1 v_avance v_K0 v_HS v_D_min v_D_max v_DATE
  v_CARTE) (<= 0 (- v_teda_0 1)))))

(declare-fun f13 (Int Int Int Int Int Int Int Int Int Int Int Int Bool Bool
  Bool Bool Bool Bool enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR (set Int) (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_DAB enum_ETAT_DAB enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_DAB enum_ETAT_DAB Int Int
  Int Int (set Int) Int (set (tuple2 Int Int)) Int Int Int Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set Int) (set Int) Int Int Int Int Int
  Int Int Int Int Int Int Int Int Int (set Int) (set Int)) Bool)

;; f13_def
  (assert
  (forall ((v_tedaz_7777 Int) (v_teda_2 Int) (v_teda_1 Int) (v_teda_0 Int)
  (v_teda Int) (v_som_0 Int) (v_som Int) (v_rjt Int) (v_retraitsz_7777 Int)
  (v_retraits_2 Int) (v_retraits_1 Int) (v_retraits Int)
  (v_panne_dabz_7777 Bool) (v_panne_dab_2 Bool) (v_panne_dab_1 Bool)
  (v_panne_dab Bool) (v_pan_dab_1 Bool) (v_pan_dab_0 Bool)
  (v_ordrez_7777 enum_ORDRE_OPERATEUR) (v_ordre_2 enum_ORDRE_OPERATEUR)
  (v_ordre_1 enum_ORDRE_OPERATEUR) (v_ordre enum_ORDRE_OPERATEUR)
  (v_oo_0 enum_ORDRE_OPERATEUR) (v_oo enum_ORDRE_OPERATEUR)
  (v_interdits_1 (set Int)) (v_interdits (set Int))
  (v_etat_dabz_7777 enum_ETAT_DAB) (v_etat_dab_2 enum_ETAT_DAB)
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_autz_7778 enum_ETAT_AUTOMATE) (v_etat_aut_1 enum_ETAT_AUTOMATE)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat_1 enum_ETAT_DAB) (v_etat_0 enum_ETAT_DAB) (v_datez_7777 Int)
  (v_date_1 Int) (v_date_0 Int) (v_date Int) (v_crt_int (set Int))
  (v_crt Int) (v_cpt_crt (set (tuple2 Int Int))) (v_corbeillez_7777 Int)
  (v_corbeille_2 Int) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptesz_7777 (set (tuple2 Int Int))) (v_comptes_2 (set (tuple2 Int
  Int))) (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int
  Int))) (v_clts (set Int)) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cartez_7778 Int) (v_carte_1 Int) (v_carte_0 Int) (v_carte Int)
  (v_caissez_7777 Int) (v_caisse_2 Int) (v_caisse_1 Int) (v_caisse Int)
  (v_avance_1 Int) (v_avance Int) (v_K0 Int) (v_HS Int) (v_D_min Int)
  (v_D_max Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f13 v_tedaz_7777 v_teda_2 v_teda_1 v_teda_0 v_teda v_som_0 v_som v_rjt
  v_retraitsz_7777 v_retraits_2 v_retraits_1 v_retraits v_panne_dabz_7777
  v_panne_dab_2 v_panne_dab_1 v_panne_dab v_pan_dab_1 v_pan_dab_0
  v_ordrez_7777 v_ordre_2 v_ordre_1 v_ordre v_oo_0 v_oo v_interdits_1
  v_interdits v_etat_dabz_7777 v_etat_dab_2 v_etat_dab_1 v_etat_dab
  v_etat_autz_7778 v_etat_aut_1 v_etat_aut_0 v_etat_aut v_etat_1 v_etat_0
  v_datez_7777 v_date_1 v_date_0 v_date v_crt_int v_crt v_cpt_crt
  v_corbeillez_7777 v_corbeille_2 v_corbeille_1 v_corbeille v_comptesz_7777
  v_comptes_2 v_comptes_1 v_comptes v_clts v_clients_1 v_clients
  v_cartez_7778 v_carte_1 v_carte_0 v_carte v_caissez_7777 v_caisse_2
  v_caisse_1 v_caisse v_avance_1 v_avance v_K0 v_HS v_D_min v_D_max v_DATE
  v_CARTE) (= (+ (+ v_som 0) 0) v_som))))

(declare-fun f14 (Int Int Int Int Int Int Int Int Int Int Int Int Bool Bool
  Bool Bool Bool Bool enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR (set Int) (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_DAB enum_ETAT_DAB enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_DAB enum_ETAT_DAB Int Int
  Int Int (set Int) Int (set (tuple2 Int Int)) Int Int Int Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set Int) (set Int) Int Int Int Int Int
  Int Int Int Int Int Int Int Int Int (set Int) (set Int)) Bool)

;; f14_def
  (assert
  (forall ((v_tedaz_7777 Int) (v_teda_2 Int) (v_teda_1 Int) (v_teda_0 Int)
  (v_teda Int) (v_som_0 Int) (v_som Int) (v_rjt Int) (v_retraitsz_7777 Int)
  (v_retraits_2 Int) (v_retraits_1 Int) (v_retraits Int)
  (v_panne_dabz_7777 Bool) (v_panne_dab_2 Bool) (v_panne_dab_1 Bool)
  (v_panne_dab Bool) (v_pan_dab_1 Bool) (v_pan_dab_0 Bool)
  (v_ordrez_7777 enum_ORDRE_OPERATEUR) (v_ordre_2 enum_ORDRE_OPERATEUR)
  (v_ordre_1 enum_ORDRE_OPERATEUR) (v_ordre enum_ORDRE_OPERATEUR)
  (v_oo_0 enum_ORDRE_OPERATEUR) (v_oo enum_ORDRE_OPERATEUR)
  (v_interdits_1 (set Int)) (v_interdits (set Int))
  (v_etat_dabz_7777 enum_ETAT_DAB) (v_etat_dab_2 enum_ETAT_DAB)
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_autz_7778 enum_ETAT_AUTOMATE) (v_etat_aut_1 enum_ETAT_AUTOMATE)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat_1 enum_ETAT_DAB) (v_etat_0 enum_ETAT_DAB) (v_datez_7777 Int)
  (v_date_1 Int) (v_date_0 Int) (v_date Int) (v_crt_int (set Int))
  (v_crt Int) (v_cpt_crt (set (tuple2 Int Int))) (v_corbeillez_7777 Int)
  (v_corbeille_2 Int) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptesz_7777 (set (tuple2 Int Int))) (v_comptes_2 (set (tuple2 Int
  Int))) (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int
  Int))) (v_clts (set Int)) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cartez_7778 Int) (v_carte_1 Int) (v_carte_0 Int) (v_carte Int)
  (v_caissez_7777 Int) (v_caisse_2 Int) (v_caisse_1 Int) (v_caisse Int)
  (v_avance_1 Int) (v_avance Int) (v_K0 Int) (v_HS Int) (v_D_min Int)
  (v_D_max Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f14 v_tedaz_7777 v_teda_2 v_teda_1 v_teda_0 v_teda v_som_0 v_som v_rjt
  v_retraitsz_7777 v_retraits_2 v_retraits_1 v_retraits v_panne_dabz_7777
  v_panne_dab_2 v_panne_dab_1 v_panne_dab v_pan_dab_1 v_pan_dab_0
  v_ordrez_7777 v_ordre_2 v_ordre_1 v_ordre v_oo_0 v_oo v_interdits_1
  v_interdits v_etat_dabz_7777 v_etat_dab_2 v_etat_dab_1 v_etat_dab
  v_etat_autz_7778 v_etat_aut_1 v_etat_aut_0 v_etat_aut v_etat_1 v_etat_0
  v_datez_7777 v_date_1 v_date_0 v_date v_crt_int v_crt v_cpt_crt
  v_corbeillez_7777 v_corbeille_2 v_corbeille_1 v_corbeille v_comptesz_7777
  v_comptes_2 v_comptes_1 v_comptes v_clts v_clients_1 v_clients
  v_cartez_7778 v_carte_1 v_carte_0 v_carte v_caissez_7777 v_caisse_2
  v_caisse_1 v_caisse v_avance_1 v_avance v_K0 v_HS v_D_min v_D_max v_DATE
  v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (=> (= v_oo E_Marche) (<= 2 v_teda_0))
  (=> (<= 2 v_teda_0) (= v_oo E_Marche))) (mem int (t2tb3 v_som)
  (t2tb2 integer))) (<= 0 v_som)) (<= v_som 2147483647)) (<= 901 v_som)) (mem
  (set1 int) (t2tb2 v_clts)
  (power int
  (diff int (t2tb2 v_CARTE)
  (union int (add int (t2tb3 v_K0) (empty int))
  (add int (t2tb3 v_HS) (empty int))))))) (mem (set1 (tuple21 int int))
  (t2tb14 v_cpt_crt) (infix_plmngt int int (t2tb2 v_clts) (t2tb2 nat))))
  (infix_eqeq int (dom int int (t2tb14 v_cpt_crt)) (t2tb2 v_clts))) (mem
  (set1 int) (t2tb2 v_crt_int) (power int (t2tb2 v_clts))))
  (=> (= v_etat_0 E_Hors_service)
  (or (= v_pan_dab_0 true) (<= (+ v_som 1) 900))))
  (=> (or (= v_pan_dab_0 true) (<= (+ v_som 1) 900))
  (= v_etat_0 E_Hors_service))) (mem int (t2tb3 v_teda_0) (t2tb2 integer)))
  (<= 0 v_teda_0)) (<= v_teda_0 2147483647)) (not (= v_teda_0 0)))
  (= v_oo E_Marche)))))

(declare-fun f15 (Int Int Int Int Int Int Int Int Int Int Int Int Bool Bool
  Bool Bool Bool Bool enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR (set Int) (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_DAB enum_ETAT_DAB enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_DAB enum_ETAT_DAB Int Int
  Int Int (set Int) Int (set (tuple2 Int Int)) Int Int Int Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set Int) (set Int) Int Int Int Int Int
  Int Int Int Int Int Int Int Int Int (set Int) (set Int)) Bool)

;; f15_def
  (assert
  (forall ((v_tedaz_7777 Int) (v_teda_2 Int) (v_teda_1 Int) (v_teda_0 Int)
  (v_teda Int) (v_som_0 Int) (v_som Int) (v_rjt Int) (v_retraitsz_7777 Int)
  (v_retraits_2 Int) (v_retraits_1 Int) (v_retraits Int)
  (v_panne_dabz_7777 Bool) (v_panne_dab_2 Bool) (v_panne_dab_1 Bool)
  (v_panne_dab Bool) (v_pan_dab_1 Bool) (v_pan_dab_0 Bool)
  (v_ordrez_7777 enum_ORDRE_OPERATEUR) (v_ordre_2 enum_ORDRE_OPERATEUR)
  (v_ordre_1 enum_ORDRE_OPERATEUR) (v_ordre enum_ORDRE_OPERATEUR)
  (v_oo_0 enum_ORDRE_OPERATEUR) (v_oo enum_ORDRE_OPERATEUR)
  (v_interdits_1 (set Int)) (v_interdits (set Int))
  (v_etat_dabz_7777 enum_ETAT_DAB) (v_etat_dab_2 enum_ETAT_DAB)
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_autz_7778 enum_ETAT_AUTOMATE) (v_etat_aut_1 enum_ETAT_AUTOMATE)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat_1 enum_ETAT_DAB) (v_etat_0 enum_ETAT_DAB) (v_datez_7777 Int)
  (v_date_1 Int) (v_date_0 Int) (v_date Int) (v_crt_int (set Int))
  (v_crt Int) (v_cpt_crt (set (tuple2 Int Int))) (v_corbeillez_7777 Int)
  (v_corbeille_2 Int) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptesz_7777 (set (tuple2 Int Int))) (v_comptes_2 (set (tuple2 Int
  Int))) (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int
  Int))) (v_clts (set Int)) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cartez_7778 Int) (v_carte_1 Int) (v_carte_0 Int) (v_carte Int)
  (v_caissez_7777 Int) (v_caisse_2 Int) (v_caisse_1 Int) (v_caisse Int)
  (v_avance_1 Int) (v_avance Int) (v_K0 Int) (v_HS Int) (v_D_min Int)
  (v_D_max Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f15 v_tedaz_7777 v_teda_2 v_teda_1 v_teda_0 v_teda v_som_0 v_som v_rjt
  v_retraitsz_7777 v_retraits_2 v_retraits_1 v_retraits v_panne_dabz_7777
  v_panne_dab_2 v_panne_dab_1 v_panne_dab v_pan_dab_1 v_pan_dab_0
  v_ordrez_7777 v_ordre_2 v_ordre_1 v_ordre v_oo_0 v_oo v_interdits_1
  v_interdits v_etat_dabz_7777 v_etat_dab_2 v_etat_dab_1 v_etat_dab
  v_etat_autz_7778 v_etat_aut_1 v_etat_aut_0 v_etat_aut v_etat_1 v_etat_0
  v_datez_7777 v_date_1 v_date_0 v_date v_crt_int v_crt v_cpt_crt
  v_corbeillez_7777 v_corbeille_2 v_corbeille_1 v_corbeille v_comptesz_7777
  v_comptes_2 v_comptes_1 v_comptes v_clts v_clients_1 v_clients
  v_cartez_7778 v_carte_1 v_carte_0 v_carte v_caissez_7777 v_caisse_2
  v_caisse_1 v_caisse v_avance_1 v_avance v_K0 v_HS v_D_min v_D_max v_DATE
  v_CARTE) (<= 1 (- v_teda_0 1)))))

(declare-fun f16 (Int Int Int Int Int Int Int Int Int Int Int Int Bool Bool
  Bool Bool Bool Bool enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR (set Int) (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_DAB enum_ETAT_DAB enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_DAB enum_ETAT_DAB Int Int
  Int Int (set Int) Int (set (tuple2 Int Int)) Int Int Int Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set Int) (set Int) Int Int Int Int Int
  Int Int Int Int Int Int Int Int Int (set Int) (set Int)) Bool)

;; f16_def
  (assert
  (forall ((v_tedaz_7777 Int) (v_teda_2 Int) (v_teda_1 Int) (v_teda_0 Int)
  (v_teda Int) (v_som_0 Int) (v_som Int) (v_rjt Int) (v_retraitsz_7777 Int)
  (v_retraits_2 Int) (v_retraits_1 Int) (v_retraits Int)
  (v_panne_dabz_7777 Bool) (v_panne_dab_2 Bool) (v_panne_dab_1 Bool)
  (v_panne_dab Bool) (v_pan_dab_1 Bool) (v_pan_dab_0 Bool)
  (v_ordrez_7777 enum_ORDRE_OPERATEUR) (v_ordre_2 enum_ORDRE_OPERATEUR)
  (v_ordre_1 enum_ORDRE_OPERATEUR) (v_ordre enum_ORDRE_OPERATEUR)
  (v_oo_0 enum_ORDRE_OPERATEUR) (v_oo enum_ORDRE_OPERATEUR)
  (v_interdits_1 (set Int)) (v_interdits (set Int))
  (v_etat_dabz_7777 enum_ETAT_DAB) (v_etat_dab_2 enum_ETAT_DAB)
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_autz_7778 enum_ETAT_AUTOMATE) (v_etat_aut_1 enum_ETAT_AUTOMATE)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat_1 enum_ETAT_DAB) (v_etat_0 enum_ETAT_DAB) (v_datez_7777 Int)
  (v_date_1 Int) (v_date_0 Int) (v_date Int) (v_crt_int (set Int))
  (v_crt Int) (v_cpt_crt (set (tuple2 Int Int))) (v_corbeillez_7777 Int)
  (v_corbeille_2 Int) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptesz_7777 (set (tuple2 Int Int))) (v_comptes_2 (set (tuple2 Int
  Int))) (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int
  Int))) (v_clts (set Int)) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cartez_7778 Int) (v_carte_1 Int) (v_carte_0 Int) (v_carte Int)
  (v_caissez_7777 Int) (v_caisse_2 Int) (v_caisse_1 Int) (v_caisse Int)
  (v_avance_1 Int) (v_avance Int) (v_K0 Int) (v_HS Int) (v_D_min Int)
  (v_D_max Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f16 v_tedaz_7777 v_teda_2 v_teda_1 v_teda_0 v_teda v_som_0 v_som v_rjt
  v_retraitsz_7777 v_retraits_2 v_retraits_1 v_retraits v_panne_dabz_7777
  v_panne_dab_2 v_panne_dab_1 v_panne_dab v_pan_dab_1 v_pan_dab_0
  v_ordrez_7777 v_ordre_2 v_ordre_1 v_ordre v_oo_0 v_oo v_interdits_1
  v_interdits v_etat_dabz_7777 v_etat_dab_2 v_etat_dab_1 v_etat_dab
  v_etat_autz_7778 v_etat_aut_1 v_etat_aut_0 v_etat_aut v_etat_1 v_etat_0
  v_datez_7777 v_date_1 v_date_0 v_date v_crt_int v_crt v_cpt_crt
  v_corbeillez_7777 v_corbeille_2 v_corbeille_1 v_corbeille v_comptesz_7777
  v_comptes_2 v_comptes_1 v_comptes v_clts v_clients_1 v_clients
  v_cartez_7778 v_carte_1 v_carte_0 v_carte v_caissez_7777 v_caisse_2
  v_caisse_1 v_caisse v_avance_1 v_avance v_K0 v_HS v_D_min v_D_max v_DATE
  v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (=> (= v_oo E_Marche) (<= 2 v_teda_0))
  (=> (<= 2 v_teda_0) (= v_oo E_Marche))) (mem int (t2tb3 v_som)
  (t2tb2 integer))) (<= 0 v_som)) (<= v_som 2147483647)) (<= 901 v_som)) (mem
  (set1 int) (t2tb2 v_clts)
  (power int
  (diff int (t2tb2 v_CARTE)
  (union int (add int (t2tb3 v_K0) (empty int))
  (add int (t2tb3 v_HS) (empty int))))))) (mem (set1 (tuple21 int int))
  (t2tb14 v_cpt_crt) (infix_plmngt int int (t2tb2 v_clts) (t2tb2 nat))))
  (infix_eqeq int (dom int int (t2tb14 v_cpt_crt)) (t2tb2 v_clts))) (mem
  (set1 int) (t2tb2 v_crt_int) (power int (t2tb2 v_clts))))
  (=> (= v_etat_0 E_Hors_service)
  (or (= v_pan_dab_0 true) (<= (+ v_som 1) 900))))
  (=> (or (= v_pan_dab_0 true) (<= (+ v_som 1) 900))
  (= v_etat_0 E_Hors_service))) (mem int (t2tb3 v_teda_0) (t2tb2 integer)))
  (<= 0 v_teda_0)) (<= v_teda_0 2147483647)) (not (= v_teda_0 0)))
  (<= 1 (- v_teda_0 1))))))

(declare-fun f18 (Int Int Int Int Int Int Int Int Int Int Int Int Bool Bool
  Bool Bool Bool Bool enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR (set Int) (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_DAB enum_ETAT_DAB enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_DAB enum_ETAT_DAB Int Int
  Int Int (set Int) Int (set (tuple2 Int Int)) Int Int Int Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set Int) (set Int) Int Int Int Int Int
  Int Int Int Int Int Int Int Int Int (set Int) (set Int)) Bool)

;; f18_def
  (assert
  (forall ((v_tedaz_7777 Int) (v_teda_2 Int) (v_teda_1 Int) (v_teda_0 Int)
  (v_teda Int) (v_som_0 Int) (v_som Int) (v_rjt Int) (v_retraitsz_7777 Int)
  (v_retraits_2 Int) (v_retraits_1 Int) (v_retraits Int)
  (v_panne_dabz_7777 Bool) (v_panne_dab_2 Bool) (v_panne_dab_1 Bool)
  (v_panne_dab Bool) (v_pan_dab_1 Bool) (v_pan_dab_0 Bool)
  (v_ordrez_7777 enum_ORDRE_OPERATEUR) (v_ordre_2 enum_ORDRE_OPERATEUR)
  (v_ordre_1 enum_ORDRE_OPERATEUR) (v_ordre enum_ORDRE_OPERATEUR)
  (v_oo_0 enum_ORDRE_OPERATEUR) (v_oo enum_ORDRE_OPERATEUR)
  (v_interdits_1 (set Int)) (v_interdits (set Int))
  (v_etat_dabz_7777 enum_ETAT_DAB) (v_etat_dab_2 enum_ETAT_DAB)
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_autz_7778 enum_ETAT_AUTOMATE) (v_etat_aut_1 enum_ETAT_AUTOMATE)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat_1 enum_ETAT_DAB) (v_etat_0 enum_ETAT_DAB) (v_datez_7777 Int)
  (v_date_1 Int) (v_date_0 Int) (v_date Int) (v_crt_int (set Int))
  (v_crt Int) (v_cpt_crt (set (tuple2 Int Int))) (v_corbeillez_7777 Int)
  (v_corbeille_2 Int) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptesz_7777 (set (tuple2 Int Int))) (v_comptes_2 (set (tuple2 Int
  Int))) (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int
  Int))) (v_clts (set Int)) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cartez_7778 Int) (v_carte_1 Int) (v_carte_0 Int) (v_carte Int)
  (v_caissez_7777 Int) (v_caisse_2 Int) (v_caisse_1 Int) (v_caisse Int)
  (v_avance_1 Int) (v_avance Int) (v_K0 Int) (v_HS Int) (v_D_min Int)
  (v_D_max Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f18 v_tedaz_7777 v_teda_2 v_teda_1 v_teda_0 v_teda v_som_0 v_som v_rjt
  v_retraitsz_7777 v_retraits_2 v_retraits_1 v_retraits v_panne_dabz_7777
  v_panne_dab_2 v_panne_dab_1 v_panne_dab v_pan_dab_1 v_pan_dab_0
  v_ordrez_7777 v_ordre_2 v_ordre_1 v_ordre v_oo_0 v_oo v_interdits_1
  v_interdits v_etat_dabz_7777 v_etat_dab_2 v_etat_dab_1 v_etat_dab
  v_etat_autz_7778 v_etat_aut_1 v_etat_aut_0 v_etat_aut v_etat_1 v_etat_0
  v_datez_7777 v_date_1 v_date_0 v_date v_crt_int v_crt v_cpt_crt
  v_corbeillez_7777 v_corbeille_2 v_corbeille_1 v_corbeille v_comptesz_7777
  v_comptes_2 v_comptes_1 v_comptes v_clts v_clients_1 v_clients
  v_cartez_7778 v_carte_1 v_carte_0 v_carte v_caissez_7777 v_caisse_2
  v_caisse_1 v_caisse v_avance_1 v_avance v_K0 v_HS v_D_min v_D_max v_DATE
  v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (=> (= v_oo E_Marche) (<= 2 v_teda_0))
  (=> (<= 2 v_teda_0) (= v_oo E_Marche))) (mem int (t2tb3 v_som)
  (t2tb2 integer))) (<= 0 v_som)) (<= v_som 2147483647)) (<= 901 v_som)) (mem
  (set1 int) (t2tb2 v_clts)
  (power int
  (diff int (t2tb2 v_CARTE)
  (union int (add int (t2tb3 v_K0) (empty int))
  (add int (t2tb3 v_HS) (empty int))))))) (mem (set1 (tuple21 int int))
  (t2tb14 v_cpt_crt) (infix_plmngt int int (t2tb2 v_clts) (t2tb2 nat))))
  (infix_eqeq int (dom int int (t2tb14 v_cpt_crt)) (t2tb2 v_clts))) (mem
  (set1 int) (t2tb2 v_crt_int) (power int (t2tb2 v_clts))))
  (=> (= v_etat_0 E_Hors_service)
  (or (= v_pan_dab_0 true) (<= (+ v_som 1) 900))))
  (=> (or (= v_pan_dab_0 true) (<= (+ v_som 1) 900))
  (= v_etat_0 E_Hors_service))) (mem int (t2tb3 v_teda_0) (t2tb2 integer)))
  (<= 0 v_teda_0)) (<= v_teda_0 2147483647)) (not (= v_teda_0 0))) (mem 
  int (t2tb3 v_teda_2) (t2tb2 integer))) (<= 0 v_teda_2))
  (= (+ (+ v_caisse_2 v_retraits_2) v_corbeille_2) v_som))
  (=> (= v_ordre_2 E_Marche) (<= 1 v_teda_2)))
  (=> (<= 1 v_teda_2) (= v_ordre_2 E_Marche)))
  (=> (= v_etat_dab_2 E_Hors_service)
  (or (= v_panne_dab_2 true) (<= (+ v_caisse_2 1) 900))))
  (=> (or (= v_panne_dab_2 true) (<= (+ v_caisse_2 1) 900))
  (= v_etat_dab_2 E_Hors_service))) (= v_ordre_2 E_Marche))
  (= v_etat_dab_2 E_En_service)) (mem int (t2tb3 v_date_0) (t2tb2 v_DATE)))
  (=> (= v_etat_1 E_Hors_service)
  (or (= v_pan_dab_1 true) (<= (+ (- v_caisse_2 v_som_0) 1) 900))))
  (=> (or (= v_pan_dab_1 true) (<= (+ (- v_caisse_2 v_som_0) 1) 900))
  (= v_etat_1 E_Hors_service))) (=> (= v_oo_0 E_Marche) (<= 2 v_teda_2)))
  (=> (<= 2 v_teda_2) (= v_oo_0 E_Marche))) (mem int (t2tb3 v_crt)
  (t2tb2 v_clts))) (mem int (t2tb3 v_som_0) (t2tb2 (mk 100 900)))) (mem 
  int (t2tb3 v_rjt)
  (union int (add int (t2tb3 0) (empty int))
  (add int (t2tb3 v_som_0) (empty int))))) (<= v_som_0 v_caisse_2))
  (<= v_som_0 (tb2t3 (apply int int (t2tb14 v_comptes_2) (t2tb3 v_crt))))))))

(declare-fun f19 (Int Int Int Int Int Int Int Int Int Int Int Int Bool Bool
  Bool Bool Bool Bool enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR (set Int) (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_DAB enum_ETAT_DAB enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_DAB enum_ETAT_DAB Int Int
  Int Int (set Int) Int (set (tuple2 Int Int)) Int Int Int Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set Int) (set Int) Int Int Int Int Int
  Int Int Int Int Int Int Int Int Int (set Int) (set Int)) Bool)

;; f19_def
  (assert
  (forall ((v_tedaz_7777 Int) (v_teda_2 Int) (v_teda_1 Int) (v_teda_0 Int)
  (v_teda Int) (v_som_0 Int) (v_som Int) (v_rjt Int) (v_retraitsz_7777 Int)
  (v_retraits_2 Int) (v_retraits_1 Int) (v_retraits Int)
  (v_panne_dabz_7777 Bool) (v_panne_dab_2 Bool) (v_panne_dab_1 Bool)
  (v_panne_dab Bool) (v_pan_dab_1 Bool) (v_pan_dab_0 Bool)
  (v_ordrez_7777 enum_ORDRE_OPERATEUR) (v_ordre_2 enum_ORDRE_OPERATEUR)
  (v_ordre_1 enum_ORDRE_OPERATEUR) (v_ordre enum_ORDRE_OPERATEUR)
  (v_oo_0 enum_ORDRE_OPERATEUR) (v_oo enum_ORDRE_OPERATEUR)
  (v_interdits_1 (set Int)) (v_interdits (set Int))
  (v_etat_dabz_7777 enum_ETAT_DAB) (v_etat_dab_2 enum_ETAT_DAB)
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_autz_7778 enum_ETAT_AUTOMATE) (v_etat_aut_1 enum_ETAT_AUTOMATE)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat_1 enum_ETAT_DAB) (v_etat_0 enum_ETAT_DAB) (v_datez_7777 Int)
  (v_date_1 Int) (v_date_0 Int) (v_date Int) (v_crt_int (set Int))
  (v_crt Int) (v_cpt_crt (set (tuple2 Int Int))) (v_corbeillez_7777 Int)
  (v_corbeille_2 Int) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptesz_7777 (set (tuple2 Int Int))) (v_comptes_2 (set (tuple2 Int
  Int))) (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int
  Int))) (v_clts (set Int)) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cartez_7778 Int) (v_carte_1 Int) (v_carte_0 Int) (v_carte Int)
  (v_caissez_7777 Int) (v_caisse_2 Int) (v_caisse_1 Int) (v_caisse Int)
  (v_avance_1 Int) (v_avance Int) (v_K0 Int) (v_HS Int) (v_D_min Int)
  (v_D_max Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f19 v_tedaz_7777 v_teda_2 v_teda_1 v_teda_0 v_teda v_som_0 v_som v_rjt
  v_retraitsz_7777 v_retraits_2 v_retraits_1 v_retraits v_panne_dabz_7777
  v_panne_dab_2 v_panne_dab_1 v_panne_dab v_pan_dab_1 v_pan_dab_0
  v_ordrez_7777 v_ordre_2 v_ordre_1 v_ordre v_oo_0 v_oo v_interdits_1
  v_interdits v_etat_dabz_7777 v_etat_dab_2 v_etat_dab_1 v_etat_dab
  v_etat_autz_7778 v_etat_aut_1 v_etat_aut_0 v_etat_aut v_etat_1 v_etat_0
  v_datez_7777 v_date_1 v_date_0 v_date v_crt_int v_crt v_cpt_crt
  v_corbeillez_7777 v_corbeille_2 v_corbeille_1 v_corbeille v_comptesz_7777
  v_comptes_2 v_comptes_1 v_comptes v_clts v_clients_1 v_clients
  v_cartez_7778 v_carte_1 v_carte_0 v_carte v_caissez_7777 v_caisse_2
  v_caisse_1 v_caisse v_avance_1 v_avance v_K0 v_HS v_D_min v_D_max v_DATE
  v_CARTE) (<= (+ (- v_teda_2 1) 1) v_teda_2))))

(declare-fun f20 (Int Int Int Int Int Int Int Int Int Int Int Int Bool Bool
  Bool Bool Bool Bool enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR (set Int) (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_DAB enum_ETAT_DAB enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_DAB enum_ETAT_DAB Int Int
  Int Int (set Int) Int (set (tuple2 Int Int)) Int Int Int Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set Int) (set Int) Int Int Int Int Int
  Int Int Int Int Int Int Int Int Int (set Int) (set Int)) Bool)

;; f20_def
  (assert
  (forall ((v_tedaz_7777 Int) (v_teda_2 Int) (v_teda_1 Int) (v_teda_0 Int)
  (v_teda Int) (v_som_0 Int) (v_som Int) (v_rjt Int) (v_retraitsz_7777 Int)
  (v_retraits_2 Int) (v_retraits_1 Int) (v_retraits Int)
  (v_panne_dabz_7777 Bool) (v_panne_dab_2 Bool) (v_panne_dab_1 Bool)
  (v_panne_dab Bool) (v_pan_dab_1 Bool) (v_pan_dab_0 Bool)
  (v_ordrez_7777 enum_ORDRE_OPERATEUR) (v_ordre_2 enum_ORDRE_OPERATEUR)
  (v_ordre_1 enum_ORDRE_OPERATEUR) (v_ordre enum_ORDRE_OPERATEUR)
  (v_oo_0 enum_ORDRE_OPERATEUR) (v_oo enum_ORDRE_OPERATEUR)
  (v_interdits_1 (set Int)) (v_interdits (set Int))
  (v_etat_dabz_7777 enum_ETAT_DAB) (v_etat_dab_2 enum_ETAT_DAB)
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_autz_7778 enum_ETAT_AUTOMATE) (v_etat_aut_1 enum_ETAT_AUTOMATE)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat_1 enum_ETAT_DAB) (v_etat_0 enum_ETAT_DAB) (v_datez_7777 Int)
  (v_date_1 Int) (v_date_0 Int) (v_date Int) (v_crt_int (set Int))
  (v_crt Int) (v_cpt_crt (set (tuple2 Int Int))) (v_corbeillez_7777 Int)
  (v_corbeille_2 Int) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptesz_7777 (set (tuple2 Int Int))) (v_comptes_2 (set (tuple2 Int
  Int))) (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int
  Int))) (v_clts (set Int)) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cartez_7778 Int) (v_carte_1 Int) (v_carte_0 Int) (v_carte Int)
  (v_caissez_7777 Int) (v_caisse_2 Int) (v_caisse_1 Int) (v_caisse Int)
  (v_avance_1 Int) (v_avance Int) (v_K0 Int) (v_HS Int) (v_D_min Int)
  (v_D_max Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f20 v_tedaz_7777 v_teda_2 v_teda_1 v_teda_0 v_teda v_som_0 v_som v_rjt
  v_retraitsz_7777 v_retraits_2 v_retraits_1 v_retraits v_panne_dabz_7777
  v_panne_dab_2 v_panne_dab_1 v_panne_dab v_pan_dab_1 v_pan_dab_0
  v_ordrez_7777 v_ordre_2 v_ordre_1 v_ordre v_oo_0 v_oo v_interdits_1
  v_interdits v_etat_dabz_7777 v_etat_dab_2 v_etat_dab_1 v_etat_dab
  v_etat_autz_7778 v_etat_aut_1 v_etat_aut_0 v_etat_aut v_etat_1 v_etat_0
  v_datez_7777 v_date_1 v_date_0 v_date v_crt_int v_crt v_cpt_crt
  v_corbeillez_7777 v_corbeille_2 v_corbeille_1 v_corbeille v_comptesz_7777
  v_comptes_2 v_comptes_1 v_comptes v_clts v_clients_1 v_clients
  v_cartez_7778 v_carte_1 v_carte_0 v_carte v_caissez_7777 v_caisse_2
  v_caisse_1 v_caisse v_avance_1 v_avance v_K0 v_HS v_D_min v_D_max v_DATE
  v_CARTE) (mem int (t2tb3 (- v_teda_2 1)) (t2tb2 integer)))))

(declare-fun f21 (Int Int Int Int Int Int Int Int Int Int Int Int Bool Bool
  Bool Bool Bool Bool enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR (set Int) (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_DAB enum_ETAT_DAB enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_DAB enum_ETAT_DAB Int Int
  Int Int (set Int) Int (set (tuple2 Int Int)) Int Int Int Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set Int) (set Int) Int Int Int Int Int
  Int Int Int Int Int Int Int Int Int (set Int) (set Int)) Bool)

;; f21_def
  (assert
  (forall ((v_tedaz_7777 Int) (v_teda_2 Int) (v_teda_1 Int) (v_teda_0 Int)
  (v_teda Int) (v_som_0 Int) (v_som Int) (v_rjt Int) (v_retraitsz_7777 Int)
  (v_retraits_2 Int) (v_retraits_1 Int) (v_retraits Int)
  (v_panne_dabz_7777 Bool) (v_panne_dab_2 Bool) (v_panne_dab_1 Bool)
  (v_panne_dab Bool) (v_pan_dab_1 Bool) (v_pan_dab_0 Bool)
  (v_ordrez_7777 enum_ORDRE_OPERATEUR) (v_ordre_2 enum_ORDRE_OPERATEUR)
  (v_ordre_1 enum_ORDRE_OPERATEUR) (v_ordre enum_ORDRE_OPERATEUR)
  (v_oo_0 enum_ORDRE_OPERATEUR) (v_oo enum_ORDRE_OPERATEUR)
  (v_interdits_1 (set Int)) (v_interdits (set Int))
  (v_etat_dabz_7777 enum_ETAT_DAB) (v_etat_dab_2 enum_ETAT_DAB)
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_autz_7778 enum_ETAT_AUTOMATE) (v_etat_aut_1 enum_ETAT_AUTOMATE)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat_1 enum_ETAT_DAB) (v_etat_0 enum_ETAT_DAB) (v_datez_7777 Int)
  (v_date_1 Int) (v_date_0 Int) (v_date Int) (v_crt_int (set Int))
  (v_crt Int) (v_cpt_crt (set (tuple2 Int Int))) (v_corbeillez_7777 Int)
  (v_corbeille_2 Int) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptesz_7777 (set (tuple2 Int Int))) (v_comptes_2 (set (tuple2 Int
  Int))) (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int
  Int))) (v_clts (set Int)) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cartez_7778 Int) (v_carte_1 Int) (v_carte_0 Int) (v_carte Int)
  (v_caissez_7777 Int) (v_caisse_2 Int) (v_caisse_1 Int) (v_caisse Int)
  (v_avance_1 Int) (v_avance Int) (v_K0 Int) (v_HS Int) (v_D_min Int)
  (v_D_max Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f21 v_tedaz_7777 v_teda_2 v_teda_1 v_teda_0 v_teda v_som_0 v_som v_rjt
  v_retraitsz_7777 v_retraits_2 v_retraits_1 v_retraits v_panne_dabz_7777
  v_panne_dab_2 v_panne_dab_1 v_panne_dab v_pan_dab_1 v_pan_dab_0
  v_ordrez_7777 v_ordre_2 v_ordre_1 v_ordre v_oo_0 v_oo v_interdits_1
  v_interdits v_etat_dabz_7777 v_etat_dab_2 v_etat_dab_1 v_etat_dab
  v_etat_autz_7778 v_etat_aut_1 v_etat_aut_0 v_etat_aut v_etat_1 v_etat_0
  v_datez_7777 v_date_1 v_date_0 v_date v_crt_int v_crt v_cpt_crt
  v_corbeillez_7777 v_corbeille_2 v_corbeille_1 v_corbeille v_comptesz_7777
  v_comptes_2 v_comptes_1 v_comptes v_clts v_clients_1 v_clients
  v_cartez_7778 v_carte_1 v_carte_0 v_carte v_caissez_7777 v_caisse_2
  v_caisse_1 v_caisse v_avance_1 v_avance v_K0 v_HS v_D_min v_D_max v_DATE
  v_CARTE) (<= 0 (- v_teda_2 1)))))

(declare-fun f22 (Int Int Int Int Int Int Int Int Int Int Int Int Bool Bool
  Bool Bool Bool Bool enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR (set Int) (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_DAB enum_ETAT_DAB enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_DAB enum_ETAT_DAB Int Int
  Int Int (set Int) Int (set (tuple2 Int Int)) Int Int Int Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set Int) (set Int) Int Int Int Int Int
  Int Int Int Int Int Int Int Int Int (set Int) (set Int)) Bool)

;; f22_def
  (assert
  (forall ((v_tedaz_7777 Int) (v_teda_2 Int) (v_teda_1 Int) (v_teda_0 Int)
  (v_teda Int) (v_som_0 Int) (v_som Int) (v_rjt Int) (v_retraitsz_7777 Int)
  (v_retraits_2 Int) (v_retraits_1 Int) (v_retraits Int)
  (v_panne_dabz_7777 Bool) (v_panne_dab_2 Bool) (v_panne_dab_1 Bool)
  (v_panne_dab Bool) (v_pan_dab_1 Bool) (v_pan_dab_0 Bool)
  (v_ordrez_7777 enum_ORDRE_OPERATEUR) (v_ordre_2 enum_ORDRE_OPERATEUR)
  (v_ordre_1 enum_ORDRE_OPERATEUR) (v_ordre enum_ORDRE_OPERATEUR)
  (v_oo_0 enum_ORDRE_OPERATEUR) (v_oo enum_ORDRE_OPERATEUR)
  (v_interdits_1 (set Int)) (v_interdits (set Int))
  (v_etat_dabz_7777 enum_ETAT_DAB) (v_etat_dab_2 enum_ETAT_DAB)
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_autz_7778 enum_ETAT_AUTOMATE) (v_etat_aut_1 enum_ETAT_AUTOMATE)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat_1 enum_ETAT_DAB) (v_etat_0 enum_ETAT_DAB) (v_datez_7777 Int)
  (v_date_1 Int) (v_date_0 Int) (v_date Int) (v_crt_int (set Int))
  (v_crt Int) (v_cpt_crt (set (tuple2 Int Int))) (v_corbeillez_7777 Int)
  (v_corbeille_2 Int) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptesz_7777 (set (tuple2 Int Int))) (v_comptes_2 (set (tuple2 Int
  Int))) (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int
  Int))) (v_clts (set Int)) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cartez_7778 Int) (v_carte_1 Int) (v_carte_0 Int) (v_carte Int)
  (v_caissez_7777 Int) (v_caisse_2 Int) (v_caisse_1 Int) (v_caisse Int)
  (v_avance_1 Int) (v_avance Int) (v_K0 Int) (v_HS Int) (v_D_min Int)
  (v_D_max Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f22 v_tedaz_7777 v_teda_2 v_teda_1 v_teda_0 v_teda v_som_0 v_som v_rjt
  v_retraitsz_7777 v_retraits_2 v_retraits_1 v_retraits v_panne_dabz_7777
  v_panne_dab_2 v_panne_dab_1 v_panne_dab v_pan_dab_1 v_pan_dab_0
  v_ordrez_7777 v_ordre_2 v_ordre_1 v_ordre v_oo_0 v_oo v_interdits_1
  v_interdits v_etat_dabz_7777 v_etat_dab_2 v_etat_dab_1 v_etat_dab
  v_etat_autz_7778 v_etat_aut_1 v_etat_aut_0 v_etat_aut v_etat_1 v_etat_0
  v_datez_7777 v_date_1 v_date_0 v_date v_crt_int v_crt v_cpt_crt
  v_corbeillez_7777 v_corbeille_2 v_corbeille_1 v_corbeille v_comptesz_7777
  v_comptes_2 v_comptes_1 v_comptes v_clts v_clients_1 v_clients
  v_cartez_7778 v_carte_1 v_carte_0 v_carte v_caissez_7777 v_caisse_2
  v_caisse_1 v_caisse v_avance_1 v_avance v_K0 v_HS v_D_min v_D_max v_DATE
  v_CARTE)
  (= (+ (+ (- v_caisse_2 v_som_0) (- (+ v_retraits_2 v_som_0) v_rjt)) (+ v_corbeille_2 v_rjt)) v_som))))

(declare-fun f23 (Int Int Int Int Int Int Int Int Int Int Int Int Bool Bool
  Bool Bool Bool Bool enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR (set Int) (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_DAB enum_ETAT_DAB enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_DAB enum_ETAT_DAB Int Int
  Int Int (set Int) Int (set (tuple2 Int Int)) Int Int Int Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set Int) (set Int) Int Int Int Int Int
  Int Int Int Int Int Int Int Int Int (set Int) (set Int)) Bool)

;; f23_def
  (assert
  (forall ((v_tedaz_7777 Int) (v_teda_2 Int) (v_teda_1 Int) (v_teda_0 Int)
  (v_teda Int) (v_som_0 Int) (v_som Int) (v_rjt Int) (v_retraitsz_7777 Int)
  (v_retraits_2 Int) (v_retraits_1 Int) (v_retraits Int)
  (v_panne_dabz_7777 Bool) (v_panne_dab_2 Bool) (v_panne_dab_1 Bool)
  (v_panne_dab Bool) (v_pan_dab_1 Bool) (v_pan_dab_0 Bool)
  (v_ordrez_7777 enum_ORDRE_OPERATEUR) (v_ordre_2 enum_ORDRE_OPERATEUR)
  (v_ordre_1 enum_ORDRE_OPERATEUR) (v_ordre enum_ORDRE_OPERATEUR)
  (v_oo_0 enum_ORDRE_OPERATEUR) (v_oo enum_ORDRE_OPERATEUR)
  (v_interdits_1 (set Int)) (v_interdits (set Int))
  (v_etat_dabz_7777 enum_ETAT_DAB) (v_etat_dab_2 enum_ETAT_DAB)
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_autz_7778 enum_ETAT_AUTOMATE) (v_etat_aut_1 enum_ETAT_AUTOMATE)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat_1 enum_ETAT_DAB) (v_etat_0 enum_ETAT_DAB) (v_datez_7777 Int)
  (v_date_1 Int) (v_date_0 Int) (v_date Int) (v_crt_int (set Int))
  (v_crt Int) (v_cpt_crt (set (tuple2 Int Int))) (v_corbeillez_7777 Int)
  (v_corbeille_2 Int) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptesz_7777 (set (tuple2 Int Int))) (v_comptes_2 (set (tuple2 Int
  Int))) (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int
  Int))) (v_clts (set Int)) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cartez_7778 Int) (v_carte_1 Int) (v_carte_0 Int) (v_carte Int)
  (v_caissez_7777 Int) (v_caisse_2 Int) (v_caisse_1 Int) (v_caisse Int)
  (v_avance_1 Int) (v_avance Int) (v_K0 Int) (v_HS Int) (v_D_min Int)
  (v_D_max Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f23 v_tedaz_7777 v_teda_2 v_teda_1 v_teda_0 v_teda v_som_0 v_som v_rjt
  v_retraitsz_7777 v_retraits_2 v_retraits_1 v_retraits v_panne_dabz_7777
  v_panne_dab_2 v_panne_dab_1 v_panne_dab v_pan_dab_1 v_pan_dab_0
  v_ordrez_7777 v_ordre_2 v_ordre_1 v_ordre v_oo_0 v_oo v_interdits_1
  v_interdits v_etat_dabz_7777 v_etat_dab_2 v_etat_dab_1 v_etat_dab
  v_etat_autz_7778 v_etat_aut_1 v_etat_aut_0 v_etat_aut v_etat_1 v_etat_0
  v_datez_7777 v_date_1 v_date_0 v_date v_crt_int v_crt v_cpt_crt
  v_corbeillez_7777 v_corbeille_2 v_corbeille_1 v_corbeille v_comptesz_7777
  v_comptes_2 v_comptes_1 v_comptes v_clts v_clients_1 v_clients
  v_cartez_7778 v_carte_1 v_carte_0 v_carte v_caissez_7777 v_caisse_2
  v_caisse_1 v_caisse v_avance_1 v_avance v_K0 v_HS v_D_min v_D_max v_DATE
  v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (=> (= v_oo E_Marche) (<= 2 v_teda_0))
  (=> (<= 2 v_teda_0) (= v_oo E_Marche))) (mem int (t2tb3 v_som)
  (t2tb2 integer))) (<= 0 v_som)) (<= v_som 2147483647)) (<= 901 v_som)) (mem
  (set1 int) (t2tb2 v_clts)
  (power int
  (diff int (t2tb2 v_CARTE)
  (union int (add int (t2tb3 v_K0) (empty int))
  (add int (t2tb3 v_HS) (empty int))))))) (mem (set1 (tuple21 int int))
  (t2tb14 v_cpt_crt) (infix_plmngt int int (t2tb2 v_clts) (t2tb2 nat))))
  (infix_eqeq int (dom int int (t2tb14 v_cpt_crt)) (t2tb2 v_clts))) (mem
  (set1 int) (t2tb2 v_crt_int) (power int (t2tb2 v_clts))))
  (=> (= v_etat_0 E_Hors_service)
  (or (= v_pan_dab_0 true) (<= (+ v_som 1) 900))))
  (=> (or (= v_pan_dab_0 true) (<= (+ v_som 1) 900))
  (= v_etat_0 E_Hors_service))) (mem int (t2tb3 v_teda_0) (t2tb2 integer)))
  (<= 0 v_teda_0)) (<= v_teda_0 2147483647)) (not (= v_teda_0 0))) (mem 
  int (t2tb3 v_teda_2) (t2tb2 integer))) (<= 0 v_teda_2))
  (= (+ (+ v_caisse_2 v_retraits_2) v_corbeille_2) v_som))
  (=> (= v_ordre_2 E_Marche) (<= 1 v_teda_2)))
  (=> (<= 1 v_teda_2) (= v_ordre_2 E_Marche)))
  (=> (= v_etat_dab_2 E_Hors_service)
  (or (= v_panne_dab_2 true) (<= (+ v_caisse_2 1) 900))))
  (=> (or (= v_panne_dab_2 true) (<= (+ v_caisse_2 1) 900))
  (= v_etat_dab_2 E_Hors_service))) (= v_ordre_2 E_Marche))
  (= v_etat_dab_2 E_En_service)) (mem int (t2tb3 v_date_0) (t2tb2 v_DATE)))
  (=> (= v_etat_1 E_Hors_service)
  (or (= v_pan_dab_1 true) (<= (+ (- v_caisse_2 v_som_0) 1) 900))))
  (=> (or (= v_pan_dab_1 true) (<= (+ (- v_caisse_2 v_som_0) 1) 900))
  (= v_etat_1 E_Hors_service))) (=> (= v_oo_0 E_Marche) (<= 2 v_teda_2)))
  (=> (<= 2 v_teda_2) (= v_oo_0 E_Marche))) (mem int (t2tb3 v_crt)
  (t2tb2 v_clts))) (mem int (t2tb3 v_som_0) (t2tb2 (mk 100 900)))) (mem 
  int (t2tb3 v_rjt)
  (union int (add int (t2tb3 0) (empty int))
  (add int (t2tb3 v_som_0) (empty int))))) (<= v_som_0 v_caisse_2))
  (<= v_som_0 (tb2t3 (apply int int (t2tb14 v_comptes_2) (t2tb3 v_crt)))))
  (= v_oo_0 E_Marche)))))

(declare-fun f24 (Int Int Int Int Int Int Int Int Int Int Int Int Bool Bool
  Bool Bool Bool Bool enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR (set Int) (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_DAB enum_ETAT_DAB enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_DAB enum_ETAT_DAB Int Int
  Int Int (set Int) Int (set (tuple2 Int Int)) Int Int Int Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set Int) (set Int) Int Int Int Int Int
  Int Int Int Int Int Int Int Int Int (set Int) (set Int)) Bool)

;; f24_def
  (assert
  (forall ((v_tedaz_7777 Int) (v_teda_2 Int) (v_teda_1 Int) (v_teda_0 Int)
  (v_teda Int) (v_som_0 Int) (v_som Int) (v_rjt Int) (v_retraitsz_7777 Int)
  (v_retraits_2 Int) (v_retraits_1 Int) (v_retraits Int)
  (v_panne_dabz_7777 Bool) (v_panne_dab_2 Bool) (v_panne_dab_1 Bool)
  (v_panne_dab Bool) (v_pan_dab_1 Bool) (v_pan_dab_0 Bool)
  (v_ordrez_7777 enum_ORDRE_OPERATEUR) (v_ordre_2 enum_ORDRE_OPERATEUR)
  (v_ordre_1 enum_ORDRE_OPERATEUR) (v_ordre enum_ORDRE_OPERATEUR)
  (v_oo_0 enum_ORDRE_OPERATEUR) (v_oo enum_ORDRE_OPERATEUR)
  (v_interdits_1 (set Int)) (v_interdits (set Int))
  (v_etat_dabz_7777 enum_ETAT_DAB) (v_etat_dab_2 enum_ETAT_DAB)
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_autz_7778 enum_ETAT_AUTOMATE) (v_etat_aut_1 enum_ETAT_AUTOMATE)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat_1 enum_ETAT_DAB) (v_etat_0 enum_ETAT_DAB) (v_datez_7777 Int)
  (v_date_1 Int) (v_date_0 Int) (v_date Int) (v_crt_int (set Int))
  (v_crt Int) (v_cpt_crt (set (tuple2 Int Int))) (v_corbeillez_7777 Int)
  (v_corbeille_2 Int) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptesz_7777 (set (tuple2 Int Int))) (v_comptes_2 (set (tuple2 Int
  Int))) (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int
  Int))) (v_clts (set Int)) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cartez_7778 Int) (v_carte_1 Int) (v_carte_0 Int) (v_carte Int)
  (v_caissez_7777 Int) (v_caisse_2 Int) (v_caisse_1 Int) (v_caisse Int)
  (v_avance_1 Int) (v_avance Int) (v_K0 Int) (v_HS Int) (v_D_min Int)
  (v_D_max Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f24 v_tedaz_7777 v_teda_2 v_teda_1 v_teda_0 v_teda v_som_0 v_som v_rjt
  v_retraitsz_7777 v_retraits_2 v_retraits_1 v_retraits v_panne_dabz_7777
  v_panne_dab_2 v_panne_dab_1 v_panne_dab v_pan_dab_1 v_pan_dab_0
  v_ordrez_7777 v_ordre_2 v_ordre_1 v_ordre v_oo_0 v_oo v_interdits_1
  v_interdits v_etat_dabz_7777 v_etat_dab_2 v_etat_dab_1 v_etat_dab
  v_etat_autz_7778 v_etat_aut_1 v_etat_aut_0 v_etat_aut v_etat_1 v_etat_0
  v_datez_7777 v_date_1 v_date_0 v_date v_crt_int v_crt v_cpt_crt
  v_corbeillez_7777 v_corbeille_2 v_corbeille_1 v_corbeille v_comptesz_7777
  v_comptes_2 v_comptes_1 v_comptes v_clts v_clients_1 v_clients
  v_cartez_7778 v_carte_1 v_carte_0 v_carte v_caissez_7777 v_caisse_2
  v_caisse_1 v_caisse v_avance_1 v_avance v_K0 v_HS v_D_min v_D_max v_DATE
  v_CARTE) (<= 1 (- v_teda_2 1)))))

(declare-fun f25 (Int Int Int Int Int Int Int Int Int Int Int Int Bool Bool
  Bool Bool Bool Bool enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR (set Int) (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_DAB enum_ETAT_DAB enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_DAB enum_ETAT_DAB Int Int
  Int Int (set Int) Int (set (tuple2 Int Int)) Int Int Int Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set Int) (set Int) Int Int Int Int Int
  Int Int Int Int Int Int Int Int Int (set Int) (set Int)) Bool)

;; f25_def
  (assert
  (forall ((v_tedaz_7777 Int) (v_teda_2 Int) (v_teda_1 Int) (v_teda_0 Int)
  (v_teda Int) (v_som_0 Int) (v_som Int) (v_rjt Int) (v_retraitsz_7777 Int)
  (v_retraits_2 Int) (v_retraits_1 Int) (v_retraits Int)
  (v_panne_dabz_7777 Bool) (v_panne_dab_2 Bool) (v_panne_dab_1 Bool)
  (v_panne_dab Bool) (v_pan_dab_1 Bool) (v_pan_dab_0 Bool)
  (v_ordrez_7777 enum_ORDRE_OPERATEUR) (v_ordre_2 enum_ORDRE_OPERATEUR)
  (v_ordre_1 enum_ORDRE_OPERATEUR) (v_ordre enum_ORDRE_OPERATEUR)
  (v_oo_0 enum_ORDRE_OPERATEUR) (v_oo enum_ORDRE_OPERATEUR)
  (v_interdits_1 (set Int)) (v_interdits (set Int))
  (v_etat_dabz_7777 enum_ETAT_DAB) (v_etat_dab_2 enum_ETAT_DAB)
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_autz_7778 enum_ETAT_AUTOMATE) (v_etat_aut_1 enum_ETAT_AUTOMATE)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat_1 enum_ETAT_DAB) (v_etat_0 enum_ETAT_DAB) (v_datez_7777 Int)
  (v_date_1 Int) (v_date_0 Int) (v_date Int) (v_crt_int (set Int))
  (v_crt Int) (v_cpt_crt (set (tuple2 Int Int))) (v_corbeillez_7777 Int)
  (v_corbeille_2 Int) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptesz_7777 (set (tuple2 Int Int))) (v_comptes_2 (set (tuple2 Int
  Int))) (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int
  Int))) (v_clts (set Int)) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cartez_7778 Int) (v_carte_1 Int) (v_carte_0 Int) (v_carte Int)
  (v_caissez_7777 Int) (v_caisse_2 Int) (v_caisse_1 Int) (v_caisse Int)
  (v_avance_1 Int) (v_avance Int) (v_K0 Int) (v_HS Int) (v_D_min Int)
  (v_D_max Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f25 v_tedaz_7777 v_teda_2 v_teda_1 v_teda_0 v_teda v_som_0 v_som v_rjt
  v_retraitsz_7777 v_retraits_2 v_retraits_1 v_retraits v_panne_dabz_7777
  v_panne_dab_2 v_panne_dab_1 v_panne_dab v_pan_dab_1 v_pan_dab_0
  v_ordrez_7777 v_ordre_2 v_ordre_1 v_ordre v_oo_0 v_oo v_interdits_1
  v_interdits v_etat_dabz_7777 v_etat_dab_2 v_etat_dab_1 v_etat_dab
  v_etat_autz_7778 v_etat_aut_1 v_etat_aut_0 v_etat_aut v_etat_1 v_etat_0
  v_datez_7777 v_date_1 v_date_0 v_date v_crt_int v_crt v_cpt_crt
  v_corbeillez_7777 v_corbeille_2 v_corbeille_1 v_corbeille v_comptesz_7777
  v_comptes_2 v_comptes_1 v_comptes v_clts v_clients_1 v_clients
  v_cartez_7778 v_carte_1 v_carte_0 v_carte v_caissez_7777 v_caisse_2
  v_caisse_1 v_caisse v_avance_1 v_avance v_K0 v_HS v_D_min v_D_max v_DATE
  v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (=> (= v_oo E_Marche) (<= 2 v_teda_0))
  (=> (<= 2 v_teda_0) (= v_oo E_Marche))) (mem int (t2tb3 v_som)
  (t2tb2 integer))) (<= 0 v_som)) (<= v_som 2147483647)) (<= 901 v_som)) (mem
  (set1 int) (t2tb2 v_clts)
  (power int
  (diff int (t2tb2 v_CARTE)
  (union int (add int (t2tb3 v_K0) (empty int))
  (add int (t2tb3 v_HS) (empty int))))))) (mem (set1 (tuple21 int int))
  (t2tb14 v_cpt_crt) (infix_plmngt int int (t2tb2 v_clts) (t2tb2 nat))))
  (infix_eqeq int (dom int int (t2tb14 v_cpt_crt)) (t2tb2 v_clts))) (mem
  (set1 int) (t2tb2 v_crt_int) (power int (t2tb2 v_clts))))
  (=> (= v_etat_0 E_Hors_service)
  (or (= v_pan_dab_0 true) (<= (+ v_som 1) 900))))
  (=> (or (= v_pan_dab_0 true) (<= (+ v_som 1) 900))
  (= v_etat_0 E_Hors_service))) (mem int (t2tb3 v_teda_0) (t2tb2 integer)))
  (<= 0 v_teda_0)) (<= v_teda_0 2147483647)) (not (= v_teda_0 0))) (mem 
  int (t2tb3 v_teda_2) (t2tb2 integer))) (<= 0 v_teda_2))
  (= (+ (+ v_caisse_2 v_retraits_2) v_corbeille_2) v_som))
  (=> (= v_ordre_2 E_Marche) (<= 1 v_teda_2)))
  (=> (<= 1 v_teda_2) (= v_ordre_2 E_Marche)))
  (=> (= v_etat_dab_2 E_Hors_service)
  (or (= v_panne_dab_2 true) (<= (+ v_caisse_2 1) 900))))
  (=> (or (= v_panne_dab_2 true) (<= (+ v_caisse_2 1) 900))
  (= v_etat_dab_2 E_Hors_service))) (= v_ordre_2 E_Marche))
  (= v_etat_dab_2 E_En_service)) (mem int (t2tb3 v_date_0) (t2tb2 v_DATE)))
  (=> (= v_etat_1 E_Hors_service)
  (or (= v_pan_dab_1 true) (<= (+ (- v_caisse_2 v_som_0) 1) 900))))
  (=> (or (= v_pan_dab_1 true) (<= (+ (- v_caisse_2 v_som_0) 1) 900))
  (= v_etat_1 E_Hors_service))) (=> (= v_oo_0 E_Marche) (<= 2 v_teda_2)))
  (=> (<= 2 v_teda_2) (= v_oo_0 E_Marche))) (mem int (t2tb3 v_crt)
  (t2tb2 v_clts))) (mem int (t2tb3 v_som_0) (t2tb2 (mk 100 900)))) (mem 
  int (t2tb3 v_rjt)
  (union int (add int (t2tb3 0) (empty int))
  (add int (t2tb3 v_som_0) (empty int))))) (<= v_som_0 v_caisse_2))
  (<= v_som_0 (tb2t3 (apply int int (t2tb14 v_comptes_2) (t2tb3 v_crt)))))
  (<= 1 (- v_teda_2 1))))))

(declare-fun f27 (Int Int Int Int Int Int Int Int Int Int Int Int Bool Bool
  Bool Bool Bool Bool enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR (set Int) (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_DAB enum_ETAT_DAB enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_DAB enum_ETAT_DAB Int Int
  Int Int (set Int) Int (set (tuple2 Int Int)) Int Int Int Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set Int) (set Int) Int Int Int Int Int
  Int Int Int Int Int Int Int Int Int (set Int) (set Int)) Bool)

;; f27_def
  (assert
  (forall ((v_tedaz_7777 Int) (v_teda_2 Int) (v_teda_1 Int) (v_teda_0 Int)
  (v_teda Int) (v_som_0 Int) (v_som Int) (v_rjt Int) (v_retraitsz_7777 Int)
  (v_retraits_2 Int) (v_retraits_1 Int) (v_retraits Int)
  (v_panne_dabz_7777 Bool) (v_panne_dab_2 Bool) (v_panne_dab_1 Bool)
  (v_panne_dab Bool) (v_pan_dab_1 Bool) (v_pan_dab_0 Bool)
  (v_ordrez_7777 enum_ORDRE_OPERATEUR) (v_ordre_2 enum_ORDRE_OPERATEUR)
  (v_ordre_1 enum_ORDRE_OPERATEUR) (v_ordre enum_ORDRE_OPERATEUR)
  (v_oo_0 enum_ORDRE_OPERATEUR) (v_oo enum_ORDRE_OPERATEUR)
  (v_interdits_1 (set Int)) (v_interdits (set Int))
  (v_etat_dabz_7777 enum_ETAT_DAB) (v_etat_dab_2 enum_ETAT_DAB)
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_autz_7778 enum_ETAT_AUTOMATE) (v_etat_aut_1 enum_ETAT_AUTOMATE)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat_1 enum_ETAT_DAB) (v_etat_0 enum_ETAT_DAB) (v_datez_7777 Int)
  (v_date_1 Int) (v_date_0 Int) (v_date Int) (v_crt_int (set Int))
  (v_crt Int) (v_cpt_crt (set (tuple2 Int Int))) (v_corbeillez_7777 Int)
  (v_corbeille_2 Int) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptesz_7777 (set (tuple2 Int Int))) (v_comptes_2 (set (tuple2 Int
  Int))) (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int
  Int))) (v_clts (set Int)) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cartez_7778 Int) (v_carte_1 Int) (v_carte_0 Int) (v_carte Int)
  (v_caissez_7777 Int) (v_caisse_2 Int) (v_caisse_1 Int) (v_caisse Int)
  (v_avance_1 Int) (v_avance Int) (v_K0 Int) (v_HS Int) (v_D_min Int)
  (v_D_max Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f27 v_tedaz_7777 v_teda_2 v_teda_1 v_teda_0 v_teda v_som_0 v_som v_rjt
  v_retraitsz_7777 v_retraits_2 v_retraits_1 v_retraits v_panne_dabz_7777
  v_panne_dab_2 v_panne_dab_1 v_panne_dab v_pan_dab_1 v_pan_dab_0
  v_ordrez_7777 v_ordre_2 v_ordre_1 v_ordre v_oo_0 v_oo v_interdits_1
  v_interdits v_etat_dabz_7777 v_etat_dab_2 v_etat_dab_1 v_etat_dab
  v_etat_autz_7778 v_etat_aut_1 v_etat_aut_0 v_etat_aut v_etat_1 v_etat_0
  v_datez_7777 v_date_1 v_date_0 v_date v_crt_int v_crt v_cpt_crt
  v_corbeillez_7777 v_corbeille_2 v_corbeille_1 v_corbeille v_comptesz_7777
  v_comptes_2 v_comptes_1 v_comptes v_clts v_clients_1 v_clients
  v_cartez_7778 v_carte_1 v_carte_0 v_carte v_caissez_7777 v_caisse_2
  v_caisse_1 v_caisse v_avance_1 v_avance v_K0 v_HS v_D_min v_D_max v_DATE
  v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (=> (= v_oo E_Marche) (<= 2 v_teda_0))
  (=> (<= 2 v_teda_0) (= v_oo E_Marche))) (mem int (t2tb3 v_som)
  (t2tb2 integer))) (<= 0 v_som)) (<= v_som 2147483647)) (<= 901 v_som)) (mem
  (set1 int) (t2tb2 v_clts)
  (power int
  (diff int (t2tb2 v_CARTE)
  (union int (add int (t2tb3 v_K0) (empty int))
  (add int (t2tb3 v_HS) (empty int))))))) (mem (set1 (tuple21 int int))
  (t2tb14 v_cpt_crt) (infix_plmngt int int (t2tb2 v_clts) (t2tb2 nat))))
  (infix_eqeq int (dom int int (t2tb14 v_cpt_crt)) (t2tb2 v_clts))) (mem
  (set1 int) (t2tb2 v_crt_int) (power int (t2tb2 v_clts))))
  (=> (= v_etat_0 E_Hors_service)
  (or (= v_pan_dab_0 true) (<= (+ v_som 1) 900))))
  (=> (or (= v_pan_dab_0 true) (<= (+ v_som 1) 900))
  (= v_etat_0 E_Hors_service))) (mem int (t2tb3 v_teda_0) (t2tb2 integer)))
  (<= 0 v_teda_0)) (<= v_teda_0 2147483647)) (not (= v_teda_0 0))) (mem 
  int (t2tb3 v_teda_2) (t2tb2 integer))) (<= 0 v_teda_2))
  (= (+ (+ v_caisse_2 v_retraits_2) v_corbeille_2) v_som))
  (=> (= v_ordre_2 E_Marche) (<= 1 v_teda_2)))
  (=> (<= 1 v_teda_2) (= v_ordre_2 E_Marche)))
  (=> (= v_etat_dab_2 E_Hors_service)
  (or (= v_panne_dab_2 true) (<= (+ v_caisse_2 1) 900))))
  (=> (or (= v_panne_dab_2 true) (<= (+ v_caisse_2 1) 900))
  (= v_etat_dab_2 E_Hors_service))) (= v_ordre_2 E_Marche))
  (= v_etat_dab_2 E_En_service)) (mem int (t2tb3 v_date_0) (t2tb2 v_DATE)))
  (=> (= v_etat_1 E_Hors_service)
  (or (= v_pan_dab_1 true) (<= (+ v_caisse_2 1) 900))))
  (=> (or (= v_pan_dab_1 true) (<= (+ v_caisse_2 1) 900))
  (= v_etat_1 E_Hors_service))) (=> (= v_oo_0 E_Marche) (<= 2 v_teda_2)))
  (=> (<= 2 v_teda_2) (= v_oo_0 E_Marche))) (mem int (t2tb3 v_carte_0)
  (t2tb2 v_CARTE))))))

(declare-fun f28 (Int Int Int Int Int Int Int Int Int Int Int Int Bool Bool
  Bool Bool Bool Bool enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR (set Int) (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_DAB enum_ETAT_DAB enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_DAB enum_ETAT_DAB Int Int
  Int Int (set Int) Int (set (tuple2 Int Int)) Int Int Int Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set Int) (set Int) Int Int Int Int Int
  Int Int Int Int Int Int Int Int Int (set Int) (set Int)) Bool)

;; f28_def
  (assert
  (forall ((v_tedaz_7777 Int) (v_teda_2 Int) (v_teda_1 Int) (v_teda_0 Int)
  (v_teda Int) (v_som_0 Int) (v_som Int) (v_rjt Int) (v_retraitsz_7777 Int)
  (v_retraits_2 Int) (v_retraits_1 Int) (v_retraits Int)
  (v_panne_dabz_7777 Bool) (v_panne_dab_2 Bool) (v_panne_dab_1 Bool)
  (v_panne_dab Bool) (v_pan_dab_1 Bool) (v_pan_dab_0 Bool)
  (v_ordrez_7777 enum_ORDRE_OPERATEUR) (v_ordre_2 enum_ORDRE_OPERATEUR)
  (v_ordre_1 enum_ORDRE_OPERATEUR) (v_ordre enum_ORDRE_OPERATEUR)
  (v_oo_0 enum_ORDRE_OPERATEUR) (v_oo enum_ORDRE_OPERATEUR)
  (v_interdits_1 (set Int)) (v_interdits (set Int))
  (v_etat_dabz_7777 enum_ETAT_DAB) (v_etat_dab_2 enum_ETAT_DAB)
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_autz_7778 enum_ETAT_AUTOMATE) (v_etat_aut_1 enum_ETAT_AUTOMATE)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat_1 enum_ETAT_DAB) (v_etat_0 enum_ETAT_DAB) (v_datez_7777 Int)
  (v_date_1 Int) (v_date_0 Int) (v_date Int) (v_crt_int (set Int))
  (v_crt Int) (v_cpt_crt (set (tuple2 Int Int))) (v_corbeillez_7777 Int)
  (v_corbeille_2 Int) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptesz_7777 (set (tuple2 Int Int))) (v_comptes_2 (set (tuple2 Int
  Int))) (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int
  Int))) (v_clts (set Int)) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cartez_7778 Int) (v_carte_1 Int) (v_carte_0 Int) (v_carte Int)
  (v_caissez_7777 Int) (v_caisse_2 Int) (v_caisse_1 Int) (v_caisse Int)
  (v_avance_1 Int) (v_avance Int) (v_K0 Int) (v_HS Int) (v_D_min Int)
  (v_D_max Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f28 v_tedaz_7777 v_teda_2 v_teda_1 v_teda_0 v_teda v_som_0 v_som v_rjt
  v_retraitsz_7777 v_retraits_2 v_retraits_1 v_retraits v_panne_dabz_7777
  v_panne_dab_2 v_panne_dab_1 v_panne_dab v_pan_dab_1 v_pan_dab_0
  v_ordrez_7777 v_ordre_2 v_ordre_1 v_ordre v_oo_0 v_oo v_interdits_1
  v_interdits v_etat_dabz_7777 v_etat_dab_2 v_etat_dab_1 v_etat_dab
  v_etat_autz_7778 v_etat_aut_1 v_etat_aut_0 v_etat_aut v_etat_1 v_etat_0
  v_datez_7777 v_date_1 v_date_0 v_date v_crt_int v_crt v_cpt_crt
  v_corbeillez_7777 v_corbeille_2 v_corbeille_1 v_corbeille v_comptesz_7777
  v_comptes_2 v_comptes_1 v_comptes v_clts v_clients_1 v_clients
  v_cartez_7778 v_carte_1 v_carte_0 v_carte v_caissez_7777 v_caisse_2
  v_caisse_1 v_caisse v_avance_1 v_avance v_K0 v_HS v_D_min v_D_max v_DATE
  v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (=> (= v_oo E_Marche) (<= 2 v_teda_0))
  (=> (<= 2 v_teda_0) (= v_oo E_Marche))) (mem int (t2tb3 v_som)
  (t2tb2 integer))) (<= 0 v_som)) (<= v_som 2147483647)) (<= 901 v_som)) (mem
  (set1 int) (t2tb2 v_clts)
  (power int
  (diff int (t2tb2 v_CARTE)
  (union int (add int (t2tb3 v_K0) (empty int))
  (add int (t2tb3 v_HS) (empty int))))))) (mem (set1 (tuple21 int int))
  (t2tb14 v_cpt_crt) (infix_plmngt int int (t2tb2 v_clts) (t2tb2 nat))))
  (infix_eqeq int (dom int int (t2tb14 v_cpt_crt)) (t2tb2 v_clts))) (mem
  (set1 int) (t2tb2 v_crt_int) (power int (t2tb2 v_clts))))
  (=> (= v_etat_0 E_Hors_service)
  (or (= v_pan_dab_0 true) (<= (+ v_som 1) 900))))
  (=> (or (= v_pan_dab_0 true) (<= (+ v_som 1) 900))
  (= v_etat_0 E_Hors_service))) (mem int (t2tb3 v_teda_0) (t2tb2 integer)))
  (<= 0 v_teda_0)) (<= v_teda_0 2147483647)) (not (= v_teda_0 0))) (mem 
  int (t2tb3 v_teda_2) (t2tb2 integer))) (<= 0 v_teda_2))
  (= (+ (+ v_caisse_2 v_retraits_2) v_corbeille_2) v_som))
  (=> (= v_ordre_2 E_Marche) (<= 1 v_teda_2)))
  (=> (<= 1 v_teda_2) (= v_ordre_2 E_Marche)))
  (=> (= v_etat_dab_2 E_Hors_service)
  (or (= v_panne_dab_2 true) (<= (+ v_caisse_2 1) 900))))
  (=> (or (= v_panne_dab_2 true) (<= (+ v_caisse_2 1) 900))
  (= v_etat_dab_2 E_Hors_service))) (= v_ordre_2 E_Marche))
  (= v_etat_dab_2 E_En_service)) (mem int (t2tb3 v_date_0) (t2tb2 v_DATE)))
  (=> (= v_etat_1 E_Hors_service)
  (or (= v_pan_dab_1 true) (<= (+ v_caisse_2 1) 900))))
  (=> (or (= v_pan_dab_1 true) (<= (+ v_caisse_2 1) 900))
  (= v_etat_1 E_Hors_service))) (=> (= v_oo_0 E_Marche) (<= 2 v_teda_2)))
  (=> (<= 2 v_teda_2) (= v_oo_0 E_Marche))) (mem int (t2tb3 v_carte_0)
  (t2tb2 v_CARTE))) (= v_oo_0 E_Marche)))))

(declare-fun f29 (Int Int Int Int Int Int Int Int Int Int Int Int Bool Bool
  Bool Bool Bool Bool enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR (set Int) (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_DAB enum_ETAT_DAB enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_DAB enum_ETAT_DAB Int Int
  Int Int (set Int) Int (set (tuple2 Int Int)) Int Int Int Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set Int) (set Int) Int Int Int Int Int
  Int Int Int Int Int Int Int Int Int (set Int) (set Int)) Bool)

;; f29_def
  (assert
  (forall ((v_tedaz_7777 Int) (v_teda_2 Int) (v_teda_1 Int) (v_teda_0 Int)
  (v_teda Int) (v_som_0 Int) (v_som Int) (v_rjt Int) (v_retraitsz_7777 Int)
  (v_retraits_2 Int) (v_retraits_1 Int) (v_retraits Int)
  (v_panne_dabz_7777 Bool) (v_panne_dab_2 Bool) (v_panne_dab_1 Bool)
  (v_panne_dab Bool) (v_pan_dab_1 Bool) (v_pan_dab_0 Bool)
  (v_ordrez_7777 enum_ORDRE_OPERATEUR) (v_ordre_2 enum_ORDRE_OPERATEUR)
  (v_ordre_1 enum_ORDRE_OPERATEUR) (v_ordre enum_ORDRE_OPERATEUR)
  (v_oo_0 enum_ORDRE_OPERATEUR) (v_oo enum_ORDRE_OPERATEUR)
  (v_interdits_1 (set Int)) (v_interdits (set Int))
  (v_etat_dabz_7777 enum_ETAT_DAB) (v_etat_dab_2 enum_ETAT_DAB)
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_autz_7778 enum_ETAT_AUTOMATE) (v_etat_aut_1 enum_ETAT_AUTOMATE)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat_1 enum_ETAT_DAB) (v_etat_0 enum_ETAT_DAB) (v_datez_7777 Int)
  (v_date_1 Int) (v_date_0 Int) (v_date Int) (v_crt_int (set Int))
  (v_crt Int) (v_cpt_crt (set (tuple2 Int Int))) (v_corbeillez_7777 Int)
  (v_corbeille_2 Int) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptesz_7777 (set (tuple2 Int Int))) (v_comptes_2 (set (tuple2 Int
  Int))) (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int
  Int))) (v_clts (set Int)) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cartez_7778 Int) (v_carte_1 Int) (v_carte_0 Int) (v_carte Int)
  (v_caissez_7777 Int) (v_caisse_2 Int) (v_caisse_1 Int) (v_caisse Int)
  (v_avance_1 Int) (v_avance Int) (v_K0 Int) (v_HS Int) (v_D_min Int)
  (v_D_max Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f29 v_tedaz_7777 v_teda_2 v_teda_1 v_teda_0 v_teda v_som_0 v_som v_rjt
  v_retraitsz_7777 v_retraits_2 v_retraits_1 v_retraits v_panne_dabz_7777
  v_panne_dab_2 v_panne_dab_1 v_panne_dab v_pan_dab_1 v_pan_dab_0
  v_ordrez_7777 v_ordre_2 v_ordre_1 v_ordre v_oo_0 v_oo v_interdits_1
  v_interdits v_etat_dabz_7777 v_etat_dab_2 v_etat_dab_1 v_etat_dab
  v_etat_autz_7778 v_etat_aut_1 v_etat_aut_0 v_etat_aut v_etat_1 v_etat_0
  v_datez_7777 v_date_1 v_date_0 v_date v_crt_int v_crt v_cpt_crt
  v_corbeillez_7777 v_corbeille_2 v_corbeille_1 v_corbeille v_comptesz_7777
  v_comptes_2 v_comptes_1 v_comptes v_clts v_clients_1 v_clients
  v_cartez_7778 v_carte_1 v_carte_0 v_carte v_caissez_7777 v_caisse_2
  v_caisse_1 v_caisse v_avance_1 v_avance v_K0 v_HS v_D_min v_D_max v_DATE
  v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (=> (= v_oo E_Marche) (<= 2 v_teda_0))
  (=> (<= 2 v_teda_0) (= v_oo E_Marche))) (mem int (t2tb3 v_som)
  (t2tb2 integer))) (<= 0 v_som)) (<= v_som 2147483647)) (<= 901 v_som)) (mem
  (set1 int) (t2tb2 v_clts)
  (power int
  (diff int (t2tb2 v_CARTE)
  (union int (add int (t2tb3 v_K0) (empty int))
  (add int (t2tb3 v_HS) (empty int))))))) (mem (set1 (tuple21 int int))
  (t2tb14 v_cpt_crt) (infix_plmngt int int (t2tb2 v_clts) (t2tb2 nat))))
  (infix_eqeq int (dom int int (t2tb14 v_cpt_crt)) (t2tb2 v_clts))) (mem
  (set1 int) (t2tb2 v_crt_int) (power int (t2tb2 v_clts))))
  (=> (= v_etat_0 E_Hors_service)
  (or (= v_pan_dab_0 true) (<= (+ v_som 1) 900))))
  (=> (or (= v_pan_dab_0 true) (<= (+ v_som 1) 900))
  (= v_etat_0 E_Hors_service))) (mem int (t2tb3 v_teda_0) (t2tb2 integer)))
  (<= 0 v_teda_0)) (<= v_teda_0 2147483647)) (not (= v_teda_0 0))) (mem 
  int (t2tb3 v_teda_2) (t2tb2 integer))) (<= 0 v_teda_2))
  (= (+ (+ v_caisse_2 v_retraits_2) v_corbeille_2) v_som))
  (=> (= v_ordre_2 E_Marche) (<= 1 v_teda_2)))
  (=> (<= 1 v_teda_2) (= v_ordre_2 E_Marche)))
  (=> (= v_etat_dab_2 E_Hors_service)
  (or (= v_panne_dab_2 true) (<= (+ v_caisse_2 1) 900))))
  (=> (or (= v_panne_dab_2 true) (<= (+ v_caisse_2 1) 900))
  (= v_etat_dab_2 E_Hors_service))) (= v_ordre_2 E_Marche))
  (= v_etat_dab_2 E_En_service)) (mem int (t2tb3 v_date_0) (t2tb2 v_DATE)))
  (=> (= v_etat_1 E_Hors_service)
  (or (= v_pan_dab_1 true) (<= (+ v_caisse_2 1) 900))))
  (=> (or (= v_pan_dab_1 true) (<= (+ v_caisse_2 1) 900))
  (= v_etat_1 E_Hors_service))) (=> (= v_oo_0 E_Marche) (<= 2 v_teda_2)))
  (=> (<= 2 v_teda_2) (= v_oo_0 E_Marche))) (mem int (t2tb3 v_carte_0)
  (t2tb2 v_CARTE))) (<= 1 (- v_teda_2 1))))))

(declare-fun f30 (Int Int Int Int Int Int Int Int Int Int Int Int Bool Bool
  Bool Bool Bool Bool enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR (set Int) (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_DAB enum_ETAT_DAB enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_DAB enum_ETAT_DAB Int Int
  Int Int (set Int) Int (set (tuple2 Int Int)) Int Int Int Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set Int) (set Int) Int Int Int Int Int
  Int Int Int Int Int Int Int Int Int (set Int) (set Int)) Bool)

;; f30_def
  (assert
  (forall ((v_tedaz_7777 Int) (v_teda_2 Int) (v_teda_1 Int) (v_teda_0 Int)
  (v_teda Int) (v_som_0 Int) (v_som Int) (v_rjt Int) (v_retraitsz_7777 Int)
  (v_retraits_2 Int) (v_retraits_1 Int) (v_retraits Int)
  (v_panne_dabz_7777 Bool) (v_panne_dab_2 Bool) (v_panne_dab_1 Bool)
  (v_panne_dab Bool) (v_pan_dab_1 Bool) (v_pan_dab_0 Bool)
  (v_ordrez_7777 enum_ORDRE_OPERATEUR) (v_ordre_2 enum_ORDRE_OPERATEUR)
  (v_ordre_1 enum_ORDRE_OPERATEUR) (v_ordre enum_ORDRE_OPERATEUR)
  (v_oo_0 enum_ORDRE_OPERATEUR) (v_oo enum_ORDRE_OPERATEUR)
  (v_interdits_1 (set Int)) (v_interdits (set Int))
  (v_etat_dabz_7777 enum_ETAT_DAB) (v_etat_dab_2 enum_ETAT_DAB)
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_autz_7778 enum_ETAT_AUTOMATE) (v_etat_aut_1 enum_ETAT_AUTOMATE)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat_1 enum_ETAT_DAB) (v_etat_0 enum_ETAT_DAB) (v_datez_7777 Int)
  (v_date_1 Int) (v_date_0 Int) (v_date Int) (v_crt_int (set Int))
  (v_crt Int) (v_cpt_crt (set (tuple2 Int Int))) (v_corbeillez_7777 Int)
  (v_corbeille_2 Int) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptesz_7777 (set (tuple2 Int Int))) (v_comptes_2 (set (tuple2 Int
  Int))) (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int
  Int))) (v_clts (set Int)) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cartez_7778 Int) (v_carte_1 Int) (v_carte_0 Int) (v_carte Int)
  (v_caissez_7777 Int) (v_caisse_2 Int) (v_caisse_1 Int) (v_caisse Int)
  (v_avance_1 Int) (v_avance Int) (v_K0 Int) (v_HS Int) (v_D_min Int)
  (v_D_max Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f30 v_tedaz_7777 v_teda_2 v_teda_1 v_teda_0 v_teda v_som_0 v_som v_rjt
  v_retraitsz_7777 v_retraits_2 v_retraits_1 v_retraits v_panne_dabz_7777
  v_panne_dab_2 v_panne_dab_1 v_panne_dab v_pan_dab_1 v_pan_dab_0
  v_ordrez_7777 v_ordre_2 v_ordre_1 v_ordre v_oo_0 v_oo v_interdits_1
  v_interdits v_etat_dabz_7777 v_etat_dab_2 v_etat_dab_1 v_etat_dab
  v_etat_autz_7778 v_etat_aut_1 v_etat_aut_0 v_etat_aut v_etat_1 v_etat_0
  v_datez_7777 v_date_1 v_date_0 v_date v_crt_int v_crt v_cpt_crt
  v_corbeillez_7777 v_corbeille_2 v_corbeille_1 v_corbeille v_comptesz_7777
  v_comptes_2 v_comptes_1 v_comptes v_clts v_clients_1 v_clients
  v_cartez_7778 v_carte_1 v_carte_0 v_carte v_caissez_7777 v_caisse_2
  v_caisse_1 v_caisse v_avance_1 v_avance v_K0 v_HS v_D_min v_D_max v_DATE
  v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (=> (= v_oo E_Marche) (<= 2 v_teda_0))
  (=> (<= 2 v_teda_0) (= v_oo E_Marche))) (mem int (t2tb3 v_som)
  (t2tb2 integer))) (<= 0 v_som)) (<= v_som 2147483647)) (<= 901 v_som)) (mem
  (set1 int) (t2tb2 v_clts)
  (power int
  (diff int (t2tb2 v_CARTE)
  (union int (add int (t2tb3 v_K0) (empty int))
  (add int (t2tb3 v_HS) (empty int))))))) (mem (set1 (tuple21 int int))
  (t2tb14 v_cpt_crt) (infix_plmngt int int (t2tb2 v_clts) (t2tb2 nat))))
  (infix_eqeq int (dom int int (t2tb14 v_cpt_crt)) (t2tb2 v_clts))) (mem
  (set1 int) (t2tb2 v_crt_int) (power int (t2tb2 v_clts))))
  (=> (= v_etat_0 E_Hors_service)
  (or (= v_pan_dab_0 true) (<= (+ v_som 1) 900))))
  (=> (or (= v_pan_dab_0 true) (<= (+ v_som 1) 900))
  (= v_etat_0 E_Hors_service))) (mem int (t2tb3 v_teda_0) (t2tb2 integer)))
  (<= 0 v_teda_0)) (<= v_teda_0 2147483647)) (not (= v_teda_0 0))) (mem 
  int (t2tb3 v_teda_2) (t2tb2 integer))) (<= 0 v_teda_2))
  (= (+ (+ v_caisse_2 v_retraits_2) v_corbeille_2) v_som))
  (=> (= v_ordre_2 E_Marche) (<= 1 v_teda_2)))
  (=> (<= 1 v_teda_2) (= v_ordre_2 E_Marche)))
  (=> (= v_etat_dab_2 E_Hors_service)
  (or (= v_panne_dab_2 true) (<= (+ v_caisse_2 1) 900))))
  (=> (or (= v_panne_dab_2 true) (<= (+ v_caisse_2 1) 900))
  (= v_etat_dab_2 E_Hors_service))) (= v_ordre_2 E_Marche))
  (= v_etat_dab_2 E_En_service)) (mem int (t2tb3 v_date_0) (t2tb2 v_DATE)))
  (=> (= v_etat_1 E_Hors_service)
  (or (= v_pan_dab_1 true) (<= (+ v_caisse_2 1) 900))))
  (=> (or (= v_pan_dab_1 true) (<= (+ v_caisse_2 1) 900))
  (= v_etat_1 E_Hors_service))) (=> (= v_oo_0 E_Marche) (<= 2 v_teda_2)))
  (=> (<= 2 v_teda_2) (= v_oo_0 E_Marche))))))

(declare-fun f31 (Int Int Int Int Int Int Int Int Int Int Int Int Bool Bool
  Bool Bool Bool Bool enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR (set Int) (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_DAB enum_ETAT_DAB enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_DAB enum_ETAT_DAB Int Int
  Int Int (set Int) Int (set (tuple2 Int Int)) Int Int Int Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set Int) (set Int) Int Int Int Int Int
  Int Int Int Int Int Int Int Int Int (set Int) (set Int)) Bool)

;; f31_def
  (assert
  (forall ((v_tedaz_7777 Int) (v_teda_2 Int) (v_teda_1 Int) (v_teda_0 Int)
  (v_teda Int) (v_som_0 Int) (v_som Int) (v_rjt Int) (v_retraitsz_7777 Int)
  (v_retraits_2 Int) (v_retraits_1 Int) (v_retraits Int)
  (v_panne_dabz_7777 Bool) (v_panne_dab_2 Bool) (v_panne_dab_1 Bool)
  (v_panne_dab Bool) (v_pan_dab_1 Bool) (v_pan_dab_0 Bool)
  (v_ordrez_7777 enum_ORDRE_OPERATEUR) (v_ordre_2 enum_ORDRE_OPERATEUR)
  (v_ordre_1 enum_ORDRE_OPERATEUR) (v_ordre enum_ORDRE_OPERATEUR)
  (v_oo_0 enum_ORDRE_OPERATEUR) (v_oo enum_ORDRE_OPERATEUR)
  (v_interdits_1 (set Int)) (v_interdits (set Int))
  (v_etat_dabz_7777 enum_ETAT_DAB) (v_etat_dab_2 enum_ETAT_DAB)
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_autz_7778 enum_ETAT_AUTOMATE) (v_etat_aut_1 enum_ETAT_AUTOMATE)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat_1 enum_ETAT_DAB) (v_etat_0 enum_ETAT_DAB) (v_datez_7777 Int)
  (v_date_1 Int) (v_date_0 Int) (v_date Int) (v_crt_int (set Int))
  (v_crt Int) (v_cpt_crt (set (tuple2 Int Int))) (v_corbeillez_7777 Int)
  (v_corbeille_2 Int) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptesz_7777 (set (tuple2 Int Int))) (v_comptes_2 (set (tuple2 Int
  Int))) (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int
  Int))) (v_clts (set Int)) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cartez_7778 Int) (v_carte_1 Int) (v_carte_0 Int) (v_carte Int)
  (v_caissez_7777 Int) (v_caisse_2 Int) (v_caisse_1 Int) (v_caisse Int)
  (v_avance_1 Int) (v_avance Int) (v_K0 Int) (v_HS Int) (v_D_min Int)
  (v_D_max Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f31 v_tedaz_7777 v_teda_2 v_teda_1 v_teda_0 v_teda v_som_0 v_som v_rjt
  v_retraitsz_7777 v_retraits_2 v_retraits_1 v_retraits v_panne_dabz_7777
  v_panne_dab_2 v_panne_dab_1 v_panne_dab v_pan_dab_1 v_pan_dab_0
  v_ordrez_7777 v_ordre_2 v_ordre_1 v_ordre v_oo_0 v_oo v_interdits_1
  v_interdits v_etat_dabz_7777 v_etat_dab_2 v_etat_dab_1 v_etat_dab
  v_etat_autz_7778 v_etat_aut_1 v_etat_aut_0 v_etat_aut v_etat_1 v_etat_0
  v_datez_7777 v_date_1 v_date_0 v_date v_crt_int v_crt v_cpt_crt
  v_corbeillez_7777 v_corbeille_2 v_corbeille_1 v_corbeille v_comptesz_7777
  v_comptes_2 v_comptes_1 v_comptes v_clts v_clients_1 v_clients
  v_cartez_7778 v_carte_1 v_carte_0 v_carte v_caissez_7777 v_caisse_2
  v_caisse_1 v_caisse v_avance_1 v_avance v_K0 v_HS v_D_min v_D_max v_DATE
  v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (=> (= v_oo E_Marche) (<= 2 v_teda_0))
  (=> (<= 2 v_teda_0) (= v_oo E_Marche))) (mem int (t2tb3 v_som)
  (t2tb2 integer))) (<= 0 v_som)) (<= v_som 2147483647)) (<= 901 v_som)) (mem
  (set1 int) (t2tb2 v_clts)
  (power int
  (diff int (t2tb2 v_CARTE)
  (union int (add int (t2tb3 v_K0) (empty int))
  (add int (t2tb3 v_HS) (empty int))))))) (mem (set1 (tuple21 int int))
  (t2tb14 v_cpt_crt) (infix_plmngt int int (t2tb2 v_clts) (t2tb2 nat))))
  (infix_eqeq int (dom int int (t2tb14 v_cpt_crt)) (t2tb2 v_clts))) (mem
  (set1 int) (t2tb2 v_crt_int) (power int (t2tb2 v_clts))))
  (=> (= v_etat_0 E_Hors_service)
  (or (= v_pan_dab_0 true) (<= (+ v_som 1) 900))))
  (=> (or (= v_pan_dab_0 true) (<= (+ v_som 1) 900))
  (= v_etat_0 E_Hors_service))) (mem int (t2tb3 v_teda_0) (t2tb2 integer)))
  (<= 0 v_teda_0)) (<= v_teda_0 2147483647)) (not (= v_teda_0 0))) (mem 
  int (t2tb3 v_teda_2) (t2tb2 integer))) (<= 0 v_teda_2))
  (= (+ (+ v_caisse_2 v_retraits_2) v_corbeille_2) v_som))
  (=> (= v_ordre_2 E_Marche) (<= 1 v_teda_2)))
  (=> (<= 1 v_teda_2) (= v_ordre_2 E_Marche)))
  (=> (= v_etat_dab_2 E_Hors_service)
  (or (= v_panne_dab_2 true) (<= (+ v_caisse_2 1) 900))))
  (=> (or (= v_panne_dab_2 true) (<= (+ v_caisse_2 1) 900))
  (= v_etat_dab_2 E_Hors_service))) (= v_ordre_2 E_Marche))
  (= v_etat_dab_2 E_En_service)) (mem int (t2tb3 v_date_0) (t2tb2 v_DATE)))
  (=> (= v_etat_1 E_Hors_service)
  (or (= v_pan_dab_1 true) (<= (+ v_caisse_2 1) 900))))
  (=> (or (= v_pan_dab_1 true) (<= (+ v_caisse_2 1) 900))
  (= v_etat_1 E_Hors_service))) (=> (= v_oo_0 E_Marche) (<= 2 v_teda_2)))
  (=> (<= 2 v_teda_2) (= v_oo_0 E_Marche))) (= v_oo_0 E_Marche)))))

(declare-fun f32 (Int Int Int Int Int Int Int Int Int Int Int Int Bool Bool
  Bool Bool Bool Bool enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR (set Int) (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_DAB enum_ETAT_DAB enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_DAB enum_ETAT_DAB Int Int
  Int Int (set Int) Int (set (tuple2 Int Int)) Int Int Int Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set Int) (set Int) Int Int Int Int Int
  Int Int Int Int Int Int Int Int Int (set Int) (set Int)) Bool)

;; f32_def
  (assert
  (forall ((v_tedaz_7777 Int) (v_teda_2 Int) (v_teda_1 Int) (v_teda_0 Int)
  (v_teda Int) (v_som_0 Int) (v_som Int) (v_rjt Int) (v_retraitsz_7777 Int)
  (v_retraits_2 Int) (v_retraits_1 Int) (v_retraits Int)
  (v_panne_dabz_7777 Bool) (v_panne_dab_2 Bool) (v_panne_dab_1 Bool)
  (v_panne_dab Bool) (v_pan_dab_1 Bool) (v_pan_dab_0 Bool)
  (v_ordrez_7777 enum_ORDRE_OPERATEUR) (v_ordre_2 enum_ORDRE_OPERATEUR)
  (v_ordre_1 enum_ORDRE_OPERATEUR) (v_ordre enum_ORDRE_OPERATEUR)
  (v_oo_0 enum_ORDRE_OPERATEUR) (v_oo enum_ORDRE_OPERATEUR)
  (v_interdits_1 (set Int)) (v_interdits (set Int))
  (v_etat_dabz_7777 enum_ETAT_DAB) (v_etat_dab_2 enum_ETAT_DAB)
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_autz_7778 enum_ETAT_AUTOMATE) (v_etat_aut_1 enum_ETAT_AUTOMATE)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat_1 enum_ETAT_DAB) (v_etat_0 enum_ETAT_DAB) (v_datez_7777 Int)
  (v_date_1 Int) (v_date_0 Int) (v_date Int) (v_crt_int (set Int))
  (v_crt Int) (v_cpt_crt (set (tuple2 Int Int))) (v_corbeillez_7777 Int)
  (v_corbeille_2 Int) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptesz_7777 (set (tuple2 Int Int))) (v_comptes_2 (set (tuple2 Int
  Int))) (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int
  Int))) (v_clts (set Int)) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cartez_7778 Int) (v_carte_1 Int) (v_carte_0 Int) (v_carte Int)
  (v_caissez_7777 Int) (v_caisse_2 Int) (v_caisse_1 Int) (v_caisse Int)
  (v_avance_1 Int) (v_avance Int) (v_K0 Int) (v_HS Int) (v_D_min Int)
  (v_D_max Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f32 v_tedaz_7777 v_teda_2 v_teda_1 v_teda_0 v_teda v_som_0 v_som v_rjt
  v_retraitsz_7777 v_retraits_2 v_retraits_1 v_retraits v_panne_dabz_7777
  v_panne_dab_2 v_panne_dab_1 v_panne_dab v_pan_dab_1 v_pan_dab_0
  v_ordrez_7777 v_ordre_2 v_ordre_1 v_ordre v_oo_0 v_oo v_interdits_1
  v_interdits v_etat_dabz_7777 v_etat_dab_2 v_etat_dab_1 v_etat_dab
  v_etat_autz_7778 v_etat_aut_1 v_etat_aut_0 v_etat_aut v_etat_1 v_etat_0
  v_datez_7777 v_date_1 v_date_0 v_date v_crt_int v_crt v_cpt_crt
  v_corbeillez_7777 v_corbeille_2 v_corbeille_1 v_corbeille v_comptesz_7777
  v_comptes_2 v_comptes_1 v_comptes v_clts v_clients_1 v_clients
  v_cartez_7778 v_carte_1 v_carte_0 v_carte v_caissez_7777 v_caisse_2
  v_caisse_1 v_caisse v_avance_1 v_avance v_K0 v_HS v_D_min v_D_max v_DATE
  v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (=> (= v_oo E_Marche) (<= 2 v_teda_0))
  (=> (<= 2 v_teda_0) (= v_oo E_Marche))) (mem int (t2tb3 v_som)
  (t2tb2 integer))) (<= 0 v_som)) (<= v_som 2147483647)) (<= 901 v_som)) (mem
  (set1 int) (t2tb2 v_clts)
  (power int
  (diff int (t2tb2 v_CARTE)
  (union int (add int (t2tb3 v_K0) (empty int))
  (add int (t2tb3 v_HS) (empty int))))))) (mem (set1 (tuple21 int int))
  (t2tb14 v_cpt_crt) (infix_plmngt int int (t2tb2 v_clts) (t2tb2 nat))))
  (infix_eqeq int (dom int int (t2tb14 v_cpt_crt)) (t2tb2 v_clts))) (mem
  (set1 int) (t2tb2 v_crt_int) (power int (t2tb2 v_clts))))
  (=> (= v_etat_0 E_Hors_service)
  (or (= v_pan_dab_0 true) (<= (+ v_som 1) 900))))
  (=> (or (= v_pan_dab_0 true) (<= (+ v_som 1) 900))
  (= v_etat_0 E_Hors_service))) (mem int (t2tb3 v_teda_0) (t2tb2 integer)))
  (<= 0 v_teda_0)) (<= v_teda_0 2147483647)) (not (= v_teda_0 0))) (mem 
  int (t2tb3 v_teda_2) (t2tb2 integer))) (<= 0 v_teda_2))
  (= (+ (+ v_caisse_2 v_retraits_2) v_corbeille_2) v_som))
  (=> (= v_ordre_2 E_Marche) (<= 1 v_teda_2)))
  (=> (<= 1 v_teda_2) (= v_ordre_2 E_Marche)))
  (=> (= v_etat_dab_2 E_Hors_service)
  (or (= v_panne_dab_2 true) (<= (+ v_caisse_2 1) 900))))
  (=> (or (= v_panne_dab_2 true) (<= (+ v_caisse_2 1) 900))
  (= v_etat_dab_2 E_Hors_service))) (= v_ordre_2 E_Marche))
  (= v_etat_dab_2 E_En_service)) (mem int (t2tb3 v_date_0) (t2tb2 v_DATE)))
  (=> (= v_etat_1 E_Hors_service)
  (or (= v_pan_dab_1 true) (<= (+ v_caisse_2 1) 900))))
  (=> (or (= v_pan_dab_1 true) (<= (+ v_caisse_2 1) 900))
  (= v_etat_1 E_Hors_service))) (=> (= v_oo_0 E_Marche) (<= 2 v_teda_2)))
  (=> (<= 2 v_teda_2) (= v_oo_0 E_Marche))) (<= 1 (- v_teda_2 1))))))

(declare-fun f33 (Int Int Int Int Int Int Int Int Int Int Int Int Bool Bool
  Bool Bool Bool Bool enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR (set Int) (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_DAB enum_ETAT_DAB enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_DAB enum_ETAT_DAB Int Int
  Int Int (set Int) Int (set (tuple2 Int Int)) Int Int Int Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set Int) (set Int) Int Int Int Int Int
  Int Int Int Int Int Int Int Int Int (set Int) (set Int)) Bool)

;; f33_def
  (assert
  (forall ((v_tedaz_7777 Int) (v_teda_2 Int) (v_teda_1 Int) (v_teda_0 Int)
  (v_teda Int) (v_som_0 Int) (v_som Int) (v_rjt Int) (v_retraitsz_7777 Int)
  (v_retraits_2 Int) (v_retraits_1 Int) (v_retraits Int)
  (v_panne_dabz_7777 Bool) (v_panne_dab_2 Bool) (v_panne_dab_1 Bool)
  (v_panne_dab Bool) (v_pan_dab_1 Bool) (v_pan_dab_0 Bool)
  (v_ordrez_7777 enum_ORDRE_OPERATEUR) (v_ordre_2 enum_ORDRE_OPERATEUR)
  (v_ordre_1 enum_ORDRE_OPERATEUR) (v_ordre enum_ORDRE_OPERATEUR)
  (v_oo_0 enum_ORDRE_OPERATEUR) (v_oo enum_ORDRE_OPERATEUR)
  (v_interdits_1 (set Int)) (v_interdits (set Int))
  (v_etat_dabz_7777 enum_ETAT_DAB) (v_etat_dab_2 enum_ETAT_DAB)
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_autz_7778 enum_ETAT_AUTOMATE) (v_etat_aut_1 enum_ETAT_AUTOMATE)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat_1 enum_ETAT_DAB) (v_etat_0 enum_ETAT_DAB) (v_datez_7777 Int)
  (v_date_1 Int) (v_date_0 Int) (v_date Int) (v_crt_int (set Int))
  (v_crt Int) (v_cpt_crt (set (tuple2 Int Int))) (v_corbeillez_7777 Int)
  (v_corbeille_2 Int) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptesz_7777 (set (tuple2 Int Int))) (v_comptes_2 (set (tuple2 Int
  Int))) (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int
  Int))) (v_clts (set Int)) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cartez_7778 Int) (v_carte_1 Int) (v_carte_0 Int) (v_carte Int)
  (v_caissez_7777 Int) (v_caisse_2 Int) (v_caisse_1 Int) (v_caisse Int)
  (v_avance_1 Int) (v_avance Int) (v_K0 Int) (v_HS Int) (v_D_min Int)
  (v_D_max Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f33 v_tedaz_7777 v_teda_2 v_teda_1 v_teda_0 v_teda v_som_0 v_som v_rjt
  v_retraitsz_7777 v_retraits_2 v_retraits_1 v_retraits v_panne_dabz_7777
  v_panne_dab_2 v_panne_dab_1 v_panne_dab v_pan_dab_1 v_pan_dab_0
  v_ordrez_7777 v_ordre_2 v_ordre_1 v_ordre v_oo_0 v_oo v_interdits_1
  v_interdits v_etat_dabz_7777 v_etat_dab_2 v_etat_dab_1 v_etat_dab
  v_etat_autz_7778 v_etat_aut_1 v_etat_aut_0 v_etat_aut v_etat_1 v_etat_0
  v_datez_7777 v_date_1 v_date_0 v_date v_crt_int v_crt v_cpt_crt
  v_corbeillez_7777 v_corbeille_2 v_corbeille_1 v_corbeille v_comptesz_7777
  v_comptes_2 v_comptes_1 v_comptes v_clts v_clients_1 v_clients
  v_cartez_7778 v_carte_1 v_carte_0 v_carte v_caissez_7777 v_caisse_2
  v_caisse_1 v_caisse v_avance_1 v_avance v_K0 v_HS v_D_min v_D_max v_DATE
  v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (not (and (= v_etat_dabz_7777 E_En_service) (= v_ordrez_7777 E_Marche)))
  (mem int (t2tb3 v_tedaz_7777) (t2tb2 integer))) (<= 0 v_tedaz_7777))
  (= (+ (+ v_caissez_7777 v_retraitsz_7777) v_corbeillez_7777) v_som))
  (=> (= v_ordrez_7777 E_Marche) (<= 1 v_tedaz_7777)))
  (=> (<= 1 v_tedaz_7777) (= v_ordrez_7777 E_Marche)))
  (=> (= v_etat_dabz_7777 E_Hors_service)
  (or (= v_panne_dabz_7777 true) (<= (+ v_caissez_7777 1) 900))))
  (=> (or (= v_panne_dabz_7777 true) (<= (+ v_caissez_7777 1) 900))
  (= v_etat_dabz_7777 E_Hors_service)))
  (=> (= v_oo E_Marche) (<= 2 v_teda_0)))
  (=> (<= 2 v_teda_0) (= v_oo E_Marche))) (mem int (t2tb3 v_som)
  (t2tb2 integer))) (<= 0 v_som)) (<= v_som 2147483647)) (<= 901 v_som)) (mem
  (set1 int) (t2tb2 v_clts)
  (power int
  (diff int (t2tb2 v_CARTE)
  (union int (add int (t2tb3 v_K0) (empty int))
  (add int (t2tb3 v_HS) (empty int))))))) (mem (set1 (tuple21 int int))
  (t2tb14 v_cpt_crt) (infix_plmngt int int (t2tb2 v_clts) (t2tb2 nat))))
  (infix_eqeq int (dom int int (t2tb14 v_cpt_crt)) (t2tb2 v_clts))) (mem
  (set1 int) (t2tb2 v_crt_int) (power int (t2tb2 v_clts))))
  (=> (= v_etat_0 E_Hors_service)
  (or (= v_pan_dab_0 true) (<= (+ v_som 1) 900))))
  (=> (or (= v_pan_dab_0 true) (<= (+ v_som 1) 900))
  (= v_etat_0 E_Hors_service))) (mem int (t2tb3 v_teda_0) (t2tb2 integer)))
  (<= 0 v_teda_0)) (<= v_teda_0 2147483647)) (not (= v_teda_0 0)))
  (= v_ordrez_7777 E_Marche)))))

(declare-fun f35 (Int Int Int Int Int Int Int Int Int Int Int Int Bool Bool
  Bool Bool Bool Bool enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR (set Int) (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_DAB enum_ETAT_DAB enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_DAB enum_ETAT_DAB Int Int
  Int Int (set Int) Int (set (tuple2 Int Int)) Int Int Int Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set Int) (set Int) Int Int Int Int Int
  Int Int Int Int Int Int Int Int Int (set Int) (set Int)) Bool)

;; f35_def
  (assert
  (forall ((v_tedaz_7777 Int) (v_teda_2 Int) (v_teda_1 Int) (v_teda_0 Int)
  (v_teda Int) (v_som_0 Int) (v_som Int) (v_rjt Int) (v_retraitsz_7777 Int)
  (v_retraits_2 Int) (v_retraits_1 Int) (v_retraits Int)
  (v_panne_dabz_7777 Bool) (v_panne_dab_2 Bool) (v_panne_dab_1 Bool)
  (v_panne_dab Bool) (v_pan_dab_1 Bool) (v_pan_dab_0 Bool)
  (v_ordrez_7777 enum_ORDRE_OPERATEUR) (v_ordre_2 enum_ORDRE_OPERATEUR)
  (v_ordre_1 enum_ORDRE_OPERATEUR) (v_ordre enum_ORDRE_OPERATEUR)
  (v_oo_0 enum_ORDRE_OPERATEUR) (v_oo enum_ORDRE_OPERATEUR)
  (v_interdits_1 (set Int)) (v_interdits (set Int))
  (v_etat_dabz_7777 enum_ETAT_DAB) (v_etat_dab_2 enum_ETAT_DAB)
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_autz_7778 enum_ETAT_AUTOMATE) (v_etat_aut_1 enum_ETAT_AUTOMATE)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat_1 enum_ETAT_DAB) (v_etat_0 enum_ETAT_DAB) (v_datez_7777 Int)
  (v_date_1 Int) (v_date_0 Int) (v_date Int) (v_crt_int (set Int))
  (v_crt Int) (v_cpt_crt (set (tuple2 Int Int))) (v_corbeillez_7777 Int)
  (v_corbeille_2 Int) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptesz_7777 (set (tuple2 Int Int))) (v_comptes_2 (set (tuple2 Int
  Int))) (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int
  Int))) (v_clts (set Int)) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cartez_7778 Int) (v_carte_1 Int) (v_carte_0 Int) (v_carte Int)
  (v_caissez_7777 Int) (v_caisse_2 Int) (v_caisse_1 Int) (v_caisse Int)
  (v_avance_1 Int) (v_avance Int) (v_K0 Int) (v_HS Int) (v_D_min Int)
  (v_D_max Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f35 v_tedaz_7777 v_teda_2 v_teda_1 v_teda_0 v_teda v_som_0 v_som v_rjt
  v_retraitsz_7777 v_retraits_2 v_retraits_1 v_retraits v_panne_dabz_7777
  v_panne_dab_2 v_panne_dab_1 v_panne_dab v_pan_dab_1 v_pan_dab_0
  v_ordrez_7777 v_ordre_2 v_ordre_1 v_ordre v_oo_0 v_oo v_interdits_1
  v_interdits v_etat_dabz_7777 v_etat_dab_2 v_etat_dab_1 v_etat_dab
  v_etat_autz_7778 v_etat_aut_1 v_etat_aut_0 v_etat_aut v_etat_1 v_etat_0
  v_datez_7777 v_date_1 v_date_0 v_date v_crt_int v_crt v_cpt_crt
  v_corbeillez_7777 v_corbeille_2 v_corbeille_1 v_corbeille v_comptesz_7777
  v_comptes_2 v_comptes_1 v_comptes v_clts v_clients_1 v_clients
  v_cartez_7778 v_carte_1 v_carte_0 v_carte v_caissez_7777 v_caisse_2
  v_caisse_1 v_caisse v_avance_1 v_avance v_K0 v_HS v_D_min v_D_max v_DATE
  v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (not (= v_etat_dabz_7777 E_En_service)) (mem int (t2tb3 v_tedaz_7777)
  (t2tb2 integer))) (<= 0 v_tedaz_7777))
  (= (+ (+ v_caissez_7777 v_retraitsz_7777) v_corbeillez_7777) v_som))
  (<= 1 v_tedaz_7777))
  (=> (= v_etat_dabz_7777 E_Hors_service)
  (or (= v_panne_dabz_7777 true) (<= (+ v_caissez_7777 1) 900))))
  (=> (or (= v_panne_dabz_7777 true) (<= (+ v_caissez_7777 1) 900))
  (= v_etat_dabz_7777 E_Hors_service)))
  (=> (= v_oo E_Marche) (<= 2 v_teda_0)))
  (=> (<= 2 v_teda_0) (= v_oo E_Marche))) (mem int (t2tb3 v_som)
  (t2tb2 integer))) (<= 0 v_som)) (<= v_som 2147483647)) (<= 901 v_som)) (mem
  (set1 int) (t2tb2 v_clts)
  (power int
  (diff int (t2tb2 v_CARTE)
  (union int (add int (t2tb3 v_K0) (empty int))
  (add int (t2tb3 v_HS) (empty int))))))) (mem (set1 (tuple21 int int))
  (t2tb14 v_cpt_crt) (infix_plmngt int int (t2tb2 v_clts) (t2tb2 nat))))
  (infix_eqeq int (dom int int (t2tb14 v_cpt_crt)) (t2tb2 v_clts))) (mem
  (set1 int) (t2tb2 v_crt_int) (power int (t2tb2 v_clts))))
  (=> (= v_etat_0 E_Hors_service)
  (or (= v_pan_dab_0 true) (<= (+ v_som 1) 900))))
  (=> (or (= v_pan_dab_0 true) (<= (+ v_som 1) 900))
  (= v_etat_0 E_Hors_service))) (mem int (t2tb3 v_teda_0) (t2tb2 integer)))
  (<= 0 v_teda_0)) (<= v_teda_0 2147483647)) (not (= v_teda_0 0))) (mem
  (set1 (tuple21 int int)) (t2tb14 v_comptesz_7777)
  (infix_plmngt int int (t2tb2 v_clts) (t2tb2 nat)))) (infix_eqeq int
  (dom int int (t2tb14 v_comptesz_7777)) (t2tb2 v_clts))) (mem int
  (t2tb3 v_caissez_7777) (t2tb2 integer))) (<= 0 v_caissez_7777))
  (<= v_caissez_7777 2147483647)) (mem int (t2tb3 v_corbeillez_7777)
  (t2tb2 integer))) (<= 0 v_corbeillez_7777))
  (<= v_corbeillez_7777 2147483647)) (mem int (t2tb3 v_retraitsz_7777)
  (t2tb2 integer))) (<= 0 v_retraitsz_7777))
  (<= v_retraitsz_7777 2147483647)) (mem int
  (t2tb3 (+ (+ v_caissez_7777 v_corbeillez_7777) v_retraitsz_7777))
  (t2tb2 integer)))
  (<= 0 (+ (+ v_caissez_7777 v_corbeillez_7777) v_retraitsz_7777)))
  (<= (+ (+ v_caissez_7777 v_corbeillez_7777) v_retraitsz_7777) 2147483647))
  (<= v_tedaz_7777 2147483647)) (mem int (t2tb3 v_datez_7777)
  (t2tb2 v_DATE))))))

(declare-fun f37 (Int Int Int Int Int Int Int Int Int Int Int Int Bool Bool
  Bool Bool Bool Bool enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR (set Int) (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_DAB enum_ETAT_DAB enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_DAB enum_ETAT_DAB Int Int
  Int Int (set Int) Int (set (tuple2 Int Int)) Int Int Int Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set Int) (set Int) Int Int Int Int Int
  Int Int Int Int Int Int Int Int Int (set Int) (set Int)) Bool)

;; f37_def
  (assert
  (forall ((v_tedaz_7777 Int) (v_teda_2 Int) (v_teda_1 Int) (v_teda_0 Int)
  (v_teda Int) (v_som_0 Int) (v_som Int) (v_rjt Int) (v_retraitsz_7777 Int)
  (v_retraits_2 Int) (v_retraits_1 Int) (v_retraits Int)
  (v_panne_dabz_7777 Bool) (v_panne_dab_2 Bool) (v_panne_dab_1 Bool)
  (v_panne_dab Bool) (v_pan_dab_1 Bool) (v_pan_dab_0 Bool)
  (v_ordrez_7777 enum_ORDRE_OPERATEUR) (v_ordre_2 enum_ORDRE_OPERATEUR)
  (v_ordre_1 enum_ORDRE_OPERATEUR) (v_ordre enum_ORDRE_OPERATEUR)
  (v_oo_0 enum_ORDRE_OPERATEUR) (v_oo enum_ORDRE_OPERATEUR)
  (v_interdits_1 (set Int)) (v_interdits (set Int))
  (v_etat_dabz_7777 enum_ETAT_DAB) (v_etat_dab_2 enum_ETAT_DAB)
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_autz_7778 enum_ETAT_AUTOMATE) (v_etat_aut_1 enum_ETAT_AUTOMATE)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat_1 enum_ETAT_DAB) (v_etat_0 enum_ETAT_DAB) (v_datez_7777 Int)
  (v_date_1 Int) (v_date_0 Int) (v_date Int) (v_crt_int (set Int))
  (v_crt Int) (v_cpt_crt (set (tuple2 Int Int))) (v_corbeillez_7777 Int)
  (v_corbeille_2 Int) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptesz_7777 (set (tuple2 Int Int))) (v_comptes_2 (set (tuple2 Int
  Int))) (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int
  Int))) (v_clts (set Int)) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cartez_7778 Int) (v_carte_1 Int) (v_carte_0 Int) (v_carte Int)
  (v_caissez_7777 Int) (v_caisse_2 Int) (v_caisse_1 Int) (v_caisse Int)
  (v_avance_1 Int) (v_avance Int) (v_K0 Int) (v_HS Int) (v_D_min Int)
  (v_D_max Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f37 v_tedaz_7777 v_teda_2 v_teda_1 v_teda_0 v_teda v_som_0 v_som v_rjt
  v_retraitsz_7777 v_retraits_2 v_retraits_1 v_retraits v_panne_dabz_7777
  v_panne_dab_2 v_panne_dab_1 v_panne_dab v_pan_dab_1 v_pan_dab_0
  v_ordrez_7777 v_ordre_2 v_ordre_1 v_ordre v_oo_0 v_oo v_interdits_1
  v_interdits v_etat_dabz_7777 v_etat_dab_2 v_etat_dab_1 v_etat_dab
  v_etat_autz_7778 v_etat_aut_1 v_etat_aut_0 v_etat_aut v_etat_1 v_etat_0
  v_datez_7777 v_date_1 v_date_0 v_date v_crt_int v_crt v_cpt_crt
  v_corbeillez_7777 v_corbeille_2 v_corbeille_1 v_corbeille v_comptesz_7777
  v_comptes_2 v_comptes_1 v_comptes v_clts v_clients_1 v_clients
  v_cartez_7778 v_carte_1 v_carte_0 v_carte v_caissez_7777 v_caisse_2
  v_caisse_1 v_caisse v_avance_1 v_avance v_K0 v_HS v_D_min v_D_max v_DATE
  v_CARTE)
  (= v_som (+ (+ v_caissez_7777 v_corbeillez_7777) v_retraitsz_7777)))))

(declare-fun f38 (Int Int Int Int Int Int Int Int Int Int Int Int Bool Bool
  Bool Bool Bool Bool enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR enum_ORDRE_OPERATEUR
  enum_ORDRE_OPERATEUR (set Int) (set Int) enum_ETAT_DAB enum_ETAT_DAB
  enum_ETAT_DAB enum_ETAT_DAB enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE
  enum_ETAT_AUTOMATE enum_ETAT_AUTOMATE enum_ETAT_DAB enum_ETAT_DAB Int Int
  Int Int (set Int) Int (set (tuple2 Int Int)) Int Int Int Int
  (set (tuple2 Int Int)) (set (tuple2 Int Int)) (set (tuple2 Int Int))
  (set (tuple2 Int Int)) (set Int) (set Int) (set Int) Int Int Int Int Int
  Int Int Int Int Int Int Int Int Int (set Int) (set Int)) Bool)

;; f38_def
  (assert
  (forall ((v_tedaz_7777 Int) (v_teda_2 Int) (v_teda_1 Int) (v_teda_0 Int)
  (v_teda Int) (v_som_0 Int) (v_som Int) (v_rjt Int) (v_retraitsz_7777 Int)
  (v_retraits_2 Int) (v_retraits_1 Int) (v_retraits Int)
  (v_panne_dabz_7777 Bool) (v_panne_dab_2 Bool) (v_panne_dab_1 Bool)
  (v_panne_dab Bool) (v_pan_dab_1 Bool) (v_pan_dab_0 Bool)
  (v_ordrez_7777 enum_ORDRE_OPERATEUR) (v_ordre_2 enum_ORDRE_OPERATEUR)
  (v_ordre_1 enum_ORDRE_OPERATEUR) (v_ordre enum_ORDRE_OPERATEUR)
  (v_oo_0 enum_ORDRE_OPERATEUR) (v_oo enum_ORDRE_OPERATEUR)
  (v_interdits_1 (set Int)) (v_interdits (set Int))
  (v_etat_dabz_7777 enum_ETAT_DAB) (v_etat_dab_2 enum_ETAT_DAB)
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_autz_7778 enum_ETAT_AUTOMATE) (v_etat_aut_1 enum_ETAT_AUTOMATE)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat_1 enum_ETAT_DAB) (v_etat_0 enum_ETAT_DAB) (v_datez_7777 Int)
  (v_date_1 Int) (v_date_0 Int) (v_date Int) (v_crt_int (set Int))
  (v_crt Int) (v_cpt_crt (set (tuple2 Int Int))) (v_corbeillez_7777 Int)
  (v_corbeille_2 Int) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptesz_7777 (set (tuple2 Int Int))) (v_comptes_2 (set (tuple2 Int
  Int))) (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int
  Int))) (v_clts (set Int)) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cartez_7778 Int) (v_carte_1 Int) (v_carte_0 Int) (v_carte Int)
  (v_caissez_7777 Int) (v_caisse_2 Int) (v_caisse_1 Int) (v_caisse Int)
  (v_avance_1 Int) (v_avance Int) (v_K0 Int) (v_HS Int) (v_D_min Int)
  (v_D_max Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (= (f38 v_tedaz_7777 v_teda_2 v_teda_1 v_teda_0 v_teda v_som_0 v_som v_rjt
  v_retraitsz_7777 v_retraits_2 v_retraits_1 v_retraits v_panne_dabz_7777
  v_panne_dab_2 v_panne_dab_1 v_panne_dab v_pan_dab_1 v_pan_dab_0
  v_ordrez_7777 v_ordre_2 v_ordre_1 v_ordre v_oo_0 v_oo v_interdits_1
  v_interdits v_etat_dabz_7777 v_etat_dab_2 v_etat_dab_1 v_etat_dab
  v_etat_autz_7778 v_etat_aut_1 v_etat_aut_0 v_etat_aut v_etat_1 v_etat_0
  v_datez_7777 v_date_1 v_date_0 v_date v_crt_int v_crt v_cpt_crt
  v_corbeillez_7777 v_corbeille_2 v_corbeille_1 v_corbeille v_comptesz_7777
  v_comptes_2 v_comptes_1 v_comptes v_clts v_clients_1 v_clients
  v_cartez_7778 v_carte_1 v_carte_0 v_carte v_caissez_7777 v_caisse_2
  v_caisse_1 v_caisse v_avance_1 v_avance v_K0 v_HS v_D_min v_D_max v_DATE
  v_CARTE)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (not (and (= v_etat_dabz_7777 E_En_service) (= v_ordrez_7777 E_Marche)))
  (mem int (t2tb3 v_tedaz_7777) (t2tb2 integer))) (<= 0 v_tedaz_7777))
  (= (+ (+ v_caissez_7777 v_retraitsz_7777) v_corbeillez_7777) v_som))
  (=> (= v_ordrez_7777 E_Marche) (<= 1 v_tedaz_7777)))
  (=> (<= 1 v_tedaz_7777) (= v_ordrez_7777 E_Marche)))
  (=> (= v_etat_dabz_7777 E_Hors_service)
  (or (= v_panne_dabz_7777 true) (<= (+ v_caissez_7777 1) 900))))
  (=> (or (= v_panne_dabz_7777 true) (<= (+ v_caissez_7777 1) 900))
  (= v_etat_dabz_7777 E_Hors_service)))
  (=> (= v_oo E_Marche) (<= 2 v_teda_0)))
  (=> (<= 2 v_teda_0) (= v_oo E_Marche))) (mem int (t2tb3 v_som)
  (t2tb2 integer))) (<= 0 v_som)) (<= v_som 2147483647)) (<= 901 v_som)) (mem
  (set1 int) (t2tb2 v_clts)
  (power int
  (diff int (t2tb2 v_CARTE)
  (union int (add int (t2tb3 v_K0) (empty int))
  (add int (t2tb3 v_HS) (empty int))))))) (mem (set1 (tuple21 int int))
  (t2tb14 v_cpt_crt) (infix_plmngt int int (t2tb2 v_clts) (t2tb2 nat))))
  (infix_eqeq int (dom int int (t2tb14 v_cpt_crt)) (t2tb2 v_clts))) (mem
  (set1 int) (t2tb2 v_crt_int) (power int (t2tb2 v_clts))))
  (=> (= v_etat_0 E_Hors_service)
  (or (= v_pan_dab_0 true) (<= (+ v_som 1) 900))))
  (=> (or (= v_pan_dab_0 true) (<= (+ v_som 1) 900))
  (= v_etat_0 E_Hors_service))) (mem int (t2tb3 v_teda_0) (t2tb2 integer)))
  (<= 0 v_teda_0)) (<= v_teda_0 2147483647)) (not (= v_teda_0 0)))
  (not (= v_ordrez_7777 E_Marche))) (mem (set1 (tuple21 int int))
  (t2tb14 v_comptesz_7777)
  (infix_plmngt int int (t2tb2 v_clts) (t2tb2 nat)))) (infix_eqeq int
  (dom int int (t2tb14 v_comptesz_7777)) (t2tb2 v_clts))) (mem int
  (t2tb3 v_caissez_7777) (t2tb2 integer))) (<= 0 v_caissez_7777))
  (<= v_caissez_7777 2147483647)) (mem int (t2tb3 v_corbeillez_7777)
  (t2tb2 integer))) (<= 0 v_corbeillez_7777))
  (<= v_corbeillez_7777 2147483647)) (mem int (t2tb3 v_retraitsz_7777)
  (t2tb2 integer))) (<= 0 v_retraitsz_7777))
  (<= v_retraitsz_7777 2147483647)) (mem int (t2tb3 v_cartez_7778)
  (t2tb2 v_CARTE))) (mem int
  (t2tb3 (+ (+ v_caissez_7777 v_corbeillez_7777) v_retraitsz_7777))
  (t2tb2 integer)))
  (<= 0 (+ (+ v_caissez_7777 v_corbeillez_7777) v_retraitsz_7777)))
  (<= (+ (+ v_caissez_7777 v_corbeillez_7777) v_retraitsz_7777) 2147483647))
  (<= v_tedaz_7777 2147483647)) (mem int (t2tb3 v_datez_7777)
  (t2tb2 v_DATE))))))

(assert
;; main_23
 ;; File "POwhy_bpo2why/DAB/Main_imp.why", line 4285, characters 7-14
  (not
  (forall ((v_tedaz_7777 Int) (v_teda_2 Int) (v_teda_1 Int) (v_teda_0 Int)
  (v_teda Int) (v_som_0 Int) (v_som Int) (v_rjt Int) (v_retraitsz_7777 Int)
  (v_retraits_2 Int) (v_retraits_1 Int) (v_retraits Int)
  (v_panne_dabz_7777 Bool) (v_panne_dab_2 Bool) (v_panne_dab_1 Bool)
  (v_panne_dab Bool) (v_pan_dab_1 Bool) (v_pan_dab_0 Bool)
  (v_ordrez_7777 enum_ORDRE_OPERATEUR) (v_ordre_2 enum_ORDRE_OPERATEUR)
  (v_ordre_1 enum_ORDRE_OPERATEUR) (v_ordre enum_ORDRE_OPERATEUR)
  (v_oo_0 enum_ORDRE_OPERATEUR) (v_oo enum_ORDRE_OPERATEUR)
  (v_interdits_1 (set Int)) (v_interdits (set Int))
  (v_etat_dabz_7777 enum_ETAT_DAB) (v_etat_dab_2 enum_ETAT_DAB)
  (v_etat_dab_1 enum_ETAT_DAB) (v_etat_dab enum_ETAT_DAB)
  (v_etat_autz_7778 enum_ETAT_AUTOMATE) (v_etat_aut_1 enum_ETAT_AUTOMATE)
  (v_etat_aut_0 enum_ETAT_AUTOMATE) (v_etat_aut enum_ETAT_AUTOMATE)
  (v_etat_1 enum_ETAT_DAB) (v_etat_0 enum_ETAT_DAB) (v_datez_7777 Int)
  (v_date_1 Int) (v_date_0 Int) (v_date Int) (v_crt_int (set Int))
  (v_crt Int) (v_cpt_crt (set (tuple2 Int Int))) (v_corbeillez_7777 Int)
  (v_corbeille_2 Int) (v_corbeille_1 Int) (v_corbeille Int)
  (v_comptesz_7777 (set (tuple2 Int Int))) (v_comptes_2 (set (tuple2 Int
  Int))) (v_comptes_1 (set (tuple2 Int Int))) (v_comptes (set (tuple2 Int
  Int))) (v_clts (set Int)) (v_clients_1 (set Int)) (v_clients (set Int))
  (v_cartez_7778 Int) (v_carte_1 Int) (v_carte_0 Int) (v_carte Int)
  (v_caissez_7777 Int) (v_caisse_2 Int) (v_caisse_1 Int) (v_caisse Int)
  (v_avance_1 Int) (v_avance Int) (v_K0 Int) (v_HS Int) (v_D_min Int)
  (v_D_max Int) (v_DATE (set Int)) (v_CARTE (set Int)))
  (=>
  (and (f2 v_tedaz_7777 v_teda_2 v_teda_1 v_teda_0 v_teda v_som_0 v_som v_rjt
  v_retraitsz_7777 v_retraits_2 v_retraits_1 v_retraits v_panne_dabz_7777
  v_panne_dab_2 v_panne_dab_1 v_panne_dab v_pan_dab_1 v_pan_dab_0
  v_ordrez_7777 v_ordre_2 v_ordre_1 v_ordre v_oo_0 v_oo v_interdits_1
  v_interdits v_etat_dabz_7777 v_etat_dab_2 v_etat_dab_1 v_etat_dab
  v_etat_autz_7778 v_etat_aut_1 v_etat_aut_0 v_etat_aut v_etat_1 v_etat_0
  v_datez_7777 v_date_1 v_date_0 v_date v_crt_int v_crt v_cpt_crt
  v_corbeillez_7777 v_corbeille_2 v_corbeille_1 v_corbeille v_comptesz_7777
  v_comptes_2 v_comptes_1 v_comptes v_clts v_clients_1 v_clients
  v_cartez_7778 v_carte_1 v_carte_0 v_carte v_caissez_7777 v_caisse_2
  v_caisse_1 v_caisse v_avance_1 v_avance v_K0 v_HS v_D_min v_D_max v_DATE
  v_CARTE)
  (and (f3 v_tedaz_7777 v_teda_2 v_teda_1 v_teda_0 v_teda v_som_0 v_som v_rjt
  v_retraitsz_7777 v_retraits_2 v_retraits_1 v_retraits v_panne_dabz_7777
  v_panne_dab_2 v_panne_dab_1 v_panne_dab v_pan_dab_1 v_pan_dab_0
  v_ordrez_7777 v_ordre_2 v_ordre_1 v_ordre v_oo_0 v_oo v_interdits_1
  v_interdits v_etat_dabz_7777 v_etat_dab_2 v_etat_dab_1 v_etat_dab
  v_etat_autz_7778 v_etat_aut_1 v_etat_aut_0 v_etat_aut v_etat_1 v_etat_0
  v_datez_7777 v_date_1 v_date_0 v_date v_crt_int v_crt v_cpt_crt
  v_corbeillez_7777 v_corbeille_2 v_corbeille_1 v_corbeille v_comptesz_7777
  v_comptes_2 v_comptes_1 v_comptes v_clts v_clients_1 v_clients
  v_cartez_7778 v_carte_1 v_carte_0 v_carte v_caissez_7777 v_caisse_2
  v_caisse_1 v_caisse v_avance_1 v_avance v_K0 v_HS v_D_min v_D_max v_DATE
  v_CARTE)
  (and (f4 v_tedaz_7777 v_teda_2 v_teda_1 v_teda_0 v_teda v_som_0 v_som v_rjt
  v_retraitsz_7777 v_retraits_2 v_retraits_1 v_retraits v_panne_dabz_7777
  v_panne_dab_2 v_panne_dab_1 v_panne_dab v_pan_dab_1 v_pan_dab_0
  v_ordrez_7777 v_ordre_2 v_ordre_1 v_ordre v_oo_0 v_oo v_interdits_1
  v_interdits v_etat_dabz_7777 v_etat_dab_2 v_etat_dab_1 v_etat_dab
  v_etat_autz_7778 v_etat_aut_1 v_etat_aut_0 v_etat_aut v_etat_1 v_etat_0
  v_datez_7777 v_date_1 v_date_0 v_date v_crt_int v_crt v_cpt_crt
  v_corbeillez_7777 v_corbeille_2 v_corbeille_1 v_corbeille v_comptesz_7777
  v_comptes_2 v_comptes_1 v_comptes v_clts v_clients_1 v_clients
  v_cartez_7778 v_carte_1 v_carte_0 v_carte v_caissez_7777 v_caisse_2
  v_caisse_1 v_caisse v_avance_1 v_avance v_K0 v_HS v_D_min v_D_max v_DATE
  v_CARTE) (f32 v_tedaz_7777 v_teda_2 v_teda_1 v_teda_0 v_teda v_som_0 v_som
  v_rjt v_retraitsz_7777 v_retraits_2 v_retraits_1 v_retraits
  v_panne_dabz_7777 v_panne_dab_2 v_panne_dab_1 v_panne_dab v_pan_dab_1
  v_pan_dab_0 v_ordrez_7777 v_ordre_2 v_ordre_1 v_ordre v_oo_0 v_oo
  v_interdits_1 v_interdits v_etat_dabz_7777 v_etat_dab_2 v_etat_dab_1
  v_etat_dab v_etat_autz_7778 v_etat_aut_1 v_etat_aut_0 v_etat_aut v_etat_1
  v_etat_0 v_datez_7777 v_date_1 v_date_0 v_date v_crt_int v_crt v_cpt_crt
  v_corbeillez_7777 v_corbeille_2 v_corbeille_1 v_corbeille v_comptesz_7777
  v_comptes_2 v_comptes_1 v_comptes v_clts v_clients_1 v_clients
  v_cartez_7778 v_carte_1 v_carte_0 v_carte v_caissez_7777 v_caisse_2
  v_caisse_1 v_caisse v_avance_1 v_avance v_K0 v_HS v_D_min v_D_max v_DATE
  v_CARTE)))) (= v_oo_0 E_Marche)))))
(check-sat)
