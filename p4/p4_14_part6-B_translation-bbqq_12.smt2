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

(declare-fun tuple2 (ty ty) ty)

(declare-fun Tuple2 (ty ty uni uni) uni)

;; Tuple2_sort
  (assert
  (forall ((a ty) (a1 ty))
  (forall ((x uni) (x1 uni)) (sort (tuple2 a1 a) (Tuple2 a1 a x x1)))))

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
  (=> (sort (tuple2 a1 a) u)
  (= u (Tuple2 a1 a (Tuple2_proj_1 a1 a u) (Tuple2_proj_2 a1 a u)))))))

(declare-fun relation (ty ty uni uni) uni)

;; relation_sort
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (x1 uni)) (sort (set1 (set1 (tuple2 a b)))
  (relation b a x x1)))))

;; mem_relation
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni))
  (and
  (=> (mem (set1 (tuple2 a b)) f (relation b a s t))
  (forall ((x uni) (y uni))
  (=> (mem (tuple2 a b) (Tuple2 a b x y) f) (and (mem a x s) (mem b y t)))))
  (=>
  (forall ((x uni) (y uni))
  (=> (sort a x)
  (=> (sort b y)
  (=> (mem (tuple2 a b) (Tuple2 a b x y) f) (and (mem a x s) (mem b y t))))))
  (mem (set1 (tuple2 a b)) f (relation b a s t)))))))

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
     (and (mem a x dom) (mem (tuple2 a b) (Tuple2 a b x y) r)))))
     (=>
     (exists ((x uni))
     (and (mem a x dom) (mem (tuple2 a b) (Tuple2 a b x y) r))) (mem b y
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
  (forall ((x uni) (x1 uni)) (sort (set1 (set1 (tuple2 a b)))
  (infix_plmngt b a x x1)))))

;; mem_function
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni))
  (and
  (=> (mem (set1 (tuple2 a b)) f (infix_plmngt b a s t))
  (and
  (forall ((x uni) (y uni))
  (=> (mem (tuple2 a b) (Tuple2 a b x y) f) (and (mem a x s) (mem b y t))))
  (forall ((x uni) (y1 uni) (y2 uni))
  (=> (sort b y1)
  (=> (sort b y2)
  (=>
  (and (mem (tuple2 a b) (Tuple2 a b x y1) f) (mem (tuple2 a b)
  (Tuple2 a b x y2) f)) (= y1 y2)))))))
  (=>
  (and
  (forall ((x uni) (y uni))
  (=> (sort a x)
  (=> (sort b y)
  (=> (mem (tuple2 a b) (Tuple2 a b x y) f) (and (mem a x s) (mem b y t))))))
  (forall ((x uni) (y1 uni) (y2 uni))
  (=> (sort a x)
  (=> (sort b y1)
  (=> (sort b y2)
  (=>
  (and (mem (tuple2 a b) (Tuple2 a b x y1) f) (mem (tuple2 a b)
  (Tuple2 a b x y2) f)) (= y1 y2))))))) (mem (set1 (tuple2 a b)) f
  (infix_plmngt b a s t)))))))

;; domain_function
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni) (x uni) (y uni))
  (=> (mem (set1 (tuple2 a b)) f (infix_plmngt b a s t))
  (=> (mem (tuple2 a b) (Tuple2 a b x y) f) (mem a x s))))))

;; range_function
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni) (x uni) (y uni))
  (=> (mem (set1 (tuple2 a b)) f (infix_plmngt b a s t))
  (=> (mem (tuple2 a b) (Tuple2 a b x y) f) (mem b y t))))))

;; function_extend_range
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni) (u uni))
  (=> (subset b t u)
  (=> (mem (set1 (tuple2 a b)) f (infix_plmngt b a s t)) (mem
  (set1 (tuple2 a b)) f (infix_plmngt b a s u)))))))

;; function_reduce_range
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni) (u uni))
  (=> (subset b u t)
  (=> (mem (set1 (tuple2 a b)) f (infix_plmngt b a s t))
  (=>
  (forall ((x uni) (y uni))
  (=> (sort a x)
  (=> (sort b y) (=> (mem (tuple2 a b) (Tuple2 a b x y) f) (mem b y u)))))
  (mem (set1 (tuple2 a b)) f (infix_plmngt b a s u))))))))

(declare-fun inverse (ty ty uni) uni)

;; inverse_sort
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni)) (sort (set1 (tuple2 b a)) (inverse b a x)))))

;; Inverse_def
  (assert
  (forall ((a ty) (b ty))
  (forall ((r uni))
  (forall ((x uni) (y uni))
  (= (mem (tuple2 b a) (Tuple2 b a y x) (inverse b a r)) (mem (tuple2 a b)
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
  (exists ((y uni)) (and (sort b y) (mem (tuple2 a b) (Tuple2 a b x y) r))))
  (=> (exists ((y uni)) (mem (tuple2 a b) (Tuple2 a b x y) r)) (mem a x
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
  (exists ((x uni)) (and (sort a x) (mem (tuple2 a b) (Tuple2 a b x y) r))))
  (=> (exists ((x uni)) (mem (tuple2 a b) (Tuple2 a b x y) r)) (mem b y
  (ran b a r))))))))

;; dom_empty
  (assert
  (forall ((a ty) (b ty)) (= (dom b a (empty (tuple2 a b))) (empty a))))

;; dom_add
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (x uni) (y uni))
  (= (dom b a (add (tuple2 a b) (Tuple2 a b x y) f)) (add a x (dom b a f))))))

;; dom_singleton
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (y uni))
  (= (dom b a (add (tuple2 a b) (Tuple2 a b x y) (empty (tuple2 a b)))) 
  (add a x (empty a))))))

(declare-fun infix_mnmngt (ty ty uni uni) uni)

;; infix -->_sort
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (x1 uni)) (sort (set1 (set1 (tuple2 a b)))
  (infix_mnmngt b a x x1)))))

;; mem_total_functions
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni))
  (=> (sort (set1 a) s)
  (= (mem (set1 (tuple2 a b)) f (infix_mnmngt b a s t))
  (and (mem (set1 (tuple2 a b)) f (infix_plmngt b a s t)) (= (dom b a f) s)))))))

;; total_function_is_function
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni))
  (! (=> (mem (set1 (tuple2 a b)) f (infix_mnmngt b a s t)) (mem
     (set1 (tuple2 a b)) f (infix_plmngt b a s t))) :pattern ((mem
  (set1 (tuple2 a b)) f (infix_mnmngt b a s t))) ))))

;; singleton_is_partial_function
  (assert
  (forall ((a ty) (b ty))
  (forall ((s uni) (t uni) (x uni) (y uni))
  (=> (and (mem a x s) (mem b y t)) (mem (set1 (tuple2 a b))
  (add (tuple2 a b) (Tuple2 a b x y) (empty (tuple2 a b)))
  (infix_plmngt b a s t))))))

;; singleton_is_function
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (y uni)) (! (mem (set1 (tuple2 a b))
  (add (tuple2 a b) (Tuple2 a b x y) (empty (tuple2 a b)))
  (infix_mnmngt b a (add a x (empty a)) (add b y (empty b)))) :pattern (
  (add (tuple2 a b) (Tuple2 a b x y) (empty (tuple2 a b)))) ))))

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
  (and (mem (set1 (tuple2 a b)) f (infix_plmngt b a s t)) (mem a a1
  (dom b a f))) (mem (tuple2 a b) (Tuple2 a b a1 (apply b a f a1)) f)))))

;; apply_def1
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni) (a1 uni))
  (=> (and (mem (set1 (tuple2 a b)) f (infix_mnmngt b a s t)) (mem a a1 s))
  (mem (tuple2 a b) (Tuple2 a b a1 (apply b a f a1)) f)))))

;; apply_def2
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni) (a1 uni) (b1 uni))
  (=> (sort b b1)
  (=>
  (and (mem (set1 (tuple2 a b)) f (infix_plmngt b a s t)) (mem (tuple2 a b)
  (Tuple2 a b a1 b1) f)) (= (apply b a f a1) b1))))))

;; apply_singleton
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (y uni))
  (=> (sort b y)
  (= (apply b a (add (tuple2 a b) (Tuple2 a b x y) (empty (tuple2 a b))) x) y)))))

;; apply_range
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (f uni) (s uni) (t uni))
  (! (=>
     (and (mem (set1 (tuple2 a b)) f (infix_plmngt b a s t)) (mem a x
     (dom b a f))) (mem b (apply b a f x) t)) :pattern ((mem
  (set1 (tuple2 a b)) f (infix_plmngt b a s t)) (apply b a f x)) ))))

(declare-fun semicolon (ty ty ty uni uni) uni)

;; semicolon_sort
  (assert
  (forall ((a ty) (b ty) (c ty))
  (forall ((x uni) (x1 uni)) (sort (set1 (tuple2 a c))
  (semicolon c b a x x1)))))

;; semicolon_def
  (assert
  (forall ((a ty) (b ty) (c ty))
  (forall ((x uni) (z uni) (p uni) (q uni))
  (and
  (=> (mem (tuple2 a c) (Tuple2 a c x z) (semicolon c b a p q))
  (exists ((y uni))
  (and (sort b y)
  (and (mem (tuple2 a b) (Tuple2 a b x y) p) (mem (tuple2 b c)
  (Tuple2 b c y z) q)))))
  (=>
  (exists ((y uni))
  (and (mem (tuple2 a b) (Tuple2 a b x y) p) (mem (tuple2 b c)
  (Tuple2 b c y z) q))) (mem (tuple2 a c) (Tuple2 a c x z)
  (semicolon c b a p q)))))))

(declare-fun direct_product (ty ty ty uni uni) uni)

;; direct_product_sort
  (assert
  (forall ((a ty) (b ty) (c ty))
  (forall ((x uni) (x1 uni)) (sort (set1 (tuple2 a (tuple2 b c)))
  (direct_product c b a x x1)))))

;; direct_product_def
  (assert
  (forall ((t ty) (u ty) (v ty))
  (forall ((e uni) (r1 uni) (r2 uni))
  (! (=> (sort (tuple2 t (tuple2 u v)) e)
     (and
     (=> (mem (tuple2 t (tuple2 u v)) e (direct_product v u t r1 r2))
     (exists ((x uni) (y uni) (z uni))
     (and (sort t x)
     (and (sort u y)
     (and (sort v z)
     (and (= (Tuple2 t (tuple2 u v) x (Tuple2 u v y z)) e)
     (and (mem (tuple2 t u) (Tuple2 t u x y) r1) (mem (tuple2 t v)
     (Tuple2 t v x z) r2))))))))
     (=>
     (exists ((x uni) (y uni) (z uni))
     (and (= (Tuple2 t (tuple2 u v) x (Tuple2 u v y z)) e)
     (and (mem (tuple2 t u) (Tuple2 t u x y) r1) (mem (tuple2 t v)
     (Tuple2 t v x z) r2)))) (mem (tuple2 t (tuple2 u v)) e
     (direct_product v u t r1 r2))))) :pattern ((mem
  (tuple2 t (tuple2 u v)) e (direct_product v u t r1 r2))) ))))

(declare-fun parallel_product (ty ty ty ty uni uni) uni)

;; parallel_product_sort
  (assert
  (forall ((a ty) (b ty) (c ty) (d ty))
  (forall ((x uni) (x1 uni)) (sort (set1 (tuple2 (tuple2 a c) (tuple2 b d)))
  (parallel_product d c b a x x1)))))

;; parallel_product_def
  (assert
  (forall ((t ty) (u ty) (v ty) (w ty))
  (forall ((e uni) (r1 uni) (r2 uni))
  (=> (sort (tuple2 (tuple2 t v) (tuple2 u w)) e)
  (and
  (=> (mem (tuple2 (tuple2 t v) (tuple2 u w)) e
  (parallel_product w v u t r1 r2))
  (exists ((x uni) (y uni) (z uni) (a uni))
  (and (sort t x)
  (and (sort v y)
  (and (sort u z)
  (and (sort w a)
  (and
  (= (Tuple2 (tuple2 t v) (tuple2 u w) (Tuple2 t v x y) (Tuple2 u w z a)) e)
  (and (mem (tuple2 t u) (Tuple2 t u x z) r1) (mem (tuple2 v w)
  (Tuple2 v w y a) r2)))))))))
  (=>
  (exists ((x uni) (y uni) (z uni) (a uni))
  (and
  (= (Tuple2 (tuple2 t v) (tuple2 u w) (Tuple2 t v x y) (Tuple2 u w z a)) e)
  (and (mem (tuple2 t u) (Tuple2 t u x z) r1) (mem (tuple2 v w)
  (Tuple2 v w y a) r2)))) (mem (tuple2 (tuple2 t v) (tuple2 u w)) e
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
  (and (mem (set1 (tuple2 a b)) f (infix_plmngt b a s t)) (mem
  (set1 (tuple2 b c)) g (infix_plmngt c b t u))) (mem (set1 (tuple2 a c))
  (semicolon c b a f g) (infix_plmngt c a s u))))))

;; apply_compose
  (assert
  (forall ((a ty) (b ty) (c ty))
  (forall ((x uni) (f uni) (g uni) (s uni) (t uni) (u uni))
  (=>
  (and (mem (set1 (tuple2 a b)) f (infix_plmngt b a s t))
  (and (mem (set1 (tuple2 b c)) g (infix_plmngt c b t u))
  (and (mem a x (dom b a f)) (mem b (apply b a f x) (dom c b g)))))
  (= (apply c a (semicolon c b a f g) x) (apply c b g (apply b a f x)))))))

(declare-fun infix_gtplgt (ty ty uni uni) uni)

;; infix >+>_sort
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (x1 uni)) (sort (set1 (set1 (tuple2 a b)))
  (infix_gtplgt b a x x1)))))

;; mem_partial_injection
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni))
  (= (mem (set1 (tuple2 a b)) f (infix_gtplgt b a s t))
  (and (mem (set1 (tuple2 a b)) f (infix_plmngt b a s t)) (mem
  (set1 (tuple2 b a)) (inverse b a f) (infix_plmngt a b t s)))))))

(declare-fun infix_gtmngt (ty ty uni uni) uni)

;; infix >->_sort
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (x1 uni)) (sort (set1 (set1 (tuple2 a b)))
  (infix_gtmngt b a x x1)))))

;; mem_total_injection
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni))
  (= (mem (set1 (tuple2 a b)) f (infix_gtmngt b a s t))
  (and (mem (set1 (tuple2 a b)) f (infix_gtplgt b a s t)) (mem
  (set1 (tuple2 a b)) f (infix_mnmngt b a s t)))))))

;; mem_total_injection_alt
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni))
  (= (mem (set1 (tuple2 a b)) f (infix_gtmngt b a s t))
  (and (mem (set1 (tuple2 a b)) f (infix_mnmngt b a s t)) (mem
  (set1 (tuple2 b a)) (inverse b a f) (infix_plmngt a b t s)))))))

;; injection
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni))
  (forall ((x uni) (y uni))
  (=> (sort a x)
  (=> (sort a y)
  (=> (mem (set1 (tuple2 a b)) f (infix_gtmngt b a s t))
  (=> (mem a x s)
  (=> (mem a y s) (=> (= (apply b a f x) (apply b a f y)) (= x y)))))))))))

(declare-fun infix_plmngtgt (ty ty uni uni) uni)

;; infix +->>_sort
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (x1 uni)) (sort (set1 (set1 (tuple2 a b)))
  (infix_plmngtgt b a x x1)))))

;; mem_partial_surjection
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni))
  (=> (sort (set1 b) t)
  (= (mem (set1 (tuple2 a b)) f (infix_plmngtgt b a s t))
  (and (mem (set1 (tuple2 a b)) f (infix_plmngt b a s t)) (= (ran b a f) t)))))))

(declare-fun infix_mnmngtgt (ty ty uni uni) uni)

;; infix -->>_sort
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (x1 uni)) (sort (set1 (set1 (tuple2 a b)))
  (infix_mnmngtgt b a x x1)))))

;; mem_total_surjection
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni))
  (= (mem (set1 (tuple2 a b)) f (infix_mnmngtgt b a s t))
  (and (mem (set1 (tuple2 a b)) f (infix_plmngtgt b a s t)) (mem
  (set1 (tuple2 a b)) f (infix_mnmngt b a s t)))))))

(declare-fun infix_gtplgtgt (ty ty uni uni) uni)

;; infix >+>>_sort
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (x1 uni)) (sort (set1 (set1 (tuple2 a b)))
  (infix_gtplgtgt b a x x1)))))

;; mem_partial_bijection
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni))
  (= (mem (set1 (tuple2 a b)) f (infix_gtplgtgt b a s t))
  (and (mem (set1 (tuple2 a b)) f (infix_gtplgt b a s t)) (mem
  (set1 (tuple2 a b)) f (infix_plmngtgt b a s t)))))))

(declare-fun infix_gtmngtgt (ty ty uni uni) uni)

;; infix >->>_sort
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (x1 uni)) (sort (set1 (set1 (tuple2 a b)))
  (infix_gtmngtgt b a x x1)))))

;; mem_total_bijection
  (assert
  (forall ((a ty) (b ty))
  (forall ((f uni) (s uni) (t uni))
  (= (mem (set1 (tuple2 a b)) f (infix_gtmngtgt b a s t))
  (and (mem (set1 (tuple2 a b)) f (infix_gtmngt b a s t)) (mem
  (set1 (tuple2 a b)) f (infix_mnmngtgt b a s t)))))))

(declare-fun id (ty uni) uni)

;; id_sort
  (assert
  (forall ((a ty)) (forall ((x uni)) (sort (set1 (tuple2 a a)) (id a x)))))

;; id_def
  (assert
  (forall ((a ty))
  (forall ((x uni) (y uni) (s uni))
  (=> (sort a x)
  (=> (sort a y)
  (= (mem (tuple2 a a) (Tuple2 a a x y) (id a s)) (and (mem a x s) (= x y))))))))

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
  (forall ((s uni)) (mem (set1 (tuple2 a a)) (id a s)
  (infix_plmngt a a s s)))))

;; id_total_fun
  (assert
  (forall ((a ty))
  (forall ((s uni)) (mem (set1 (tuple2 a a)) (id a s)
  (infix_mnmngt a a s s)))))

(declare-fun seq_length (ty Int uni) uni)

;; seq_length_sort
  (assert
  (forall ((a ty))
  (forall ((x Int) (x1 uni)) (sort (set1 (set1 (tuple2 int a)))
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
  (=> (and (<= 0 n1) (mem (set1 (tuple2 int a)) r (seq_length a n1 s1)))
  (=> (and (<= 0 n2) (mem (set1 (tuple2 int a)) r (seq_length a n2 s2)))
  (= n1 n2))))))

(declare-fun size (ty uni) Int)

;; size_def
  (assert
  (forall ((a ty))
  (forall ((n Int) (s uni) (r uni))
  (=> (and (<= 0 n) (mem (set1 (tuple2 int a)) r (seq_length a n s)))
  (= (size a r) n)))))

(declare-fun seq (ty uni) uni)

;; seq_sort
  (assert
  (forall ((a ty))
  (forall ((x uni)) (sort (set1 (set1 (tuple2 int a))) (seq a x)))))

;; seq_def
  (assert
  (forall ((a ty))
  (forall ((s uni) (r uni))
  (= (mem (set1 (tuple2 int a)) r (seq a s))
  (and (<= 0 (size a r)) (mem (set1 (tuple2 int a)) r
  (seq_length a (size a r) s)))))))

;; seq_as_total_function
  (assert
  (forall ((a ty))
  (forall ((s uni) (r uni))
  (=> (mem (set1 (tuple2 int a)) r (seq a s)) (mem (set1 (tuple2 int a)) r
  (infix_mnmngt a int (t2tb2 (mk 1 (size a r))) s))))))

(declare-fun seq1 (ty uni) uni)

;; seq1_sort
  (assert
  (forall ((a ty))
  (forall ((x uni)) (sort (set1 (set1 (tuple2 int a))) (seq1 a x)))))

(declare-fun iseq (ty uni) uni)

;; iseq_sort
  (assert
  (forall ((a ty))
  (forall ((x uni)) (sort (set1 (set1 (tuple2 int a))) (iseq a x)))))

(declare-fun iseq1 (ty uni) uni)

;; iseq1_sort
  (assert
  (forall ((a ty))
  (forall ((x uni)) (sort (set1 (set1 (tuple2 int a))) (iseq1 a x)))))

(declare-fun perm (ty uni) uni)

;; perm_sort
  (assert
  (forall ((a ty))
  (forall ((x uni)) (sort (set1 (set1 (tuple2 int a))) (perm a x)))))

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
  (forall ((x uni) (x1 uni)) (sort (set1 (tuple2 a b)) (times b a x x1)))))

;; times_def
  (assert
  (forall ((a ty) (b ty))
  (forall ((a1 uni) (b1 uni) (x uni) (y uni))
  (! (= (mem (tuple2 a b) (Tuple2 a b x y) (times b a a1 b1))
     (and (mem a x a1) (mem b y b1))) :pattern ((mem
  (tuple2 a b) (Tuple2 a b x y) (times b a a1 b1))) ))))

(declare-fun relations (ty ty uni uni) uni)

;; relations_sort
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (x1 uni)) (sort (set1 (set1 (tuple2 a b)))
  (relations b a x x1)))))

;; relations_def
  (assert
  (forall ((a ty) (b ty))
  (forall ((u uni) (v uni))
  (= (relations b a u v) (power (tuple2 a b) (times b a u v))))))

;; break_mem_in_add
  (assert
  (forall ((a ty) (b ty))
  (forall ((c uni) (s uni) (x uni) (y uni))
  (=> (sort (tuple2 a b) c)
  (= (mem (tuple2 a b) c (add (tuple2 a b) (Tuple2 a b x y) s))
  (or (= c (Tuple2 a b x y)) (mem (tuple2 a b) c s)))))))

;; break_power_times
  (assert
  (forall ((a ty) (b ty))
  (forall ((r uni) (u uni) (v uni))
  (= (mem (set1 (tuple2 a b)) r (power (tuple2 a b) (times b a u v))) (subset
  (tuple2 a b) r (times b a u v))))))

;; subset_of_times
  (assert
  (forall ((a ty) (b ty))
  (forall ((r uni) (u uni) (v uni))
  (and
  (=> (subset (tuple2 a b) r (times b a u v))
  (forall ((x uni) (y uni))
  (=> (mem (tuple2 a b) (Tuple2 a b x y) r) (and (mem a x u) (mem b y v)))))
  (=>
  (forall ((x uni) (y uni))
  (=> (sort a x)
  (=> (sort b y)
  (=> (mem (tuple2 a b) (Tuple2 a b x y) r) (and (mem a x u) (mem b y v))))))
  (subset (tuple2 a b) r (times b a u v)))))))

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
  (forall ((x uni) (x1 uni)) (sort (set1 (tuple2 a b))
  (infix_lspl b a x x1)))))

;; overriding_def
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (y uni) (q uni) (r uni))
  (= (mem (tuple2 a b) (Tuple2 a b x y) (infix_lspl b a q r))
  (ite (mem a x (dom b a r)) (mem (tuple2 a b) (Tuple2 a b x y) r) (mem
  (tuple2 a b) (Tuple2 a b x y) q))))))

;; function_overriding
  (assert
  (forall ((a ty) (b ty))
  (forall ((s uni) (t uni) (f uni) (g uni))
  (=>
  (and (mem (set1 (tuple2 a b)) f (infix_plmngt b a s t)) (mem
  (set1 (tuple2 a b)) g (infix_plmngt b a s t))) (mem (set1 (tuple2 a b))
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
     (and (mem (set1 (tuple2 a b)) f (infix_plmngt b a s t)) (mem
     (set1 (tuple2 a b)) g (infix_plmngt b a s t)))
     (=> (mem a x (dom b a g))
     (= (apply b a (infix_lspl b a f g) x) (apply b a g x)))) :pattern ((mem
  (set1 (tuple2 a b)) f (infix_plmngt b a s t)) (mem (set1 (tuple2 a b)) g
  (infix_plmngt b a s t)) (apply b a (infix_lspl b a f g) x)) ))))

;; apply_overriding_2
  (assert
  (forall ((a ty) (b ty))
  (forall ((s uni) (t uni) (f uni) (g uni) (x uni))
  (! (=>
     (and (mem (set1 (tuple2 a b)) f (infix_plmngt b a s t)) (mem
     (set1 (tuple2 a b)) g (infix_plmngt b a s t)))
     (=> (not (mem a x (dom b a g)))
     (=> (mem a x (dom b a f))
     (= (apply b a (infix_lspl b a f g) x) (apply b a f x))))) :pattern ((mem
  (set1 (tuple2 a b)) f (infix_plmngt b a s t))
  (apply b a (infix_lspl b a f g) x)) :pattern ((mem (set1 (tuple2 a b)) g
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

(declare-fun t2tb4 ((set enum_aa)) uni)

;; t2tb_sort
  (assert (forall ((x (set enum_aa))) (sort (set1 enum_aa1) (t2tb4 x))))

(declare-fun tb2t4 (uni) (set enum_aa))

;; BridgeL
  (assert
  (forall ((i (set enum_aa)))
  (! (= (tb2t4 (t2tb4 i)) i) :pattern ((t2tb4 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 enum_aa1) j) (= (t2tb4 (tb2t4 j)) j)) :pattern (
  (t2tb4 (tb2t4 j))) )))

(declare-fun t2tb5 (enum_aa) uni)

;; t2tb_sort
  (assert (forall ((x enum_aa)) (sort enum_aa1 (t2tb5 x))))

(declare-fun tb2t5 (uni) enum_aa)

;; BridgeL
  (assert
  (forall ((i enum_aa)) (! (= (tb2t5 (t2tb5 i)) i) :pattern ((t2tb5 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort enum_aa1 j) (= (t2tb5 (tb2t5 j)) j)) :pattern ((t2tb5
                                                              (tb2t5 j))) )))

;; set_enum_aa_axiom
  (assert
  (forall ((x enum_aa)) (mem enum_aa1 (t2tb5 x) (t2tb4 set_enum_aa))))

(declare-fun f1 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f1_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f1 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
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
  (and (and (= v_bbll 0) (= v_bbmm 1)) (mem int (t2tb3 v_bbnn)
  (t2tb2 integer))) (<= 0 v_bbnn)) (<= v_bbnn 2147483647)) (mem int
  (t2tb3 v_bboo) (t2tb2 integer))) (<= 0 v_bboo)) (<= v_bboo 2147483647))
  (mem int (t2tb3 v_bbpp) (t2tb2 integer))) (<= 0 v_bbpp))
  (<= v_bbpp 2147483647)) (mem int (t2tb3 v_vv) (t2tb2 integer)))
  (<= 0 v_vv)) (<= v_vv 2147483647)) (<= 1 v_vv)) (<= v_vv 254))
  (= v_vv v_bboo)) (mem int (t2tb3 v_xx) (t2tb2 integer))) (<= 0 v_xx))
  (<= v_xx 2147483647)) (<= 1 v_xx)) (<= v_xx 254)) (= v_xx v_bboo)) (mem 
  int (t2tb3 v_bbjj) (t2tb2 integer))) (<= 0 v_bbjj)) (<= v_bbjj 2147483647))
  (<= 1 v_bbjj)) (<= (+ v_bbjj 1) 2147483647)) (= v_bbjj v_bbpp)) (mem 
  int (t2tb3 v_ww) (t2tb2 integer))) (<= 0 v_ww)) (<= v_ww 2147483647))
  (<= 2 v_ww)) (= v_ww v_bbnn)) (<= (+ v_ww v_xx) 253))
  (<= (+ (+ v_ww v_vv) v_xx) 251)) (mem int (t2tb3 v_uu) (t2tb2 integer)))
  (<= 0 v_uu)) (<= v_uu 2147483647)) (<= 1 v_uu)) (<= (+ v_uu 1) 254))
  (= v_uu v_bbnn)))))

(declare-fun f2 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f2_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f2 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
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
  (and (mem int (t2tb3 v_yy) (t2tb2 (mk 0 255))) (mem int (t2tb3 v_zz)
  (t2tb2 (mk 0 255)))) (mem int (t2tb3 v_bbaa) (t2tb2 (mk 0 255)))) (mem 
  int (t2tb3 v_bbbb) (t2tb2 (mk 0 255)))) (mem int (t2tb3 v_bbgg)
  (t2tb2 integer))) (<= 0 v_bbgg)) (mem int (t2tb3 v_bbii) (t2tb2 integer)))
  (<= 0 v_bbii))
  (=> (mem enum_aa1 (t2tb5 v_bbhh)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_zz 0)))
  (=> (= v_bbhh E_cc) (<= v_yy v_uu))) (=> (= v_bbhh E_ee) (<= v_zz v_vv)))
  (=> (= v_bbhh E_ff) (<= v_zz (+ v_vv 1))))
  (=> (mem enum_aa1 (t2tb5 v_bbhh)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbaa 0)))
  (=> (mem enum_aa1 (t2tb5 v_bbhh)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbbb 0)))
  (=> (= v_bbhh E_gg) (<= v_bbbb 1)))
  (=> (= v_bbhh E_gg) (= (- v_bbgg v_bbii) v_bbbb)))
  (=> (mem enum_aa1 (t2tb5 v_bbhh)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_gg) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_hh) (empty enum_aa1))))
  (and (<= v_bbaa (+ (+ v_ww v_xx) 1)) (<= v_zz (+ (+ v_vv v_bbaa) 2)))))
  (=> (= v_bbhh E_hh)
  (and (and (= (- (- v_bbgg 1) v_bbii) v_bbbb) (<= v_bbaa (+ v_bbbb v_xx)))
  (<= v_bbbb v_ww)))))))

(declare-fun f3 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f3_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f3 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
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
  (and (and (mem int (t2tb3 v_yy) (t2tb2 integer)) (<= 0 v_yy)) (mem 
  int (t2tb3 v_zz) (t2tb2 integer))) (<= 0 v_zz)) (mem int (t2tb3 v_bbaa)
  (t2tb2 integer))) (<= 0 v_bbaa)) (mem int (t2tb3 v_bbbb) (t2tb2 integer)))
  (<= 0 v_bbbb)) (mem int (t2tb3 v_bbkk) (t2tb2 integer))) (<= 0 v_bbkk))
  (mem int (t2tb3 v_bbii) (t2tb2 integer))) (<= 0 v_bbii))
  (=> (mem enum_aa1 (t2tb5 v_bbhh)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbaa 0)))
  (=> (mem enum_aa1 (t2tb5 v_bbhh)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbbb 0)))
  (=> (= v_bbhh E_gg) (<= v_bbbb 1)))
  (=> (= v_bbhh E_gg) (= (- v_bbgg v_bbii) v_bbbb)))
  (=> (= v_bbhh E_hh) (= (- (- v_bbgg 1) v_bbii) v_bbbb)))
  (=> (mem enum_aa1 (t2tb5 v_bbhh)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_gg) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_hh) (empty enum_aa1))))
  (and (= (- (- v_bbgg 1) v_bbkk) v_bbaa) (<= v_bbaa (+ (+ v_ww v_xx) 1)))))
  (=> (= v_bbhh E_hh) (and (<= v_bbaa (+ v_bbbb v_xx)) (<= v_bbbb v_ww))))
  (mem int (t2tb3 v_bbgg) (t2tb2 integer))) (<= 0 v_bbgg))
  (=> (mem enum_aa1 (t2tb5 v_bbhh)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_zz 0)))
  (=> (= v_bbhh E_ee) (<= v_zz v_vv)))
  (=> (= v_bbhh E_ff) (= v_bbkk v_bbgg))) (=> (= v_bbhh E_cc) (<= v_yy 254)))
  (= v_jj v_yy)) (= v_kk v_zz)) (= v_ll v_bbaa)) (= v_mm v_bbbb))
  (= v_oo v_bbcc)) (= v_pp v_bbdd)) (= v_qq v_bbee)) (= v_rr v_bbff))
  (= v_nn v_bbgg)) (= v_ss v_bbhh)) (= v_tt v_bbii)))))

(declare-fun f4 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f4_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f4 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
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
  (and (and (not (= v_bbhh E_ii)) (not (= v_bbhh E_hh)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_cc)))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= v_bbhh E_bb)) (mem int (t2tb3 0)
  (t2tb2 (mk 0 255)))) (mem int (t2tb3 (+ v_bbgg 1)) (t2tb2 integer)))
  (<= 0 (+ v_bbgg 1))) (=> (= v_bbhh E_cc) (<= 0 v_uu)))
  (=> (= v_bbhh E_ee) (<= 0 v_vv))) (=> (= v_bbhh E_ff) (<= 0 (+ v_vv 1))))
  (=> (= v_bbhh E_gg) (= (- (+ v_bbgg 1) v_bbii) 0)))
  (=> (mem enum_aa1 (t2tb5 v_bbhh)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_gg) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_hh) (empty enum_aa1))))
  (and (<= 0 (+ (+ v_ww v_xx) 1)) (<= 0 (+ (+ v_vv 0) 2)))))
  (=> (= v_bbhh E_hh)
  (and (and (= (- (- (+ v_bbgg 1) 1) v_bbii) 0) (<= 0 (+ 0 v_xx)))
  (<= 0 v_ww))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ff)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_ii)))
  (= 0 v_yy)) (= 0 v_bbaa)) (= 0 v_zz)) (= 0 v_bbbb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ff)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_hh))) (= v_bbhh E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))
  (or (<= (+ (- v_bbgg v_bbii) 1) (+ v_ww v_bbjj))
  (and (not (<= (+ (- v_bbgg v_bbii) 1) (+ v_ww v_bbjj))) (= v_bbhh E_bb))))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= v_bbhh E_bb)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (= v_bbhh E_bb)))
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= v_bbhh E_bb)))
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= v_bbhh E_bb)))) (= 0 v_bbbb)) (= 0 v_zz))
  (= 0 v_bbaa)) (= 0 v_yy))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff)) (= 0 v_zz))
  (= 0 v_yy)) (= 0 v_bbaa))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= v_bbhh E_bb)) (= 0 v_bbbb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff)) (= 0 v_zz))
  (= 0 v_yy)) (= 0 v_bbaa)) (= v_bbcc false)) (= v_bbdd true))
  (= v_bbee false)) (= v_bbff false)) (= 0 v_bbbb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff)) (= 0 v_zz))
  (= 0 v_yy)) (= 0 v_bbaa))
  (or
  (and
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= v_bbhh E_bb)) (= 0 v_bbbb))
  (and
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (= v_bbhh E_bb)) (= 0 v_bbbb))))))
  (<= (+ (+ v_zz 1) 1) v_vv))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd)) (= 0 v_yy))
  (= 0 v_bbaa)) (= 0 v_zz))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= v_bbhh E_bb)) (= 0 v_bbbb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd)) (= 0 v_yy))
  (= 0 v_bbaa)) (= 0 v_zz)) (= v_bbcc false)) (= v_bbdd true))
  (= v_bbee false)) (= v_bbff false)) (= v_bbhh E_ee)) (= 0 v_bbbb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd)) (= 0 v_yy))
  (= 0 v_bbaa)) (= 0 v_zz)) (= v_bbcc true)) (= v_bbdd true))
  (= v_bbee true)) (= v_bbff false)) (= v_bbhh E_gg))
  (= v_bbii (+ v_bbgg 1))) (= 0 v_bbbb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd)) (= 0 v_yy))
  (= 0 v_bbaa)) (= 0 v_zz)) (= v_bbcc true)) (= v_bbdd true))
  (= v_bbee false)) (= v_bbff false)) (= 0 v_bbbb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_ii)) (not (= v_bbhh E_hh)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_cc)))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))))))))

(declare-fun f12 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f12_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f12 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
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
  (and (and (not (= v_bbhh E_ii)) (not (= v_bbhh E_hh)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_cc)))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= v_bbhh E_bb)) (mem int (t2tb3 0)
  (t2tb2 (mk 0 255)))) (mem int (t2tb3 (+ v_bbgg 1)) (t2tb2 integer)))
  (<= 0 (+ v_bbgg 1))) (=> (= v_bbhh E_cc) (<= 0 v_uu)))
  (=> (= v_bbhh E_ee) (<= 0 v_vv))) (=> (= v_bbhh E_ff) (<= 0 (+ v_vv 1))))
  (=> (= v_bbhh E_gg) (= (- (+ v_bbgg 1) v_bbii) 0)))
  (=> (mem enum_aa1 (t2tb5 v_bbhh)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_gg) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_hh) (empty enum_aa1))))
  (and (<= 0 (+ (+ v_ww v_xx) 1)) (<= 0 (+ (+ v_vv 0) 2)))))
  (=> (= v_bbhh E_hh)
  (and (and (= (- (- (+ v_bbgg 1) 1) v_bbii) 0) (<= 0 (+ 0 v_xx)))
  (<= 0 v_ww))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ff)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_ii)))
  (= 0 v_yy)) (= 0 v_bbaa)) (= 0 v_zz)) (= 0 v_bbbb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ff)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_hh))) (= v_bbhh E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))
  (or (<= (+ (- v_bbgg v_bbii) 1) (+ v_ww v_bbjj))
  (and (not (<= (+ (- v_bbgg v_bbii) 1) (+ v_ww v_bbjj))) (= v_bbhh E_bb))))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= v_bbhh E_bb)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (= v_bbhh E_bb)))
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= v_bbhh E_bb)))
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= v_bbhh E_bb)))) (= 0 v_bbbb)) (= 0 v_zz))
  (= 0 v_bbaa)) (= 0 v_yy))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff)) (= 0 v_zz))
  (= 0 v_yy)) (= 0 v_bbaa))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= v_bbhh E_bb)) (= 0 v_bbbb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff)) (= 0 v_zz))
  (= 0 v_yy)) (= 0 v_bbaa)) (= v_bbcc false)) (= v_bbdd true))
  (= v_bbee false)) (= v_bbff false)) (= 0 v_bbbb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff)) (= 0 v_zz))
  (= 0 v_yy)) (= 0 v_bbaa))
  (or
  (and
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= v_bbhh E_bb)) (= 0 v_bbbb))
  (and
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (= v_bbhh E_bb)) (= 0 v_bbbb))))))
  (not (<= (+ (+ v_zz 1) 1) v_vv)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd)) (= 0 v_yy))
  (= 0 v_bbaa)) (= 0 v_zz))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= v_bbhh E_bb)) (= 0 v_bbbb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd)) (= 0 v_yy))
  (= 0 v_bbaa)) (= 0 v_zz)) (= v_bbcc false)) (= v_bbdd true))
  (= v_bbee false)) (= v_bbff false)) (= v_bbhh E_ee)) (= 0 v_bbbb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd)) (= 0 v_yy))
  (= 0 v_bbaa)) (= 0 v_zz)) (= v_bbcc true)) (= v_bbdd true))
  (= v_bbee true)) (= v_bbff false)) (= v_bbhh E_gg))
  (= v_bbii (+ v_bbgg 1))) (= 0 v_bbbb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd)) (= 0 v_yy))
  (= 0 v_bbaa)) (= 0 v_zz)) (= v_bbcc true)) (= v_bbdd true))
  (= v_bbee false)) (= v_bbff false)) (= 0 v_bbbb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_ii)) (not (= v_bbhh E_hh)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_cc)))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))))))))

(declare-fun f13 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f13_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f13 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
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
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (not (= v_bbhh E_ff)))
  (not (= v_bbhh E_ee))) (not (= v_bbhh E_dd))) (not (= v_bbcc false)))
  (not (= v_bbdd false))) (not (= v_bbee true))) (not (= v_bbff true)))
  (not
  (and
  (and (and (and (<= v_uu (+ v_yy 1)) (= v_bbcc true)) (= v_bbdd true))
  (= v_bbee false)) (= v_bbff false)))) (= v_bbhh E_cc)) (mem int
  (t2tb3 (+ v_yy 1)) (t2tb2 (mk 0 255)))) (mem int (t2tb3 (+ v_bbgg 1))
  (t2tb2 integer))) (<= 0 (+ v_bbgg 1)))
  (=> (= v_bbhh E_cc) (<= (+ v_yy 1) v_uu)))
  (=> (= v_bbhh E_gg) (= (- (+ v_bbgg 1) v_bbii) v_bbbb)))
  (=> (= v_bbhh E_hh)
  (and
  (and (= (- (- (+ v_bbgg 1) 1) v_bbii) v_bbbb) (<= v_bbaa (+ v_bbbb v_xx)))
  (<= v_bbbb v_ww)))) (<= (+ (+ v_zz 1) 1) v_vv))
  (not
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_ii)) (not (= v_bbhh E_hh)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee)))
  (not (= v_bbhh E_dd))) (= v_bbhh E_cc))
  (not
  (and
  (and (and (and (<= v_uu (+ v_yy 1)) (= v_bbcc true)) (= v_bbdd true))
  (= v_bbee false)) (= v_bbff false)))))))))

(declare-fun f14 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f14_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f14 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
  v_bbhh v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (<= v_uu (+ v_yy 1)))))

(declare-fun f16 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f16_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f16 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
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
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (not (= v_bbhh E_ff)))
  (not (= v_bbhh E_ee))) (not (= v_bbhh E_dd))) (not (= v_bbcc false)))
  (not (= v_bbdd false))) (not (= v_bbee true))) (not (= v_bbff true)))
  (not
  (and
  (and (and (and (<= v_uu (+ v_yy 1)) (= v_bbcc true)) (= v_bbdd true))
  (= v_bbee false)) (= v_bbff false)))) (= v_bbhh E_cc)) (mem int
  (t2tb3 (+ v_yy 1)) (t2tb2 (mk 0 255)))) (mem int (t2tb3 (+ v_bbgg 1))
  (t2tb2 integer))) (<= 0 (+ v_bbgg 1)))
  (=> (= v_bbhh E_cc) (<= (+ v_yy 1) v_uu)))
  (=> (= v_bbhh E_gg) (= (- (+ v_bbgg 1) v_bbii) v_bbbb)))
  (=> (= v_bbhh E_hh)
  (and
  (and (= (- (- (+ v_bbgg 1) 1) v_bbii) v_bbbb) (<= v_bbaa (+ v_bbbb v_xx)))
  (<= v_bbbb v_ww)))) (not (<= (+ (+ v_zz 1) 1) v_vv)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_ii)) (not (= v_bbhh E_hh)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee)))
  (not (= v_bbhh E_dd))) (= v_bbhh E_cc))
  (not
  (and
  (and (and (and (<= v_uu (+ v_yy 1)) (= v_bbcc true)) (= v_bbdd true))
  (= v_bbee false)) (= v_bbff false)))))))))

(declare-fun f17 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f17_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f17 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
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
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false)) (mem
  int (t2tb3 1) (t2tb2 (mk 0 255)))) (mem int (t2tb3 (+ v_bbgg 1))
  (t2tb2 integer))) (<= 0 (+ v_bbgg 1)))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_zz 0)))
  (=> (= E_gg E_cc) (<= v_yy v_uu))) (=> (= E_gg E_ee) (<= v_zz v_vv)))
  (=> (= E_gg E_ff) (<= v_zz (+ v_vv 1))))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbaa 0)))
  (not (= E_gg E_cc))) (not (= E_gg E_dd))) (not (= E_gg E_ee)))
  (not (= E_gg E_ff))) (= (- (+ v_bbgg 1) v_bbgg) 1))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_gg) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_hh) (empty enum_aa1))))
  (and (<= v_bbaa (+ (+ v_ww v_xx) 1)) (<= v_zz (+ (+ v_vv v_bbaa) 2)))))
  (=> (= E_gg E_hh)
  (and (and (= (- (- (+ v_bbgg 1) 1) v_bbgg) 1) (<= v_bbaa (+ 1 v_xx)))
  (<= 1 v_ww))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ff)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_hh))) (= v_bbhh E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))
  (and (not (<= (+ (- v_bbgg v_bbii) 1) (+ v_ww v_bbjj))) (= E_gg E_bb)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= E_gg E_bb)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (= E_gg E_bb)))
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= E_gg E_bb)))
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_gg E_bb)))) (= 1 v_bbbb)) (= v_bbgg v_bbii))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_gg E_bb)) (= v_bbgg v_bbii)) (= 1 v_bbbb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (or
  (or
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))
  (and
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= E_gg E_bb)) (and (= 1 v_bbbb) (= v_bbgg v_bbii))))
  (and
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (= E_gg E_bb)) (and (= v_bbgg v_bbii) (= 1 v_bbbb)))))))
  (<= (+ (+ v_zz 1) 1) v_vv))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_gg E_bb)) (= 1 v_bbbb)) (= v_bbgg v_bbii))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))
  (= E_gg E_ee)) (= v_bbgg v_bbii)) (= 1 v_bbbb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false)))))))

(declare-fun f19 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f19_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f19 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
  v_bbhh v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (not (= v_bbhh E_dd)))))

(declare-fun f21 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f21_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f21 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
  v_bbhh v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (= v_yy (+ v_yy 1)))))

(declare-fun f25 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f25_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f25 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
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
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false)) (mem
  int (t2tb3 1) (t2tb2 (mk 0 255)))) (mem int (t2tb3 (+ v_bbgg 1))
  (t2tb2 integer))) (<= 0 (+ v_bbgg 1)))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_zz 0)))
  (=> (= E_gg E_cc) (<= v_yy v_uu))) (=> (= E_gg E_ee) (<= v_zz v_vv)))
  (=> (= E_gg E_ff) (<= v_zz (+ v_vv 1))))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbaa 0)))
  (not (= E_gg E_cc))) (not (= E_gg E_dd))) (not (= E_gg E_ee)))
  (not (= E_gg E_ff))) (= (- (+ v_bbgg 1) v_bbgg) 1))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_gg) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_hh) (empty enum_aa1))))
  (and (<= v_bbaa (+ (+ v_ww v_xx) 1)) (<= v_zz (+ (+ v_vv v_bbaa) 2)))))
  (=> (= E_gg E_hh)
  (and (and (= (- (- (+ v_bbgg 1) 1) v_bbgg) 1) (<= v_bbaa (+ 1 v_xx)))
  (<= 1 v_ww))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ff)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_hh))) (= v_bbhh E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))
  (and (not (<= (+ (- v_bbgg v_bbii) 1) (+ v_ww v_bbjj))) (= E_gg E_bb)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= E_gg E_bb)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (= E_gg E_bb)))
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= E_gg E_bb)))
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_gg E_bb)))) (= 1 v_bbbb)) (= v_bbgg v_bbii))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_gg E_bb)) (= v_bbgg v_bbii)) (= 1 v_bbbb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (or
  (or
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))
  (and
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= E_gg E_bb)) (and (= 1 v_bbbb) (= v_bbgg v_bbii))))
  (and
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (= E_gg E_bb)) (and (= v_bbgg v_bbii) (= 1 v_bbbb)))))))
  (<= (+ (+ v_zz 1) 1) v_vv))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_gg E_bb)) (= 1 v_bbbb)) (= v_bbgg v_bbii))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))
  (= E_gg E_ee)) (= v_bbgg v_bbii)) (= 1 v_bbbb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))))
  (= v_bbdd false)))))

(declare-fun f26 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f26_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f26 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
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
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false)) (mem
  int (t2tb3 1) (t2tb2 (mk 0 255)))) (mem int (t2tb3 (+ v_bbgg 1))
  (t2tb2 integer))) (<= 0 (+ v_bbgg 1)))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_zz 0)))
  (=> (= E_gg E_cc) (<= v_yy v_uu))) (=> (= E_gg E_ee) (<= v_zz v_vv)))
  (=> (= E_gg E_ff) (<= v_zz (+ v_vv 1))))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbaa 0)))
  (not (= E_gg E_cc))) (not (= E_gg E_dd))) (not (= E_gg E_ee)))
  (not (= E_gg E_ff))) (= (- (+ v_bbgg 1) v_bbgg) 1))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_gg) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_hh) (empty enum_aa1))))
  (and (<= v_bbaa (+ (+ v_ww v_xx) 1)) (<= v_zz (+ (+ v_vv v_bbaa) 2)))))
  (=> (= E_gg E_hh)
  (and (and (= (- (- (+ v_bbgg 1) 1) v_bbgg) 1) (<= v_bbaa (+ 1 v_xx)))
  (<= 1 v_ww))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ff)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_hh))) (= v_bbhh E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))
  (and (not (<= (+ (- v_bbgg v_bbii) 1) (+ v_ww v_bbjj))) (= E_gg E_bb)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= E_gg E_bb)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (= E_gg E_bb)))
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= E_gg E_bb)))
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_gg E_bb)))) (= 1 v_bbbb)) (= v_bbgg v_bbii))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_gg E_bb)) (= v_bbgg v_bbii)) (= 1 v_bbbb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (or
  (or
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))
  (and
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= E_gg E_bb)) (and (= 1 v_bbbb) (= v_bbgg v_bbii))))
  (and
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (= E_gg E_bb)) (and (= v_bbgg v_bbii) (= 1 v_bbbb)))))))
  (not (<= (+ (+ v_zz 1) 1) v_vv)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_gg E_bb)) (= 1 v_bbbb)) (= v_bbgg v_bbii))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))
  (= E_gg E_ee)) (= v_bbgg v_bbii)) (= 1 v_bbbb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false)))))))

(declare-fun f27 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f27_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f27 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
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
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false)) (mem
  int (t2tb3 1) (t2tb2 (mk 0 255)))) (mem int (t2tb3 (+ v_bbgg 1))
  (t2tb2 integer))) (<= 0 (+ v_bbgg 1)))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_zz 0)))
  (=> (= E_gg E_cc) (<= v_yy v_uu))) (=> (= E_gg E_ee) (<= v_zz v_vv)))
  (=> (= E_gg E_ff) (<= v_zz (+ v_vv 1))))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbaa 0)))
  (not (= E_gg E_cc))) (not (= E_gg E_dd))) (not (= E_gg E_ee)))
  (not (= E_gg E_ff))) (= (- (+ v_bbgg 1) v_bbgg) 1))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_gg) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_hh) (empty enum_aa1))))
  (and (<= v_bbaa (+ (+ v_ww v_xx) 1)) (<= v_zz (+ (+ v_vv v_bbaa) 2)))))
  (=> (= E_gg E_hh)
  (and (and (= (- (- (+ v_bbgg 1) 1) v_bbgg) 1) (<= v_bbaa (+ 1 v_xx)))
  (<= 1 v_ww))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ff)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_hh))) (= v_bbhh E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))
  (and (not (<= (+ (- v_bbgg v_bbii) 1) (+ v_ww v_bbjj))) (= E_gg E_bb)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= E_gg E_bb)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (= E_gg E_bb)))
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= E_gg E_bb)))
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_gg E_bb)))) (= 1 v_bbbb)) (= v_bbgg v_bbii))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_gg E_bb)) (= v_bbgg v_bbii)) (= 1 v_bbbb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (or
  (or
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))
  (and
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= E_gg E_bb)) (and (= 1 v_bbbb) (= v_bbgg v_bbii))))
  (and
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (= E_gg E_bb)) (and (= v_bbgg v_bbii) (= 1 v_bbbb)))))))
  (not (<= (+ (+ v_zz 1) 1) v_vv)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_gg E_bb)) (= 1 v_bbbb)) (= v_bbgg v_bbii))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))
  (= E_gg E_ee)) (= v_bbgg v_bbii)) (= 1 v_bbbb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))))
  (= v_bbdd false)))))

(declare-fun f28 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f28_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f28 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
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
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false)) (mem
  int (t2tb3 (+ v_bbgg 1)) (t2tb2 integer))) (<= 0 (+ v_bbgg 1)))
  (=> (= v_bbhh E_gg) (= (- (+ v_bbgg 1) v_bbii) v_bbbb)))
  (=> (= v_bbhh E_hh)
  (and
  (and (= (- (- (+ v_bbgg 1) 1) v_bbii) v_bbbb) (<= v_bbaa (+ v_bbbb v_xx)))
  (<= v_bbbb v_ww))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ff)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_ii)))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ff)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_hh))) (= v_bbhh E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))
  (or (<= (+ (- v_bbgg v_bbii) 1) (+ v_ww v_bbjj))
  (and (not (<= (+ (- v_bbgg v_bbii) 1) (+ v_ww v_bbjj))) (= v_bbhh E_bb))))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= v_bbhh E_bb)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (= v_bbhh E_bb)))
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= v_bbhh E_bb)))
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= v_bbhh E_bb))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= v_bbhh E_bb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))
  (and (and (= v_bbhh E_gg) (= v_bbbb 1)) (= v_bbii v_bbgg)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= v_bbhh E_bb)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (= v_bbhh E_bb)))))) (<= (+ (+ v_zz 1) 1) v_vv))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= v_bbhh E_bb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))
  (= v_bbhh E_ee))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))
  (= v_bbhh E_gg)) (= v_bbii (+ v_bbgg 1)))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))
  (= v_bbhh E_gg)) (= v_bbii v_bbgg)) (= v_bbbb 1)))) (= v_bbcc false)))))

(declare-fun f30 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f30_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f30 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
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
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false)) (mem
  int (t2tb3 (+ v_bbgg 1)) (t2tb2 integer))) (<= 0 (+ v_bbgg 1)))
  (=> (= v_bbhh E_gg) (= (- (+ v_bbgg 1) v_bbii) v_bbbb)))
  (=> (= v_bbhh E_hh)
  (and
  (and (= (- (- (+ v_bbgg 1) 1) v_bbii) v_bbbb) (<= v_bbaa (+ v_bbbb v_xx)))
  (<= v_bbbb v_ww))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ff)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_ii)))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ff)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_hh))) (= v_bbhh E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))
  (or (<= (+ (- v_bbgg v_bbii) 1) (+ v_ww v_bbjj))
  (and (not (<= (+ (- v_bbgg v_bbii) 1) (+ v_ww v_bbjj))) (= v_bbhh E_bb))))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= v_bbhh E_bb)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (= v_bbhh E_bb)))
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= v_bbhh E_bb)))
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= v_bbhh E_bb))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= v_bbhh E_bb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))
  (and (and (= v_bbhh E_gg) (= v_bbbb 1)) (= v_bbii v_bbgg)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= v_bbhh E_bb)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (= v_bbhh E_bb)))))) (<= (+ (+ v_zz 1) 1) v_vv))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= v_bbhh E_bb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))
  (= v_bbhh E_ee))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))
  (= v_bbhh E_gg)) (= v_bbii (+ v_bbgg 1)))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))
  (= v_bbhh E_gg)) (= v_bbii v_bbgg)) (= v_bbbb 1)))) (= v_bbdd false)))))

(declare-fun f31 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f31_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f31 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
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
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false)) (mem
  int (t2tb3 (+ v_bbgg 1)) (t2tb2 integer))) (<= 0 (+ v_bbgg 1)))
  (=> (= v_bbhh E_gg) (= (- (+ v_bbgg 1) v_bbii) v_bbbb)))
  (=> (= v_bbhh E_hh)
  (and
  (and (= (- (- (+ v_bbgg 1) 1) v_bbii) v_bbbb) (<= v_bbaa (+ v_bbbb v_xx)))
  (<= v_bbbb v_ww))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ff)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_ii)))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ff)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_hh))) (= v_bbhh E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))
  (or (<= (+ (- v_bbgg v_bbii) 1) (+ v_ww v_bbjj))
  (and (not (<= (+ (- v_bbgg v_bbii) 1) (+ v_ww v_bbjj))) (= v_bbhh E_bb))))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= v_bbhh E_bb)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (= v_bbhh E_bb)))
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= v_bbhh E_bb)))
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= v_bbhh E_bb))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= v_bbhh E_bb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))
  (and (and (= v_bbhh E_gg) (= v_bbbb 1)) (= v_bbii v_bbgg)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= v_bbhh E_bb)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (= v_bbhh E_bb)))))) (<= (+ (+ v_zz 1) 1) v_vv))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= v_bbhh E_bb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))
  (= v_bbhh E_ee))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))
  (= v_bbhh E_gg)) (= v_bbii (+ v_bbgg 1)))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))
  (= v_bbhh E_gg)) (= v_bbii v_bbgg)) (= v_bbbb 1)))) (not (= v_bbcc false)))
  (not (= v_bbdd false))) (not (= v_bbee true))) (not (= v_bbff true))))))

(declare-fun f33 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f33_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f33 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
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
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false)) (mem
  int (t2tb3 (+ v_bbgg 1)) (t2tb2 integer))) (<= 0 (+ v_bbgg 1)))
  (=> (= v_bbhh E_gg) (= (- (+ v_bbgg 1) v_bbii) v_bbbb)))
  (=> (= v_bbhh E_hh)
  (and
  (and (= (- (- (+ v_bbgg 1) 1) v_bbii) v_bbbb) (<= v_bbaa (+ v_bbbb v_xx)))
  (<= v_bbbb v_ww))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ff)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_ii)))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ff)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_hh))) (= v_bbhh E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))
  (or (<= (+ (- v_bbgg v_bbii) 1) (+ v_ww v_bbjj))
  (and (not (<= (+ (- v_bbgg v_bbii) 1) (+ v_ww v_bbjj))) (= v_bbhh E_bb))))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= v_bbhh E_bb)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (= v_bbhh E_bb)))
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= v_bbhh E_bb)))
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= v_bbhh E_bb))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= v_bbhh E_bb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))
  (and (and (= v_bbhh E_gg) (= v_bbbb 1)) (= v_bbii v_bbgg)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= v_bbhh E_bb)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (= v_bbhh E_bb)))))) (not (<= (+ (+ v_zz 1) 1) v_vv)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= v_bbhh E_bb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))
  (= v_bbhh E_ee))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))
  (= v_bbhh E_gg)) (= v_bbii (+ v_bbgg 1)))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))
  (= v_bbhh E_gg)) (= v_bbii v_bbgg)) (= v_bbbb 1)))) (= v_bbcc false)))))

(declare-fun f34 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f34_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f34 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
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
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false)) (mem
  int (t2tb3 (+ v_bbgg 1)) (t2tb2 integer))) (<= 0 (+ v_bbgg 1)))
  (=> (= v_bbhh E_gg) (= (- (+ v_bbgg 1) v_bbii) v_bbbb)))
  (=> (= v_bbhh E_hh)
  (and
  (and (= (- (- (+ v_bbgg 1) 1) v_bbii) v_bbbb) (<= v_bbaa (+ v_bbbb v_xx)))
  (<= v_bbbb v_ww))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ff)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_ii)))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ff)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_hh))) (= v_bbhh E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))
  (or (<= (+ (- v_bbgg v_bbii) 1) (+ v_ww v_bbjj))
  (and (not (<= (+ (- v_bbgg v_bbii) 1) (+ v_ww v_bbjj))) (= v_bbhh E_bb))))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= v_bbhh E_bb)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (= v_bbhh E_bb)))
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= v_bbhh E_bb)))
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= v_bbhh E_bb))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= v_bbhh E_bb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))
  (and (and (= v_bbhh E_gg) (= v_bbbb 1)) (= v_bbii v_bbgg)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= v_bbhh E_bb)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (= v_bbhh E_bb)))))) (not (<= (+ (+ v_zz 1) 1) v_vv)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= v_bbhh E_bb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))
  (= v_bbhh E_ee))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))
  (= v_bbhh E_gg)) (= v_bbii (+ v_bbgg 1)))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))
  (= v_bbhh E_gg)) (= v_bbii v_bbgg)) (= v_bbbb 1)))) (= v_bbdd false)))))

(declare-fun f35 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f35_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f35 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
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
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false)) (mem
  int (t2tb3 (+ v_bbgg 1)) (t2tb2 integer))) (<= 0 (+ v_bbgg 1)))
  (=> (= v_bbhh E_gg) (= (- (+ v_bbgg 1) v_bbii) v_bbbb)))
  (=> (= v_bbhh E_hh)
  (and
  (and (= (- (- (+ v_bbgg 1) 1) v_bbii) v_bbbb) (<= v_bbaa (+ v_bbbb v_xx)))
  (<= v_bbbb v_ww))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ff)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_ii)))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ff)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_hh))) (= v_bbhh E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))
  (or (<= (+ (- v_bbgg v_bbii) 1) (+ v_ww v_bbjj))
  (and (not (<= (+ (- v_bbgg v_bbii) 1) (+ v_ww v_bbjj))) (= v_bbhh E_bb))))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= v_bbhh E_bb)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (= v_bbhh E_bb)))
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= v_bbhh E_bb)))
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= v_bbhh E_bb))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= v_bbhh E_bb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))
  (and (and (= v_bbhh E_gg) (= v_bbbb 1)) (= v_bbii v_bbgg)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= v_bbhh E_bb)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (= v_bbhh E_bb)))))) (not (<= (+ (+ v_zz 1) 1) v_vv)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= v_bbhh E_bb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))
  (= v_bbhh E_ee))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))
  (= v_bbhh E_gg)) (= v_bbii (+ v_bbgg 1)))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))
  (= v_bbhh E_gg)) (= v_bbii v_bbgg)) (= v_bbbb 1)))) (not (= v_bbcc false)))
  (not (= v_bbdd false))) (not (= v_bbee true))) (not (= v_bbff true))))))

(declare-fun f36 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f36_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f36 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
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
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false)) (mem
  int (t2tb3 (+ v_bbgg 1)) (t2tb2 integer))) (<= 0 (+ v_bbgg 1)))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_zz 0)))
  (=> (= E_gg E_cc) (<= v_yy v_uu))) (=> (= E_gg E_ee) (<= v_zz v_vv)))
  (=> (= E_gg E_ff) (<= v_zz (+ v_vv 1))))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbaa 0)))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbbb 0)))
  (<= v_bbbb 1)) (= (- (+ v_bbgg 1) (+ v_bbgg 1)) v_bbbb))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_gg) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_hh) (empty enum_aa1))))
  (and (<= v_bbaa (+ (+ v_ww v_xx) 1)) (<= v_zz (+ (+ v_vv v_bbaa) 2)))))
  (=> (= E_gg E_hh)
  (and
  (and (= (- (- (+ v_bbgg 1) 1) (+ v_bbgg 1)) v_bbbb)
  (<= v_bbaa (+ v_bbbb v_xx))) (<= v_bbbb v_ww))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ff)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_hh))) (= v_bbhh E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))
  (and (not (<= (+ (- v_bbgg v_bbii) 1) (+ v_ww v_bbjj))) (= E_gg E_bb)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= E_gg E_bb)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (= E_gg E_bb)))
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= E_gg E_bb)))
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_gg E_bb)))) (= (+ v_bbgg 1) v_bbii))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_gg E_bb)) (= (+ v_bbgg 1) v_bbii))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (or
  (and
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= E_gg E_bb)) (= (+ v_bbgg 1) v_bbii))
  (and
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (= E_gg E_bb)) (= (+ v_bbgg 1) v_bbii))))))
  (<= (+ (+ v_zz 1) 1) v_vv))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_gg E_bb)) (= (+ v_bbgg 1) v_bbii))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))
  (= E_gg E_ee)) (= (+ v_bbgg 1) v_bbii))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))))
  (= v_bbcc false)))))

(declare-fun f37 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f37_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f37 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
  v_bbhh v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (= (+ v_bbgg 1) v_bbii))))

(declare-fun f38 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f38_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f38 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
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
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false)) (mem
  int (t2tb3 (+ v_bbgg 1)) (t2tb2 integer))) (<= 0 (+ v_bbgg 1)))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_zz 0)))
  (=> (= E_gg E_cc) (<= v_yy v_uu))) (=> (= E_gg E_ee) (<= v_zz v_vv)))
  (=> (= E_gg E_ff) (<= v_zz (+ v_vv 1))))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbaa 0)))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbbb 0)))
  (<= v_bbbb 1)) (= (- (+ v_bbgg 1) (+ v_bbgg 1)) v_bbbb))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_gg) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_hh) (empty enum_aa1))))
  (and (<= v_bbaa (+ (+ v_ww v_xx) 1)) (<= v_zz (+ (+ v_vv v_bbaa) 2)))))
  (=> (= E_gg E_hh)
  (and
  (and (= (- (- (+ v_bbgg 1) 1) (+ v_bbgg 1)) v_bbbb)
  (<= v_bbaa (+ v_bbbb v_xx))) (<= v_bbbb v_ww))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ff)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_hh))) (= v_bbhh E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))
  (and (not (<= (+ (- v_bbgg v_bbii) 1) (+ v_ww v_bbjj))) (= E_gg E_bb)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= E_gg E_bb)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (= E_gg E_bb)))
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= E_gg E_bb)))
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_gg E_bb)))) (= (+ v_bbgg 1) v_bbii))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_gg E_bb)) (= (+ v_bbgg 1) v_bbii))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (or
  (and
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= E_gg E_bb)) (= (+ v_bbgg 1) v_bbii))
  (and
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (= E_gg E_bb)) (= (+ v_bbgg 1) v_bbii))))))
  (<= (+ (+ v_zz 1) 1) v_vv))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_gg E_bb)) (= (+ v_bbgg 1) v_bbii))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))
  (= E_gg E_ee)) (= (+ v_bbgg 1) v_bbii))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))))
  (= v_bbdd false)))))

(declare-fun f39 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f39_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f39 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
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
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false)) (mem
  int (t2tb3 (+ v_bbgg 1)) (t2tb2 integer))) (<= 0 (+ v_bbgg 1)))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_zz 0)))
  (=> (= E_gg E_cc) (<= v_yy v_uu))) (=> (= E_gg E_ee) (<= v_zz v_vv)))
  (=> (= E_gg E_ff) (<= v_zz (+ v_vv 1))))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbaa 0)))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbbb 0)))
  (<= v_bbbb 1)) (= (- (+ v_bbgg 1) (+ v_bbgg 1)) v_bbbb))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_gg) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_hh) (empty enum_aa1))))
  (and (<= v_bbaa (+ (+ v_ww v_xx) 1)) (<= v_zz (+ (+ v_vv v_bbaa) 2)))))
  (=> (= E_gg E_hh)
  (and
  (and (= (- (- (+ v_bbgg 1) 1) (+ v_bbgg 1)) v_bbbb)
  (<= v_bbaa (+ v_bbbb v_xx))) (<= v_bbbb v_ww))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ff)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_hh))) (= v_bbhh E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))
  (and (not (<= (+ (- v_bbgg v_bbii) 1) (+ v_ww v_bbjj))) (= E_gg E_bb)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= E_gg E_bb)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (= E_gg E_bb)))
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= E_gg E_bb)))
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_gg E_bb)))) (= (+ v_bbgg 1) v_bbii))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_gg E_bb)) (= (+ v_bbgg 1) v_bbii))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (or
  (and
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= E_gg E_bb)) (= (+ v_bbgg 1) v_bbii))
  (and
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (= E_gg E_bb)) (= (+ v_bbgg 1) v_bbii))))))
  (<= (+ (+ v_zz 1) 1) v_vv))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_gg E_bb)) (= (+ v_bbgg 1) v_bbii))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))
  (= E_gg E_ee)) (= (+ v_bbgg 1) v_bbii))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false)))))))

(declare-fun f40 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f40_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f40 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
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
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false)) (mem
  int (t2tb3 (+ v_bbgg 1)) (t2tb2 integer))) (<= 0 (+ v_bbgg 1)))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_zz 0)))
  (=> (= E_gg E_cc) (<= v_yy v_uu))) (=> (= E_gg E_ee) (<= v_zz v_vv)))
  (=> (= E_gg E_ff) (<= v_zz (+ v_vv 1))))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbaa 0)))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbbb 0)))
  (<= v_bbbb 1)) (= (- (+ v_bbgg 1) (+ v_bbgg 1)) v_bbbb))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_gg) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_hh) (empty enum_aa1))))
  (and (<= v_bbaa (+ (+ v_ww v_xx) 1)) (<= v_zz (+ (+ v_vv v_bbaa) 2)))))
  (=> (= E_gg E_hh)
  (and
  (and (= (- (- (+ v_bbgg 1) 1) (+ v_bbgg 1)) v_bbbb)
  (<= v_bbaa (+ v_bbbb v_xx))) (<= v_bbbb v_ww))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ff)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_hh))) (= v_bbhh E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))
  (and (not (<= (+ (- v_bbgg v_bbii) 1) (+ v_ww v_bbjj))) (= E_gg E_bb)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= E_gg E_bb)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (= E_gg E_bb)))
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= E_gg E_bb)))
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_gg E_bb)))) (= (+ v_bbgg 1) v_bbii))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_gg E_bb)) (= (+ v_bbgg 1) v_bbii))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (or
  (and
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= E_gg E_bb)) (= (+ v_bbgg 1) v_bbii))
  (and
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (= E_gg E_bb)) (= (+ v_bbgg 1) v_bbii))))))
  (not (<= (+ (+ v_zz 1) 1) v_vv)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_gg E_bb)) (= (+ v_bbgg 1) v_bbii))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))
  (= E_gg E_ee)) (= (+ v_bbgg 1) v_bbii))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))))
  (= v_bbcc false)))))

(declare-fun f41 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f41_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f41 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
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
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false)) (mem
  int (t2tb3 (+ v_bbgg 1)) (t2tb2 integer))) (<= 0 (+ v_bbgg 1)))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_zz 0)))
  (=> (= E_gg E_cc) (<= v_yy v_uu))) (=> (= E_gg E_ee) (<= v_zz v_vv)))
  (=> (= E_gg E_ff) (<= v_zz (+ v_vv 1))))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbaa 0)))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbbb 0)))
  (<= v_bbbb 1)) (= (- (+ v_bbgg 1) (+ v_bbgg 1)) v_bbbb))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_gg) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_hh) (empty enum_aa1))))
  (and (<= v_bbaa (+ (+ v_ww v_xx) 1)) (<= v_zz (+ (+ v_vv v_bbaa) 2)))))
  (=> (= E_gg E_hh)
  (and
  (and (= (- (- (+ v_bbgg 1) 1) (+ v_bbgg 1)) v_bbbb)
  (<= v_bbaa (+ v_bbbb v_xx))) (<= v_bbbb v_ww))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ff)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_hh))) (= v_bbhh E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))
  (and (not (<= (+ (- v_bbgg v_bbii) 1) (+ v_ww v_bbjj))) (= E_gg E_bb)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= E_gg E_bb)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (= E_gg E_bb)))
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= E_gg E_bb)))
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_gg E_bb)))) (= (+ v_bbgg 1) v_bbii))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_gg E_bb)) (= (+ v_bbgg 1) v_bbii))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (or
  (and
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= E_gg E_bb)) (= (+ v_bbgg 1) v_bbii))
  (and
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (= E_gg E_bb)) (= (+ v_bbgg 1) v_bbii))))))
  (not (<= (+ (+ v_zz 1) 1) v_vv)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_gg E_bb)) (= (+ v_bbgg 1) v_bbii))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))
  (= E_gg E_ee)) (= (+ v_bbgg 1) v_bbii))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))))
  (= v_bbdd false)))))

(declare-fun f42 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f42_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f42 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
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
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false)) (mem
  int (t2tb3 (+ v_bbgg 1)) (t2tb2 integer))) (<= 0 (+ v_bbgg 1)))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_zz 0)))
  (=> (= E_gg E_cc) (<= v_yy v_uu))) (=> (= E_gg E_ee) (<= v_zz v_vv)))
  (=> (= E_gg E_ff) (<= v_zz (+ v_vv 1))))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbaa 0)))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbbb 0)))
  (<= v_bbbb 1)) (= (- (+ v_bbgg 1) (+ v_bbgg 1)) v_bbbb))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_gg) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_hh) (empty enum_aa1))))
  (and (<= v_bbaa (+ (+ v_ww v_xx) 1)) (<= v_zz (+ (+ v_vv v_bbaa) 2)))))
  (=> (= E_gg E_hh)
  (and
  (and (= (- (- (+ v_bbgg 1) 1) (+ v_bbgg 1)) v_bbbb)
  (<= v_bbaa (+ v_bbbb v_xx))) (<= v_bbbb v_ww))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ff)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_hh))) (= v_bbhh E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))
  (and (not (<= (+ (- v_bbgg v_bbii) 1) (+ v_ww v_bbjj))) (= E_gg E_bb)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= E_gg E_bb)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (= E_gg E_bb)))
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= E_gg E_bb)))
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_gg E_bb)))) (= (+ v_bbgg 1) v_bbii))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_gg E_bb)) (= (+ v_bbgg 1) v_bbii))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (or
  (and
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= E_gg E_bb)) (= (+ v_bbgg 1) v_bbii))
  (and
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (= E_gg E_bb)) (= (+ v_bbgg 1) v_bbii))))))
  (not (<= (+ (+ v_zz 1) 1) v_vv)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_gg E_bb)) (= (+ v_bbgg 1) v_bbii))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))
  (= E_gg E_ee)) (= (+ v_bbgg 1) v_bbii))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false)))))))

(declare-fun f43 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f43_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f43 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
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
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false)) (mem
  int (t2tb3 (+ v_bbgg 1)) (t2tb2 integer))) (<= 0 (+ v_bbgg 1)))
  (=> (mem enum_aa1 (t2tb5 E_ee)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_zz 0)))
  (=> (= E_ee E_cc) (<= v_yy v_uu))) (<= v_zz v_vv))
  (=> (= E_ee E_ff) (<= v_zz (+ v_vv 1))))
  (=> (mem enum_aa1 (t2tb5 E_ee)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbaa 0)))
  (=> (mem enum_aa1 (t2tb5 E_ee)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbbb 0)))
  (=> (= E_ee E_gg) (<= v_bbbb 1)))
  (=> (= E_ee E_gg) (= (- (+ v_bbgg 1) v_bbii) v_bbbb)))
  (=> (mem enum_aa1 (t2tb5 E_ee)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_gg) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_hh) (empty enum_aa1))))
  (and (<= v_bbaa (+ (+ v_ww v_xx) 1)) (<= v_zz (+ (+ v_vv v_bbaa) 2)))))
  (=> (= E_ee E_hh)
  (and
  (and (= (- (- (+ v_bbgg 1) 1) v_bbii) v_bbbb) (<= v_bbaa (+ v_bbbb v_xx)))
  (<= v_bbbb v_ww))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ff)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_hh))) (= v_bbhh E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))
  (and (not (<= (+ (- v_bbgg v_bbii) 1) (+ v_ww v_bbjj))) (= E_ee E_bb)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= E_ee E_bb)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (= E_ee E_bb)))
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= E_ee E_bb)))
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_ee E_bb))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_ee E_bb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (and (and (= E_ee E_gg) (= v_bbbb 1)) (= v_bbii v_bbgg)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= E_ee E_bb)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (= E_ee E_bb)))))) (<= (+ (+ v_zz 1) 1) v_vv))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_ee E_bb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))
  (= E_ee E_gg)) (= v_bbii (+ v_bbgg 1)))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))
  (= E_ee E_gg)) (= v_bbii v_bbgg)) (= v_bbbb 1)))))))

(declare-fun f45 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f45_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f45 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
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
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false)) (mem
  int (t2tb3 (+ v_bbgg 1)) (t2tb2 integer))) (<= 0 (+ v_bbgg 1)))
  (=> (mem enum_aa1 (t2tb5 E_ee)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_zz 0)))
  (=> (= E_ee E_cc) (<= v_yy v_uu))) (<= v_zz v_vv))
  (=> (= E_ee E_ff) (<= v_zz (+ v_vv 1))))
  (=> (mem enum_aa1 (t2tb5 E_ee)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbaa 0)))
  (=> (mem enum_aa1 (t2tb5 E_ee)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbbb 0)))
  (=> (= E_ee E_gg) (<= v_bbbb 1)))
  (=> (= E_ee E_gg) (= (- (+ v_bbgg 1) v_bbii) v_bbbb)))
  (=> (mem enum_aa1 (t2tb5 E_ee)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_gg) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_hh) (empty enum_aa1))))
  (and (<= v_bbaa (+ (+ v_ww v_xx) 1)) (<= v_zz (+ (+ v_vv v_bbaa) 2)))))
  (=> (= E_ee E_hh)
  (and
  (and (= (- (- (+ v_bbgg 1) 1) v_bbii) v_bbbb) (<= v_bbaa (+ v_bbbb v_xx)))
  (<= v_bbbb v_ww))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ff)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_hh))) (= v_bbhh E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))
  (and (not (<= (+ (- v_bbgg v_bbii) 1) (+ v_ww v_bbjj))) (= E_ee E_bb)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= E_ee E_bb)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (= E_ee E_bb)))
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= E_ee E_bb)))
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_ee E_bb))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_ee E_bb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (and (and (= E_ee E_gg) (= v_bbbb 1)) (= v_bbii v_bbgg)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= E_ee E_bb)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (= E_ee E_bb)))))) (<= (+ (+ v_zz 1) 1) v_vv))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_ee E_bb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))
  (= E_ee E_gg)) (= v_bbii (+ v_bbgg 1)))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))
  (= E_ee E_gg)) (= v_bbii v_bbgg)) (= v_bbbb 1)))) (= v_bbdd false)))))

(declare-fun f46 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f46_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f46 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
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
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false)) (mem
  int (t2tb3 (+ v_bbgg 1)) (t2tb2 integer))) (<= 0 (+ v_bbgg 1)))
  (=> (mem enum_aa1 (t2tb5 E_ee)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_zz 0)))
  (=> (= E_ee E_cc) (<= v_yy v_uu))) (<= v_zz v_vv))
  (=> (= E_ee E_ff) (<= v_zz (+ v_vv 1))))
  (=> (mem enum_aa1 (t2tb5 E_ee)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbaa 0)))
  (=> (mem enum_aa1 (t2tb5 E_ee)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbbb 0)))
  (=> (= E_ee E_gg) (<= v_bbbb 1)))
  (=> (= E_ee E_gg) (= (- (+ v_bbgg 1) v_bbii) v_bbbb)))
  (=> (mem enum_aa1 (t2tb5 E_ee)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_gg) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_hh) (empty enum_aa1))))
  (and (<= v_bbaa (+ (+ v_ww v_xx) 1)) (<= v_zz (+ (+ v_vv v_bbaa) 2)))))
  (=> (= E_ee E_hh)
  (and
  (and (= (- (- (+ v_bbgg 1) 1) v_bbii) v_bbbb) (<= v_bbaa (+ v_bbbb v_xx)))
  (<= v_bbbb v_ww))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ff)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_hh))) (= v_bbhh E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))
  (and (not (<= (+ (- v_bbgg v_bbii) 1) (+ v_ww v_bbjj))) (= E_ee E_bb)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= E_ee E_bb)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (= E_ee E_bb)))
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= E_ee E_bb)))
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_ee E_bb))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_ee E_bb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (and (and (= E_ee E_gg) (= v_bbbb 1)) (= v_bbii v_bbgg)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= E_ee E_bb)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (= E_ee E_bb)))))) (not (<= (+ (+ v_zz 1) 1) v_vv)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_ee E_bb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))
  (= E_ee E_gg)) (= v_bbii (+ v_bbgg 1)))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))
  (= E_ee E_gg)) (= v_bbii v_bbgg)) (= v_bbbb 1)))))))

(declare-fun f47 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f47_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f47 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
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
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false)) (mem
  int (t2tb3 (+ v_bbgg 1)) (t2tb2 integer))) (<= 0 (+ v_bbgg 1)))
  (=> (mem enum_aa1 (t2tb5 E_ee)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_zz 0)))
  (=> (= E_ee E_cc) (<= v_yy v_uu))) (<= v_zz v_vv))
  (=> (= E_ee E_ff) (<= v_zz (+ v_vv 1))))
  (=> (mem enum_aa1 (t2tb5 E_ee)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbaa 0)))
  (=> (mem enum_aa1 (t2tb5 E_ee)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbbb 0)))
  (=> (= E_ee E_gg) (<= v_bbbb 1)))
  (=> (= E_ee E_gg) (= (- (+ v_bbgg 1) v_bbii) v_bbbb)))
  (=> (mem enum_aa1 (t2tb5 E_ee)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_gg) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_hh) (empty enum_aa1))))
  (and (<= v_bbaa (+ (+ v_ww v_xx) 1)) (<= v_zz (+ (+ v_vv v_bbaa) 2)))))
  (=> (= E_ee E_hh)
  (and
  (and (= (- (- (+ v_bbgg 1) 1) v_bbii) v_bbbb) (<= v_bbaa (+ v_bbbb v_xx)))
  (<= v_bbbb v_ww))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ff)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_hh))) (= v_bbhh E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))
  (and (not (<= (+ (- v_bbgg v_bbii) 1) (+ v_ww v_bbjj))) (= E_ee E_bb)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= E_ee E_bb)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (= E_ee E_bb)))
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= E_ee E_bb)))
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_ee E_bb))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_ee E_bb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (and (and (= E_ee E_gg) (= v_bbbb 1)) (= v_bbii v_bbgg)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (= E_ee E_bb)))
  (and
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (= E_ee E_bb)))))) (not (<= (+ (+ v_zz 1) 1) v_vv)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_ee E_bb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))
  (= E_ee E_gg)) (= v_bbii (+ v_bbgg 1)))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))
  (= E_ee E_gg)) (= v_bbii v_bbgg)) (= v_bbbb 1)))) (= v_bbdd false)))))

(declare-fun f48 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f48_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f48 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
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
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee)))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= v_bbhh E_dd)) (mem int (t2tb3 (+ v_bbgg 1))
  (t2tb2 integer))) (<= 0 (+ v_bbgg 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_zz 0)))
  (=> (= E_bb E_cc) (<= v_yy v_uu))) (=> (= E_bb E_ee) (<= v_zz v_vv)))
  (=> (= E_bb E_ff) (<= v_zz (+ v_vv 1))))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbaa 0)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbbb 0)))
  (=> (= E_bb E_gg) (<= v_bbbb 1)))
  (=> (= E_bb E_gg) (= (- (+ v_bbgg 1) v_bbii) v_bbbb)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_gg) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_hh) (empty enum_aa1))))
  (and (<= v_bbaa (+ (+ v_ww v_xx) 1)) (<= v_zz (+ (+ v_vv v_bbaa) 2)))))
  (=> (= E_bb E_hh)
  (and
  (and (= (- (- (+ v_bbgg 1) 1) v_bbii) v_bbbb) (<= v_bbaa (+ v_bbbb v_xx)))
  (<= v_bbbb v_ww))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ff)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_hh))) (= v_bbhh E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (not (<= (+ (- v_bbgg v_bbii) 1) (+ v_ww v_bbjj))))
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (and (and (= E_bb E_gg) (= v_bbbb 1)) (= v_bbii v_bbgg)))
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))))) (<= (+ (+ v_zz 1) 1) v_vv))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))
  (= E_bb E_ee))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))
  (= E_bb E_gg)) (= v_bbii (+ v_bbgg 1)))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))
  (= E_bb E_gg)) (= v_bbii v_bbgg)) (= v_bbbb 1)))) (= v_bbcc false)))))

(declare-fun f49 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f49_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f49 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
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
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee)))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= v_bbhh E_dd)) (mem int (t2tb3 (+ v_bbgg 1))
  (t2tb2 integer))) (<= 0 (+ v_bbgg 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_zz 0)))
  (=> (= E_bb E_cc) (<= v_yy v_uu))) (=> (= E_bb E_ee) (<= v_zz v_vv)))
  (=> (= E_bb E_ff) (<= v_zz (+ v_vv 1))))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbaa 0)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbbb 0)))
  (=> (= E_bb E_gg) (<= v_bbbb 1)))
  (=> (= E_bb E_gg) (= (- (+ v_bbgg 1) v_bbii) v_bbbb)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_gg) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_hh) (empty enum_aa1))))
  (and (<= v_bbaa (+ (+ v_ww v_xx) 1)) (<= v_zz (+ (+ v_vv v_bbaa) 2)))))
  (=> (= E_bb E_hh)
  (and
  (and (= (- (- (+ v_bbgg 1) 1) v_bbii) v_bbbb) (<= v_bbaa (+ v_bbbb v_xx)))
  (<= v_bbbb v_ww))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ff)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_hh))) (= v_bbhh E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (not (<= (+ (- v_bbgg v_bbii) 1) (+ v_ww v_bbjj))))
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (and (and (= E_bb E_gg) (= v_bbbb 1)) (= v_bbii v_bbgg)))
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))))) (<= (+ (+ v_zz 1) 1) v_vv))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))
  (= E_bb E_ee))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))
  (= E_bb E_gg)) (= v_bbii (+ v_bbgg 1)))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))
  (= E_bb E_gg)) (= v_bbii v_bbgg)) (= v_bbbb 1)))) (= v_bbdd false)))))

(declare-fun f50 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f50_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f50 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
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
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee)))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= v_bbhh E_dd)) (mem int (t2tb3 (+ v_bbgg 1))
  (t2tb2 integer))) (<= 0 (+ v_bbgg 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_zz 0)))
  (=> (= E_bb E_cc) (<= v_yy v_uu))) (=> (= E_bb E_ee) (<= v_zz v_vv)))
  (=> (= E_bb E_ff) (<= v_zz (+ v_vv 1))))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbaa 0)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbbb 0)))
  (=> (= E_bb E_gg) (<= v_bbbb 1)))
  (=> (= E_bb E_gg) (= (- (+ v_bbgg 1) v_bbii) v_bbbb)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_gg) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_hh) (empty enum_aa1))))
  (and (<= v_bbaa (+ (+ v_ww v_xx) 1)) (<= v_zz (+ (+ v_vv v_bbaa) 2)))))
  (=> (= E_bb E_hh)
  (and
  (and (= (- (- (+ v_bbgg 1) 1) v_bbii) v_bbbb) (<= v_bbaa (+ v_bbbb v_xx)))
  (<= v_bbbb v_ww))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ff)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_hh))) (= v_bbhh E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (not (<= (+ (- v_bbgg v_bbii) 1) (+ v_ww v_bbjj))))
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (and (and (= E_bb E_gg) (= v_bbbb 1)) (= v_bbii v_bbgg)))
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))))) (<= (+ (+ v_zz 1) 1) v_vv))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))
  (= E_bb E_ee))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))
  (= E_bb E_gg)) (= v_bbii (+ v_bbgg 1)))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))
  (= E_bb E_gg)) (= v_bbii v_bbgg)) (= v_bbbb 1)))) (= v_bbee true)))))

(declare-fun f51 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f51_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f51 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
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
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee)))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= v_bbhh E_dd)) (mem int (t2tb3 (+ v_bbgg 1))
  (t2tb2 integer))) (<= 0 (+ v_bbgg 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_zz 0)))
  (=> (= E_bb E_cc) (<= v_yy v_uu))) (=> (= E_bb E_ee) (<= v_zz v_vv)))
  (=> (= E_bb E_ff) (<= v_zz (+ v_vv 1))))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbaa 0)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbbb 0)))
  (=> (= E_bb E_gg) (<= v_bbbb 1)))
  (=> (= E_bb E_gg) (= (- (+ v_bbgg 1) v_bbii) v_bbbb)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_gg) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_hh) (empty enum_aa1))))
  (and (<= v_bbaa (+ (+ v_ww v_xx) 1)) (<= v_zz (+ (+ v_vv v_bbaa) 2)))))
  (=> (= E_bb E_hh)
  (and
  (and (= (- (- (+ v_bbgg 1) 1) v_bbii) v_bbbb) (<= v_bbaa (+ v_bbbb v_xx)))
  (<= v_bbbb v_ww))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ff)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_hh))) (= v_bbhh E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (not (<= (+ (- v_bbgg v_bbii) 1) (+ v_ww v_bbjj))))
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (and (and (= E_bb E_gg) (= v_bbbb 1)) (= v_bbii v_bbgg)))
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))))) (<= (+ (+ v_zz 1) 1) v_vv))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))
  (= E_bb E_ee))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))
  (= E_bb E_gg)) (= v_bbii (+ v_bbgg 1)))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))
  (= E_bb E_gg)) (= v_bbii v_bbgg)) (= v_bbbb 1)))) (= v_bbff true)))))

(declare-fun f52 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f52_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f52 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
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
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee)))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= v_bbhh E_dd)) (mem int (t2tb3 (+ v_bbgg 1))
  (t2tb2 integer))) (<= 0 (+ v_bbgg 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_zz 0)))
  (=> (= E_bb E_cc) (<= v_yy v_uu))) (=> (= E_bb E_ee) (<= v_zz v_vv)))
  (=> (= E_bb E_ff) (<= v_zz (+ v_vv 1))))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbaa 0)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbbb 0)))
  (=> (= E_bb E_gg) (<= v_bbbb 1)))
  (=> (= E_bb E_gg) (= (- (+ v_bbgg 1) v_bbii) v_bbbb)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_gg) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_hh) (empty enum_aa1))))
  (and (<= v_bbaa (+ (+ v_ww v_xx) 1)) (<= v_zz (+ (+ v_vv v_bbaa) 2)))))
  (=> (= E_bb E_hh)
  (and
  (and (= (- (- (+ v_bbgg 1) 1) v_bbii) v_bbbb) (<= v_bbaa (+ v_bbbb v_xx)))
  (<= v_bbbb v_ww))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ff)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_hh))) (= v_bbhh E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (not (<= (+ (- v_bbgg v_bbii) 1) (+ v_ww v_bbjj))))
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (and (and (= E_bb E_gg) (= v_bbbb 1)) (= v_bbii v_bbgg)))
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))))) (<= (+ (+ v_zz 1) 1) v_vv))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))
  (= E_bb E_ee))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))
  (= E_bb E_gg)) (= v_bbii (+ v_bbgg 1)))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))
  (= E_bb E_gg)) (= v_bbii v_bbgg)) (= v_bbbb 1)))) (not (= v_bbcc false)))
  (not (= v_bbdd false))) (not (= v_bbee true))) (not (= v_bbff true))))))

(declare-fun f54 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f54_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f54 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
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
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee)))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= v_bbhh E_dd)) (mem int (t2tb3 (+ v_bbgg 1))
  (t2tb2 integer))) (<= 0 (+ v_bbgg 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_zz 0)))
  (=> (= E_bb E_cc) (<= v_yy v_uu))) (=> (= E_bb E_ee) (<= v_zz v_vv)))
  (=> (= E_bb E_ff) (<= v_zz (+ v_vv 1))))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbaa 0)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbbb 0)))
  (=> (= E_bb E_gg) (<= v_bbbb 1)))
  (=> (= E_bb E_gg) (= (- (+ v_bbgg 1) v_bbii) v_bbbb)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_gg) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_hh) (empty enum_aa1))))
  (and (<= v_bbaa (+ (+ v_ww v_xx) 1)) (<= v_zz (+ (+ v_vv v_bbaa) 2)))))
  (=> (= E_bb E_hh)
  (and
  (and (= (- (- (+ v_bbgg 1) 1) v_bbii) v_bbbb) (<= v_bbaa (+ v_bbbb v_xx)))
  (<= v_bbbb v_ww))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ff)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_hh))) (= v_bbhh E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (not (<= (+ (- v_bbgg v_bbii) 1) (+ v_ww v_bbjj))))
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (and (and (= E_bb E_gg) (= v_bbbb 1)) (= v_bbii v_bbgg)))
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))))) (not (<= (+ (+ v_zz 1) 1) v_vv)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))
  (= E_bb E_ee))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))
  (= E_bb E_gg)) (= v_bbii (+ v_bbgg 1)))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))
  (= E_bb E_gg)) (= v_bbii v_bbgg)) (= v_bbbb 1)))) (= v_bbcc false)))))

(declare-fun f55 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f55_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f55 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
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
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee)))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= v_bbhh E_dd)) (mem int (t2tb3 (+ v_bbgg 1))
  (t2tb2 integer))) (<= 0 (+ v_bbgg 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_zz 0)))
  (=> (= E_bb E_cc) (<= v_yy v_uu))) (=> (= E_bb E_ee) (<= v_zz v_vv)))
  (=> (= E_bb E_ff) (<= v_zz (+ v_vv 1))))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbaa 0)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbbb 0)))
  (=> (= E_bb E_gg) (<= v_bbbb 1)))
  (=> (= E_bb E_gg) (= (- (+ v_bbgg 1) v_bbii) v_bbbb)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_gg) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_hh) (empty enum_aa1))))
  (and (<= v_bbaa (+ (+ v_ww v_xx) 1)) (<= v_zz (+ (+ v_vv v_bbaa) 2)))))
  (=> (= E_bb E_hh)
  (and
  (and (= (- (- (+ v_bbgg 1) 1) v_bbii) v_bbbb) (<= v_bbaa (+ v_bbbb v_xx)))
  (<= v_bbbb v_ww))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ff)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_hh))) (= v_bbhh E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (not (<= (+ (- v_bbgg v_bbii) 1) (+ v_ww v_bbjj))))
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (and (and (= E_bb E_gg) (= v_bbbb 1)) (= v_bbii v_bbgg)))
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))))) (not (<= (+ (+ v_zz 1) 1) v_vv)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))
  (= E_bb E_ee))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))
  (= E_bb E_gg)) (= v_bbii (+ v_bbgg 1)))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))
  (= E_bb E_gg)) (= v_bbii v_bbgg)) (= v_bbbb 1)))) (= v_bbdd false)))))

(declare-fun f56 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f56_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f56 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
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
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee)))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= v_bbhh E_dd)) (mem int (t2tb3 (+ v_bbgg 1))
  (t2tb2 integer))) (<= 0 (+ v_bbgg 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_zz 0)))
  (=> (= E_bb E_cc) (<= v_yy v_uu))) (=> (= E_bb E_ee) (<= v_zz v_vv)))
  (=> (= E_bb E_ff) (<= v_zz (+ v_vv 1))))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbaa 0)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbbb 0)))
  (=> (= E_bb E_gg) (<= v_bbbb 1)))
  (=> (= E_bb E_gg) (= (- (+ v_bbgg 1) v_bbii) v_bbbb)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_gg) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_hh) (empty enum_aa1))))
  (and (<= v_bbaa (+ (+ v_ww v_xx) 1)) (<= v_zz (+ (+ v_vv v_bbaa) 2)))))
  (=> (= E_bb E_hh)
  (and
  (and (= (- (- (+ v_bbgg 1) 1) v_bbii) v_bbbb) (<= v_bbaa (+ v_bbbb v_xx)))
  (<= v_bbbb v_ww))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ff)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_hh))) (= v_bbhh E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (not (<= (+ (- v_bbgg v_bbii) 1) (+ v_ww v_bbjj))))
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (and (and (= E_bb E_gg) (= v_bbbb 1)) (= v_bbii v_bbgg)))
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))))) (not (<= (+ (+ v_zz 1) 1) v_vv)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))
  (= E_bb E_ee))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))
  (= E_bb E_gg)) (= v_bbii (+ v_bbgg 1)))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))
  (= E_bb E_gg)) (= v_bbii v_bbgg)) (= v_bbbb 1)))) (= v_bbee true)))))

(declare-fun f57 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f57_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f57 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
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
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee)))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= v_bbhh E_dd)) (mem int (t2tb3 (+ v_bbgg 1))
  (t2tb2 integer))) (<= 0 (+ v_bbgg 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_zz 0)))
  (=> (= E_bb E_cc) (<= v_yy v_uu))) (=> (= E_bb E_ee) (<= v_zz v_vv)))
  (=> (= E_bb E_ff) (<= v_zz (+ v_vv 1))))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbaa 0)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbbb 0)))
  (=> (= E_bb E_gg) (<= v_bbbb 1)))
  (=> (= E_bb E_gg) (= (- (+ v_bbgg 1) v_bbii) v_bbbb)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_gg) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_hh) (empty enum_aa1))))
  (and (<= v_bbaa (+ (+ v_ww v_xx) 1)) (<= v_zz (+ (+ v_vv v_bbaa) 2)))))
  (=> (= E_bb E_hh)
  (and
  (and (= (- (- (+ v_bbgg 1) 1) v_bbii) v_bbbb) (<= v_bbaa (+ v_bbbb v_xx)))
  (<= v_bbbb v_ww))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ff)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_hh))) (= v_bbhh E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (not (<= (+ (- v_bbgg v_bbii) 1) (+ v_ww v_bbjj))))
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (and (and (= E_bb E_gg) (= v_bbbb 1)) (= v_bbii v_bbgg)))
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))))) (not (<= (+ (+ v_zz 1) 1) v_vv)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))
  (= E_bb E_ee))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))
  (= E_bb E_gg)) (= v_bbii (+ v_bbgg 1)))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))
  (= E_bb E_gg)) (= v_bbii v_bbgg)) (= v_bbbb 1)))) (= v_bbff true)))))

(declare-fun f58 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f58_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f58 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
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
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee)))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= v_bbhh E_dd)) (mem int (t2tb3 (+ v_bbgg 1))
  (t2tb2 integer))) (<= 0 (+ v_bbgg 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_zz 0)))
  (=> (= E_bb E_cc) (<= v_yy v_uu))) (=> (= E_bb E_ee) (<= v_zz v_vv)))
  (=> (= E_bb E_ff) (<= v_zz (+ v_vv 1))))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbaa 0)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbbb 0)))
  (=> (= E_bb E_gg) (<= v_bbbb 1)))
  (=> (= E_bb E_gg) (= (- (+ v_bbgg 1) v_bbii) v_bbbb)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_gg) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_hh) (empty enum_aa1))))
  (and (<= v_bbaa (+ (+ v_ww v_xx) 1)) (<= v_zz (+ (+ v_vv v_bbaa) 2)))))
  (=> (= E_bb E_hh)
  (and
  (and (= (- (- (+ v_bbgg 1) 1) v_bbii) v_bbbb) (<= v_bbaa (+ v_bbbb v_xx)))
  (<= v_bbbb v_ww))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ff)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_hh))) (= v_bbhh E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (not (<= (+ (- v_bbgg v_bbii) 1) (+ v_ww v_bbjj))))
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ee))) (not (= v_bbhh E_ii)))
  (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg))) (= v_bbhh E_ff))
  (or
  (or
  (and
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)) (and (and (= E_bb E_gg) (= v_bbbb 1)) (= v_bbii v_bbgg)))
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false)))))) (not (<= (+ (+ v_zz 1) 1) v_vv)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))
  (= E_bb E_ee))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))
  (= E_bb E_gg)) (= v_bbii (+ v_bbgg 1)))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh))) (not (= v_bbhh E_gg)))
  (not (= v_bbhh E_ff))) (not (= v_bbhh E_ee))) (= v_bbhh E_dd))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))
  (= E_bb E_gg)) (= v_bbii v_bbgg)) (= v_bbbb 1)))) (not (= v_bbcc false)))
  (not (= v_bbdd false))) (not (= v_bbee true))) (not (= v_bbff true))))))

(declare-fun f59 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f59_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f59 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
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
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_ff))) (= v_bbhh E_ee))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false)) (mem
  int (t2tb3 (+ v_zz 1)) (t2tb2 (mk 0 255)))) (mem int (t2tb3 1)
  (t2tb2 (mk 0 255)))) (mem int (t2tb3 (+ v_bbgg 1)) (t2tb2 integer)))
  (<= 0 (+ v_bbgg 1)))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= (+ v_zz 1) 0)))
  (=> (= E_gg E_cc) (<= v_yy v_uu))) (=> (= E_gg E_ee) (<= (+ v_zz 1) v_vv)))
  (=> (= E_gg E_ff) (<= v_zz v_vv)))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbaa 0)))
  (not (= E_gg E_cc))) (not (= E_gg E_dd))) (not (= E_gg E_ee)))
  (not (= E_gg E_ff))) (= (- (+ v_bbgg 1) v_bbgg) 1))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_gg) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_hh) (empty enum_aa1))))
  (and (<= v_bbaa (+ (+ v_ww v_xx) 1)) (<= (+ v_zz 1) (+ (+ v_vv v_bbaa) 2)))))
  (=> (= E_gg E_hh)
  (and (and (= (- (- (+ v_bbgg 1) 1) v_bbgg) 1) (<= v_bbaa (+ 1 v_xx)))
  (<= 1 v_ww))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_ff))) (= v_bbhh E_ee))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_gg E_bb)) (= 1 v_bbbb)) (= v_bbgg v_bbii))))
  (<= (+ (+ v_zz 1) 1) v_vv))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (and (= E_gg E_ee) (not (= v_bbhh E_bb))) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_ff))) (= v_bbhh E_ee))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))
  (= v_bbgg v_bbii)) (= 1 v_bbbb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_ff))) (= v_bbhh E_ee))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))
  (or (and (<= (+ (+ v_zz 1) 1) v_vv) (= E_gg E_ee))
  (and (not (<= (+ (+ v_zz 1) 1) v_vv)) (= E_gg E_bb)))) (= v_bbgg v_bbii))
  (= 1 v_bbbb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_ff))) (= v_bbhh E_ee))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false)))))))

(declare-fun f60 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f60_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f60 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
  v_bbhh v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (not (= v_bbhh E_ee)))))

(declare-fun f62 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f62_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f62 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
  v_bbhh v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (= (+ v_zz 1) v_zz))))

(declare-fun f63 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f63_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f63 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
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
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_ff))) (= v_bbhh E_ee))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false)) (mem
  int (t2tb3 (+ v_zz 1)) (t2tb2 (mk 0 255)))) (mem int (t2tb3 1)
  (t2tb2 (mk 0 255)))) (mem int (t2tb3 (+ v_bbgg 1)) (t2tb2 integer)))
  (<= 0 (+ v_bbgg 1)))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= (+ v_zz 1) 0)))
  (=> (= E_gg E_cc) (<= v_yy v_uu))) (=> (= E_gg E_ee) (<= (+ v_zz 1) v_vv)))
  (=> (= E_gg E_ff) (<= v_zz v_vv)))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbaa 0)))
  (not (= E_gg E_cc))) (not (= E_gg E_dd))) (not (= E_gg E_ee)))
  (not (= E_gg E_ff))) (= (- (+ v_bbgg 1) v_bbgg) 1))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_gg) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_hh) (empty enum_aa1))))
  (and (<= v_bbaa (+ (+ v_ww v_xx) 1)) (<= (+ v_zz 1) (+ (+ v_vv v_bbaa) 2)))))
  (=> (= E_gg E_hh)
  (and (and (= (- (- (+ v_bbgg 1) 1) v_bbgg) 1) (<= v_bbaa (+ 1 v_xx)))
  (<= 1 v_ww))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_ff))) (= v_bbhh E_ee))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_gg E_bb)) (= 1 v_bbbb)) (= v_bbgg v_bbii))))
  (<= (+ (+ v_zz 1) 1) v_vv))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (and (= E_gg E_ee) (not (= v_bbhh E_bb))) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_ff))) (= v_bbhh E_ee))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))
  (= v_bbgg v_bbii)) (= 1 v_bbbb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_ff))) (= v_bbhh E_ee))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))
  (or (and (<= (+ (+ v_zz 1) 1) v_vv) (= E_gg E_ee))
  (and (not (<= (+ (+ v_zz 1) 1) v_vv)) (= E_gg E_bb)))) (= v_bbgg v_bbii))
  (= 1 v_bbbb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_ff))) (= v_bbhh E_ee))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))))
  (= v_bbdd false)))))

(declare-fun f64 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f64_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f64 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
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
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_ff))) (= v_bbhh E_ee))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false)) (mem
  int (t2tb3 (+ v_zz 1)) (t2tb2 (mk 0 255)))) (mem int (t2tb3 1)
  (t2tb2 (mk 0 255)))) (mem int (t2tb3 (+ v_bbgg 1)) (t2tb2 integer)))
  (<= 0 (+ v_bbgg 1)))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= (+ v_zz 1) 0)))
  (=> (= E_gg E_cc) (<= v_yy v_uu))) (=> (= E_gg E_ee) (<= (+ v_zz 1) v_vv)))
  (=> (= E_gg E_ff) (<= v_zz v_vv)))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbaa 0)))
  (not (= E_gg E_cc))) (not (= E_gg E_dd))) (not (= E_gg E_ee)))
  (not (= E_gg E_ff))) (= (- (+ v_bbgg 1) v_bbgg) 1))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_gg) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_hh) (empty enum_aa1))))
  (and (<= v_bbaa (+ (+ v_ww v_xx) 1)) (<= (+ v_zz 1) (+ (+ v_vv v_bbaa) 2)))))
  (=> (= E_gg E_hh)
  (and (and (= (- (- (+ v_bbgg 1) 1) v_bbgg) 1) (<= v_bbaa (+ 1 v_xx)))
  (<= 1 v_ww))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_ff))) (= v_bbhh E_ee))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_gg E_bb)) (= 1 v_bbbb)) (= v_bbgg v_bbii))))
  (not (<= (+ (+ v_zz 1) 1) v_vv)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (and (= E_gg E_ff) (not (= v_bbhh E_bb))) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_ff))) (= v_bbhh E_ee))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))
  (= v_bbgg v_bbii)) (= 1 v_bbbb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_ff))) (= v_bbhh E_ee))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))
  (or (and (<= (+ (+ v_zz 1) 1) v_vv) (= E_gg E_ee))
  (and (not (<= (+ (+ v_zz 1) 1) v_vv)) (= E_gg E_bb)))) (= v_bbgg v_bbii))
  (= 1 v_bbbb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_ff))) (= v_bbhh E_ee))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false)))))))

(declare-fun f65 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f65_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f65 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
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
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_ff))) (= v_bbhh E_ee))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false)) (mem
  int (t2tb3 (+ v_zz 1)) (t2tb2 (mk 0 255)))) (mem int (t2tb3 1)
  (t2tb2 (mk 0 255)))) (mem int (t2tb3 (+ v_bbgg 1)) (t2tb2 integer)))
  (<= 0 (+ v_bbgg 1)))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= (+ v_zz 1) 0)))
  (=> (= E_gg E_cc) (<= v_yy v_uu))) (=> (= E_gg E_ee) (<= (+ v_zz 1) v_vv)))
  (=> (= E_gg E_ff) (<= v_zz v_vv)))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbaa 0)))
  (not (= E_gg E_cc))) (not (= E_gg E_dd))) (not (= E_gg E_ee)))
  (not (= E_gg E_ff))) (= (- (+ v_bbgg 1) v_bbgg) 1))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_gg) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_hh) (empty enum_aa1))))
  (and (<= v_bbaa (+ (+ v_ww v_xx) 1)) (<= (+ v_zz 1) (+ (+ v_vv v_bbaa) 2)))))
  (=> (= E_gg E_hh)
  (and (and (= (- (- (+ v_bbgg 1) 1) v_bbgg) 1) (<= v_bbaa (+ 1 v_xx)))
  (<= 1 v_ww))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_ff))) (= v_bbhh E_ee))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_gg E_bb)) (= 1 v_bbbb)) (= v_bbgg v_bbii))))
  (not (<= (+ (+ v_zz 1) 1) v_vv)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (and (= E_gg E_ff) (not (= v_bbhh E_bb))) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_ff))) (= v_bbhh E_ee))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))
  (= v_bbgg v_bbii)) (= 1 v_bbbb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_ff))) (= v_bbhh E_ee))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))
  (or (and (<= (+ (+ v_zz 1) 1) v_vv) (= E_gg E_ee))
  (and (not (<= (+ (+ v_zz 1) 1) v_vv)) (= E_gg E_bb)))) (= v_bbgg v_bbii))
  (= 1 v_bbbb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_ff))) (= v_bbhh E_ee))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))))
  (= v_bbdd false)))))

(declare-fun f66 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f66_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f66 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
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
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_ff))) (<= (+ (+ v_zz 1) 1) v_vv))
  (= v_bbhh E_ee)) (= v_bbcc true)) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (mem int (t2tb3 (+ v_zz 1)) (t2tb2 (mk 0 255)))) (mem 
  int (t2tb3 (+ v_bbgg 1)) (t2tb2 integer))) (<= 0 (+ v_bbgg 1)))
  (=> (mem enum_aa1 (t2tb5 E_ee)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= (+ v_zz 1) 0)))
  (=> (= E_ee E_cc) (<= v_yy v_uu))) (<= (+ v_zz 1) v_vv))
  (=> (= E_ee E_ff) (<= v_zz v_vv)))
  (=> (mem enum_aa1 (t2tb5 E_ee)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbaa 0)))
  (=> (mem enum_aa1 (t2tb5 E_ee)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbbb 0)))
  (=> (= E_ee E_gg) (<= v_bbbb 1)))
  (=> (= E_ee E_gg) (= (- (+ v_bbgg 1) v_bbii) v_bbbb)))
  (=> (mem enum_aa1 (t2tb5 E_ee)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_gg) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_hh) (empty enum_aa1))))
  (and (<= v_bbaa (+ (+ v_ww v_xx) 1)) (<= (+ v_zz 1) (+ (+ v_vv v_bbaa) 2)))))
  (=> (= E_ee E_hh)
  (and
  (and (= (- (- (+ v_bbgg 1) 1) v_bbii) v_bbbb) (<= v_bbaa (+ v_bbbb v_xx)))
  (<= v_bbbb v_ww))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_ff))) (= v_bbhh E_ee))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_ee E_bb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_ff))) (= v_bbhh E_ee))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_ff))) (= v_bbhh E_ee))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))
  (= v_bbii (+ v_bbgg 1))) (= E_ee E_gg))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_ff))) (= v_bbhh E_ee))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))
  (or (<= (+ (+ v_zz 1) 1) v_vv)
  (and (not (<= (+ (+ v_zz 1) 1) v_vv)) (= E_ee E_bb))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_ff))) (= v_bbhh E_ee))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))
  (= v_bbii v_bbgg)) (= v_bbbb 1)) (= E_ee E_gg)))) (= v_bbcc false)))))

(declare-fun f67 (Int Int Int Int Int Int Int enum_aa Bool Bool Bool Bool Int
  Int Int Int Int Int Int Int Int Int Int Int Int enum_aa Int Bool Bool Bool
  Bool Int Int) Bool)

;; f67_def
  (assert
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (= (f67 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
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
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_ff))) (<= (+ (+ v_zz 1) 1) v_vv))
  (= v_bbhh E_ee)) (= v_bbcc true)) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)) (mem int (t2tb3 (+ v_zz 1)) (t2tb2 (mk 0 255)))) (mem 
  int (t2tb3 (+ v_bbgg 1)) (t2tb2 integer))) (<= 0 (+ v_bbgg 1)))
  (=> (mem enum_aa1 (t2tb5 E_ee)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= (+ v_zz 1) 0)))
  (=> (= E_ee E_cc) (<= v_yy v_uu))) (<= (+ v_zz 1) v_vv))
  (=> (= E_ee E_ff) (<= v_zz v_vv)))
  (=> (mem enum_aa1 (t2tb5 E_ee)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbaa 0)))
  (=> (mem enum_aa1 (t2tb5 E_ee)
  (union enum_aa1
  (union enum_aa1
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ee) (empty enum_aa1)))
  (add enum_aa1 (t2tb5 E_ff) (empty enum_aa1)))) (= v_bbbb 0)))
  (=> (= E_ee E_gg) (<= v_bbbb 1)))
  (=> (= E_ee E_gg) (= (- (+ v_bbgg 1) v_bbii) v_bbbb)))
  (=> (mem enum_aa1 (t2tb5 E_ee)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_gg) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_hh) (empty enum_aa1))))
  (and (<= v_bbaa (+ (+ v_ww v_xx) 1)) (<= (+ v_zz 1) (+ (+ v_vv v_bbaa) 2)))))
  (=> (= E_ee E_hh)
  (and
  (and (= (- (- (+ v_bbgg 1) 1) v_bbii) v_bbbb) (<= v_bbaa (+ v_bbbb v_xx)))
  (<= v_bbbb v_ww))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_ff))) (= v_bbhh E_ee))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc true) (= v_bbdd true)) (= v_bbee true))
  (= v_bbff false))))
  (not
  (and (and (and (= v_bbcc false) (= v_bbdd true)) (= v_bbee false))
  (= v_bbff false)))) (= E_ee E_bb))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_ff))) (= v_bbhh E_ee))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_ff))) (= v_bbhh E_ee))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))
  (= v_bbii (+ v_bbgg 1))) (= E_ee E_gg))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_ff))) (= v_bbhh E_ee))
  (= v_bbcc true)) (= v_bbdd true)) (= v_bbee false)) (= v_bbff false))
  (or (<= (+ (+ v_zz 1) 1) v_vv)
  (and (not (<= (+ (+ v_zz 1) 1) v_vv)) (= E_ee E_bb))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbhh E_bb)) (not (= v_bbhh E_cc)))
  (not (= v_bbhh E_dd))) (not (= v_bbhh E_ii))) (not (= v_bbhh E_hh)))
  (not (= v_bbhh E_gg))) (not (= v_bbhh E_ff))) (= v_bbhh E_ee))
  (= v_bbcc false)) (= v_bbdd true)) (= v_bbee true)) (= v_bbff false))
  (= v_bbii v_bbgg)) (= v_bbbb 1)) (= E_ee E_gg)))) (= v_bbdd false)))))

(assert
;; bbqq_12
 ;; File "POwhy_bpo2why/p4/p4_14_part6.why", line 5080, characters 7-14
  (not
  (forall ((v_zz Int) (v_yy Int) (v_xx Int) (v_ww Int) (v_vv Int) (v_uu Int)
  (v_tt Int) (v_ss enum_aa) (v_rr Bool) (v_qq Bool) (v_pp Bool) (v_oo Bool)
  (v_nn Int) (v_mm Int) (v_ll Int) (v_kk Int) (v_jj Int) (v_bbpp Int)
  (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int) (v_bbkk Int)
  (v_bbjj Int) (v_bbii Int) (v_bbhh enum_aa) (v_bbgg Int) (v_bbff Bool)
  (v_bbee Bool) (v_bbdd Bool) (v_bbcc Bool) (v_bbbb Int) (v_bbaa Int))
  (=>
  (and (f1 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
  v_bbhh v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (and (f2 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
  v_bbhh v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (and (f3 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
  v_bbhh v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa) (f13 v_zz v_yy
  v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn v_mm v_ll v_kk v_jj
  v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii v_bbhh v_bbgg
  v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)))) (= v_bbhh E_dd)))))
(check-sat)
