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

(declare-fun f1 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f1_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
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
  (<= v_bbpp 2147483647)) (mem int (t2tb3 v_tt) (t2tb2 integer)))
  (<= 0 v_tt)) (<= v_tt 2147483647)) (<= 1 v_tt)) (<= v_tt 254))
  (= v_tt v_bboo)) (mem int (t2tb3 v_bbii) (t2tb2 integer))) (<= 0 v_bbii))
  (<= v_bbii 2147483647)) (<= 1 v_bbii)) (<= v_bbii 254)) (= v_bbii v_bboo))
  (mem int (t2tb3 v_bbff) (t2tb2 integer))) (<= 0 v_bbff))
  (<= v_bbff 2147483647)) (<= 1 v_bbff)) (<= (+ v_bbff 1) 2147483647))
  (= v_bbff v_bbpp)) (mem int (t2tb3 v_bbee) (t2tb2 integer))) (<= 0 v_bbee))
  (<= v_bbee 2147483647)) (<= 2 v_bbee)) (= v_bbee v_bbnn))
  (<= (+ v_bbee v_bbii) 253)) (<= (+ (+ v_bbee v_tt) v_bbii) 251)) (mem 
  int (t2tb3 v_bbjj) (t2tb2 integer))) (<= 0 v_bbjj)) (<= v_bbjj 2147483647))
  (<= 1 v_bbjj)) (<= (+ v_bbjj 1) 254)) (= v_bbjj v_bbnn)))))

(declare-fun f2 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f2_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
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
  (and (and (mem int (t2tb3 v_uu) (t2tb2 integer)) (<= 0 v_uu)) (mem 
  int (t2tb3 v_vv) (t2tb2 integer))) (<= 0 v_vv)) (mem int (t2tb3 v_bbaa)
  (t2tb2 integer))) (<= 0 v_bbaa)) (mem int (t2tb3 v_bbcc) (t2tb2 integer)))
  (<= 0 v_bbcc)) (mem int (t2tb3 v_bbdd) (t2tb2 integer))) (<= 0 v_bbdd))
  (=> (mem enum_aa1 (t2tb5 v_bbbb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_vv 0)))
  (=> (= v_bbbb E_ee) (<= v_vv v_tt)))
  (=> (= v_bbbb E_ff) (= v_bbcc v_bbaa))) (=> (= v_bbbb E_cc) (<= v_uu 254))))))

(declare-fun f3 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f3_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
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
  (and (and (mem int (t2tb3 v_uu) (t2tb2 integer)) (<= 0 v_uu)) (mem 
  int (t2tb3 v_vv) (t2tb2 integer))) (<= 0 v_vv)) (mem int (t2tb3 v_bbgg)
  (t2tb2 integer))) (<= 0 v_bbgg)) (mem int (t2tb3 v_bbhh) (t2tb2 integer)))
  (<= 0 v_bbhh)) (mem int (t2tb3 v_bbcc) (t2tb2 integer))) (<= 0 v_bbcc))
  (mem int (t2tb3 v_bbdd) (t2tb2 integer))) (<= 0 v_bbdd))
  (=> (mem enum_aa1 (t2tb5 v_bbbb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_vv 0)))
  (=> (= v_bbbb E_dd) (= v_bbgg v_bbaa)))
  (=> (= v_bbbb E_ee)
  (and (and (= v_bbhh v_bbaa) (= (- (- v_bbhh v_bbgg) 1) v_vv))
  (<= v_vv v_tt)))) (=> (= v_bbbb E_ff) (= v_bbcc v_bbaa)))
  (=> (= v_bbbb E_cc) (= v_bbkk (- v_bbaa v_uu)))) (mem int (t2tb3 v_bbaa)
  (t2tb2 integer))) (<= 0 v_bbaa)) (mem int (t2tb3 v_bbkk) (t2tb2 integer)))
  (<= 0 v_bbkk)) (= v_jj v_uu)) (= v_kk v_vv)) (= v_mm v_ww)) (= v_nn v_xx))
  (= v_oo v_yy)) (= v_pp v_zz)) (= v_ll v_bbaa)) (= v_qq v_bbbb))
  (= v_rr v_bbcc)) (= v_ss v_bbdd)))))

(declare-fun f14 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f14_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f14 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
  v_bbhh v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (<= v_bbjj (+ v_uu 1)))))

(declare-fun f21 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f21_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f21 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
  v_bbhh v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (= v_uu (+ v_uu 1)))))

(declare-fun f37 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f37_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f37 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
  v_bbhh v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (= (+ v_bbaa 1) v_bbdd))))

(declare-fun f60 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f60_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f60 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
  v_bbhh v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (not (= v_bbbb E_ee)))))

(declare-fun f62 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f62_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f62 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
  v_bbhh v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (= (+ v_vv 1) v_vv))))

(declare-fun f78 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f78_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f78 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false)) (mem int
  (t2tb3 (+ v_vv 1)) (t2tb2 integer))) (<= 0 (+ v_vv 1))) (mem int
  (t2tb3 (+ v_bbaa 1)) (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= (+ v_vv 1) 0)))
  (=> (= E_gg E_ee) (<= (+ v_vv 1) v_tt))) (not (= E_gg E_ff)))
  (=> (= E_gg E_cc) (<= v_uu 254)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ii))) (= v_bbbb E_hh))
  (or
  (or
  (or
  (or
  (and
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (not (<= (+ (- (- (+ v_bbaa 1) v_bbdd) 1) 1) v_bbee)) (= E_gg E_ii)))
  (= (+ v_bbaa 1) v_bbdd))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))
  (and
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= E_gg E_bb)) (= (+ v_bbaa 1) v_bbdd))))
  (= v_bbaa v_bbcc))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (= v_bbbb E_gg))
  (or (and (= E_gg E_bb) (= (+ v_bbaa 1) v_bbdd))
  (or
  (or
  (or
  (or
  (and
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (or (and (<= (- (- (+ v_bbaa 1) v_bbcc) 1) v_bbii) (= E_gg E_hh))
  (and (not (<= (- (- (+ v_bbaa 1) v_bbcc) 1) v_bbii)) (= E_gg E_bb))))
  (= (+ v_bbaa 1) v_bbdd))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (or (<= (- (- (+ v_bbaa 1) v_bbcc) 1) v_bbii)
  (and (and (not (<= (- (- (+ v_bbaa 1) v_bbcc) 1) v_bbii)) (= E_gg E_bb))
  (= (+ v_bbaa 1) v_bbdd)))))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (or (<= (- (- (+ v_bbaa 1) v_bbcc) 1) v_bbii)
  (and (and (not (<= (- (- (+ v_bbaa 1) v_bbcc) 1) v_bbii)) (= E_gg E_bb))
  (= (+ v_bbaa 1) v_bbdd)))))
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))
  (or (<= (- (- (+ v_bbaa 1) v_bbcc) 1) v_bbii)
  (and (and (not (<= (- (- (+ v_bbaa 1) v_bbcc) 1) v_bbii)) (= E_gg E_bb))
  (= (+ v_bbaa 1) v_bbdd)))))
  (and
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= E_gg E_bb)) (= (+ v_bbaa 1) v_bbdd)))))
  (= v_bbaa v_bbcc))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= E_gg E_bb)) (= v_bbaa v_bbcc))
  (= (+ v_bbaa 1) v_bbdd)))) (not (<= (+ (+ v_vv 1) 1) v_tt)))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbaa v_bbhh))))
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
  (and (and (and (= E_gg E_bb) (not (= v_bbbb E_bb))) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww true)) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (= v_bbaa v_bbcc)) (= (+ v_bbaa 1) v_bbdd)))))))

(declare-fun f79 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f79_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f79 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (<= (+ (+ v_vv 1) 1) v_tt))
  (= v_bbbb E_ee)) (= v_ww false)) (= v_xx true)) (= v_yy false))
  (= v_zz false)) (mem int (t2tb3 (+ v_vv 1)) (t2tb2 integer)))
  (<= 0 (+ v_vv 1))) (mem int (t2tb3 (+ v_bbaa 1)) (t2tb2 integer)))
  (<= 0 (+ v_bbaa 1)))
  (=> (mem enum_aa1 (t2tb5 E_ee)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= (+ v_vv 1) 0)))
  (<= (+ v_vv 1) v_tt)) (=> (= E_ee E_ff) (= v_bbcc (+ v_bbaa 1))))
  (=> (= E_ee E_cc) (<= v_uu 254)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ii))) (= v_bbbb E_hh))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (or (and (<= (+ (- (- (+ v_bbaa 1) v_bbdd) 1) 1) v_bbee) (= E_ee v_bbbb))
  (and (not (<= (+ (- (- (+ v_bbaa 1) v_bbdd) 1) 1) v_bbee)) (= E_ee E_ii))))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (and (= E_ee E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (= E_ee E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)) (and (= E_ee E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= E_ee E_bb))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (= v_bbbb E_gg))
  (or (= E_ee E_bb)
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (or (and (<= (- (- (+ v_bbaa 1) v_bbcc) 1) v_bbii) (= E_ee E_hh))
  (and (not (<= (- (- (+ v_bbaa 1) v_bbcc) 1) v_bbii)) (= E_ee E_bb))))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (or
  (and (<= (- (- (+ v_bbaa 1) v_bbcc) 1) v_bbii)
  (and (= E_ee E_gg) (= v_bbdd (+ v_bbaa 1))))
  (and (not (<= (- (- (+ v_bbaa 1) v_bbcc) 1) v_bbii)) (= E_ee E_bb)))))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (or
  (and (<= (- (- (+ v_bbaa 1) v_bbcc) 1) v_bbii)
  (and (= E_ee E_gg) (= v_bbdd (+ v_bbaa 1))))
  (and (not (<= (- (- (+ v_bbaa 1) v_bbcc) 1) v_bbii)) (= E_ee E_bb)))))
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))
  (or
  (and (<= (- (- (+ v_bbaa 1) v_bbcc) 1) v_bbii)
  (and (= E_ee E_gg) (= v_bbdd (+ v_bbaa 1))))
  (and (not (<= (- (- (+ v_bbaa 1) v_bbcc) 1) v_bbii)) (= E_ee E_bb)))))
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= E_ee E_bb)))))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= E_ee E_bb))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbcc v_bbhh)) (= v_bbdd (+ v_bbaa 1))) (= E_ee E_gg))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww true)) (= v_xx true)) (= v_yy false)) (= v_zz false))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbcc v_bbhh)) (= v_bbdd v_bbaa)) (= E_ee E_gg)))))))

(declare-fun f80 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f80_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f80 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (<= (+ (+ v_vv 1) 1) v_tt))
  (= v_bbbb E_ee)) (= v_ww false)) (= v_xx true)) (= v_yy false))
  (= v_zz false)) (mem int (t2tb3 (+ v_vv 1)) (t2tb2 integer)))
  (<= 0 (+ v_vv 1))) (mem int (t2tb3 (+ v_bbaa 1)) (t2tb2 integer)))
  (<= 0 (+ v_bbaa 1)))
  (=> (mem enum_aa1 (t2tb5 E_ee)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= (+ v_vv 1) 0)))
  (<= (+ v_vv 1) v_tt)) (=> (= E_ee E_ff) (= v_bbcc (+ v_bbaa 1))))
  (=> (= E_ee E_cc) (<= v_uu 254)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ii))) (= v_bbbb E_hh))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (or (and (<= (+ (- (- (+ v_bbaa 1) v_bbdd) 1) 1) v_bbee) (= E_ee v_bbbb))
  (and (not (<= (+ (- (- (+ v_bbaa 1) v_bbdd) 1) 1) v_bbee)) (= E_ee E_ii))))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (and (= E_ee E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (= E_ee E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)) (and (= E_ee E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= E_ee E_bb))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (= v_bbbb E_gg))
  (or (= E_ee E_bb)
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (or (and (<= (- (- (+ v_bbaa 1) v_bbcc) 1) v_bbii) (= E_ee E_hh))
  (and (not (<= (- (- (+ v_bbaa 1) v_bbcc) 1) v_bbii)) (= E_ee E_bb))))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (or
  (and (<= (- (- (+ v_bbaa 1) v_bbcc) 1) v_bbii)
  (and (= E_ee E_gg) (= v_bbdd (+ v_bbaa 1))))
  (and (not (<= (- (- (+ v_bbaa 1) v_bbcc) 1) v_bbii)) (= E_ee E_bb)))))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (or
  (and (<= (- (- (+ v_bbaa 1) v_bbcc) 1) v_bbii)
  (and (= E_ee E_gg) (= v_bbdd (+ v_bbaa 1))))
  (and (not (<= (- (- (+ v_bbaa 1) v_bbcc) 1) v_bbii)) (= E_ee E_bb)))))
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))
  (or
  (and (<= (- (- (+ v_bbaa 1) v_bbcc) 1) v_bbii)
  (and (= E_ee E_gg) (= v_bbdd (+ v_bbaa 1))))
  (and (not (<= (- (- (+ v_bbaa 1) v_bbcc) 1) v_bbii)) (= E_ee E_bb)))))
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= E_ee E_bb)))))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= E_ee E_bb))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbcc v_bbhh)) (= v_bbdd (+ v_bbaa 1))) (= E_ee E_gg))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww true)) (= v_xx true)) (= v_yy false)) (= v_zz false))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbcc v_bbhh)) (= v_bbdd v_bbaa)) (= E_ee E_gg)))) (= v_xx false)))))

(declare-fun f81 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f81_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f81 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff)))
  (not (<= (+ (+ v_vv 1) 1) v_tt))) (= v_bbbb E_ee)) (= v_ww false))
  (= v_xx true)) (= v_yy false)) (= v_zz false)) (mem int (t2tb3 (+ v_vv 1))
  (t2tb2 integer))) (<= 0 (+ v_vv 1))) (mem int (t2tb3 (+ v_bbaa 1))
  (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (=> (mem enum_aa1 (t2tb5 E_ff)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= (+ v_vv 1) 0)))
  (=> (= E_ff E_ee) (<= (+ v_vv 1) v_tt))) (=> (= E_ff E_cc) (<= v_uu 254)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ii))) (= v_bbbb E_hh))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (not (<= (+ (- (- (+ v_bbaa 1) v_bbdd) 1) 1) v_bbee)) (= E_ff E_ii)))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (and (= E_ff E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (= E_ff E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)) (and (= E_ff E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= E_ff E_bb)))) (= (+ v_bbaa 1) v_bbcc))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (= v_bbbb E_gg))
  (or (= E_ff E_bb)
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (or (and (<= (- (- (+ v_bbaa 1) v_bbcc) 1) v_bbii) (= E_ff E_hh))
  (and (not (<= (- (- (+ v_bbaa 1) v_bbcc) 1) v_bbii)) (= E_ff E_bb))))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (or
  (and (<= (- (- (+ v_bbaa 1) v_bbcc) 1) v_bbii)
  (and (= E_ff E_gg) (= v_bbdd (+ v_bbaa 1))))
  (and (not (<= (- (- (+ v_bbaa 1) v_bbcc) 1) v_bbii)) (= E_ff E_bb)))))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (or
  (and (<= (- (- (+ v_bbaa 1) v_bbcc) 1) v_bbii)
  (and (= E_ff E_gg) (= v_bbdd (+ v_bbaa 1))))
  (and (not (<= (- (- (+ v_bbaa 1) v_bbcc) 1) v_bbii)) (= E_ff E_bb)))))
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))
  (or
  (and (<= (- (- (+ v_bbaa 1) v_bbcc) 1) v_bbii)
  (and (= E_ff E_gg) (= v_bbdd (+ v_bbaa 1))))
  (and (not (<= (- (- (+ v_bbaa 1) v_bbcc) 1) v_bbii)) (= E_ff E_bb)))))
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= E_ff E_bb))))) (= (+ v_bbaa 1) v_bbcc))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= E_ff E_bb)) (= (+ v_bbaa 1) v_bbcc))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= (+ v_bbaa 1) v_bbhh)) (= v_bbdd (+ v_bbaa 1))) (= E_ff E_gg))))
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
  (and (and (and (= E_ff E_bb) (not (= v_bbbb E_bb))) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww true)) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (= (+ v_bbaa 1) v_bbcc))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= (+ v_bbaa 1) v_bbhh)) (= v_bbdd v_bbaa)) (= E_ff E_gg)))))))

(declare-fun f83 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f83_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f83 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
  v_bbhh v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (= (+ v_bbaa 1) v_bbcc))))

(declare-fun f84 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f84_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f84 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff)))
  (not (<= (+ (+ v_vv 1) 1) v_tt))) (= v_bbbb E_ee)) (= v_ww false))
  (= v_xx true)) (= v_yy false)) (= v_zz false)) (mem int (t2tb3 (+ v_vv 1))
  (t2tb2 integer))) (<= 0 (+ v_vv 1))) (mem int (t2tb3 (+ v_bbaa 1))
  (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (=> (mem enum_aa1 (t2tb5 E_ff)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= (+ v_vv 1) 0)))
  (=> (= E_ff E_ee) (<= (+ v_vv 1) v_tt))) (=> (= E_ff E_cc) (<= v_uu 254)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ii))) (= v_bbbb E_hh))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (not (<= (+ (- (- (+ v_bbaa 1) v_bbdd) 1) 1) v_bbee)) (= E_ff E_ii)))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (and (= E_ff E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (= E_ff E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)) (and (= E_ff E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= E_ff E_bb)))) (= (+ v_bbaa 1) v_bbcc))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (= v_bbbb E_gg))
  (or (= E_ff E_bb)
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (or (and (<= (- (- (+ v_bbaa 1) v_bbcc) 1) v_bbii) (= E_ff E_hh))
  (and (not (<= (- (- (+ v_bbaa 1) v_bbcc) 1) v_bbii)) (= E_ff E_bb))))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (or
  (and (<= (- (- (+ v_bbaa 1) v_bbcc) 1) v_bbii)
  (and (= E_ff E_gg) (= v_bbdd (+ v_bbaa 1))))
  (and (not (<= (- (- (+ v_bbaa 1) v_bbcc) 1) v_bbii)) (= E_ff E_bb)))))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (or
  (and (<= (- (- (+ v_bbaa 1) v_bbcc) 1) v_bbii)
  (and (= E_ff E_gg) (= v_bbdd (+ v_bbaa 1))))
  (and (not (<= (- (- (+ v_bbaa 1) v_bbcc) 1) v_bbii)) (= E_ff E_bb)))))
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))
  (or
  (and (<= (- (- (+ v_bbaa 1) v_bbcc) 1) v_bbii)
  (and (= E_ff E_gg) (= v_bbdd (+ v_bbaa 1))))
  (and (not (<= (- (- (+ v_bbaa 1) v_bbcc) 1) v_bbii)) (= E_ff E_bb)))))
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= E_ff E_bb))))) (= (+ v_bbaa 1) v_bbcc))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= E_ff E_bb)) (= (+ v_bbaa 1) v_bbcc))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= (+ v_bbaa 1) v_bbhh)) (= v_bbdd (+ v_bbaa 1))) (= E_ff E_gg))))
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
  (and (and (and (= E_ff E_bb) (not (= v_bbbb E_bb))) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww true)) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (= (+ v_bbaa 1) v_bbcc))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= (+ v_bbaa 1) v_bbhh)) (= v_bbdd v_bbaa)) (= E_ff E_gg))))
  (= v_xx false)))))

(declare-fun f85 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f85_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f85 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff)))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= v_bbbb E_ee)) (mem int (t2tb3 (+ v_vv 1))
  (t2tb2 integer))) (<= 0 (+ v_vv 1))) (mem int (t2tb3 (+ v_bbaa 1))
  (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= (+ v_vv 1) 0)))
  (=> (= E_bb E_ee) (<= (+ v_vv 1) v_tt)))
  (=> (= E_bb E_ff) (= v_bbcc (+ v_bbaa 1))))
  (=> (= E_bb E_cc) (<= v_uu 254)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ii))) (= v_bbbb E_hh))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (not (<= (+ (- (- (+ v_bbaa 1) v_bbdd) 1) 1) v_bbee)) (= E_bb E_ii)))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)) (and (= E_bb E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (= v_bbbb E_gg))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))))) (<= (+ (+ v_vv 1) 1) v_tt))
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
  (and (and (and (= E_bb E_ee) (not (= v_bbbb E_bb))) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbcc v_bbhh)) (= v_bbdd (+ v_bbaa 1))) (= E_bb E_gg))))
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
  (and (and (and (= E_bb E_ee) (not (= v_bbbb E_bb))) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww true)) (= v_xx true)) (= v_yy false)) (= v_zz false))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbcc v_bbhh)) (= v_bbdd v_bbaa)) (= E_bb E_gg)))) (= v_ww false)))))

(declare-fun f86 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f86_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f86 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff)))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= v_bbbb E_ee)) (mem int (t2tb3 (+ v_vv 1))
  (t2tb2 integer))) (<= 0 (+ v_vv 1))) (mem int (t2tb3 (+ v_bbaa 1))
  (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= (+ v_vv 1) 0)))
  (=> (= E_bb E_ee) (<= (+ v_vv 1) v_tt)))
  (=> (= E_bb E_ff) (= v_bbcc (+ v_bbaa 1))))
  (=> (= E_bb E_cc) (<= v_uu 254)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ii))) (= v_bbbb E_hh))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (not (<= (+ (- (- (+ v_bbaa 1) v_bbdd) 1) 1) v_bbee)) (= E_bb E_ii)))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)) (and (= E_bb E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (= v_bbbb E_gg))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))))) (<= (+ (+ v_vv 1) 1) v_tt))
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
  (and (and (and (= E_bb E_ee) (not (= v_bbbb E_bb))) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbcc v_bbhh)) (= v_bbdd (+ v_bbaa 1))) (= E_bb E_gg))))
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
  (and (and (and (= E_bb E_ee) (not (= v_bbbb E_bb))) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww true)) (= v_xx true)) (= v_yy false)) (= v_zz false))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbcc v_bbhh)) (= v_bbdd v_bbaa)) (= E_bb E_gg)))) (= v_xx false)))))

(declare-fun f87 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f87_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f87 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff)))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= v_bbbb E_ee)) (mem int (t2tb3 (+ v_vv 1))
  (t2tb2 integer))) (<= 0 (+ v_vv 1))) (mem int (t2tb3 (+ v_bbaa 1))
  (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= (+ v_vv 1) 0)))
  (=> (= E_bb E_ee) (<= (+ v_vv 1) v_tt)))
  (=> (= E_bb E_ff) (= v_bbcc (+ v_bbaa 1))))
  (=> (= E_bb E_cc) (<= v_uu 254)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ii))) (= v_bbbb E_hh))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (not (<= (+ (- (- (+ v_bbaa 1) v_bbdd) 1) 1) v_bbee)) (= E_bb E_ii)))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)) (and (= E_bb E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (= v_bbbb E_gg))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))))) (<= (+ (+ v_vv 1) 1) v_tt))
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
  (and (and (and (= E_bb E_ee) (not (= v_bbbb E_bb))) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbcc v_bbhh)) (= v_bbdd (+ v_bbaa 1))) (= E_bb E_gg))))
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
  (and (and (and (= E_bb E_ee) (not (= v_bbbb E_bb))) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww true)) (= v_xx true)) (= v_yy false)) (= v_zz false))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbcc v_bbhh)) (= v_bbdd v_bbaa)) (= E_bb E_gg)))) (= v_yy true)))))

(declare-fun f88 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f88_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f88 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff)))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= v_bbbb E_ee)) (mem int (t2tb3 (+ v_vv 1))
  (t2tb2 integer))) (<= 0 (+ v_vv 1))) (mem int (t2tb3 (+ v_bbaa 1))
  (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= (+ v_vv 1) 0)))
  (=> (= E_bb E_ee) (<= (+ v_vv 1) v_tt)))
  (=> (= E_bb E_ff) (= v_bbcc (+ v_bbaa 1))))
  (=> (= E_bb E_cc) (<= v_uu 254)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ii))) (= v_bbbb E_hh))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (not (<= (+ (- (- (+ v_bbaa 1) v_bbdd) 1) 1) v_bbee)) (= E_bb E_ii)))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)) (and (= E_bb E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (= v_bbbb E_gg))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))))) (<= (+ (+ v_vv 1) 1) v_tt))
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
  (and (and (and (= E_bb E_ee) (not (= v_bbbb E_bb))) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbcc v_bbhh)) (= v_bbdd (+ v_bbaa 1))) (= E_bb E_gg))))
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
  (and (and (and (= E_bb E_ee) (not (= v_bbbb E_bb))) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww true)) (= v_xx true)) (= v_yy false)) (= v_zz false))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbcc v_bbhh)) (= v_bbdd v_bbaa)) (= E_bb E_gg)))) (= v_zz true)))))

(declare-fun f89 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f89_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f89 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff)))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= v_bbbb E_ee)) (mem int (t2tb3 (+ v_vv 1))
  (t2tb2 integer))) (<= 0 (+ v_vv 1))) (mem int (t2tb3 (+ v_bbaa 1))
  (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= (+ v_vv 1) 0)))
  (=> (= E_bb E_ee) (<= (+ v_vv 1) v_tt)))
  (=> (= E_bb E_ff) (= v_bbcc (+ v_bbaa 1))))
  (=> (= E_bb E_cc) (<= v_uu 254)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ii))) (= v_bbbb E_hh))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (not (<= (+ (- (- (+ v_bbaa 1) v_bbdd) 1) 1) v_bbee)) (= E_bb E_ii)))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)) (and (= E_bb E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (= v_bbbb E_gg))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))))) (<= (+ (+ v_vv 1) 1) v_tt))
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
  (and (and (and (= E_bb E_ee) (not (= v_bbbb E_bb))) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbcc v_bbhh)) (= v_bbdd (+ v_bbaa 1))) (= E_bb E_gg))))
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
  (and (and (and (= E_bb E_ee) (not (= v_bbbb E_bb))) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww true)) (= v_xx true)) (= v_yy false)) (= v_zz false))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbcc v_bbhh)) (= v_bbdd v_bbaa)) (= E_bb E_gg))))
  (not (= v_ww false))) (not (= v_xx false))) (not (= v_yy true)))
  (not (= v_zz true))))))

(declare-fun f90 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f90_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f90 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff)))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= v_bbbb E_ee)) (mem int (t2tb3 (+ v_vv 1))
  (t2tb2 integer))) (<= 0 (+ v_vv 1))) (mem int (t2tb3 (+ v_bbaa 1))
  (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= (+ v_vv 1) 0)))
  (=> (= E_bb E_ee) (<= (+ v_vv 1) v_tt)))
  (=> (= E_bb E_ff) (= v_bbcc (+ v_bbaa 1))))
  (=> (= E_bb E_cc) (<= v_uu 254)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ii))) (= v_bbbb E_hh))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (not (<= (+ (- (- (+ v_bbaa 1) v_bbdd) 1) 1) v_bbee)) (= E_bb E_ii)))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)) (and (= E_bb E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (= v_bbbb E_gg))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))))) (not (<= (+ (+ v_vv 1) 1) v_tt)))
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
  (and (and (= v_bbcc (+ v_bbaa 1)) (= E_bb E_ff)) (not (= v_bbbb E_bb)))
  (not (= v_bbbb E_cc))) (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff)))
  (= v_bbbb E_ee)) (= v_ww false)) (= v_xx true)) (= v_yy false))
  (= v_zz false))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbcc v_bbhh)) (= v_bbdd (+ v_bbaa 1))) (= E_bb E_gg))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww true)) (= v_xx true)) (= v_yy false)) (= v_zz false))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbcc v_bbhh)) (= v_bbdd v_bbaa)) (= E_bb E_gg)))) (= v_ww false)))))

(declare-fun f91 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f91_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f91 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff)))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= v_bbbb E_ee)) (mem int (t2tb3 (+ v_vv 1))
  (t2tb2 integer))) (<= 0 (+ v_vv 1))) (mem int (t2tb3 (+ v_bbaa 1))
  (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= (+ v_vv 1) 0)))
  (=> (= E_bb E_ee) (<= (+ v_vv 1) v_tt)))
  (=> (= E_bb E_ff) (= v_bbcc (+ v_bbaa 1))))
  (=> (= E_bb E_cc) (<= v_uu 254)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ii))) (= v_bbbb E_hh))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (not (<= (+ (- (- (+ v_bbaa 1) v_bbdd) 1) 1) v_bbee)) (= E_bb E_ii)))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)) (and (= E_bb E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (= v_bbbb E_gg))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))))) (not (<= (+ (+ v_vv 1) 1) v_tt)))
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
  (and (and (= v_bbcc (+ v_bbaa 1)) (= E_bb E_ff)) (not (= v_bbbb E_bb)))
  (not (= v_bbbb E_cc))) (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff)))
  (= v_bbbb E_ee)) (= v_ww false)) (= v_xx true)) (= v_yy false))
  (= v_zz false))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbcc v_bbhh)) (= v_bbdd (+ v_bbaa 1))) (= E_bb E_gg))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww true)) (= v_xx true)) (= v_yy false)) (= v_zz false))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbcc v_bbhh)) (= v_bbdd v_bbaa)) (= E_bb E_gg)))) (= v_xx false)))))

(declare-fun f92 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f92_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f92 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff)))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= v_bbbb E_ee)) (mem int (t2tb3 (+ v_vv 1))
  (t2tb2 integer))) (<= 0 (+ v_vv 1))) (mem int (t2tb3 (+ v_bbaa 1))
  (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= (+ v_vv 1) 0)))
  (=> (= E_bb E_ee) (<= (+ v_vv 1) v_tt)))
  (=> (= E_bb E_ff) (= v_bbcc (+ v_bbaa 1))))
  (=> (= E_bb E_cc) (<= v_uu 254)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ii))) (= v_bbbb E_hh))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (not (<= (+ (- (- (+ v_bbaa 1) v_bbdd) 1) 1) v_bbee)) (= E_bb E_ii)))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)) (and (= E_bb E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (= v_bbbb E_gg))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))))) (not (<= (+ (+ v_vv 1) 1) v_tt)))
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
  (and (and (= v_bbcc (+ v_bbaa 1)) (= E_bb E_ff)) (not (= v_bbbb E_bb)))
  (not (= v_bbbb E_cc))) (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff)))
  (= v_bbbb E_ee)) (= v_ww false)) (= v_xx true)) (= v_yy false))
  (= v_zz false))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbcc v_bbhh)) (= v_bbdd (+ v_bbaa 1))) (= E_bb E_gg))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww true)) (= v_xx true)) (= v_yy false)) (= v_zz false))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbcc v_bbhh)) (= v_bbdd v_bbaa)) (= E_bb E_gg)))) (= v_yy true)))))

(declare-fun f93 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f93_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f93 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff)))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= v_bbbb E_ee)) (mem int (t2tb3 (+ v_vv 1))
  (t2tb2 integer))) (<= 0 (+ v_vv 1))) (mem int (t2tb3 (+ v_bbaa 1))
  (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= (+ v_vv 1) 0)))
  (=> (= E_bb E_ee) (<= (+ v_vv 1) v_tt)))
  (=> (= E_bb E_ff) (= v_bbcc (+ v_bbaa 1))))
  (=> (= E_bb E_cc) (<= v_uu 254)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ii))) (= v_bbbb E_hh))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (not (<= (+ (- (- (+ v_bbaa 1) v_bbdd) 1) 1) v_bbee)) (= E_bb E_ii)))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)) (and (= E_bb E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (= v_bbbb E_gg))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))))) (not (<= (+ (+ v_vv 1) 1) v_tt)))
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
  (and (and (= v_bbcc (+ v_bbaa 1)) (= E_bb E_ff)) (not (= v_bbbb E_bb)))
  (not (= v_bbbb E_cc))) (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff)))
  (= v_bbbb E_ee)) (= v_ww false)) (= v_xx true)) (= v_yy false))
  (= v_zz false))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbcc v_bbhh)) (= v_bbdd (+ v_bbaa 1))) (= E_bb E_gg))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww true)) (= v_xx true)) (= v_yy false)) (= v_zz false))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbcc v_bbhh)) (= v_bbdd v_bbaa)) (= E_bb E_gg)))) (= v_zz true)))))

(declare-fun f94 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f94_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f94 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff)))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= v_bbbb E_ee)) (mem int (t2tb3 (+ v_vv 1))
  (t2tb2 integer))) (<= 0 (+ v_vv 1))) (mem int (t2tb3 (+ v_bbaa 1))
  (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= (+ v_vv 1) 0)))
  (=> (= E_bb E_ee) (<= (+ v_vv 1) v_tt)))
  (=> (= E_bb E_ff) (= v_bbcc (+ v_bbaa 1))))
  (=> (= E_bb E_cc) (<= v_uu 254)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ii))) (= v_bbbb E_hh))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (not (<= (+ (- (- (+ v_bbaa 1) v_bbdd) 1) 1) v_bbee)) (= E_bb E_ii)))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)) (and (= E_bb E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (= v_bbbb E_gg))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))))) (not (<= (+ (+ v_vv 1) 1) v_tt)))
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
  (and (and (= v_bbcc (+ v_bbaa 1)) (= E_bb E_ff)) (not (= v_bbbb E_bb)))
  (not (= v_bbbb E_cc))) (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff)))
  (= v_bbbb E_ee)) (= v_ww false)) (= v_xx true)) (= v_yy false))
  (= v_zz false))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbcc v_bbhh)) (= v_bbdd (+ v_bbaa 1))) (= E_bb E_gg))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww true)) (= v_xx true)) (= v_yy false)) (= v_zz false))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbcc v_bbhh)) (= v_bbdd v_bbaa)) (= E_bb E_gg))))
  (not (= v_ww false))) (not (= v_xx false))) (not (= v_yy true)))
  (not (= v_zz true))))))

(declare-fun f95 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f95_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f95 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false)) (mem 
  int (t2tb3 (+ v_bbaa 1)) (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_vv 0)))
  (=> (= E_gg E_ee) (<= v_vv v_tt)))
  (=> (= E_gg E_ff) (= v_bbcc (+ v_bbaa 1))))
  (=> (= E_gg E_cc) (<= v_uu 254)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_hh))) (= v_bbbb E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (not (<= (+ (- v_bbaa v_bbdd) 1) (+ v_bbee v_bbff))) (= E_gg E_bb)))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (= E_gg E_bb)))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= E_gg E_bb)))
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)) (= E_gg E_bb)))
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= E_gg E_bb)))) (= v_bbaa v_bbdd))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (or
  (or
  (or
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (= E_gg E_bb)) (= v_bbaa v_bbdd)))
  (and
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= E_gg E_bb)) (= v_bbaa v_bbdd)))
  (and
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= E_gg E_bb)) (= v_bbaa v_bbdd))))))
  (<= (+ (+ v_vv 1) 1) v_tt))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= E_gg E_bb)) (= v_bbaa v_bbdd))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (= E_gg E_ee)) (= v_bbaa v_bbdd))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbcc v_bbgg)))))))

(declare-fun f96 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f96_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f96 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
  v_bbhh v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (not (= v_bbbb E_ff)))))

(declare-fun f97 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f97_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f97 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false)) (mem 
  int (t2tb3 (+ v_bbaa 1)) (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_vv 0)))
  (=> (= E_gg E_ee) (<= v_vv v_tt)))
  (=> (= E_gg E_ff) (= v_bbcc (+ v_bbaa 1))))
  (=> (= E_gg E_cc) (<= v_uu 254)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_hh))) (= v_bbbb E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (not (<= (+ (- v_bbaa v_bbdd) 1) (+ v_bbee v_bbff))) (= E_gg E_bb)))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (= E_gg E_bb)))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= E_gg E_bb)))
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)) (= E_gg E_bb)))
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= E_gg E_bb)))) (= v_bbaa v_bbdd))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (or
  (or
  (or
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (= E_gg E_bb)) (= v_bbaa v_bbdd)))
  (and
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= E_gg E_bb)) (= v_bbaa v_bbdd)))
  (and
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= E_gg E_bb)) (= v_bbaa v_bbdd))))))
  (<= (+ (+ v_vv 1) 1) v_tt))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= E_gg E_bb)) (= v_bbaa v_bbdd))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (= E_gg E_ee)) (= v_bbaa v_bbdd))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbcc v_bbgg)))) (= v_xx false)))))

(declare-fun f98 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f98_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f98 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false)) (mem 
  int (t2tb3 (+ v_bbaa 1)) (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_vv 0)))
  (=> (= E_gg E_ee) (<= v_vv v_tt)))
  (=> (= E_gg E_ff) (= v_bbcc (+ v_bbaa 1))))
  (=> (= E_gg E_cc) (<= v_uu 254)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_hh))) (= v_bbbb E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (not (<= (+ (- v_bbaa v_bbdd) 1) (+ v_bbee v_bbff))) (= E_gg E_bb)))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (= E_gg E_bb)))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= E_gg E_bb)))
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)) (= E_gg E_bb)))
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= E_gg E_bb)))) (= v_bbaa v_bbdd))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (or
  (or
  (or
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (= E_gg E_bb)) (= v_bbaa v_bbdd)))
  (and
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= E_gg E_bb)) (= v_bbaa v_bbdd)))
  (and
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= E_gg E_bb)) (= v_bbaa v_bbdd))))))
  (not (<= (+ (+ v_vv 1) 1) v_tt)))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= E_gg E_bb)) (= v_bbaa v_bbdd))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (= E_gg E_ee)) (= v_bbaa v_bbdd))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbcc v_bbgg)))))))

(declare-fun f99 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f99_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f99 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false)) (mem 
  int (t2tb3 (+ v_bbaa 1)) (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (=> (mem enum_aa1 (t2tb5 E_gg)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_vv 0)))
  (=> (= E_gg E_ee) (<= v_vv v_tt)))
  (=> (= E_gg E_ff) (= v_bbcc (+ v_bbaa 1))))
  (=> (= E_gg E_cc) (<= v_uu 254)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_hh))) (= v_bbbb E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (not (<= (+ (- v_bbaa v_bbdd) 1) (+ v_bbee v_bbff))) (= E_gg E_bb)))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (= E_gg E_bb)))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= E_gg E_bb)))
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)) (= E_gg E_bb)))
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= E_gg E_bb)))) (= v_bbaa v_bbdd))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (or
  (or
  (or
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (= E_gg E_bb)) (= v_bbaa v_bbdd)))
  (and
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= E_gg E_bb)) (= v_bbaa v_bbdd)))
  (and
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= E_gg E_bb)) (= v_bbaa v_bbdd))))))
  (not (<= (+ (+ v_vv 1) 1) v_tt)))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= E_gg E_bb)) (= v_bbaa v_bbdd))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (= E_gg E_ee)) (= v_bbaa v_bbdd))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbcc v_bbgg)))) (= v_xx false)))))

(declare-fun f100 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f100_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f100 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (= v_ww true)) (= v_xx true)) (= v_yy false)) (= v_zz false)) (mem 
  int (t2tb3 (+ v_bbaa 1)) (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_vv 0)))
  (=> (= E_bb E_ee) (<= v_vv v_tt)))
  (=> (= E_bb E_ff) (= v_bbcc (+ v_bbaa 1))))
  (=> (= E_bb E_cc) (<= v_uu 254)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_hh))) (= v_bbbb E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (not (<= (+ (- v_bbaa v_bbdd) 1) (+ v_bbee v_bbff))))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd v_bbaa)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))))))) (<= (+ (+ v_vv 1) 1) v_tt))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false))
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
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false)) (= E_bb 
  E_gg)) (= v_bbcc v_bbgg)) (= v_bbdd (+ v_bbaa 1)))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= E_bb E_gg)) (= v_bbcc v_bbgg)) (= v_bbdd v_bbaa)))) (= v_ww false)))))

(declare-fun f101 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f101_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f101 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (= v_ww true)) (= v_xx true)) (= v_yy false)) (= v_zz false)) (mem 
  int (t2tb3 (+ v_bbaa 1)) (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_vv 0)))
  (=> (= E_bb E_ee) (<= v_vv v_tt)))
  (=> (= E_bb E_ff) (= v_bbcc (+ v_bbaa 1))))
  (=> (= E_bb E_cc) (<= v_uu 254)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_hh))) (= v_bbbb E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (not (<= (+ (- v_bbaa v_bbdd) 1) (+ v_bbee v_bbff))))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd v_bbaa)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))))))) (<= (+ (+ v_vv 1) 1) v_tt))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false))
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
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false)) (= E_bb 
  E_gg)) (= v_bbcc v_bbgg)) (= v_bbdd (+ v_bbaa 1)))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= E_bb E_gg)) (= v_bbcc v_bbgg)) (= v_bbdd v_bbaa)))) (= v_xx false)))))

(declare-fun f102 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f102_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f102 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (= v_ww true)) (= v_xx true)) (= v_yy false)) (= v_zz false)) (mem 
  int (t2tb3 (+ v_bbaa 1)) (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_vv 0)))
  (=> (= E_bb E_ee) (<= v_vv v_tt)))
  (=> (= E_bb E_ff) (= v_bbcc (+ v_bbaa 1))))
  (=> (= E_bb E_cc) (<= v_uu 254)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_hh))) (= v_bbbb E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (not (<= (+ (- v_bbaa v_bbdd) 1) (+ v_bbee v_bbff))))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd v_bbaa)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))))))) (<= (+ (+ v_vv 1) 1) v_tt))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false))
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
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false)) (= E_bb 
  E_gg)) (= v_bbcc v_bbgg)) (= v_bbdd (+ v_bbaa 1)))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= E_bb E_gg)) (= v_bbcc v_bbgg)) (= v_bbdd v_bbaa))))
  (not (= v_ww false))) (not (= v_xx false))) (not (= v_yy true)))
  (not (= v_zz true))))))

(declare-fun f103 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f103_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f103 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (= v_ww true)) (= v_xx true)) (= v_yy false)) (= v_zz false)) (mem 
  int (t2tb3 (+ v_bbaa 1)) (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_vv 0)))
  (=> (= E_bb E_ee) (<= v_vv v_tt)))
  (=> (= E_bb E_ff) (= v_bbcc (+ v_bbaa 1))))
  (=> (= E_bb E_cc) (<= v_uu 254)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_hh))) (= v_bbbb E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (not (<= (+ (- v_bbaa v_bbdd) 1) (+ v_bbee v_bbff))))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd v_bbaa)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))))))) (not (<= (+ (+ v_vv 1) 1) v_tt)))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false))
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
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false)) (= E_bb 
  E_gg)) (= v_bbcc v_bbgg)) (= v_bbdd (+ v_bbaa 1)))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= E_bb E_gg)) (= v_bbcc v_bbgg)) (= v_bbdd v_bbaa)))) (= v_ww false)))))

(declare-fun f104 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f104_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f104 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (= v_ww true)) (= v_xx true)) (= v_yy false)) (= v_zz false)) (mem 
  int (t2tb3 (+ v_bbaa 1)) (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_vv 0)))
  (=> (= E_bb E_ee) (<= v_vv v_tt)))
  (=> (= E_bb E_ff) (= v_bbcc (+ v_bbaa 1))))
  (=> (= E_bb E_cc) (<= v_uu 254)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_hh))) (= v_bbbb E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (not (<= (+ (- v_bbaa v_bbdd) 1) (+ v_bbee v_bbff))))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd v_bbaa)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))))))) (not (<= (+ (+ v_vv 1) 1) v_tt)))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false))
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
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false)) (= E_bb 
  E_gg)) (= v_bbcc v_bbgg)) (= v_bbdd (+ v_bbaa 1)))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= E_bb E_gg)) (= v_bbcc v_bbgg)) (= v_bbdd v_bbaa)))) (= v_xx false)))))

(declare-fun f105 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f105_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f105 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (= v_ww true)) (= v_xx true)) (= v_yy false)) (= v_zz false)) (mem 
  int (t2tb3 (+ v_bbaa 1)) (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_vv 0)))
  (=> (= E_bb E_ee) (<= v_vv v_tt)))
  (=> (= E_bb E_ff) (= v_bbcc (+ v_bbaa 1))))
  (=> (= E_bb E_cc) (<= v_uu 254)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_hh))) (= v_bbbb E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (not (<= (+ (- v_bbaa v_bbdd) 1) (+ v_bbee v_bbff))))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd v_bbaa)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))))))) (not (<= (+ (+ v_vv 1) 1) v_tt)))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false))
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
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false)) (= E_bb 
  E_gg)) (= v_bbcc v_bbgg)) (= v_bbdd (+ v_bbaa 1)))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= E_bb E_gg)) (= v_bbcc v_bbgg)) (= v_bbdd v_bbaa))))
  (not (= v_ww false))) (not (= v_xx false))) (not (= v_yy true)))
  (not (= v_zz true))))))

(declare-fun f106 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f106_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f106 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false)) (mem int
  (t2tb3 (+ v_bbaa 1)) (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_vv 0)))
  (=> (= E_bb E_ee) (<= v_vv v_tt)))
  (=> (= E_bb E_ff) (= v_bbcc (+ v_bbaa 1))))
  (=> (= E_bb E_cc) (<= v_uu 254)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_hh))) (= v_bbbb E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (not (<= (+ (- v_bbaa v_bbdd) 1) (+ v_bbee v_bbff))))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd v_bbaa)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))))))) (<= (+ (+ v_vv 1) 1) v_tt))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false))
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
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false)) (= E_bb 
  E_gg)) (= v_bbcc v_bbgg)) (= v_bbdd (+ v_bbaa 1)))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= E_bb E_gg)) (= v_bbcc v_bbgg)) (= v_bbdd v_bbaa)))) (= v_ww false)))))

(declare-fun f107 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f107_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f107 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false)) (mem int
  (t2tb3 (+ v_bbaa 1)) (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_vv 0)))
  (=> (= E_bb E_ee) (<= v_vv v_tt)))
  (=> (= E_bb E_ff) (= v_bbcc (+ v_bbaa 1))))
  (=> (= E_bb E_cc) (<= v_uu 254)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_hh))) (= v_bbbb E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (not (<= (+ (- v_bbaa v_bbdd) 1) (+ v_bbee v_bbff))))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd v_bbaa)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))))))) (<= (+ (+ v_vv 1) 1) v_tt))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false))
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
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false)) (= E_bb 
  E_gg)) (= v_bbcc v_bbgg)) (= v_bbdd (+ v_bbaa 1)))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= E_bb E_gg)) (= v_bbcc v_bbgg)) (= v_bbdd v_bbaa)))) (= v_xx false)))))

(declare-fun f108 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f108_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f108 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false)) (mem int
  (t2tb3 (+ v_bbaa 1)) (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_vv 0)))
  (=> (= E_bb E_ee) (<= v_vv v_tt)))
  (=> (= E_bb E_ff) (= v_bbcc (+ v_bbaa 1))))
  (=> (= E_bb E_cc) (<= v_uu 254)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_hh))) (= v_bbbb E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (not (<= (+ (- v_bbaa v_bbdd) 1) (+ v_bbee v_bbff))))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd v_bbaa)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))))))) (<= (+ (+ v_vv 1) 1) v_tt))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false))
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
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false)) (= E_bb 
  E_gg)) (= v_bbcc v_bbgg)) (= v_bbdd (+ v_bbaa 1)))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= E_bb E_gg)) (= v_bbcc v_bbgg)) (= v_bbdd v_bbaa)))))))

(declare-fun f109 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f109_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f109 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false)) (mem int
  (t2tb3 (+ v_bbaa 1)) (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_vv 0)))
  (=> (= E_bb E_ee) (<= v_vv v_tt)))
  (=> (= E_bb E_ff) (= v_bbcc (+ v_bbaa 1))))
  (=> (= E_bb E_cc) (<= v_uu 254)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_hh))) (= v_bbbb E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (not (<= (+ (- v_bbaa v_bbdd) 1) (+ v_bbee v_bbff))))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd v_bbaa)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))))))) (not (<= (+ (+ v_vv 1) 1) v_tt)))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false))
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
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false)) (= E_bb 
  E_gg)) (= v_bbcc v_bbgg)) (= v_bbdd (+ v_bbaa 1)))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= E_bb E_gg)) (= v_bbcc v_bbgg)) (= v_bbdd v_bbaa)))) (= v_ww false)))))

(declare-fun f110 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f110_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f110 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false)) (mem int
  (t2tb3 (+ v_bbaa 1)) (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_vv 0)))
  (=> (= E_bb E_ee) (<= v_vv v_tt)))
  (=> (= E_bb E_ff) (= v_bbcc (+ v_bbaa 1))))
  (=> (= E_bb E_cc) (<= v_uu 254)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_hh))) (= v_bbbb E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (not (<= (+ (- v_bbaa v_bbdd) 1) (+ v_bbee v_bbff))))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd v_bbaa)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))))))) (not (<= (+ (+ v_vv 1) 1) v_tt)))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false))
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
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false)) (= E_bb 
  E_gg)) (= v_bbcc v_bbgg)) (= v_bbdd (+ v_bbaa 1)))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= E_bb E_gg)) (= v_bbcc v_bbgg)) (= v_bbdd v_bbaa)))) (= v_xx false)))))

(declare-fun f111 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f111_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f111 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false)) (mem int
  (t2tb3 (+ v_bbaa 1)) (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_vv 0)))
  (=> (= E_bb E_ee) (<= v_vv v_tt)))
  (=> (= E_bb E_ff) (= v_bbcc (+ v_bbaa 1))))
  (=> (= E_bb E_cc) (<= v_uu 254)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_hh))) (= v_bbbb E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (not (<= (+ (- v_bbaa v_bbdd) 1) (+ v_bbee v_bbff))))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd v_bbaa)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))))))) (not (<= (+ (+ v_vv 1) 1) v_tt)))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false))
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
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false)) (= E_bb 
  E_gg)) (= v_bbcc v_bbgg)) (= v_bbdd (+ v_bbaa 1)))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= E_bb E_gg)) (= v_bbcc v_bbgg)) (= v_bbdd v_bbaa)))))))

(declare-fun f112 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f112_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f112 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false)) (mem 
  int (t2tb3 (+ v_bbaa 1)) (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_ii)))
  (= (+ v_bbaa 1) v_bbcc))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_hh))) (= v_bbbb E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (or (<= (+ (- v_bbaa v_bbdd) 1) (+ v_bbee v_bbff))
  (and (not (<= (+ (- v_bbaa v_bbdd) 1) (+ v_bbee v_bbff))) (= v_bbbb E_bb))))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (= v_bbbb E_bb)))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbbb E_bb)))
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)) (= v_bbbb E_bb)))
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= v_bbbb E_bb)))) (= (+ v_bbaa 1) v_bbcc))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (or
  (or
  (and
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (= v_bbbb E_gg) (= v_bbdd v_bbaa)))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (= v_bbbb E_bb)))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbbb E_bb))) (= (+ v_bbaa 1) v_bbcc))
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))
  (and
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= v_bbbb E_bb)) (= (+ v_bbaa 1) v_bbcc))))))
  (<= (+ (+ v_vv 1) 1) v_tt))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= v_bbbb E_bb)) (= (+ v_bbaa 1) v_bbcc))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (= v_bbbb E_ee)) (= (+ v_bbaa 1) v_bbcc))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbbb E_gg)) (= (+ v_bbaa 1) v_bbgg)) (= v_bbdd (+ v_bbaa 1)))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww true)) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (= (+ v_bbaa 1) v_bbcc))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbbb E_gg)) (= (+ v_bbaa 1) v_bbgg)) (= v_bbdd v_bbaa)))))))

(declare-fun f113 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f113_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f113 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false)) (mem 
  int (t2tb3 (+ v_bbaa 1)) (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_ii)))
  (= (+ v_bbaa 1) v_bbcc))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_hh))) (= v_bbbb E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (or (<= (+ (- v_bbaa v_bbdd) 1) (+ v_bbee v_bbff))
  (and (not (<= (+ (- v_bbaa v_bbdd) 1) (+ v_bbee v_bbff))) (= v_bbbb E_bb))))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (= v_bbbb E_bb)))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbbb E_bb)))
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)) (= v_bbbb E_bb)))
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= v_bbbb E_bb)))) (= (+ v_bbaa 1) v_bbcc))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (or
  (or
  (and
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (= v_bbbb E_gg) (= v_bbdd v_bbaa)))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (= v_bbbb E_bb)))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbbb E_bb))) (= (+ v_bbaa 1) v_bbcc))
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))
  (and
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= v_bbbb E_bb)) (= (+ v_bbaa 1) v_bbcc))))))
  (<= (+ (+ v_vv 1) 1) v_tt))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= v_bbbb E_bb)) (= (+ v_bbaa 1) v_bbcc))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (= v_bbbb E_ee)) (= (+ v_bbaa 1) v_bbcc))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbbb E_gg)) (= (+ v_bbaa 1) v_bbgg)) (= v_bbdd (+ v_bbaa 1)))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww true)) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (= (+ v_bbaa 1) v_bbcc))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbbb E_gg)) (= (+ v_bbaa 1) v_bbgg)) (= v_bbdd v_bbaa))))
  (= v_xx false)))))

(declare-fun f114 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f114_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f114 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false)) (mem 
  int (t2tb3 (+ v_bbaa 1)) (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_ii)))
  (= (+ v_bbaa 1) v_bbcc))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_hh))) (= v_bbbb E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (or (<= (+ (- v_bbaa v_bbdd) 1) (+ v_bbee v_bbff))
  (and (not (<= (+ (- v_bbaa v_bbdd) 1) (+ v_bbee v_bbff))) (= v_bbbb E_bb))))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (= v_bbbb E_bb)))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbbb E_bb)))
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)) (= v_bbbb E_bb)))
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= v_bbbb E_bb)))) (= (+ v_bbaa 1) v_bbcc))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (or
  (or
  (and
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (= v_bbbb E_gg) (= v_bbdd v_bbaa)))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (= v_bbbb E_bb)))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbbb E_bb))) (= (+ v_bbaa 1) v_bbcc))
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))
  (and
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= v_bbbb E_bb)) (= (+ v_bbaa 1) v_bbcc))))))
  (not (<= (+ (+ v_vv 1) 1) v_tt)))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= v_bbbb E_bb)) (= (+ v_bbaa 1) v_bbcc))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (= v_bbbb E_ee)) (= (+ v_bbaa 1) v_bbcc))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbbb E_gg)) (= (+ v_bbaa 1) v_bbgg)) (= v_bbdd (+ v_bbaa 1)))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww true)) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (= (+ v_bbaa 1) v_bbcc))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbbb E_gg)) (= (+ v_bbaa 1) v_bbgg)) (= v_bbdd v_bbaa)))))))

(declare-fun f115 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f115_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f115 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false)) (mem 
  int (t2tb3 (+ v_bbaa 1)) (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_ii)))
  (= (+ v_bbaa 1) v_bbcc))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_hh))) (= v_bbbb E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (or (<= (+ (- v_bbaa v_bbdd) 1) (+ v_bbee v_bbff))
  (and (not (<= (+ (- v_bbaa v_bbdd) 1) (+ v_bbee v_bbff))) (= v_bbbb E_bb))))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (= v_bbbb E_bb)))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbbb E_bb)))
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)) (= v_bbbb E_bb)))
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= v_bbbb E_bb)))) (= (+ v_bbaa 1) v_bbcc))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (or
  (or
  (and
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (= v_bbbb E_gg) (= v_bbdd v_bbaa)))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (= v_bbbb E_bb)))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbbb E_bb))) (= (+ v_bbaa 1) v_bbcc))
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))
  (and
  (and
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= v_bbbb E_bb)) (= (+ v_bbaa 1) v_bbcc))))))
  (not (<= (+ (+ v_vv 1) 1) v_tt)))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= v_bbbb E_bb)) (= (+ v_bbaa 1) v_bbcc))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (= v_bbbb E_ee)) (= (+ v_bbaa 1) v_bbcc))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbbb E_gg)) (= (+ v_bbaa 1) v_bbgg)) (= v_bbdd (+ v_bbaa 1)))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww true)) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (= (+ v_bbaa 1) v_bbcc))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbbb E_gg)) (= (+ v_bbaa 1) v_bbgg)) (= v_bbdd v_bbaa))))
  (= v_xx false)))))

(declare-fun f116 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f116_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f116 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= v_bbbb E_ff)) (mem int (t2tb3 (+ v_bbaa 1))
  (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_vv 0)))
  (=> (= E_bb E_ee) (<= v_vv v_tt)))
  (=> (= E_bb E_ff) (= v_bbcc (+ v_bbaa 1))))
  (=> (= E_bb E_cc) (<= v_uu 254)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_hh))) (= v_bbbb E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (not (<= (+ (- v_bbaa v_bbdd) 1) (+ v_bbee v_bbff))))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd v_bbaa)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))))))) (<= (+ (+ v_vv 1) 1) v_tt))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false))
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
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false)) (= E_bb 
  E_gg)) (= v_bbcc v_bbgg)) (= v_bbdd (+ v_bbaa 1)))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= E_bb E_gg)) (= v_bbcc v_bbgg)) (= v_bbdd v_bbaa)))) (= v_ww false)))))

(declare-fun f117 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f117_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f117 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= v_bbbb E_ff)) (mem int (t2tb3 (+ v_bbaa 1))
  (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_vv 0)))
  (=> (= E_bb E_ee) (<= v_vv v_tt)))
  (=> (= E_bb E_ff) (= v_bbcc (+ v_bbaa 1))))
  (=> (= E_bb E_cc) (<= v_uu 254)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_hh))) (= v_bbbb E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (not (<= (+ (- v_bbaa v_bbdd) 1) (+ v_bbee v_bbff))))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd v_bbaa)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))))))) (<= (+ (+ v_vv 1) 1) v_tt))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false))
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
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false)) (= E_bb 
  E_gg)) (= v_bbcc v_bbgg)) (= v_bbdd (+ v_bbaa 1)))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= E_bb E_gg)) (= v_bbcc v_bbgg)) (= v_bbdd v_bbaa)))) (= v_xx false)))))

(declare-fun f118 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f118_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f118 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= v_bbbb E_ff)) (mem int (t2tb3 (+ v_bbaa 1))
  (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_vv 0)))
  (=> (= E_bb E_ee) (<= v_vv v_tt)))
  (=> (= E_bb E_ff) (= v_bbcc (+ v_bbaa 1))))
  (=> (= E_bb E_cc) (<= v_uu 254)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_hh))) (= v_bbbb E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (not (<= (+ (- v_bbaa v_bbdd) 1) (+ v_bbee v_bbff))))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd v_bbaa)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))))))) (<= (+ (+ v_vv 1) 1) v_tt))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false))
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
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false)) (= E_bb 
  E_gg)) (= v_bbcc v_bbgg)) (= v_bbdd (+ v_bbaa 1)))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= E_bb E_gg)) (= v_bbcc v_bbgg)) (= v_bbdd v_bbaa)))) (= v_yy true)))))

(declare-fun f119 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f119_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f119 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= v_bbbb E_ff)) (mem int (t2tb3 (+ v_bbaa 1))
  (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_vv 0)))
  (=> (= E_bb E_ee) (<= v_vv v_tt)))
  (=> (= E_bb E_ff) (= v_bbcc (+ v_bbaa 1))))
  (=> (= E_bb E_cc) (<= v_uu 254)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_hh))) (= v_bbbb E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (not (<= (+ (- v_bbaa v_bbdd) 1) (+ v_bbee v_bbff))))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd v_bbaa)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))))))) (<= (+ (+ v_vv 1) 1) v_tt))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false))
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
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false)) (= E_bb 
  E_gg)) (= v_bbcc v_bbgg)) (= v_bbdd (+ v_bbaa 1)))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= E_bb E_gg)) (= v_bbcc v_bbgg)) (= v_bbdd v_bbaa)))) (= v_zz true)))))

(declare-fun f120 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f120_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f120 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= v_bbbb E_ff)) (mem int (t2tb3 (+ v_bbaa 1))
  (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_vv 0)))
  (=> (= E_bb E_ee) (<= v_vv v_tt)))
  (=> (= E_bb E_ff) (= v_bbcc (+ v_bbaa 1))))
  (=> (= E_bb E_cc) (<= v_uu 254)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_hh))) (= v_bbbb E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (not (<= (+ (- v_bbaa v_bbdd) 1) (+ v_bbee v_bbff))))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd v_bbaa)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))))))) (<= (+ (+ v_vv 1) 1) v_tt))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false))
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
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false)) (= E_bb 
  E_gg)) (= v_bbcc v_bbgg)) (= v_bbdd (+ v_bbaa 1)))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= E_bb E_gg)) (= v_bbcc v_bbgg)) (= v_bbdd v_bbaa))))
  (not (= v_ww false))) (not (= v_xx false))) (not (= v_yy true)))
  (not (= v_zz true))))))

(declare-fun f121 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f121_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f121 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= v_bbbb E_ff)) (mem int (t2tb3 (+ v_bbaa 1))
  (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_vv 0)))
  (=> (= E_bb E_ee) (<= v_vv v_tt)))
  (=> (= E_bb E_ff) (= v_bbcc (+ v_bbaa 1))))
  (=> (= E_bb E_cc) (<= v_uu 254)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_hh))) (= v_bbbb E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (not (<= (+ (- v_bbaa v_bbdd) 1) (+ v_bbee v_bbff))))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd v_bbaa)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))))))) (not (<= (+ (+ v_vv 1) 1) v_tt)))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false))
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
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false)) (= E_bb 
  E_gg)) (= v_bbcc v_bbgg)) (= v_bbdd (+ v_bbaa 1)))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= E_bb E_gg)) (= v_bbcc v_bbgg)) (= v_bbdd v_bbaa)))) (= v_ww false)))))

(declare-fun f122 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f122_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f122 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= v_bbbb E_ff)) (mem int (t2tb3 (+ v_bbaa 1))
  (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_vv 0)))
  (=> (= E_bb E_ee) (<= v_vv v_tt)))
  (=> (= E_bb E_ff) (= v_bbcc (+ v_bbaa 1))))
  (=> (= E_bb E_cc) (<= v_uu 254)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_hh))) (= v_bbbb E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (not (<= (+ (- v_bbaa v_bbdd) 1) (+ v_bbee v_bbff))))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd v_bbaa)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))))))) (not (<= (+ (+ v_vv 1) 1) v_tt)))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false))
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
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false)) (= E_bb 
  E_gg)) (= v_bbcc v_bbgg)) (= v_bbdd (+ v_bbaa 1)))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= E_bb E_gg)) (= v_bbcc v_bbgg)) (= v_bbdd v_bbaa)))) (= v_xx false)))))

(declare-fun f123 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f123_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f123 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= v_bbbb E_ff)) (mem int (t2tb3 (+ v_bbaa 1))
  (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_vv 0)))
  (=> (= E_bb E_ee) (<= v_vv v_tt)))
  (=> (= E_bb E_ff) (= v_bbcc (+ v_bbaa 1))))
  (=> (= E_bb E_cc) (<= v_uu 254)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_hh))) (= v_bbbb E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (not (<= (+ (- v_bbaa v_bbdd) 1) (+ v_bbee v_bbff))))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd v_bbaa)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))))))) (not (<= (+ (+ v_vv 1) 1) v_tt)))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false))
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
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false)) (= E_bb 
  E_gg)) (= v_bbcc v_bbgg)) (= v_bbdd (+ v_bbaa 1)))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= E_bb E_gg)) (= v_bbcc v_bbgg)) (= v_bbdd v_bbaa)))) (= v_yy true)))))

(declare-fun f124 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f124_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f124 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= v_bbbb E_ff)) (mem int (t2tb3 (+ v_bbaa 1))
  (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_vv 0)))
  (=> (= E_bb E_ee) (<= v_vv v_tt)))
  (=> (= E_bb E_ff) (= v_bbcc (+ v_bbaa 1))))
  (=> (= E_bb E_cc) (<= v_uu 254)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_hh))) (= v_bbbb E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (not (<= (+ (- v_bbaa v_bbdd) 1) (+ v_bbee v_bbff))))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd v_bbaa)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))))))) (not (<= (+ (+ v_vv 1) 1) v_tt)))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false))
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
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false)) (= E_bb 
  E_gg)) (= v_bbcc v_bbgg)) (= v_bbdd (+ v_bbaa 1)))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= E_bb E_gg)) (= v_bbcc v_bbgg)) (= v_bbdd v_bbaa)))) (= v_zz true)))))

(declare-fun f125 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f125_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f125 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))) (= v_bbbb E_ff)) (mem int (t2tb3 (+ v_bbaa 1))
  (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= v_vv 0)))
  (=> (= E_bb E_ee) (<= v_vv v_tt)))
  (=> (= E_bb E_ff) (= v_bbcc (+ v_bbaa 1))))
  (=> (= E_bb E_cc) (<= v_uu 254)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_hh))) (= v_bbbb E_ii))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (not (<= (+ (- v_bbaa v_bbdd) 1) (+ v_bbee v_bbff))))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ii)))
  (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg))) (= v_bbbb E_ff))
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd v_bbaa)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false)))
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))))))) (not (<= (+ (+ v_vv 1) 1) v_tt)))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false))
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
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false)) (= E_bb 
  E_gg)) (= v_bbcc v_bbgg)) (= v_bbdd (+ v_bbaa 1)))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (not (= v_bbbb E_gg)))
  (not (= v_bbbb E_ff))) (not (= v_bbbb E_ee))) (= v_bbbb E_dd))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= E_bb E_gg)) (= v_bbcc v_bbgg)) (= v_bbdd v_bbaa))))
  (not (= v_ww false))) (not (= v_xx false))) (not (= v_yy true)))
  (not (= v_zz true))))))

(declare-fun f126 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f126_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f126 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (= v_bbbb E_gg)) (mem 
  int (t2tb3 (+ v_vv 1)) (t2tb2 integer))) (<= 0 (+ v_vv 1))) (mem int
  (t2tb3 (+ v_bbaa 1)) (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= (+ v_vv 1) 0)))
  (=> (= E_bb E_ee) (<= (+ v_vv 1) v_tt)))
  (=> (= E_bb E_ff) (= v_bbcc (+ v_bbaa 1))))
  (=> (= E_bb E_cc) (<= v_uu 254)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ii))) (= v_bbbb E_hh))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (not (<= (+ (- (- (+ v_bbaa 1) v_bbdd) 1) 1) v_bbee)) (= E_bb E_ii)))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)) (and (= E_bb E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (= v_bbbb E_gg))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))))) (<= (+ (+ v_vv 1) 1) v_tt))
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
  (and (and (and (= E_bb E_ee) (not (= v_bbbb E_bb))) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbcc v_bbhh)) (= v_bbdd (+ v_bbaa 1))) (= E_bb E_gg))))
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
  (and (and (and (= E_bb E_ee) (not (= v_bbbb E_bb))) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww true)) (= v_xx true)) (= v_yy false)) (= v_zz false))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbcc v_bbhh)) (= v_bbdd v_bbaa)) (= E_bb E_gg)))) (= v_ww false)))))

(declare-fun f127 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f127_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f127 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
  v_bbhh v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (not (= v_bbbb E_gg)))))

(declare-fun f128 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f128_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f128 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (= v_bbbb E_gg)) (mem 
  int (t2tb3 (+ v_vv 1)) (t2tb2 integer))) (<= 0 (+ v_vv 1))) (mem int
  (t2tb3 (+ v_bbaa 1)) (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= (+ v_vv 1) 0)))
  (=> (= E_bb E_ee) (<= (+ v_vv 1) v_tt)))
  (=> (= E_bb E_ff) (= v_bbcc (+ v_bbaa 1))))
  (=> (= E_bb E_cc) (<= v_uu 254)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ii))) (= v_bbbb E_hh))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (not (<= (+ (- (- (+ v_bbaa 1) v_bbdd) 1) 1) v_bbee)) (= E_bb E_ii)))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)) (and (= E_bb E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (= v_bbbb E_gg))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))))) (<= (+ (+ v_vv 1) 1) v_tt))
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
  (and (and (and (= E_bb E_ee) (not (= v_bbbb E_bb))) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbcc v_bbhh)) (= v_bbdd (+ v_bbaa 1))) (= E_bb E_gg))))
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
  (and (and (and (= E_bb E_ee) (not (= v_bbbb E_bb))) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww true)) (= v_xx true)) (= v_yy false)) (= v_zz false))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbcc v_bbhh)) (= v_bbdd v_bbaa)) (= E_bb E_gg)))) (= v_xx false)))))

(declare-fun f129 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f129_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f129 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (= v_bbbb E_gg)) (mem 
  int (t2tb3 (+ v_vv 1)) (t2tb2 integer))) (<= 0 (+ v_vv 1))) (mem int
  (t2tb3 (+ v_bbaa 1)) (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= (+ v_vv 1) 0)))
  (=> (= E_bb E_ee) (<= (+ v_vv 1) v_tt)))
  (=> (= E_bb E_ff) (= v_bbcc (+ v_bbaa 1))))
  (=> (= E_bb E_cc) (<= v_uu 254)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ii))) (= v_bbbb E_hh))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (not (<= (+ (- (- (+ v_bbaa 1) v_bbdd) 1) 1) v_bbee)) (= E_bb E_ii)))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)) (and (= E_bb E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (= v_bbbb E_gg))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))))) (<= (+ (+ v_vv 1) 1) v_tt))
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
  (and (and (and (= E_bb E_ee) (not (= v_bbbb E_bb))) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbcc v_bbhh)) (= v_bbdd (+ v_bbaa 1))) (= E_bb E_gg))))
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
  (and (and (and (= E_bb E_ee) (not (= v_bbbb E_bb))) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww true)) (= v_xx true)) (= v_yy false)) (= v_zz false))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbcc v_bbhh)) (= v_bbdd v_bbaa)) (= E_bb E_gg)))) (= v_yy true)))))

(declare-fun f130 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f130_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f130 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (= v_bbbb E_gg)) (mem 
  int (t2tb3 (+ v_vv 1)) (t2tb2 integer))) (<= 0 (+ v_vv 1))) (mem int
  (t2tb3 (+ v_bbaa 1)) (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= (+ v_vv 1) 0)))
  (=> (= E_bb E_ee) (<= (+ v_vv 1) v_tt)))
  (=> (= E_bb E_ff) (= v_bbcc (+ v_bbaa 1))))
  (=> (= E_bb E_cc) (<= v_uu 254)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ii))) (= v_bbbb E_hh))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (not (<= (+ (- (- (+ v_bbaa 1) v_bbdd) 1) 1) v_bbee)) (= E_bb E_ii)))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)) (and (= E_bb E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (= v_bbbb E_gg))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))))) (<= (+ (+ v_vv 1) 1) v_tt))
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
  (and (and (and (= E_bb E_ee) (not (= v_bbbb E_bb))) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbcc v_bbhh)) (= v_bbdd (+ v_bbaa 1))) (= E_bb E_gg))))
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
  (and (and (and (= E_bb E_ee) (not (= v_bbbb E_bb))) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww true)) (= v_xx true)) (= v_yy false)) (= v_zz false))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbcc v_bbhh)) (= v_bbdd v_bbaa)) (= E_bb E_gg)))) (= v_zz true)))))

(declare-fun f131 (Bool Bool Bool Bool Int Int Int Int Int enum_aa Bool Bool
  Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int
  Int enum_aa Int) Bool)

;; f131_def
  (assert
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (= (f131 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (= v_bbbb E_gg)) (mem 
  int (t2tb3 (+ v_vv 1)) (t2tb2 integer))) (<= 0 (+ v_vv 1))) (mem int
  (t2tb3 (+ v_bbaa 1)) (t2tb2 integer))) (<= 0 (+ v_bbaa 1)))
  (=> (mem enum_aa1 (t2tb5 E_bb)
  (union enum_aa1 (add enum_aa1 (t2tb5 E_cc) (empty enum_aa1))
  (add enum_aa1 (t2tb5 E_dd) (empty enum_aa1)))) (= (+ v_vv 1) 0)))
  (=> (= E_bb E_ee) (<= (+ v_vv 1) v_tt)))
  (=> (= E_bb E_ff) (= v_bbcc (+ v_bbaa 1))))
  (=> (= E_bb E_cc) (<= v_uu 254)))
  (not
  (and
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ii))) (= v_bbbb E_hh))
  (or
  (or
  (or
  (or
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (not (<= (+ (- (- (+ v_bbaa 1) v_bbdd) 1) 1) v_bbee)) (= E_bb E_ii)))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (and (= E_bb E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)) (and (= E_bb E_gg) (= v_bbdd (+ v_bbaa 1)))))
  (and
  (and
  (and
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false)))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false))))))))
  (not
  (and
  (and
  (and
  (and
  (and
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ee))) (not (= v_bbbb E_ff)))
  (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh))) (= v_bbbb E_gg))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy false)) (= v_zz false))))
  (not
  (and (and (and (= v_ww true) (= v_xx true)) (= v_yy true)) (= v_zz false))))
  (not
  (and (and (and (= v_ww false) (= v_xx true)) (= v_yy false))
  (= v_zz false)))))) (<= (+ (+ v_vv 1) 1) v_tt))
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
  (and (and (and (= E_bb E_ee) (not (= v_bbbb E_bb))) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww false)) (= v_xx true)) (= v_yy false)) (= v_zz false))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww true)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbcc v_bbhh)) (= v_bbdd (+ v_bbaa 1))) (= E_bb E_gg))))
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
  (and (and (and (= E_bb E_ee) (not (= v_bbbb E_bb))) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww true)) (= v_xx true)) (= v_yy false)) (= v_zz false))))
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
  (and (and (not (= v_bbbb E_bb)) (not (= v_bbbb E_cc)))
  (not (= v_bbbb E_dd))) (not (= v_bbbb E_ii))) (not (= v_bbbb E_hh)))
  (not (= v_bbbb E_gg))) (not (= v_bbbb E_ff))) (= v_bbbb E_ee))
  (= v_ww false)) (= v_xx true)) (= v_yy true)) (= v_zz false))
  (= v_bbcc v_bbhh)) (= v_bbdd v_bbaa)) (= E_bb E_gg))))
  (not (= v_ww false))) (not (= v_xx false))) (not (= v_yy true)))
  (not (= v_zz true))))))

(assert
;; bbqq_260
 ;; File "POwhy_bpo2why/p4/p4_8_part4.why", line 5726, characters 7-15
  (not
  (forall ((v_zz Bool) (v_yy Bool) (v_xx Bool) (v_ww Bool) (v_vv Int)
  (v_uu Int) (v_tt Int) (v_ss Int) (v_rr Int) (v_qq enum_aa) (v_pp Bool)
  (v_oo Bool) (v_nn Bool) (v_mm Bool) (v_ll Int) (v_kk Int) (v_jj Int)
  (v_bbpp Int) (v_bboo Int) (v_bbnn Int) (v_bbmm Int) (v_bbll Int)
  (v_bbkk Int) (v_bbjj Int) (v_bbii Int) (v_bbhh Int) (v_bbgg Int)
  (v_bbff Int) (v_bbee Int) (v_bbdd Int) (v_bbcc Int) (v_bbbb enum_aa)
  (v_bbaa Int))
  (=>
  (and (f1 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
  v_bbhh v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (and (f2 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
  v_bbhh v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)
  (and (f3 v_zz v_yy v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn
  v_mm v_ll v_kk v_jj v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii
  v_bbhh v_bbgg v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa) (f81 v_zz v_yy
  v_xx v_ww v_vv v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn v_mm v_ll v_kk v_jj
  v_bbpp v_bboo v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii v_bbhh v_bbgg
  v_bbff v_bbee v_bbdd v_bbcc v_bbbb v_bbaa)))) (f60 v_zz v_yy v_xx v_ww v_vv
  v_uu v_tt v_ss v_rr v_qq v_pp v_oo v_nn v_mm v_ll v_kk v_jj v_bbpp v_bboo
  v_bbnn v_bbmm v_bbll v_bbkk v_bbjj v_bbii v_bbhh v_bbgg v_bbff v_bbee
  v_bbdd v_bbcc v_bbbb v_bbaa)))))
(check-sat)
