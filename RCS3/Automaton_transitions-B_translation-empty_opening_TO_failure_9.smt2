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

(declare-fun power1 (ty uni) uni)

;; power_sort
  (assert
  (forall ((a ty)) (forall ((x uni)) (sort (set1 (set1 a)) (power1 a x)))))

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
  (= (relations b a u v) (power1 (tuple21 a b) (times b a u v))))))

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
  (= (mem (set1 (tuple21 a b)) r (power1 (tuple21 a b) (times b a u v)))
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

(declare-sort enum_t_AUTOMATON_STATE 0)

(declare-fun enum_t_AUTOMATON_STATE1 () ty)

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

(declare-fun t2tb4 ((set enum_t_AUTOMATON_STATE)) uni)

;; t2tb_sort
  (assert
  (forall ((x (set enum_t_AUTOMATON_STATE))) (sort
  (set1 enum_t_AUTOMATON_STATE1) (t2tb4 x))))

(declare-fun tb2t4 (uni) (set enum_t_AUTOMATON_STATE))

;; BridgeL
  (assert
  (forall ((i (set enum_t_AUTOMATON_STATE)))
  (! (= (tb2t4 (t2tb4 i)) i) :pattern ((t2tb4 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 enum_t_AUTOMATON_STATE1) j) (= (t2tb4 (tb2t4 j)) j)) :pattern (
  (t2tb4 (tb2t4 j))) )))

(declare-fun t2tb5 (enum_t_AUTOMATON_STATE) uni)

;; t2tb_sort
  (assert
  (forall ((x enum_t_AUTOMATON_STATE)) (sort enum_t_AUTOMATON_STATE1
  (t2tb5 x))))

(declare-fun tb2t5 (uni) enum_t_AUTOMATON_STATE)

;; BridgeL
  (assert
  (forall ((i enum_t_AUTOMATON_STATE))
  (! (= (tb2t5 (t2tb5 i)) i) :pattern ((t2tb5 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort enum_t_AUTOMATON_STATE1 j) (= (t2tb5 (tb2t5 j)) j)) :pattern (
  (t2tb5 (tb2t5 j))) )))

;; set_enum_t_AUTOMATON_STATE_axiom
  (assert
  (forall ((x enum_t_AUTOMATON_STATE)) (mem enum_t_AUTOMATON_STATE1 (t2tb5 x)
  (t2tb4 set_enum_t_AUTOMATON_STATE))))

(declare-sort enum_t_BOOM_MOVEMENT_ORDER 0)

(declare-fun enum_t_BOOM_MOVEMENT_ORDER1 () ty)

(declare-fun E_go_up () enum_t_BOOM_MOVEMENT_ORDER)

(declare-fun E_go_down () enum_t_BOOM_MOVEMENT_ORDER)

(declare-fun match_enum_t_BOOM_MOVEMENT_ORDER (ty enum_t_BOOM_MOVEMENT_ORDER
  uni uni) uni)

;; match_enum_t_BOOM_MOVEMENT_ORDER_sort
  (assert
  (forall ((a ty))
  (forall ((x enum_t_BOOM_MOVEMENT_ORDER) (x1 uni) (x2 uni)) (sort a
  (match_enum_t_BOOM_MOVEMENT_ORDER a x x1 x2)))))

;; match_enum_t_BOOM_MOVEMENT_ORDER_E_go_up
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni))
  (=> (sort a z) (= (match_enum_t_BOOM_MOVEMENT_ORDER a E_go_up z z1) z)))))

;; match_enum_t_BOOM_MOVEMENT_ORDER_E_go_down
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni))
  (=> (sort a z1) (= (match_enum_t_BOOM_MOVEMENT_ORDER a E_go_down z z1) z1)))))

(declare-fun index_enum_t_BOOM_MOVEMENT_ORDER (enum_t_BOOM_MOVEMENT_ORDER) Int)

;; index_enum_t_BOOM_MOVEMENT_ORDER_E_go_up
  (assert (= (index_enum_t_BOOM_MOVEMENT_ORDER E_go_up) 0))

;; index_enum_t_BOOM_MOVEMENT_ORDER_E_go_down
  (assert (= (index_enum_t_BOOM_MOVEMENT_ORDER E_go_down) 1))

;; enum_t_BOOM_MOVEMENT_ORDER_inversion
  (assert
  (forall ((u enum_t_BOOM_MOVEMENT_ORDER))
  (or (= u E_go_up) (= u E_go_down))))

(declare-fun set_enum_t_BOOM_MOVEMENT_ORDER () (set enum_t_BOOM_MOVEMENT_ORDER))

(declare-fun t2tb6 ((set enum_t_BOOM_MOVEMENT_ORDER)) uni)

;; t2tb_sort
  (assert
  (forall ((x (set enum_t_BOOM_MOVEMENT_ORDER))) (sort
  (set1 enum_t_BOOM_MOVEMENT_ORDER1) (t2tb6 x))))

(declare-fun tb2t6 (uni) (set enum_t_BOOM_MOVEMENT_ORDER))

;; BridgeL
  (assert
  (forall ((i (set enum_t_BOOM_MOVEMENT_ORDER)))
  (! (= (tb2t6 (t2tb6 i)) i) :pattern ((t2tb6 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 enum_t_BOOM_MOVEMENT_ORDER1) j) (= (t2tb6 (tb2t6 j)) j)) :pattern (
  (t2tb6 (tb2t6 j))) )))

(declare-fun t2tb7 (enum_t_BOOM_MOVEMENT_ORDER) uni)

;; t2tb_sort
  (assert
  (forall ((x enum_t_BOOM_MOVEMENT_ORDER)) (sort enum_t_BOOM_MOVEMENT_ORDER1
  (t2tb7 x))))

(declare-fun tb2t7 (uni) enum_t_BOOM_MOVEMENT_ORDER)

;; BridgeL
  (assert
  (forall ((i enum_t_BOOM_MOVEMENT_ORDER))
  (! (= (tb2t7 (t2tb7 i)) i) :pattern ((t2tb7 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort enum_t_BOOM_MOVEMENT_ORDER1 j) (= (t2tb7 (tb2t7 j)) j)) :pattern (
  (t2tb7 (tb2t7 j))) )))

;; set_enum_t_BOOM_MOVEMENT_ORDER_axiom
  (assert
  (forall ((x enum_t_BOOM_MOVEMENT_ORDER)) (mem enum_t_BOOM_MOVEMENT_ORDER1
  (t2tb7 x) (t2tb6 set_enum_t_BOOM_MOVEMENT_ORDER))))

(declare-sort enum_t_BOOM_TYPE 0)

(declare-fun enum_t_BOOM_TYPE1 () ty)

(declare-fun E_primary_boom () enum_t_BOOM_TYPE)

(declare-fun E_secondary_boom () enum_t_BOOM_TYPE)

(declare-fun match_enum_t_BOOM_TYPE (ty enum_t_BOOM_TYPE uni uni) uni)

;; match_enum_t_BOOM_TYPE_sort
  (assert
  (forall ((a ty))
  (forall ((x enum_t_BOOM_TYPE) (x1 uni) (x2 uni)) (sort a
  (match_enum_t_BOOM_TYPE a x x1 x2)))))

;; match_enum_t_BOOM_TYPE_E_primary_boom
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni))
  (=> (sort a z) (= (match_enum_t_BOOM_TYPE a E_primary_boom z z1) z)))))

;; match_enum_t_BOOM_TYPE_E_secondary_boom
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni))
  (=> (sort a z1) (= (match_enum_t_BOOM_TYPE a E_secondary_boom z z1) z1)))))

(declare-fun index_enum_t_BOOM_TYPE (enum_t_BOOM_TYPE) Int)

;; index_enum_t_BOOM_TYPE_E_primary_boom
  (assert (= (index_enum_t_BOOM_TYPE E_primary_boom) 0))

;; index_enum_t_BOOM_TYPE_E_secondary_boom
  (assert (= (index_enum_t_BOOM_TYPE E_secondary_boom) 1))

;; enum_t_BOOM_TYPE_inversion
  (assert
  (forall ((u enum_t_BOOM_TYPE))
  (or (= u E_primary_boom) (= u E_secondary_boom))))

(declare-fun set_enum_t_BOOM_TYPE () (set enum_t_BOOM_TYPE))

(declare-fun t2tb8 ((set enum_t_BOOM_TYPE)) uni)

;; t2tb_sort
  (assert
  (forall ((x (set enum_t_BOOM_TYPE))) (sort (set1 enum_t_BOOM_TYPE1)
  (t2tb8 x))))

(declare-fun tb2t8 (uni) (set enum_t_BOOM_TYPE))

;; BridgeL
  (assert
  (forall ((i (set enum_t_BOOM_TYPE)))
  (! (= (tb2t8 (t2tb8 i)) i) :pattern ((t2tb8 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 enum_t_BOOM_TYPE1) j) (= (t2tb8 (tb2t8 j)) j)) :pattern (
  (t2tb8 (tb2t8 j))) )))

(declare-fun t2tb9 (enum_t_BOOM_TYPE) uni)

;; t2tb_sort
  (assert (forall ((x enum_t_BOOM_TYPE)) (sort enum_t_BOOM_TYPE1 (t2tb9 x))))

(declare-fun tb2t9 (uni) enum_t_BOOM_TYPE)

;; BridgeL
  (assert
  (forall ((i enum_t_BOOM_TYPE))
  (! (= (tb2t9 (t2tb9 i)) i) :pattern ((t2tb9 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort enum_t_BOOM_TYPE1 j) (= (t2tb9 (tb2t9 j)) j)) :pattern (
  (t2tb9 (tb2t9 j))) )))

;; set_enum_t_BOOM_TYPE_axiom
  (assert
  (forall ((x enum_t_BOOM_TYPE)) (mem enum_t_BOOM_TYPE1 (t2tb9 x)
  (t2tb8 set_enum_t_BOOM_TYPE))))

(declare-sort enum_t_DETECTOR 0)

(declare-fun enum_t_DETECTOR1 () ty)

(declare-fun E_adc_detector () enum_t_DETECTOR)

(declare-fun E_bdc_detector () enum_t_DETECTOR)

(declare-fun match_enum_t_DETECTOR (ty enum_t_DETECTOR uni uni) uni)

;; match_enum_t_DETECTOR_sort
  (assert
  (forall ((a ty))
  (forall ((x enum_t_DETECTOR) (x1 uni) (x2 uni)) (sort a
  (match_enum_t_DETECTOR a x x1 x2)))))

;; match_enum_t_DETECTOR_E_adc_detector
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni))
  (=> (sort a z) (= (match_enum_t_DETECTOR a E_adc_detector z z1) z)))))

;; match_enum_t_DETECTOR_E_bdc_detector
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni))
  (=> (sort a z1) (= (match_enum_t_DETECTOR a E_bdc_detector z z1) z1)))))

(declare-fun index_enum_t_DETECTOR (enum_t_DETECTOR) Int)

;; index_enum_t_DETECTOR_E_adc_detector
  (assert (= (index_enum_t_DETECTOR E_adc_detector) 0))

;; index_enum_t_DETECTOR_E_bdc_detector
  (assert (= (index_enum_t_DETECTOR E_bdc_detector) 1))

;; enum_t_DETECTOR_inversion
  (assert
  (forall ((u enum_t_DETECTOR))
  (or (= u E_adc_detector) (= u E_bdc_detector))))

(declare-fun set_enum_t_DETECTOR () (set enum_t_DETECTOR))

(declare-fun t2tb10 ((set enum_t_DETECTOR)) uni)

;; t2tb_sort
  (assert
  (forall ((x (set enum_t_DETECTOR))) (sort (set1 enum_t_DETECTOR1)
  (t2tb10 x))))

(declare-fun tb2t10 (uni) (set enum_t_DETECTOR))

;; BridgeL
  (assert
  (forall ((i (set enum_t_DETECTOR)))
  (! (= (tb2t10 (t2tb10 i)) i) :pattern ((t2tb10 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 enum_t_DETECTOR1) j) (= (t2tb10 (tb2t10 j)) j)) :pattern (
  (t2tb10 (tb2t10 j))) )))

(declare-fun t2tb11 (enum_t_DETECTOR) uni)

;; t2tb_sort
  (assert (forall ((x enum_t_DETECTOR)) (sort enum_t_DETECTOR1 (t2tb11 x))))

(declare-fun tb2t11 (uni) enum_t_DETECTOR)

;; BridgeL
  (assert
  (forall ((i enum_t_DETECTOR))
  (! (= (tb2t11 (t2tb11 i)) i) :pattern ((t2tb11 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort enum_t_DETECTOR1 j) (= (t2tb11 (tb2t11 j)) j)) :pattern (
  (t2tb11 (tb2t11 j))) )))

;; set_enum_t_DETECTOR_axiom
  (assert
  (forall ((x enum_t_DETECTOR)) (mem enum_t_DETECTOR1 (t2tb11 x)
  (t2tb10 set_enum_t_DETECTOR))))

(declare-sort enum_t_GATE 0)

(declare-fun enum_t_GATE1 () ty)

(declare-fun E_inbound_lineside_gate () enum_t_GATE)

(declare-fun E_outbound_lineside_gate () enum_t_GATE)

(declare-fun match_enum_t_GATE (ty enum_t_GATE uni uni) uni)

;; match_enum_t_GATE_sort
  (assert
  (forall ((a ty))
  (forall ((x enum_t_GATE) (x1 uni) (x2 uni)) (sort a
  (match_enum_t_GATE a x x1 x2)))))

;; match_enum_t_GATE_E_inbound_lineside_gate
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni))
  (=> (sort a z) (= (match_enum_t_GATE a E_inbound_lineside_gate z z1) z)))))

;; match_enum_t_GATE_E_outbound_lineside_gate
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni))
  (=> (sort a z1) (= (match_enum_t_GATE a E_outbound_lineside_gate z z1) z1)))))

(declare-fun index_enum_t_GATE (enum_t_GATE) Int)

;; index_enum_t_GATE_E_inbound_lineside_gate
  (assert (= (index_enum_t_GATE E_inbound_lineside_gate) 0))

;; index_enum_t_GATE_E_outbound_lineside_gate
  (assert (= (index_enum_t_GATE E_outbound_lineside_gate) 1))

;; enum_t_GATE_inversion
  (assert
  (forall ((u enum_t_GATE))
  (or (= u E_inbound_lineside_gate) (= u E_outbound_lineside_gate))))

(declare-fun set_enum_t_GATE () (set enum_t_GATE))

(declare-fun t2tb12 ((set enum_t_GATE)) uni)

;; t2tb_sort
  (assert
  (forall ((x (set enum_t_GATE))) (sort (set1 enum_t_GATE1) (t2tb12 x))))

(declare-fun tb2t12 (uni) (set enum_t_GATE))

;; BridgeL
  (assert
  (forall ((i (set enum_t_GATE)))
  (! (= (tb2t12 (t2tb12 i)) i) :pattern ((t2tb12 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 enum_t_GATE1) j) (= (t2tb12 (tb2t12 j)) j)) :pattern (
  (t2tb12 (tb2t12 j))) )))

(declare-fun t2tb13 (enum_t_GATE) uni)

;; t2tb_sort
  (assert (forall ((x enum_t_GATE)) (sort enum_t_GATE1 (t2tb13 x))))

(declare-fun tb2t13 (uni) enum_t_GATE)

;; BridgeL
  (assert
  (forall ((i enum_t_GATE))
  (! (= (tb2t13 (t2tb13 i)) i) :pattern ((t2tb13 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort enum_t_GATE1 j) (= (t2tb13 (tb2t13 j)) j)) :pattern ((t2tb13
                                                                    (tb2t13
                                                                    j))) )))

;; set_enum_t_GATE_axiom
  (assert
  (forall ((x enum_t_GATE)) (mem enum_t_GATE1 (t2tb13 x)
  (t2tb12 set_enum_t_GATE))))

(declare-sort enum_t_LINE 0)

(declare-fun enum_t_LINE1 () ty)

(declare-fun E_inbound_line () enum_t_LINE)

(declare-fun E_outbound_line () enum_t_LINE)

(declare-fun match_enum_t_LINE (ty enum_t_LINE uni uni) uni)

;; match_enum_t_LINE_sort
  (assert
  (forall ((a ty))
  (forall ((x enum_t_LINE) (x1 uni) (x2 uni)) (sort a
  (match_enum_t_LINE a x x1 x2)))))

;; match_enum_t_LINE_E_inbound_line
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni))
  (=> (sort a z) (= (match_enum_t_LINE a E_inbound_line z z1) z)))))

;; match_enum_t_LINE_E_outbound_line
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni))
  (=> (sort a z1) (= (match_enum_t_LINE a E_outbound_line z z1) z1)))))

(declare-fun index_enum_t_LINE (enum_t_LINE) Int)

;; index_enum_t_LINE_E_inbound_line
  (assert (= (index_enum_t_LINE E_inbound_line) 0))

;; index_enum_t_LINE_E_outbound_line
  (assert (= (index_enum_t_LINE E_outbound_line) 1))

;; enum_t_LINE_inversion
  (assert
  (forall ((u enum_t_LINE)) (or (= u E_inbound_line) (= u E_outbound_line))))

(declare-fun set_enum_t_LINE () (set enum_t_LINE))

(declare-fun t2tb14 ((set enum_t_LINE)) uni)

;; t2tb_sort
  (assert
  (forall ((x (set enum_t_LINE))) (sort (set1 enum_t_LINE1) (t2tb14 x))))

(declare-fun tb2t14 (uni) (set enum_t_LINE))

;; BridgeL
  (assert
  (forall ((i (set enum_t_LINE)))
  (! (= (tb2t14 (t2tb14 i)) i) :pattern ((t2tb14 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort (set1 enum_t_LINE1) j) (= (t2tb14 (tb2t14 j)) j)) :pattern (
  (t2tb14 (tb2t14 j))) )))

(declare-fun t2tb15 (enum_t_LINE) uni)

;; t2tb_sort
  (assert (forall ((x enum_t_LINE)) (sort enum_t_LINE1 (t2tb15 x))))

(declare-fun tb2t15 (uni) enum_t_LINE)

;; BridgeL
  (assert
  (forall ((i enum_t_LINE))
  (! (= (tb2t15 (t2tb15 i)) i) :pattern ((t2tb15 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort enum_t_LINE1 j) (= (t2tb15 (tb2t15 j)) j)) :pattern ((t2tb15
                                                                    (tb2t15
                                                                    j))) )))

;; set_enum_t_LINE_axiom
  (assert
  (forall ((x enum_t_LINE)) (mem enum_t_LINE1 (t2tb15 x)
  (t2tb14 set_enum_t_LINE))))

(declare-fun f1 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int) Bool
  Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

(declare-fun t2tb16 ((set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))) (sort
  (set1 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
  (t2tb16 x))))

(declare-fun tb2t16 (uni) (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))))

;; BridgeL
  (assert
  (forall ((i (set (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))))
  (! (= (tb2t16 (t2tb16 i)) i) :pattern ((t2tb16 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1 (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)))
     j) (= (t2tb16 (tb2t16 j)) j)) :pattern ((t2tb16 (tb2t16 j))) )))

(declare-fun t2tb17 ((set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (sort (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (t2tb17 x))))

(declare-fun tb2t17 (uni) (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 enum_t_AUTOMATON_STATE enum_t_AUTOMATON_STATE))))
  (! (= (tb2t17 (t2tb17 i)) i) :pattern ((t2tb17 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (=> (sort
     (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1)) j)
     (= (t2tb17 (tb2t17 j)) j)) :pattern ((t2tb17 (tb2t17 j))) )))

(declare-fun t2tb18 ((set (set Int))) uni)

;; t2tb_sort
  (assert (forall ((x (set (set Int)))) (sort (set1 (set1 int)) (t2tb18 x))))

(declare-fun tb2t18 (uni) (set (set Int)))

;; BridgeL
  (assert
  (forall ((i (set (set Int))))
  (! (= (tb2t18 (t2tb18 i)) i) :pattern ((t2tb18 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb18 (tb2t18 j)) j) :pattern ((t2tb18 (tb2t18 j))) )))

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

(declare-fun t2tb20 ((set (tuple2 Int Int))) uni)

;; t2tb_sort
  (assert
  (forall ((x (set (tuple2 Int Int)))) (sort (set1 (tuple21 int int))
  (t2tb20 x))))

(declare-fun tb2t20 (uni) (set (tuple2 Int Int)))

;; BridgeL
  (assert
  (forall ((i (set (tuple2 Int Int))))
  (! (= (tb2t20 (t2tb20 i)) i) :pattern ((t2tb20 i)) )))

;; BridgeR
  (assert
  (forall ((j uni))
  (! (= (t2tb20 (tb2t20 j)) j) :pattern ((t2tb20 (tb2t20 j))) )))

;; f1_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f1 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (mem int (t2tb3 v_maximum_train_length) (t2tb2 integer))
  (<= 0 v_maximum_train_length)) (<= v_maximum_train_length 2147483647))
  (not (= v_maximum_train_length 0))) (mem int (t2tb3 v_minimum_train_length)
  (t2tb2 integer))) (<= 0 v_minimum_train_length))
  (<= v_minimum_train_length 2147483647)) (not (= v_minimum_train_length 0)))
  (= v_maximum_train_length 400)) (= v_minimum_train_length 50)) (mem 
  int (t2tb3 v_maximum_train_speed) (t2tb2 integer)))
  (<= 0 v_maximum_train_speed)) (<= v_maximum_train_speed 2147483647))
  (not (= v_maximum_train_speed 0))) (= v_maximum_train_speed 28)) (mem 
  int (t2tb3 v_number_of_booms) (t2tb2 (mk 1 2)))) (mem int
  (t2tb3 v_adc_start_to_crossing_start) (t2tb2 integer)))
  (<= 0 v_adc_start_to_crossing_start))
  (<= v_adc_start_to_crossing_start 2147483647))
  (not (= v_adc_start_to_crossing_start 0))) (mem int
  (t2tb3 v_adc_end_to_crossing_start) (t2tb2 integer)))
  (<= 0 v_adc_end_to_crossing_start))
  (<= v_adc_end_to_crossing_start 2147483647))
  (not (= v_adc_end_to_crossing_start 0))) (mem int
  (t2tb3 v_bdc_start_to_crossing_start) (t2tb2 integer)))
  (<= 0 v_bdc_start_to_crossing_start))
  (<= v_bdc_start_to_crossing_start 2147483647))
  (not (= v_bdc_start_to_crossing_start 0))) (mem int
  (t2tb3 v_crossing_end_to_bdc_end) (t2tb2 integer)))
  (<= 0 v_crossing_end_to_bdc_end))
  (<= v_crossing_end_to_bdc_end 2147483647))
  (not (= v_crossing_end_to_bdc_end 0))) (mem int
  (t2tb3 v_crossing_start_to_crossing_end) (t2tb2 integer)))
  (<= 0 v_crossing_start_to_crossing_end))
  (<= v_crossing_start_to_crossing_end 2147483647))
  (not (= v_crossing_start_to_crossing_end 0)))
  (= v_adc_start_to_crossing_start 1000))
  (= v_adc_end_to_crossing_start 950)) (= v_bdc_start_to_crossing_start 25))
  (= v_crossing_end_to_bdc_end 15)) (= v_crossing_start_to_crossing_end 10))
  (<= v_minimum_train_length (- v_adc_start_to_crossing_start v_adc_end_to_crossing_start)))
  (<= v_minimum_train_length (+ (+ v_bdc_start_to_crossing_start v_crossing_start_to_crossing_end) v_crossing_end_to_bdc_end)))
  (<= 30 (div1 v_adc_start_to_crossing_start v_maximum_train_speed)))
  (= v_cycle_duration 100)) (mem int
  (t2tb3 v_closing_boom_timer__initial_time) (t2tb2 integer)))
  (<= 0 v_closing_boom_timer__initial_time))
  (<= v_closing_boom_timer__initial_time 2147483647))
  (not (= v_closing_boom_timer__initial_time 0))) (mem int
  (t2tb3 v_secondary_wait_timer__initial_time) (t2tb2 integer)))
  (<= 0 v_secondary_wait_timer__initial_time))
  (<= v_secondary_wait_timer__initial_time 2147483647))
  (not (= v_secondary_wait_timer__initial_time 0))) (mem int
  (t2tb3 v_opening_boom_timer__initial_time) (t2tb2 integer)))
  (<= 0 v_opening_boom_timer__initial_time))
  (<= v_opening_boom_timer__initial_time 2147483647))
  (not (= v_opening_boom_timer__initial_time 0))) (mem int
  (t2tb3 v_first_train_in_warning_timer__initial_time) (t2tb2 integer)))
  (<= 0 v_first_train_in_warning_timer__initial_time))
  (<= v_first_train_in_warning_timer__initial_time 2147483647))
  (not (= v_first_train_in_warning_timer__initial_time 0))) (mem int
  (t2tb3 v_last_train_in_warning_timer__initial_time) (t2tb2 integer)))
  (<= 0 v_last_train_in_warning_timer__initial_time))
  (<= v_last_train_in_warning_timer__initial_time 2147483647))
  (not (= v_last_train_in_warning_timer__initial_time 0)))
  (= v_closing_boom_timer__initial_time 8000))
  (= v_secondary_wait_timer__initial_time 2000))
  (= v_opening_boom_timer__initial_time 8000))
  (= v_first_train_in_warning_timer__initial_time 10000))
  (= v_last_train_in_warning_timer__initial_time 5000)) (mem
  (set1 (tuple21 int int)) (t2tb20 v_bijection_trains)
  (seq int (t2tb2 v_TRAINS)))) (mem (set1 (tuple21 int int))
  (inverse int int (t2tb20 v_bijection_trains))
  (infix_plmngt int int (t2tb2 v_TRAINS) (t2tb2 natural)))) (mem
  (set1 (tuple21 int int)) (t2tb20 v_bijection_trains)
  (infix_plmngt int int
  (diff int (t2tb2 natural) (add int (t2tb3 0) (empty int)))
  (t2tb2 v_TRAINS)))) (infix_eqeq int
  (ran int int (t2tb20 v_bijection_trains)) (t2tb2 v_TRAINS))) (mem int
  (t2tb3 v_max_number_of_trains) (t2tb2 integer)))
  (<= 0 v_max_number_of_trains)) (<= v_max_number_of_trains 2147483647))
  (not (= v_max_number_of_trains 0)))
  (= v_max_number_of_trains (size int (t2tb20 v_bijection_trains))))
  (<= (+ (div1
         (+ (+ v_adc_start_to_crossing_start v_crossing_start_to_crossing_end) v_crossing_end_to_bdc_end)
         v_minimum_train_length) 1) v_max_number_of_trains))
  (mem (set1 int) (t2tb2 v_TRAINS) (finite_subsets int (t2tb2 integer))))
  (not (infix_eqeq int (t2tb2 v_TRAINS) (empty int)))) (mem
  (set1 (tuple21 enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1))
  (t2tb17 v_allowed_transitions)
  (relation enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
  (t2tb4 set_enum_t_AUTOMATON_STATE) (t2tb4 set_enum_t_AUTOMATON_STATE))))
  (infix_eqeq enum_t_AUTOMATON_STATE1
  (image enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
  (t2tb17 v_allowed_transitions)
  (add enum_t_AUTOMATON_STATE1 (t2tb5 E_empty_open)
  (empty enum_t_AUTOMATON_STATE1)))
  (union enum_t_AUTOMATON_STATE1
  (union enum_t_AUTOMATON_STATE1
  (add enum_t_AUTOMATON_STATE1 (t2tb5 E_empty_open)
  (empty enum_t_AUTOMATON_STATE1))
  (add enum_t_AUTOMATON_STATE1 (t2tb5 E_train_open)
  (empty enum_t_AUTOMATON_STATE1)))
  (add enum_t_AUTOMATON_STATE1 (t2tb5 E_failure)
  (empty enum_t_AUTOMATON_STATE1))))) (infix_eqeq enum_t_AUTOMATON_STATE1
  (image enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
  (t2tb17 v_allowed_transitions)
  (add enum_t_AUTOMATON_STATE1 (t2tb5 E_train_open)
  (empty enum_t_AUTOMATON_STATE1)))
  (union enum_t_AUTOMATON_STATE1
  (union enum_t_AUTOMATON_STATE1
  (add enum_t_AUTOMATON_STATE1 (t2tb5 E_train_open)
  (empty enum_t_AUTOMATON_STATE1))
  (add enum_t_AUTOMATON_STATE1 (t2tb5 E_train_primary_closing)
  (empty enum_t_AUTOMATON_STATE1)))
  (add enum_t_AUTOMATON_STATE1 (t2tb5 E_failure)
  (empty enum_t_AUTOMATON_STATE1))))) (infix_eqeq enum_t_AUTOMATON_STATE1
  (image enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
  (t2tb17 v_allowed_transitions)
  (add enum_t_AUTOMATON_STATE1 (t2tb5 E_train_primary_closing)
  (empty enum_t_AUTOMATON_STATE1)))
  (union enum_t_AUTOMATON_STATE1
  (union enum_t_AUTOMATON_STATE1
  (union enum_t_AUTOMATON_STATE1
  (add enum_t_AUTOMATON_STATE1 (t2tb5 E_train_primary_closing)
  (empty enum_t_AUTOMATON_STATE1))
  (add enum_t_AUTOMATON_STATE1 (t2tb5 E_train_secondary_wait)
  (empty enum_t_AUTOMATON_STATE1)))
  (add enum_t_AUTOMATON_STATE1 (t2tb5 E_train_closed)
  (empty enum_t_AUTOMATON_STATE1)))
  (add enum_t_AUTOMATON_STATE1 (t2tb5 E_failure)
  (empty enum_t_AUTOMATON_STATE1))))) (infix_eqeq enum_t_AUTOMATON_STATE1
  (image enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
  (t2tb17 v_allowed_transitions)
  (add enum_t_AUTOMATON_STATE1 (t2tb5 E_train_secondary_wait)
  (empty enum_t_AUTOMATON_STATE1)))
  (union enum_t_AUTOMATON_STATE1
  (union enum_t_AUTOMATON_STATE1
  (add enum_t_AUTOMATON_STATE1 (t2tb5 E_train_secondary_wait)
  (empty enum_t_AUTOMATON_STATE1))
  (add enum_t_AUTOMATON_STATE1 (t2tb5 E_train_secondary_closing)
  (empty enum_t_AUTOMATON_STATE1)))
  (add enum_t_AUTOMATON_STATE1 (t2tb5 E_failure)
  (empty enum_t_AUTOMATON_STATE1))))) (infix_eqeq enum_t_AUTOMATON_STATE1
  (image enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
  (t2tb17 v_allowed_transitions)
  (add enum_t_AUTOMATON_STATE1 (t2tb5 E_train_secondary_closing)
  (empty enum_t_AUTOMATON_STATE1)))
  (union enum_t_AUTOMATON_STATE1
  (union enum_t_AUTOMATON_STATE1
  (add enum_t_AUTOMATON_STATE1 (t2tb5 E_train_secondary_closing)
  (empty enum_t_AUTOMATON_STATE1))
  (add enum_t_AUTOMATON_STATE1 (t2tb5 E_train_closed)
  (empty enum_t_AUTOMATON_STATE1)))
  (add enum_t_AUTOMATON_STATE1 (t2tb5 E_failure)
  (empty enum_t_AUTOMATON_STATE1))))) (infix_eqeq enum_t_AUTOMATON_STATE1
  (image enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
  (t2tb17 v_allowed_transitions)
  (add enum_t_AUTOMATON_STATE1 (t2tb5 E_train_closed)
  (empty enum_t_AUTOMATON_STATE1)))
  (union enum_t_AUTOMATON_STATE1
  (union enum_t_AUTOMATON_STATE1
  (add enum_t_AUTOMATON_STATE1 (t2tb5 E_train_closed)
  (empty enum_t_AUTOMATON_STATE1))
  (add enum_t_AUTOMATON_STATE1 (t2tb5 E_empty_closed)
  (empty enum_t_AUTOMATON_STATE1)))
  (add enum_t_AUTOMATON_STATE1 (t2tb5 E_failure)
  (empty enum_t_AUTOMATON_STATE1))))) (infix_eqeq enum_t_AUTOMATON_STATE1
  (image enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
  (t2tb17 v_allowed_transitions)
  (add enum_t_AUTOMATON_STATE1 (t2tb5 E_empty_closed)
  (empty enum_t_AUTOMATON_STATE1)))
  (union enum_t_AUTOMATON_STATE1
  (union enum_t_AUTOMATON_STATE1
  (union enum_t_AUTOMATON_STATE1
  (add enum_t_AUTOMATON_STATE1 (t2tb5 E_empty_closed)
  (empty enum_t_AUTOMATON_STATE1))
  (add enum_t_AUTOMATON_STATE1 (t2tb5 E_empty_opening)
  (empty enum_t_AUTOMATON_STATE1)))
  (add enum_t_AUTOMATON_STATE1 (t2tb5 E_train_closed)
  (empty enum_t_AUTOMATON_STATE1)))
  (add enum_t_AUTOMATON_STATE1 (t2tb5 E_failure)
  (empty enum_t_AUTOMATON_STATE1))))) (infix_eqeq enum_t_AUTOMATON_STATE1
  (image enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
  (t2tb17 v_allowed_transitions)
  (add enum_t_AUTOMATON_STATE1 (t2tb5 E_empty_opening)
  (empty enum_t_AUTOMATON_STATE1)))
  (union enum_t_AUTOMATON_STATE1
  (union enum_t_AUTOMATON_STATE1
  (union enum_t_AUTOMATON_STATE1
  (add enum_t_AUTOMATON_STATE1 (t2tb5 E_empty_opening)
  (empty enum_t_AUTOMATON_STATE1))
  (add enum_t_AUTOMATON_STATE1 (t2tb5 E_empty_open)
  (empty enum_t_AUTOMATON_STATE1)))
  (add enum_t_AUTOMATON_STATE1 (t2tb5 E_train_open)
  (empty enum_t_AUTOMATON_STATE1)))
  (add enum_t_AUTOMATON_STATE1 (t2tb5 E_failure)
  (empty enum_t_AUTOMATON_STATE1))))) (infix_eqeq enum_t_AUTOMATON_STATE1
  (image enum_t_AUTOMATON_STATE1 enum_t_AUTOMATON_STATE1
  (t2tb17 v_allowed_transitions)
  (add enum_t_AUTOMATON_STATE1 (t2tb5 E_failure)
  (empty enum_t_AUTOMATON_STATE1)))
  (add enum_t_AUTOMATON_STATE1 (t2tb5 E_failure)
  (empty enum_t_AUTOMATON_STATE1)))))))

(declare-fun f3 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int) Bool
  Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f3_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f3 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS) (mem
  (set1 int) (empty int) (power1 int (t2tb2 v_TRAINS))))))

(declare-fun f4 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int) Bool
  Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f4_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f4 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (= E_empty_open E_train_open))))

(declare-fun f7 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int) Bool
  Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f7_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f7 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (= E_empty_open E_train_primary_closing))))

(declare-fun f9 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int) Bool
  Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f9_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f9 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (= E_empty_open E_train_secondary_closing))))

(declare-fun f10 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f10_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f10 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (= E_empty_open E_train_secondary_wait))))

(declare-fun f12 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f12_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f12 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (= E_empty_open E_empty_closed))))

(declare-fun f14 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f14_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f14 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (= E_empty_open E_empty_opening))))

(declare-fun f18 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f18_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f18 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and
  (and (mem (set1 int) (t2tb2 v_inbound_trains_in_warning)
  (power1 int (t2tb2 v_TRAINS))) (mem (set1 int)
  (t2tb2 v_outbound_trains_in_warning) (power1 int (t2tb2 v_TRAINS)))) (mem
  int (t2tb3 v_closing_boom_timer__remaining_time) (t2tb2 integer)))
  (<= 0 v_closing_boom_timer__remaining_time))
  (<= v_closing_boom_timer__remaining_time 2147483647)) (mem int
  (t2tb3 v_secondary_wait_timer__remaining_time) (t2tb2 integer)))
  (<= 0 v_secondary_wait_timer__remaining_time))
  (<= v_secondary_wait_timer__remaining_time 2147483647)) (mem int
  (t2tb3 v_opening_boom_timer__remaining_time) (t2tb2 integer)))
  (<= 0 v_opening_boom_timer__remaining_time))
  (<= v_opening_boom_timer__remaining_time 2147483647)) (mem int
  (t2tb3 v_first_train_in_warning_timer__remaining_time) (t2tb2 integer)))
  (<= 0 v_first_train_in_warning_timer__remaining_time))
  (<= v_first_train_in_warning_timer__remaining_time 2147483647)) (mem 
  int (t2tb3 v_last_train_in_warning_timer__remaining_time) (t2tb2 integer)))
  (<= 0 v_last_train_in_warning_timer__remaining_time))
  (<= v_last_train_in_warning_timer__remaining_time 2147483647))
  (=> (not (= v_status E_train_open))
  (= v_first_train_in_warning_timer__active false)))
  (=> (= v_status E_train_open)
  (= v_first_train_in_warning_timer__active true)))
  (=>
  (and (not (= v_status E_train_primary_closing))
  (not (= v_status E_train_secondary_closing)))
  (= v_closing_boom_timer__active false)))
  (=>
  (or (= v_status E_train_primary_closing)
  (= v_status E_train_secondary_closing))
  (= v_closing_boom_timer__active true)))
  (=> (not (= v_status E_train_secondary_wait))
  (= v_secondary_wait_timer__active false)))
  (=> (= v_status E_train_secondary_wait)
  (= v_secondary_wait_timer__active true)))
  (=> (not (= v_status E_empty_closed))
  (= v_last_train_in_warning_timer__active false)))
  (=> (= v_status E_empty_closed)
  (= v_last_train_in_warning_timer__active true)))
  (=> (not (= v_status E_empty_opening))
  (= v_opening_boom_timer__active false)))
  (=> (= v_status E_empty_opening) (= v_opening_boom_timer__active true)))
  (=>
  (or (= v_status E_train_secondary_wait)
  (= v_status E_train_secondary_closing)) (= v_number_of_booms 2)))
  (=> (= v_status E_train_secondary_wait)
  (= v_primary_boom_closed_detector true)))
  (=> (= v_status E_train_secondary_closing)
  (= v_primary_boom_closed_detector true))))))

(declare-fun f19 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f19_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f19 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (or (= v_inbound_safety_mode true) (= v_outbound_safety_mode true)))))

(declare-fun f20 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f20_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f20 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (= E_failure E_train_open))))

(declare-fun f22 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f22_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f22 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (= E_failure E_train_primary_closing))))

(declare-fun f24 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f24_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f24 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (= E_failure E_train_secondary_closing))))

(declare-fun f25 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f25_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f25 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (= E_failure E_train_secondary_wait))))

(declare-fun f27 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f27_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f27 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (= E_failure E_empty_closed))))

(declare-fun f29 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f29_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f29 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (= E_failure E_empty_opening))))

(declare-fun f35 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f35_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f35 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and (and (= v_initialised true) (= v_status E_empty_open))
  (or (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))))
  (= v_first_train_in_warning_timer__active false)))))

(declare-fun f36 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f36_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f36 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (and
  (=> (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int))
  (= v_inbound_indicators_on_1 false))
  (=> (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (= v_inbound_indicators_on_1 true)))
  (=> (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int))
  (= v_outbound_indicators_on_1 false)))
  (=> (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_outbound_indicators_on_1 true)))
  (not (= E_train_open E_train_primary_closing)))
  (not (= E_train_open E_train_secondary_closing))))))

(declare-fun f39 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f39_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f39 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (=> (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int))
  (= v_inbound_indicators_on_1 false))
  (=> (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (= v_inbound_indicators_on_1 true)))
  (=> (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int))
  (= v_outbound_indicators_on_1 false)))
  (=> (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_outbound_indicators_on_1 true)))
  (= E_train_open E_train_primary_closing)))))

(declare-fun f41 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f41_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f41 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (=> (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int))
  (= v_inbound_indicators_on_1 false))
  (=> (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (= v_inbound_indicators_on_1 true)))
  (=> (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int))
  (= v_outbound_indicators_on_1 false)))
  (=> (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_outbound_indicators_on_1 true)))
  (= E_train_open E_train_secondary_closing)))))

(declare-fun f42 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f42_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f42 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (=> (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int))
  (= v_inbound_indicators_on_1 false))
  (=> (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (= v_inbound_indicators_on_1 true)))
  (=> (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int))
  (= v_outbound_indicators_on_1 false)))
  (=> (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_outbound_indicators_on_1 true)))
  (not (= E_train_open E_train_secondary_wait))))))

(declare-fun f45 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f45_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f45 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (=> (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int))
  (= v_inbound_indicators_on_1 false))
  (=> (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (= v_inbound_indicators_on_1 true)))
  (=> (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int))
  (= v_outbound_indicators_on_1 false)))
  (=> (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_outbound_indicators_on_1 true)))
  (= E_train_open E_train_secondary_wait)))))

(declare-fun f47 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f47_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f47 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (=> (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int))
  (= v_inbound_indicators_on_1 false))
  (=> (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (= v_inbound_indicators_on_1 true)))
  (=> (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int))
  (= v_outbound_indicators_on_1 false)))
  (=> (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_outbound_indicators_on_1 true)))
  (not (= E_train_open E_empty_closed))))))

(declare-fun f50 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f50_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f50 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (=> (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int))
  (= v_inbound_indicators_on_1 false))
  (=> (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (= v_inbound_indicators_on_1 true)))
  (=> (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int))
  (= v_outbound_indicators_on_1 false)))
  (=> (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_outbound_indicators_on_1 true))) (= E_train_open E_empty_closed)))))

(declare-fun f52 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f52_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f52 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (=> (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int))
  (= v_inbound_indicators_on_1 false))
  (=> (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (= v_inbound_indicators_on_1 true)))
  (=> (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int))
  (= v_outbound_indicators_on_1 false)))
  (=> (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_outbound_indicators_on_1 true)))
  (not (= E_train_open E_empty_opening))))))

(declare-fun f55 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f55_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f55 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (=> (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int))
  (= v_inbound_indicators_on_1 false))
  (=> (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (= v_inbound_indicators_on_1 true)))
  (=> (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int))
  (= v_outbound_indicators_on_1 false)))
  (=> (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_outbound_indicators_on_1 true))) (= E_train_open E_empty_opening)))))

(declare-fun f57 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f57_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f57 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and (and (= v_initialised true) (= v_status E_train_open))
  (= v_first_train_in_warning_timer__active true))
  (= v_first_train_in_warning_timer__remaining_time 0))
  (= v_closing_boom_timer__active false)))))

(declare-fun f58 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f58_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f58 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (=> (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int))
  (= v_inbound_indicators_on_1 false))
  (=> (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (= v_inbound_indicators_on_1 true)))
  (=> (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int))
  (= v_outbound_indicators_on_1 false)))
  (=> (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_outbound_indicators_on_1 true)))
  (= E_train_primary_closing E_train_open)))))

(declare-fun f59 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f59_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f59 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (=> (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int))
  (= v_inbound_indicators_on_1 false))
  (=> (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (= v_inbound_indicators_on_1 true)))
  (=> (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int))
  (= v_outbound_indicators_on_1 false)))
  (=> (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_outbound_indicators_on_1 true)))
  (not (= E_train_primary_closing E_train_secondary_wait))))))

(declare-fun f60 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f60_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f60 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (=> (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int))
  (= v_inbound_indicators_on_1 false))
  (=> (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (= v_inbound_indicators_on_1 true)))
  (=> (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int))
  (= v_outbound_indicators_on_1 false)))
  (=> (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_outbound_indicators_on_1 true)))
  (= E_train_primary_closing E_train_secondary_wait)))))

(declare-fun f61 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f61_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f61 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (=> (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int))
  (= v_inbound_indicators_on_1 false))
  (=> (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (= v_inbound_indicators_on_1 true)))
  (=> (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int))
  (= v_outbound_indicators_on_1 false)))
  (=> (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_outbound_indicators_on_1 true)))
  (not (= E_train_primary_closing E_empty_closed))))))

(declare-fun f62 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f62_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f62 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (=> (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int))
  (= v_inbound_indicators_on_1 false))
  (=> (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (= v_inbound_indicators_on_1 true)))
  (=> (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int))
  (= v_outbound_indicators_on_1 false)))
  (=> (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_outbound_indicators_on_1 true)))
  (= E_train_primary_closing E_empty_closed)))))

(declare-fun f63 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f63_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f63 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (=> (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int))
  (= v_inbound_indicators_on_1 false))
  (=> (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (= v_inbound_indicators_on_1 true)))
  (=> (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int))
  (= v_outbound_indicators_on_1 false)))
  (=> (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_outbound_indicators_on_1 true)))
  (not (= E_train_primary_closing E_empty_opening))))))

(declare-fun f64 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f64_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f64 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (=> (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int))
  (= v_inbound_indicators_on_1 false))
  (=> (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (= v_inbound_indicators_on_1 true)))
  (=> (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int))
  (= v_outbound_indicators_on_1 false)))
  (=> (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_outbound_indicators_on_1 true)))
  (= E_train_primary_closing E_empty_opening)))))

(declare-fun f65 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f65_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f65 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (=> (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int))
  (= v_inbound_indicators_on_1 false))
  (=> (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (= v_inbound_indicators_on_1 true)))
  (=> (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int))
  (= v_outbound_indicators_on_1 false)))
  (=> (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_outbound_indicators_on_1 true)))
  (= E_train_primary_closing E_train_secondary_closing)))))

(declare-fun f66 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f66_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f66 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and (and (= v_initialised true) (= v_status E_train_primary_closing))
  (= v_closing_boom_timer__active true))
  (= v_closing_boom_timer__remaining_time 0)))))

(declare-fun f67 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f67_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f67 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (not (= E_failure E_train_open)))))

(declare-fun f71 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f71_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f71 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (not (= E_failure E_train_secondary_wait)))))

(declare-fun f72 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f72_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f72 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (not (= E_failure E_empty_closed)))))

(declare-fun f73 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f73_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f73 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (not (= E_failure E_empty_opening)))))

(declare-fun f74 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f74_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f74 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and (and (= v_initialised true) (= v_status E_train_primary_closing))
  (= v_closing_boom_timer__active true))
  (<= 1 v_closing_boom_timer__remaining_time))
  (= v_primary_boom_closed_detector true)) (= v_number_of_booms 1)))))

(declare-fun f75 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f75_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f75 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (=> (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int))
  (= v_inbound_indicators_on_1 false))
  (=> (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (= v_inbound_indicators_on_1 true)))
  (=> (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int))
  (= v_outbound_indicators_on_1 false)))
  (=> (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_outbound_indicators_on_1 true)))
  (not (= E_train_closed E_train_open))))))

(declare-fun f76 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f76_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f76 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (=> (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int))
  (= v_inbound_indicators_on_1 false))
  (=> (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (= v_inbound_indicators_on_1 true)))
  (=> (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int))
  (= v_outbound_indicators_on_1 false)))
  (=> (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_outbound_indicators_on_1 true))) (= E_train_closed E_train_open)))))

(declare-fun f77 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f77_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f77 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (=> (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int))
  (= v_inbound_indicators_on_1 false))
  (=> (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (= v_inbound_indicators_on_1 true)))
  (=> (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int))
  (= v_outbound_indicators_on_1 false)))
  (=> (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_outbound_indicators_on_1 true)))
  (= E_train_closed E_train_primary_closing)))))

(declare-fun f78 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f78_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f78 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (=> (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int))
  (= v_inbound_indicators_on_1 false))
  (=> (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (= v_inbound_indicators_on_1 true)))
  (=> (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int))
  (= v_outbound_indicators_on_1 false)))
  (=> (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_outbound_indicators_on_1 true)))
  (= E_train_closed E_train_secondary_closing)))))

(declare-fun f79 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f79_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f79 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (=> (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int))
  (= v_inbound_indicators_on_1 false))
  (=> (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (= v_inbound_indicators_on_1 true)))
  (=> (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int))
  (= v_outbound_indicators_on_1 false)))
  (=> (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_outbound_indicators_on_1 true)))
  (not (= E_train_closed E_train_secondary_wait))))))

(declare-fun f80 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f80_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f80 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (=> (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int))
  (= v_inbound_indicators_on_1 false))
  (=> (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (= v_inbound_indicators_on_1 true)))
  (=> (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int))
  (= v_outbound_indicators_on_1 false)))
  (=> (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_outbound_indicators_on_1 true)))
  (= E_train_closed E_train_secondary_wait)))))

(declare-fun f81 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f81_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f81 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (=> (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int))
  (= v_inbound_indicators_on_1 false))
  (=> (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (= v_inbound_indicators_on_1 true)))
  (=> (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int))
  (= v_outbound_indicators_on_1 false)))
  (=> (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_outbound_indicators_on_1 true)))
  (not (= E_train_closed E_empty_closed))))))

(declare-fun f82 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f82_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f82 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (=> (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int))
  (= v_inbound_indicators_on_1 false))
  (=> (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (= v_inbound_indicators_on_1 true)))
  (=> (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int))
  (= v_outbound_indicators_on_1 false)))
  (=> (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_outbound_indicators_on_1 true))) (= E_train_closed E_empty_closed)))))

(declare-fun f83 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f83_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f83 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (=> (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int))
  (= v_inbound_indicators_on_1 false))
  (=> (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (= v_inbound_indicators_on_1 true)))
  (=> (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int))
  (= v_outbound_indicators_on_1 false)))
  (=> (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_outbound_indicators_on_1 true)))
  (not (= E_train_closed E_empty_opening))))))

(declare-fun f84 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f84_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f84 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (=> (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int))
  (= v_inbound_indicators_on_1 false))
  (=> (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (= v_inbound_indicators_on_1 true)))
  (=> (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int))
  (= v_outbound_indicators_on_1 false)))
  (=> (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_outbound_indicators_on_1 true))) (= E_train_closed E_empty_opening)))))

(declare-fun f85 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f85_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f85 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and (and (= v_initialised true) (= v_status E_train_primary_closing))
  (= v_closing_boom_timer__active true))
  (<= 1 v_closing_boom_timer__remaining_time))
  (= v_primary_boom_closed_detector true)) (= v_number_of_booms 2)))))

(declare-fun f86 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f86_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f86 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (=> (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int))
  (= v_inbound_indicators_on_1 false))
  (=> (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (= v_inbound_indicators_on_1 true)))
  (=> (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int))
  (= v_outbound_indicators_on_1 false)))
  (=> (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_outbound_indicators_on_1 true)))
  (not (= E_train_secondary_wait E_train_open))))))

(declare-fun f87 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f87_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f87 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (=> (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int))
  (= v_inbound_indicators_on_1 false))
  (=> (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (= v_inbound_indicators_on_1 true)))
  (=> (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int))
  (= v_outbound_indicators_on_1 false)))
  (=> (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_outbound_indicators_on_1 true)))
  (= E_train_secondary_wait E_train_open)))))

(declare-fun f88 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f88_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f88 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (=> (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int))
  (= v_inbound_indicators_on_1 false))
  (=> (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (= v_inbound_indicators_on_1 true)))
  (=> (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int))
  (= v_outbound_indicators_on_1 false)))
  (=> (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_outbound_indicators_on_1 true)))
  (= E_train_secondary_wait E_train_primary_closing)))))

(declare-fun f89 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f89_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f89 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (=> (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int))
  (= v_inbound_indicators_on_1 false))
  (=> (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (= v_inbound_indicators_on_1 true)))
  (=> (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int))
  (= v_outbound_indicators_on_1 false)))
  (=> (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_outbound_indicators_on_1 true)))
  (= E_train_secondary_wait E_train_secondary_closing)))))

(declare-fun f90 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f90_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f90 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (=> (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int))
  (= v_inbound_indicators_on_1 false))
  (=> (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (= v_inbound_indicators_on_1 true)))
  (=> (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int))
  (= v_outbound_indicators_on_1 false)))
  (=> (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_outbound_indicators_on_1 true)))
  (not (= E_train_secondary_wait E_empty_closed))))))

(declare-fun f91 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f91_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f91 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (=> (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int))
  (= v_inbound_indicators_on_1 false))
  (=> (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (= v_inbound_indicators_on_1 true)))
  (=> (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int))
  (= v_outbound_indicators_on_1 false)))
  (=> (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_outbound_indicators_on_1 true)))
  (= E_train_secondary_wait E_empty_closed)))))

(declare-fun f92 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f92_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f92 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (=> (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int))
  (= v_inbound_indicators_on_1 false))
  (=> (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (= v_inbound_indicators_on_1 true)))
  (=> (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int))
  (= v_outbound_indicators_on_1 false)))
  (=> (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_outbound_indicators_on_1 true)))
  (not (= E_train_secondary_wait E_empty_opening))))))

(declare-fun f93 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f93_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f93 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (=> (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int))
  (= v_inbound_indicators_on_1 false))
  (=> (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (= v_inbound_indicators_on_1 true)))
  (=> (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int))
  (= v_outbound_indicators_on_1 false)))
  (=> (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_outbound_indicators_on_1 true)))
  (= E_train_secondary_wait E_empty_opening)))))

(declare-fun f94 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f94_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f94 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and (and (= v_initialised true) (= v_status E_train_secondary_wait))
  (= v_secondary_wait_timer__active true))
  (= v_secondary_wait_timer__remaining_time 0)))))

(declare-fun f95 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f95_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f95 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (=> (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int))
  (= v_inbound_indicators_on_1 false))
  (=> (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (= v_inbound_indicators_on_1 true)))
  (=> (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int))
  (= v_outbound_indicators_on_1 false)))
  (=> (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_outbound_indicators_on_1 true)))
  (not (= E_train_secondary_closing E_train_open))))))

(declare-fun f96 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f96_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f96 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (=> (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int))
  (= v_inbound_indicators_on_1 false))
  (=> (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (= v_inbound_indicators_on_1 true)))
  (=> (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int))
  (= v_outbound_indicators_on_1 false)))
  (=> (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_outbound_indicators_on_1 true)))
  (= E_train_secondary_closing E_train_open)))))

(declare-fun f97 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f97_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f97 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (=> (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int))
  (= v_inbound_indicators_on_1 false))
  (=> (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (= v_inbound_indicators_on_1 true)))
  (=> (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int))
  (= v_outbound_indicators_on_1 false)))
  (=> (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_outbound_indicators_on_1 true)))
  (= E_train_secondary_closing E_train_secondary_wait)))))

(declare-fun f98 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f98_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f98 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (=> (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int))
  (= v_inbound_indicators_on_1 false))
  (=> (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (= v_inbound_indicators_on_1 true)))
  (=> (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int))
  (= v_outbound_indicators_on_1 false)))
  (=> (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_outbound_indicators_on_1 true)))
  (not (= E_train_secondary_closing E_empty_closed))))))

(declare-fun f99 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f99_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f99 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (=> (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int))
  (= v_inbound_indicators_on_1 false))
  (=> (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (= v_inbound_indicators_on_1 true)))
  (=> (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int))
  (= v_outbound_indicators_on_1 false)))
  (=> (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_outbound_indicators_on_1 true)))
  (= E_train_secondary_closing E_empty_closed)))))

(declare-fun f100 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f100_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f100 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (=> (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int))
  (= v_inbound_indicators_on_1 false))
  (=> (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (= v_inbound_indicators_on_1 true)))
  (=> (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int))
  (= v_outbound_indicators_on_1 false)))
  (=> (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_outbound_indicators_on_1 true)))
  (not (= E_train_secondary_closing E_empty_opening))))))

(declare-fun f101 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f101_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f101 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (=> (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int))
  (= v_inbound_indicators_on_1 false))
  (=> (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (= v_inbound_indicators_on_1 true)))
  (=> (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int))
  (= v_outbound_indicators_on_1 false)))
  (=> (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_outbound_indicators_on_1 true)))
  (= E_train_secondary_closing E_empty_opening)))))

(declare-fun f102 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f102_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f102 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (=> (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int))
  (= v_inbound_indicators_on_1 false))
  (=> (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (= v_inbound_indicators_on_1 true)))
  (=> (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int))
  (= v_outbound_indicators_on_1 false)))
  (=> (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_outbound_indicators_on_1 true))))))

(declare-fun f103 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f103_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f103 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and (and (= v_initialised true) (= v_status E_train_secondary_closing))
  (= v_closing_boom_timer__active true))
  (= v_closing_boom_timer__remaining_time 0)))))

(declare-fun f104 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f104_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f104 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and (and (= v_initialised true) (= v_status E_train_secondary_closing))
  (= v_closing_boom_timer__active true))
  (<= 1 v_closing_boom_timer__remaining_time))
  (= v_secondary_boom_closed_detector true)))))

(declare-fun f105 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f105_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f105 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and (and (= v_initialised true) (= v_status E_train_closed)) (infix_eqeq
  int (t2tb2 v_inbound_trains_in_warning) (empty int))) (infix_eqeq int
  (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_last_train_in_warning_timer__active false)))))

(declare-fun f106 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f106_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f106 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (not (= E_empty_closed E_train_open)))))

(declare-fun f107 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f107_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f107 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (= E_empty_closed E_train_open))))

(declare-fun f108 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f108_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f108 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and (not (= E_empty_closed E_train_primary_closing))
  (not (= E_empty_closed E_train_secondary_closing))))))

(declare-fun f109 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f109_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f109 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (= E_empty_closed E_train_primary_closing))))

(declare-fun f110 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f110_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f110 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (= E_empty_closed E_train_secondary_closing))))

(declare-fun f111 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f111_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f111 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (not (= E_empty_closed E_train_secondary_wait)))))

(declare-fun f112 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f112_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f112 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (= E_empty_closed E_train_secondary_wait))))

(declare-fun f113 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f113_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f113 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (not (= E_empty_closed E_empty_opening)))))

(declare-fun f114 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f114_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f114 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (= E_empty_closed E_empty_opening))))

(declare-fun f115 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f115_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f115 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and (and (= v_initialised true) (= v_status E_empty_closed))
  (or (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))))
  (= v_last_train_in_warning_timer__active true)))))

(declare-fun f116 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f116_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f116 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (and
  (=> (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int))
  (= v_inbound_indicators_on_1 false))
  (=> (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (= v_inbound_indicators_on_1 true)))
  (=> (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int))
  (= v_outbound_indicators_on_1 false)))
  (=> (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_outbound_indicators_on_1 true)))
  (not (= E_train_closed E_train_primary_closing)))
  (not (= E_train_closed E_train_secondary_closing))))))

(declare-fun f117 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f117_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f117 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (and
  (and (and (= v_initialised true) (= v_status E_empty_closed)) (infix_eqeq
  int (t2tb2 v_inbound_trains_in_warning) (empty int))) (infix_eqeq int
  (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_last_train_in_warning_timer__active true))
  (= v_last_train_in_warning_timer__remaining_time 0))
  (= v_opening_boom_timer__active false)) (= v_boom_safety_close false)))))

(declare-fun f118 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f118_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f118 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (not (= E_empty_opening E_train_open)))))

(declare-fun f119 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f119_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f119 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (= E_empty_opening E_train_open))))

(declare-fun f120 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f120_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f120 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and (not (= E_empty_opening E_train_primary_closing))
  (not (= E_empty_opening E_train_secondary_closing))))))

(declare-fun f121 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f121_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f121 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (= E_empty_opening E_train_primary_closing))))

(declare-fun f122 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f122_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f122 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (= E_empty_opening E_train_secondary_closing))))

(declare-fun f123 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f123_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f123 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (not (= E_empty_opening E_train_secondary_wait)))))

(declare-fun f124 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f124_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f124 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (= E_empty_opening E_train_secondary_wait))))

(declare-fun f125 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f125_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f125 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (= E_empty_opening E_empty_closed))))

(declare-fun f126 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f126_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f126 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and (and (= v_initialised true) (= v_status E_empty_opening))
  (= v_opening_boom_timer__active true))
  (= v_opening_boom_timer__remaining_time 0)))))

(declare-fun f127 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f127_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f127 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and (not (= E_failure E_train_primary_closing))
  (not (= E_failure E_train_secondary_closing))))))

(declare-fun f128 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f128_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f128 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and
  (and
  (and (and (= v_initialised true) (= v_status E_empty_opening)) (infix_eqeq
  int (t2tb2 v_inbound_trains_in_warning) (empty int))) (infix_eqeq int
  (t2tb2 v_outbound_trains_in_warning) (empty int)))
  (= v_opening_boom_timer__active true))
  (<= 1 v_opening_boom_timer__remaining_time)) (= v_boom_open_detector true)))))

(declare-fun f129 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f129_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f129 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (not (= E_empty_open E_train_open)))))

(declare-fun f130 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f130_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f130 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and (not (= E_empty_open E_train_primary_closing))
  (not (= E_empty_open E_train_secondary_closing))))))

(declare-fun f131 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f131_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f131 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (not (= E_empty_open E_train_secondary_wait)))))

(declare-fun f132 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f132_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f132 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (not (= E_empty_open E_empty_closed)))))

(declare-fun f133 (enum_t_AUTOMATON_STATE Int Int Bool Bool Bool (set Int)
  Bool Bool Bool Int Int Bool Int Int Int Int Int Int Int Bool Bool Bool
  (set Int) Bool Bool Bool Int Int Bool Int Int Int Int Int Bool Bool Bool
  (set (tuple2 Int Int)) Int (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE)) Int Int (set Int)) Bool)

;; f133_def
  (assert
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (= (f133 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and
  (and
  (and (and (= v_initialised true) (= v_status E_empty_opening))
  (or (not (infix_eqeq int (t2tb2 v_inbound_trains_in_warning) (empty int)))
  (not (infix_eqeq int (t2tb2 v_outbound_trains_in_warning) (empty int)))))
  (= v_opening_boom_timer__active true))
  (= v_first_train_in_warning_timer__active false)))))

(assert
;; empty_opening_TO_failure_9
 ;; File "POwhy_bpo2why/RCS3/Automaton_transitions.why", line 34124, characters 7-33
  (not
  (forall ((v_status enum_t_AUTOMATON_STATE)
  (v_secondary_wait_timer__remaining_time Int)
  (v_secondary_wait_timer__initial_time Int)
  (v_secondary_wait_timer__active Bool)
  (v_secondary_boom_closed_detector Bool)
  (v_primary_boom_closed_detector Bool)
  (v_outbound_trains_in_warning (set Int)) (v_outbound_safety_mode Bool)
  (v_outbound_indicators_on_1 Bool) (v_outbound_indicators_on Bool)
  (v_opening_boom_timer__remaining_time Int)
  (v_opening_boom_timer__initial_time Int)
  (v_opening_boom_timer__active Bool) (v_number_of_booms Int)
  (v_minimum_train_length Int) (v_maximum_train_speed Int)
  (v_maximum_train_length Int) (v_max_number_of_trains Int)
  (v_last_train_in_warning_timer__remaining_time Int)
  (v_last_train_in_warning_timer__initial_time Int)
  (v_last_train_in_warning_timer__active Bool) (v_lamps_bells_on Bool)
  (v_initialised Bool) (v_inbound_trains_in_warning (set Int))
  (v_inbound_safety_mode Bool) (v_inbound_indicators_on_1 Bool)
  (v_inbound_indicators_on Bool)
  (v_first_train_in_warning_timer__remaining_time Int)
  (v_first_train_in_warning_timer__initial_time Int)
  (v_first_train_in_warning_timer__active Bool) (v_cycle_duration Int)
  (v_crossing_start_to_crossing_end Int) (v_crossing_end_to_bdc_end Int)
  (v_closing_boom_timer__remaining_time Int)
  (v_closing_boom_timer__initial_time Int)
  (v_closing_boom_timer__active Bool) (v_boom_safety_close Bool)
  (v_boom_open_detector Bool) (v_bijection_trains (set (tuple2 Int Int)))
  (v_bdc_start_to_crossing_start Int)
  (v_allowed_transitions (set (tuple2 enum_t_AUTOMATON_STATE
  enum_t_AUTOMATON_STATE))) (v_adc_start_to_crossing_start Int)
  (v_adc_end_to_crossing_start Int) (v_TRAINS (set Int)))
  (=>
  (and (f1 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and (f18 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS)
  (and (f27 v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS) (f126
  v_status v_secondary_wait_timer__remaining_time
  v_secondary_wait_timer__initial_time v_secondary_wait_timer__active
  v_secondary_boom_closed_detector v_primary_boom_closed_detector
  v_outbound_trains_in_warning v_outbound_safety_mode
  v_outbound_indicators_on_1 v_outbound_indicators_on
  v_opening_boom_timer__remaining_time v_opening_boom_timer__initial_time
  v_opening_boom_timer__active v_number_of_booms v_minimum_train_length
  v_maximum_train_speed v_maximum_train_length v_max_number_of_trains
  v_last_train_in_warning_timer__remaining_time
  v_last_train_in_warning_timer__initial_time
  v_last_train_in_warning_timer__active v_lamps_bells_on v_initialised
  v_inbound_trains_in_warning v_inbound_safety_mode v_inbound_indicators_on_1
  v_inbound_indicators_on v_first_train_in_warning_timer__remaining_time
  v_first_train_in_warning_timer__initial_time
  v_first_train_in_warning_timer__active v_cycle_duration
  v_crossing_start_to_crossing_end v_crossing_end_to_bdc_end
  v_closing_boom_timer__remaining_time v_closing_boom_timer__initial_time
  v_closing_boom_timer__active v_boom_safety_close v_boom_open_detector
  v_bijection_trains v_bdc_start_to_crossing_start v_allowed_transitions
  v_adc_start_to_crossing_start v_adc_end_to_crossing_start v_TRAINS))))
  (= v_last_train_in_warning_timer__active true)))))
(check-sat)
