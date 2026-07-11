
(declare-datatypes ()
	((OTypeD0
		(OString (str String))
		(ONumber (num Int))
		(OBoolean (bool Bool))
		ONull
		OUndef
	))
)


(declare-datatypes ()
  ((OTypeD1
    (Atom1 (atom1 OTypeD0))
    (OObj1 (obj1 (Array String OTypeD0)))
    (OArray1 (arr1 (Seq OTypeD0)))
    (OSet1 (set1 (Array OTypeD0 Bool)))
	(Wrap1 (wrap1 OTypeD0))
  ))
)

(declare-datatypes ()
  ((OTypeD2
    (Atom2 (atom2 OTypeD0))
    (OObj2 (obj2 (Array String OTypeD1)))
    (OArray2 (arr2 (Seq OTypeD1)))
    (OSet2 (set2 (Array OTypeD1 Bool)))
	(Wrap2 (wrap2 OTypeD1))
  ))
)

(declare-datatypes ()
  ((RefHeadResult0
    (mkRefHeadResult0 (rhrVal0 OTypeD0) (rhrPath0 (Seq String)))
  ))
)

(declare-datatypes ()
  ((RefHeadResult1
    (mkRefHeadResult1 (rhrVal1 OTypeD1) (rhrPath1 (Seq String)))
  ))
)

(declare-datatypes ()
  ((RefHeadResult2
    (mkRefHeadResult2 (rhrVal2 OTypeD2) (rhrPath2 (Seq String)))
  ))
)
(define-fun Compare_0_0 ((x OTypeD0) (y OTypeD0)) Bool
  (= x y))
(define-fun Compare_1_0 ((x OTypeD1) (y OTypeD0)) Bool
  (ite (is-Atom1 x) (= (atom1 x) y)
  (ite (is-Wrap1 x) (Compare_0_0 (wrap1 x) y)
  false)))
(define-fun Compare_1_1 ((x OTypeD1) (y OTypeD1)) Bool
  (ite (is-Wrap1 x) (Compare_1_0 y (wrap1 x))
  (ite (is-Wrap1 y) (Compare_1_0 x (wrap1 y))
  (ite (is-Atom1 x) (ite (is-Atom1 y) (= (atom1 x) (atom1 y)) false)
  (ite (is-OObj1 x) (ite (is-OObj1 y)
    (forall ((ks String)) (Compare_0_0 (select (obj1 x) ks) (select (obj1 y) ks)))
  false)
  (ite (is-OArray1 x) (ite (is-OArray1 y)
    (and (= (seq.len (arr1 x)) (seq.len (arr1 y)))
         (forall ((ki Int)) (or (>= ki (seq.len (arr1 x))) (Compare_0_0 (seq.nth (arr1 x) ki) (seq.nth (arr1 y) ki)))))
  false)
  (ite (is-OSet1 x) (ite (is-OSet1 y)
    (= (set1 x) (set1 y))
  false)
  false)))))))
(define-fun Compare_2_0 ((x OTypeD2) (y OTypeD0)) Bool
  (ite (is-Atom2 x) (= (atom2 x) y)
  (ite (is-Wrap2 x) (Compare_1_0 (wrap2 x) y)
  false)))
(define-fun Compare_2_1 ((x OTypeD2) (y OTypeD1)) Bool
  (ite (is-Wrap2 x) (Compare_1_1 (wrap2 x) y)
  (ite (is-Wrap1 y) (Compare_2_0 x (wrap1 y))
  (ite (is-Atom2 x)
    (ite (is-Atom1 y) (= (atom2 x) (atom1 y)) false)
  (ite (is-OObj2 x)
    (ite (is-OObj1 y)
      (forall ((ks String)) (Compare_1_0 (select (obj2 x) ks) (select (obj1 y) ks)))
    false)
  (ite (is-OArray2 x)
    (ite (is-OArray1 y)
      (and (= (seq.len (arr2 x)) (seq.len (arr1 y)))
           (forall ((ki Int)) (or (>= ki (seq.len (arr2 x))) (Compare_1_0 (seq.nth (arr2 x) ki) (seq.nth (arr1 y) ki)))))
    false)
  (ite (is-OSet2 x)
    (ite (is-OSet1 y)
      (and (forall ((se1 OTypeD1)) (=> (select (set2 x) se1) (exists ((se2 OTypeD0)) (and (select (set1 y) se2) (Compare_1_0 se1 se2)))))
           (forall ((se2 OTypeD0)) (=> (select (set1 y) se2) (exists ((se1 OTypeD1)) (and (select (set2 x) se1) (Compare_1_0 se1 se2))))))
    false)
  false)))))))
(define-fun Compare_2_2 ((x OTypeD2) (y OTypeD2)) Bool
  (ite (is-Wrap2 x) (Compare_2_1 y (wrap2 x))
  (ite (is-Wrap2 y) (Compare_2_1 x (wrap2 y))
  (ite (is-Atom2 x) (ite (is-Atom2 y) (= (atom2 x) (atom2 y)) false)
  (ite (is-OObj2 x) (ite (is-OObj2 y)
    (forall ((ks String)) (Compare_1_1 (select (obj2 x) ks) (select (obj2 y) ks)))
  false)
  (ite (is-OArray2 x) (ite (is-OArray2 y)
    (and (= (seq.len (arr2 x)) (seq.len (arr2 y)))
         (forall ((ki Int)) (or (>= ki (seq.len (arr2 x))) (Compare_1_1 (seq.nth (arr2 x) ki) (seq.nth (arr2 y) ki)))))
  false)
  (ite (is-OSet2 x) (ite (is-OSet2 y)
    (and (forall ((se1 OTypeD1)) (=> (select (set2 x) se1) (exists ((se2 OTypeD1)) (and (select (set2 y) se2) (Compare_1_1 se1 se2)))))
         (forall ((se2 OTypeD1)) (=> (select (set2 y) se2) (exists ((se1 OTypeD1)) (and (select (set2 x) se1) (Compare_1_1 se1 se2))))))
  false)
  false)))))))
(define-fun OSetUnion1 ((x OTypeD1) (y OTypeD1)) OTypeD1
  (OSet1 ((_ map or) (set1 x) (set1 y))))
(define-fun OSetUnion2 ((x OTypeD2) (y OTypeD2)) OTypeD2
  (OSet2 ((_ map or) (set2 x) (set2 y))))
(define-fun oto_string_D0 ((x OTypeD0)) String
  (ite (is-OString x) (str x)
  (ite (is-ONumber x) (int.to.str (num x))
  (ite (is-OBoolean x) (ite (bool x) "true" "false")
  (ite (is-ONull x) "null"
  "undefined")))))
(define-fun oto_string_fold_D1 ((acc String) (x OTypeD0)) String
  (ite (= acc "")
    (oto_string_D0 x)
    (str.++ acc ", " (oto_string_D0 x))))
(define-fun oto_string_D1 ((x OTypeD1)) String
  (ite (is-Atom1 x) (oto_string_D0 (atom1 x))
  (ite (is-Wrap1 x) (oto_string_D0 (wrap1 x))
  (ite (is-OArray1 x) (str.++ "[" (str.++ (seq.fold_left oto_string_fold_D1 "" (arr1 x)) "]"))
  ""))))
(define-fun oto_string_fold_D2 ((acc String) (x OTypeD1)) String
  (ite (= acc "")
    (oto_string_D1 x)
    (str.++ acc ", " (oto_string_D1 x))))
(define-fun oto_string_D2 ((x OTypeD2)) String
  (ite (is-Atom2 x) (oto_string_D0 (atom2 x))
  (ite (is-Wrap2 x) (oto_string_D1 (wrap2 x))
  (ite (is-OArray2 x) (str.++ "[" (str.++ (seq.fold_left oto_string_fold_D2 "" (arr2 x)) "]"))
  ""))))
(define-fun sprintf_0 ((fmt String)) String fmt)
(define-fun sprintf_1 ((fmt String) (s0 String)) String
  (str.replace fmt "%v" s0))
(define-fun sprintf_2 ((fmt String) (s0 String) (s1 String)) String
  (str.replace (str.replace fmt "%v" s0) "%v" s1))
(define-fun sprintf_3 ((fmt String) (s0 String) (s1 String) (s2 String)) String
  (str.replace (str.replace (str.replace fmt "%v" s0) "%v" s1) "%v" s2))
(define-fun sprintf_4 ((fmt String) (s0 String) (s1 String) (s2 String) (s3 String)) String
  (str.replace (str.replace (str.replace (str.replace fmt "%v" s0) "%v" s1) "%v" s2) "%v" s3))
(define-fun sprintf_5 ((fmt String) (s0 String) (s1 String) (s2 String) (s3 String) (s4 String)) String
  (str.replace (str.replace (str.replace (str.replace (str.replace fmt "%v" s0) "%v" s1) "%v" s2) "%v" s3) "%v" s4))
(declare-fun input () OTypeD2)
(declare-fun input_arr () OTypeD1)
(declare-fun input_arr_1 () OTypeD1)
(declare-fun allow () OTypeD0)
(define-fun allow_upd_1 ((obj OTypeD0)(__out RefHeadResult0)) Bool (or (exists ((__lv0 OTypeD0)) (exists ((__lv1 OTypeD0)) (and (is-ONumber __lv0) (and (is-ONumber __lv1) (and (and (Compare_0_0 (ite (and (is-OArray1 (ite (is-OObj2 input) (select (obj2 input) "front") (Wrap1 OUndef))) (>= (num __lv0) 0) (< (num __lv0) (seq.len (arr1 (ite (is-OObj2 input) (select (obj2 input) "front") (Wrap1 OUndef)))))) (seq.nth (arr1 (ite (is-OObj2 input) (select (obj2 input) "front") (Wrap1 OUndef))) (num __lv0)) OUndef) (OString "valid")) (Compare_0_0 (ite (and (is-OArray1 (ite (is-OObj2 input) (select (obj2 input) "back") (Wrap1 OUndef))) (>= (num __lv1) 0) (< (num __lv1) (seq.len (arr1 (ite (is-OObj2 input) (select (obj2 input) "back") (Wrap1 OUndef)))))) (seq.nth (arr1 (ite (is-OObj2 input) (select (obj2 input) "back") (Wrap1 OUndef))) (num __lv1)) OUndef) (OString "valid"))) (= __out (mkRefHeadResult0 (OBoolean true) (as seq.empty (Seq String))))))))) (and (not (exists ((__lv0 OTypeD0)) (exists ((__lv1 OTypeD0)) (and (is-ONumber __lv0) (and (is-ONumber __lv1) (and (Compare_0_0 (ite (and (is-OArray1 (ite (is-OObj2 input) (select (obj2 input) "front") (Wrap1 OUndef))) (>= (num __lv0) 0) (< (num __lv0) (seq.len (arr1 (ite (is-OObj2 input) (select (obj2 input) "front") (Wrap1 OUndef)))))) (seq.nth (arr1 (ite (is-OObj2 input) (select (obj2 input) "front") (Wrap1 OUndef))) (num __lv0)) OUndef) (OString "valid")) (Compare_0_0 (ite (and (is-OArray1 (ite (is-OObj2 input) (select (obj2 input) "back") (Wrap1 OUndef))) (>= (num __lv1) 0) (< (num __lv1) (seq.len (arr1 (ite (is-OObj2 input) (select (obj2 input) "back") (Wrap1 OUndef)))))) (seq.nth (arr1 (ite (is-OObj2 input) (select (obj2 input) "back") (Wrap1 OUndef))) (num __lv1)) OUndef) (OString "valid")))))))) (= __out (mkRefHeadResult0 OUndef (as seq.empty (Seq String)))))))
(declare-fun allow__res_1 () RefHeadResult0)
(assert (and (= input (OObj2 (store (store ((as const (Array String OTypeD1)) (Wrap1 OUndef)) "back" input_arr) "front" input_arr_1))) (is-OArray1 input_arr) (forall ((BthXY Int)) (let ((DFjPa (arr1 input_arr))) (=> (and (>= BthXY 0) (< BthXY (seq.len DFjPa))) (let ((ps4H2 (seq.nth DFjPa BthXY))) (is-OString ps4H2))))) (is-OArray1 input_arr_1) (forall ((kwo9j Int)) (let ((YfZl5 (arr1 input_arr_1))) (=> (and (>= kwo9j 0) (< kwo9j (seq.len YfZl5))) (let ((p627P (seq.nth YfZl5 kwo9j))) (is-OString p627P)))))))
(assert (let ((allow__cur_1 (ite (not (= (rhrVal0 allow__res_1) OUndef)) (rhrVal0 allow__res_1) OUndef))) (and (allow_upd_1 OUndef allow__res_1) (= allow allow__cur_1))))
