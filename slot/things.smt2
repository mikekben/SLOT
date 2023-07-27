; 
(set-info :status unknown)
(declare-fun x6_plus () (_ BitVec 3))
(declare-fun x6_minus () (_ BitVec 3))
(declare-fun x9_plus () (_ BitVec 3))
(declare-fun x9_minus () (_ BitVec 3))
(declare-fun x7_plus () (_ BitVec 3))
(declare-fun x7_minus () (_ BitVec 3))
(declare-fun x1_plus () (_ BitVec 3))
(declare-fun x1_minus () (_ BitVec 3))
(declare-fun x0_plus () (_ BitVec 3))
(declare-fun x0_minus () (_ BitVec 3))
(declare-fun x8_plus () (_ BitVec 3))
(declare-fun x8_minus () (_ BitVec 3))
(declare-fun x5_plus () (_ BitVec 3))
(declare-fun x5_minus () (_ BitVec 3))
(declare-fun x4_plus () (_ BitVec 3))
(declare-fun x4_minus () (_ BitVec 3))
(declare-fun x3_plus () (_ BitVec 3))
(declare-fun x3_minus () (_ BitVec 3))
(declare-fun x2_plus () (_ BitVec 3))
(declare-fun x2_minus () (_ BitVec 3))
(assert
 (not (= (_ bv0 3) (bvshl (_ bv1 3) (_ bv2 3)))))
(assert
 (bvsge x6_plus (_ bv0 3)))
(assert
 (not (= (_ bv0 3) (bvshl (_ bv1 3) (_ bv2 3)))))
(assert
 (bvsge x6_minus (_ bv0 3)))
(assert
 (not (= (_ bv0 3) (bvshl (_ bv1 3) (_ bv2 3)))))
(assert
 (bvsge x9_plus (_ bv0 3)))
(assert
 (not (= (_ bv0 3) (bvshl (_ bv1 3) (_ bv2 3)))))
(assert
 (bvsge x9_minus (_ bv0 3)))
(assert
 (not (= (_ bv0 3) (bvshl (_ bv1 3) (_ bv2 3)))))
(assert
 (bvsge x7_plus (_ bv0 3)))
(assert
 (not (= (_ bv0 3) (bvshl (_ bv1 3) (_ bv2 3)))))
(assert
 (bvsge x7_minus (_ bv0 3)))
(assert
 (not (= (_ bv0 3) (bvshl (_ bv1 3) (_ bv2 3)))))
(assert
 (bvsge x1_plus (_ bv0 3)))
(assert
 (not (= (_ bv0 3) (bvshl (_ bv1 3) (_ bv2 3)))))
(assert
 (bvsge x1_minus (_ bv0 3)))
(assert
 (not (= (_ bv0 3) (bvshl (_ bv1 3) (_ bv2 3)))))
(assert
 (bvsge x0_plus (_ bv0 3)))
(assert
 (not (= (_ bv0 3) (bvshl (_ bv1 3) (_ bv2 3)))))
(assert
 (bvsge x0_minus (_ bv0 3)))
(assert
 (not (= (_ bv0 3) (bvshl (_ bv1 3) (_ bv2 3)))))
(assert
 (bvsge x8_plus (_ bv0 3)))
(assert
 (not (= (_ bv0 3) (bvshl (_ bv1 3) (_ bv2 3)))))
(assert
 (bvsge x8_minus (_ bv0 3)))
(assert
 (not (= (_ bv0 3) (bvshl (_ bv1 3) (_ bv2 3)))))
(assert
 (bvsge x5_plus (_ bv0 3)))
(assert
 (not (= (_ bv0 3) (bvshl (_ bv1 3) (_ bv2 3)))))
(assert
 (bvsge x5_minus (_ bv0 3)))
(assert
 (not (= (_ bv0 3) (bvshl (_ bv1 3) (_ bv2 3)))))
(assert
 (bvsge x4_plus (_ bv0 3)))
(assert
 (not (= (_ bv0 3) (bvshl (_ bv1 3) (_ bv2 3)))))
(assert
 (bvsge x4_minus (_ bv0 3)))
(assert
 (not (= (_ bv0 3) (bvshl (_ bv1 3) (_ bv2 3)))))
(assert
 (bvsge x3_plus (_ bv0 3)))
(assert
 (not (= (_ bv0 3) (bvshl (_ bv1 3) (_ bv2 3)))))
(assert
 (bvsge x3_minus (_ bv0 3)))
(assert
 (not (= (_ bv0 3) (bvshl (_ bv1 3) (_ bv2 3)))))
(assert
 (bvsge x2_plus (_ bv0 3)))
(assert
 (not (= (_ bv0 3) (bvshl (_ bv1 3) (_ bv2 3)))))
(assert
 (bvsge x2_minus (_ bv0 3)))
(assert
 (not (= (_ bv0 3) (bvshl (_ bv1 3) (_ bv2 3)))))
(assert
 (not (= (_ bv1 3) (bvshl (_ bv1 3) (_ bv2 3)))))
(assert
 (not (= (_ bv1 3) (bvshl (_ bv1 3) (_ bv2 3)))))
(assert
 (let ((?x140 (bvneg (_ bv1 3))))
 (bvsmul_noovfl ?x140 x9_minus)))
(assert
 (let (($x148 (and (bvslt (_ bv0 3) x9_plus) (bvslt (_ bv0 3) (bvmul (bvneg (_ bv1 3)) x9_minus)))))
 (=> $x148 (bvslt (_ bv0 3) (bvadd x9_plus (bvmul (bvneg (_ bv1 3)) x9_minus))))))
(assert
 (let (($x164 (and (bvslt x9_plus (_ bv0 3)) (bvslt (bvmul (bvneg (_ bv1 3)) x9_minus) (_ bv0 3)))))
 (=> $x164 (bvslt (bvadd x9_plus (bvmul (bvneg (_ bv1 3)) x9_minus)) (_ bv0 3)))))
(assert
 (let ((?x140 (bvneg (_ bv1 3))))
 (let ((?x144 (bvmul ?x140 x9_minus)))
 (let ((?x145 (bvadd x9_plus ?x144)))
 (bvsle ?x145 (_ bv0 3))))))
(check-sat)
