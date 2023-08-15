; 
(set-info :status unknown)
(declare-fun y () (_ FloatingPoint 11 53))
(declare-fun x () (_ FloatingPoint 11 53))
(assert
 (let ((?x14 (fp.add roundNearestTiesToEven x y)))
 (let (($x18 (= x ?x14)))
 (let (($x17 (and (or (fp.isNaN x) (fp.isNaN ((_ to_fp 11 53) (_ bv0 64)))) (or (fp.isNaN ?x14) (fp.isNaN ((_ to_fp 11 53) (_ bv0 64)))))))
 (or $x17 $x18)))))
(check-sat)
