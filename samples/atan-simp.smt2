; 
(set-info :status unknown)
(declare-fun skoS3 () (_ FloatingPoint 3 20))
(declare-fun skoSX () (_ FloatingPoint 3 20))
(declare-fun skoX () (_ FloatingPoint 3 20))
(assert
 (let (($x50 (and (not (fp.leq skoSX ((_ to_fp 3 20) roundNearestTiesToEven 0.0))) (not (fp.leq skoS3 ((_ to_fp 3 20) roundNearestTiesToEven 0.0))))))
 (let ((?x35 (fp.neg skoX)))
 (let ((?x37 (fp.sub roundNearestTiesToEven ((_ to_fp 3 20) roundNearestTiesToEven (/ 129.0 10.0)) ?x35)))
 (let ((?x40 (fp.add roundNearestTiesToEven ((_ to_fp 3 20) roundNearestTiesToEven (/ 71.0 10.0)) (fp.div roundNearestTiesToEven skoS3 ?x37))))
 (let ((?x41 (fp.mul roundNearestTiesToEven ?x40 ((_ to_fp 3 20) roundNearestTiesToEven (- (/ 17827.0 5000.0))))))
 (and (= ?x41 ((_ to_fp 3 20) roundNearestTiesToEven (/ 91.0 10.0))) (and (not (fp.leq skoX ((_ to_fp 3 20) roundNearestTiesToEven 0.0))) $x50))))))))
(assert
 (= skoS3 skoS3))
(check-sat)
