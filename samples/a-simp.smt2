; 
(set-info :status unknown)
(declare-fun x1 () (_ BitVec 9))
(declare-fun x4 () (_ BitVec 9))
(declare-fun x3 () (_ BitVec 9))
(declare-fun z () Bool)
(declare-fun x2 () (_ BitVec 9))
(assert
 (let (($x51 (bvsgt (_ bv5 9) (ite (bvsle x1 (_ bv3 9)) (bvmul x1 (_ bv4 9)) (bvsdiv x1 (_ bv4 9))))))
 (let ((?x38 (bvadd x1 x2)))
 (let (($x40 (or (bvsgt ?x38 (bvsmod (ite (bvslt x2 (_ bv0 9)) (bvneg x2) x2) (_ bv20 9))) z)))
 (or $x40 (and (bvsgt (_ bv497 9) (bvsub x3 x4)) $x51))))))
(check-sat)
