; 
(set-info :status unknown)
(declare-fun x6_plus () (_ BitVec 5))
(declare-fun x6_minus () (_ BitVec 5))
(declare-fun x9_plus () (_ BitVec 5))
(declare-fun x9_minus () (_ BitVec 5))
(declare-fun x7_plus () (_ BitVec 5))
(declare-fun x7_minus () (_ BitVec 5))
(declare-fun x1_plus () (_ BitVec 5))
(declare-fun x1_minus () (_ BitVec 5))
(declare-fun x0_plus () (_ BitVec 5))
(declare-fun x0_minus () (_ BitVec 5))
(declare-fun x8_plus () (_ BitVec 5))
(declare-fun x8_minus () (_ BitVec 5))
(declare-fun x5_plus () (_ BitVec 5))
(declare-fun x5_minus () (_ BitVec 5))
(declare-fun x4_plus () (_ BitVec 5))
(declare-fun x4_minus () (_ BitVec 5))
(declare-fun x3_plus () (_ BitVec 5))
(declare-fun x3_minus () (_ BitVec 5))
(declare-fun x2_plus () (_ BitVec 5))
(declare-fun x2_minus () (_ BitVec 5))
(assert
 (bvsge x6_plus (_ bv0 5)))
(assert
 (bvsge x6_minus (_ bv0 5)))
(assert
 (bvsge x9_plus (_ bv0 5)))
(assert
 (bvsge x9_minus (_ bv0 5)))
(assert
 (bvsge x7_plus (_ bv0 5)))
(assert
 (bvsge x7_minus (_ bv0 5)))
(assert
 (bvsge x1_plus (_ bv0 5)))
(assert
 (bvsge x1_minus (_ bv0 5)))
(assert
 (bvsge x0_plus (_ bv0 5)))
(assert
 (bvsge x0_minus (_ bv0 5)))
(assert
 (bvsge x8_plus (_ bv0 5)))
(assert
 (bvsge x8_minus (_ bv0 5)))
(assert
 (bvsge x5_plus (_ bv0 5)))
(assert
 (bvsge x5_minus (_ bv0 5)))
(assert
 (bvsge x4_plus (_ bv0 5)))
(assert
 (bvsge x4_minus (_ bv0 5)))
(assert
 (bvsge x3_plus (_ bv0 5)))
(assert
 (bvsge x3_minus (_ bv0 5)))
(assert
 (bvsge x2_plus (_ bv0 5)))
(assert
 (bvsge x2_minus (_ bv0 5)))
(assert
 (let (($x165 (and (bvslt (_ bv0 5) (bvsub x6_plus x6_minus)) (bvslt (_ bv0 5) (bvneg x6_minus)))))
 (let (($x167 (=> $x165 (bvslt (_ bv0 5) (bvadd (bvsub x6_plus x6_minus) (bvneg x6_minus))))))
 (let ((?x156 (bvsub x6_plus x6_minus)))
 (let (($x161 (bvslt ?x156 (_ bv0 5))))
 (ite (= x6_minus (bvshl (_ bv1 5) (_ bv4 5))) $x161 $x167))))))
(assert
 (let ((?x156 (bvsub x6_plus x6_minus)))
 (let (($x161 (bvslt ?x156 (_ bv0 5))))
 (let (($x194 (=> (and $x161 (bvslt (bvneg x6_minus) (_ bv0 5))) (bvslt (bvadd ?x156 (bvneg x6_minus)) (_ bv0 5)))))
 (let (($x190 (bvslt (_ bv0 5) x6_minus)))
 (=> (and $x190 (and $x161 (bvslt (bvneg x6_minus) (_ bv0 5)))) (bvslt (bvadd ?x156 (bvneg x6_minus)) (_ bv0 5))))))))
(assert
 (let ((?x155 (bvneg (_ bv1 5))))
 (bvsle x6_minus ?x155)))
(assert
 (let ((?x208 (bvmul (_ bv2 5) x9_plus)))
 (bvsmul_noovfl ?x208 x9_plus)))
(assert
 (let ((?x210 (bvneg (_ bv2 5))))
 (let ((?x211 (bvmul ?x210 x9_minus)))
 (bvsmul_noovfl ?x211 x9_minus))))
(assert
 (=> (and (bvslt (_ bv0 5) (bvadd x9_plus x9_minus)) (bvslt (_ bv0 5) x9_minus)) (bvslt (_ bv0 5) (bvadd (bvadd x9_plus x9_minus) x9_minus))))
(assert
 (=> (and (bvslt (bvadd x9_plus x9_minus) (_ bv0 5)) (bvslt x9_minus (_ bv0 5))) (bvslt (bvadd (bvadd x9_plus x9_minus) x9_minus) (_ bv0 5))))
(assert
 (let ((?x215 (bvadd x9_plus x9_minus)))
 (let ((?x247 (bvadd ?x215 x7_plus)))
 (let ((?x248 (bvadd ?x247 x7_plus)))
 (=> (and (bvslt (_ bv0 5) ?x247) (bvslt (_ bv0 5) x7_plus)) (bvslt (_ bv0 5) ?x248))))))
(assert
 (let ((?x215 (bvadd x9_plus x9_minus)))
 (let ((?x247 (bvadd ?x215 x7_plus)))
 (let ((?x248 (bvadd ?x247 x7_plus)))
 (=> (and (bvslt ?x247 (_ bv0 5)) (bvslt x7_plus (_ bv0 5))) (bvslt ?x248 (_ bv0 5)))))))
(assert
 (let ((?x155 (bvneg (_ bv1 5))))
 (let ((?x279 (bvmul ?x155 x7_minus)))
 (bvsmul_noovfl ?x279 x7_minus))))
(assert
 (let ((?x215 (bvadd x9_plus x9_minus)))
 (let ((?x247 (bvadd ?x215 x7_plus)))
 (let ((?x283 (bvadd ?x247 x7_minus)))
 (let ((?x284 (bvadd ?x283 x7_minus)))
 (=> (and (bvslt (_ bv0 5) ?x283) (bvslt (_ bv0 5) x7_minus)) (bvslt (_ bv0 5) ?x284)))))))
(assert
 (let ((?x215 (bvadd x9_plus x9_minus)))
 (let ((?x247 (bvadd ?x215 x7_plus)))
 (let ((?x283 (bvadd ?x247 x7_minus)))
 (let ((?x284 (bvadd ?x283 x7_minus)))
 (=> (and (bvslt ?x283 (_ bv0 5)) (bvslt x7_minus (_ bv0 5))) (bvslt ?x284 (_ bv0 5))))))))
(assert
 (let ((?x215 (bvadd x9_plus x9_minus)))
 (let ((?x247 (bvadd ?x215 x7_plus)))
 (let ((?x283 (bvadd ?x247 x7_minus)))
 (let ((?x315 (bvadd ?x283 x1_plus)))
 (let ((?x316 (bvadd ?x315 x1_plus)))
 (=> (and (bvslt (_ bv0 5) ?x315) (bvslt (_ bv0 5) x1_plus)) (bvslt (_ bv0 5) ?x316))))))))
(assert
 (let ((?x215 (bvadd x9_plus x9_minus)))
 (let ((?x247 (bvadd ?x215 x7_plus)))
 (let ((?x283 (bvadd ?x247 x7_minus)))
 (let ((?x315 (bvadd ?x283 x1_plus)))
 (let ((?x316 (bvadd ?x315 x1_plus)))
 (=> (and (bvslt ?x315 (_ bv0 5)) (bvslt x1_plus (_ bv0 5))) (bvslt ?x316 (_ bv0 5)))))))))
(assert
 (let ((?x155 (bvneg (_ bv1 5))))
 (let ((?x347 (bvmul ?x155 x1_minus)))
 (bvsmul_noovfl ?x347 x1_minus))))
(assert
 (let ((?x215 (bvadd x9_plus x9_minus)))
 (let ((?x247 (bvadd ?x215 x7_plus)))
 (let ((?x283 (bvadd ?x247 x7_minus)))
 (let ((?x315 (bvadd ?x283 x1_plus)))
 (let ((?x351 (bvadd ?x315 x1_minus)))
 (let ((?x352 (bvadd ?x351 x1_minus)))
 (=> (and (bvslt (_ bv0 5) ?x351) (bvslt (_ bv0 5) x1_minus)) (bvslt (_ bv0 5) ?x352)))))))))
(assert
 (let ((?x215 (bvadd x9_plus x9_minus)))
 (let ((?x247 (bvadd ?x215 x7_plus)))
 (let ((?x283 (bvadd ?x247 x7_minus)))
 (let ((?x315 (bvadd ?x283 x1_plus)))
 (let ((?x351 (bvadd ?x315 x1_minus)))
 (let ((?x352 (bvadd ?x351 x1_minus)))
 (=> (and (bvslt ?x351 (_ bv0 5)) (bvslt x1_minus (_ bv0 5))) (bvslt ?x352 (_ bv0 5))))))))))
(assert
 (let ((?x215 (bvadd x9_plus x9_minus)))
 (let ((?x247 (bvadd ?x215 x7_plus)))
 (let ((?x283 (bvadd ?x247 x7_minus)))
 (let ((?x315 (bvadd ?x283 x1_plus)))
 (let ((?x351 (bvadd ?x315 x1_minus)))
 (let ((?x383 (bvadd ?x351 x0_plus)))
 (let ((?x384 (bvadd ?x383 x0_plus)))
 (=> (and (bvslt (_ bv0 5) ?x383) (bvslt (_ bv0 5) x0_plus)) (bvslt (_ bv0 5) ?x384))))))))))
(assert
 (let ((?x215 (bvadd x9_plus x9_minus)))
 (let ((?x247 (bvadd ?x215 x7_plus)))
 (let ((?x283 (bvadd ?x247 x7_minus)))
 (let ((?x315 (bvadd ?x283 x1_plus)))
 (let ((?x351 (bvadd ?x315 x1_minus)))
 (let ((?x383 (bvadd ?x351 x0_plus)))
 (let ((?x384 (bvadd ?x383 x0_plus)))
 (=> (and (bvslt ?x383 (_ bv0 5)) (bvslt x0_plus (_ bv0 5))) (bvslt ?x384 (_ bv0 5)))))))))))
(assert
 (let ((?x155 (bvneg (_ bv1 5))))
 (let ((?x415 (bvmul ?x155 x0_minus)))
 (bvsmul_noovfl ?x415 x0_minus))))
(assert
 (let ((?x215 (bvadd x9_plus x9_minus)))
 (let ((?x247 (bvadd ?x215 x7_plus)))
 (let ((?x283 (bvadd ?x247 x7_minus)))
 (let ((?x315 (bvadd ?x283 x1_plus)))
 (let ((?x351 (bvadd ?x315 x1_minus)))
 (let ((?x383 (bvadd ?x351 x0_plus)))
 (let ((?x419 (bvadd ?x383 x0_minus)))
 (let ((?x420 (bvadd ?x419 x0_minus)))
 (=> (and (bvslt (_ bv0 5) ?x419) (bvslt (_ bv0 5) x0_minus)) (bvslt (_ bv0 5) ?x420)))))))))))
(assert
 (let ((?x215 (bvadd x9_plus x9_minus)))
 (let ((?x247 (bvadd ?x215 x7_plus)))
 (let ((?x283 (bvadd ?x247 x7_minus)))
 (let ((?x315 (bvadd ?x283 x1_plus)))
 (let ((?x351 (bvadd ?x315 x1_minus)))
 (let ((?x383 (bvadd ?x351 x0_plus)))
 (let ((?x419 (bvadd ?x383 x0_minus)))
 (let ((?x420 (bvadd ?x419 x0_minus)))
 (=> (and (bvslt ?x419 (_ bv0 5)) (bvslt x0_minus (_ bv0 5))) (bvslt ?x420 (_ bv0 5))))))))))))
(assert
 (bvsle x0_minus (_ bv0 5)))
(assert
 (let ((?x155 (bvneg (_ bv1 5))))
 (let ((?x451 (bvmul ?x155 x9_minus)))
 (bvsmul_noovfl ?x451 x9_minus))))
(assert
 (=> (and (bvslt (_ bv0 5) (bvadd x9_plus x9_minus)) (bvslt (_ bv0 5) x9_minus)) (bvslt (_ bv0 5) (bvadd (bvadd x9_plus x9_minus) x9_minus))))
(assert
 (=> (and (bvslt (bvadd x9_plus x9_minus) (_ bv0 5)) (bvslt x9_minus (_ bv0 5))) (bvslt (bvadd (bvadd x9_plus x9_minus) x9_minus) (_ bv0 5))))
(assert
 (let ((?x215 (bvadd x9_plus x9_minus)))
 (let ((?x455 (bvadd ?x215 x8_plus)))
 (let ((?x456 (bvadd ?x455 x8_plus)))
 (=> (and (bvslt (_ bv0 5) ?x455) (bvslt (_ bv0 5) x8_plus)) (bvslt (_ bv0 5) ?x456))))))
(assert
 (let ((?x215 (bvadd x9_plus x9_minus)))
 (let ((?x455 (bvadd ?x215 x8_plus)))
 (let ((?x456 (bvadd ?x455 x8_plus)))
 (=> (and (bvslt ?x455 (_ bv0 5)) (bvslt x8_plus (_ bv0 5))) (bvslt ?x456 (_ bv0 5)))))))
(assert
 (let ((?x155 (bvneg (_ bv1 5))))
 (let ((?x487 (bvmul ?x155 x8_minus)))
 (bvsmul_noovfl ?x487 x8_minus))))
(assert
 (let ((?x215 (bvadd x9_plus x9_minus)))
 (let ((?x455 (bvadd ?x215 x8_plus)))
 (let ((?x491 (bvadd ?x455 x8_minus)))
 (let ((?x492 (bvadd ?x491 x8_minus)))
 (=> (and (bvslt (_ bv0 5) ?x491) (bvslt (_ bv0 5) x8_minus)) (bvslt (_ bv0 5) ?x492)))))))
(assert
 (let ((?x215 (bvadd x9_plus x9_minus)))
 (let ((?x455 (bvadd ?x215 x8_plus)))
 (let ((?x491 (bvadd ?x455 x8_minus)))
 (let ((?x492 (bvadd ?x491 x8_minus)))
 (=> (and (bvslt ?x491 (_ bv0 5)) (bvslt x8_minus (_ bv0 5))) (bvslt ?x492 (_ bv0 5))))))))
(assert
 (let ((?x155 (bvneg (_ bv1 5))))
 (let ((?x523 (bvmul ?x155 x0_plus)))
 (bvsmul_noovfl ?x523 x0_plus))))
(assert
 (let ((?x215 (bvadd x9_plus x9_minus)))
 (let ((?x455 (bvadd ?x215 x8_plus)))
 (let ((?x491 (bvadd ?x455 x8_minus)))
 (let ((?x527 (bvadd ?x491 x0_plus)))
 (let ((?x528 (bvadd ?x527 x0_plus)))
 (=> (and (bvslt (_ bv0 5) ?x527) (bvslt (_ bv0 5) x0_plus)) (bvslt (_ bv0 5) ?x528))))))))
(assert
 (let ((?x215 (bvadd x9_plus x9_minus)))
 (let ((?x455 (bvadd ?x215 x8_plus)))
 (let ((?x491 (bvadd ?x455 x8_minus)))
 (let ((?x527 (bvadd ?x491 x0_plus)))
 (let ((?x528 (bvadd ?x527 x0_plus)))
 (=> (and (bvslt ?x527 (_ bv0 5)) (bvslt x0_plus (_ bv0 5))) (bvslt ?x528 (_ bv0 5)))))))))
(assert
 (let ((?x215 (bvadd x9_plus x9_minus)))
 (let ((?x455 (bvadd ?x215 x8_plus)))
 (let ((?x491 (bvadd ?x455 x8_minus)))
 (let ((?x527 (bvadd ?x491 x0_plus)))
 (let ((?x553 (bvadd ?x527 x0_minus)))
 (let ((?x554 (bvadd ?x553 x0_minus)))
 (=> (and (bvslt (_ bv0 5) ?x553) (bvslt (_ bv0 5) x0_minus)) (bvslt (_ bv0 5) ?x554)))))))))
(assert
 (let ((?x215 (bvadd x9_plus x9_minus)))
 (let ((?x455 (bvadd ?x215 x8_plus)))
 (let ((?x491 (bvadd ?x455 x8_minus)))
 (let ((?x527 (bvadd ?x491 x0_plus)))
 (let ((?x553 (bvadd ?x527 x0_minus)))
 (let ((?x554 (bvadd ?x553 x0_minus)))
 (=> (and (bvslt ?x553 (_ bv0 5)) (bvslt x0_minus (_ bv0 5))) (bvslt ?x554 (_ bv0 5))))))))))
(assert
 (bvsle x0_minus (_ bv0 5)))
(assert
 (let ((?x155 (bvneg (_ bv1 5))))
 (let ((?x451 (bvmul ?x155 x9_minus)))
 (bvsmul_noovfl ?x451 x9_minus))))
(assert
 (=> (and (bvslt (_ bv0 5) (bvadd x9_plus x9_minus)) (bvslt (_ bv0 5) x9_minus)) (bvslt (_ bv0 5) (bvadd (bvadd x9_plus x9_minus) x9_minus))))
(assert
 (=> (and (bvslt (bvadd x9_plus x9_minus) (_ bv0 5)) (bvslt x9_minus (_ bv0 5))) (bvslt (bvadd (bvadd x9_plus x9_minus) x9_minus) (_ bv0 5))))
(assert
 (let ((?x155 (bvneg (_ bv1 5))))
 (let ((?x579 (bvmul ?x155 x6_plus)))
 (bvsmul_noovfl ?x579 x6_plus))))
(assert
 (let ((?x215 (bvadd x9_plus x9_minus)))
 (let ((?x583 (bvadd ?x215 x6_plus)))
 (let ((?x584 (bvadd ?x583 x6_plus)))
 (=> (and (bvslt (_ bv0 5) ?x583) (bvslt (_ bv0 5) x6_plus)) (bvslt (_ bv0 5) ?x584))))))
(assert
 (let ((?x215 (bvadd x9_plus x9_minus)))
 (let ((?x583 (bvadd ?x215 x6_plus)))
 (let ((?x584 (bvadd ?x583 x6_plus)))
 (=> (and (bvslt ?x583 (_ bv0 5)) (bvslt x6_plus (_ bv0 5))) (bvslt ?x584 (_ bv0 5)))))))
(assert
 (let ((?x215 (bvadd x9_plus x9_minus)))
 (let ((?x583 (bvadd ?x215 x6_plus)))
 (let ((?x615 (bvadd ?x583 x6_minus)))
 (let ((?x616 (bvadd ?x615 x6_minus)))
 (=> (and (bvslt (_ bv0 5) ?x615) (bvslt (_ bv0 5) x6_minus)) (bvslt (_ bv0 5) ?x616)))))))
(assert
 (let ((?x215 (bvadd x9_plus x9_minus)))
 (let ((?x583 (bvadd ?x215 x6_plus)))
 (let ((?x615 (bvadd ?x583 x6_minus)))
 (let ((?x616 (bvadd ?x615 x6_minus)))
 (=> (and (bvslt ?x615 (_ bv0 5)) (bvslt x6_minus (_ bv0 5))) (bvslt ?x616 (_ bv0 5))))))))
(assert
 (let ((?x215 (bvadd x9_plus x9_minus)))
 (let ((?x583 (bvadd ?x215 x6_plus)))
 (let ((?x615 (bvadd ?x583 x6_minus)))
 (let ((?x644 (bvadd ?x615 x5_plus)))
 (let ((?x645 (bvadd ?x644 x5_plus)))
 (=> (and (bvslt (_ bv0 5) ?x644) (bvslt (_ bv0 5) x5_plus)) (bvslt (_ bv0 5) ?x645))))))))
(assert
 (let ((?x215 (bvadd x9_plus x9_minus)))
 (let ((?x583 (bvadd ?x215 x6_plus)))
 (let ((?x615 (bvadd ?x583 x6_minus)))
 (let ((?x644 (bvadd ?x615 x5_plus)))
 (let ((?x645 (bvadd ?x644 x5_plus)))
 (=> (and (bvslt ?x644 (_ bv0 5)) (bvslt x5_plus (_ bv0 5))) (bvslt ?x645 (_ bv0 5)))))))))
(assert
 (let ((?x155 (bvneg (_ bv1 5))))
 (let ((?x676 (bvmul ?x155 x5_minus)))
 (bvsmul_noovfl ?x676 x5_minus))))
(assert
 (let ((?x215 (bvadd x9_plus x9_minus)))
 (let ((?x583 (bvadd ?x215 x6_plus)))
 (let ((?x615 (bvadd ?x583 x6_minus)))
 (let ((?x644 (bvadd ?x615 x5_plus)))
 (let ((?x680 (bvadd ?x644 x5_minus)))
 (let ((?x681 (bvadd ?x680 x5_minus)))
 (=> (and (bvslt (_ bv0 5) ?x680) (bvslt (_ bv0 5) x5_minus)) (bvslt (_ bv0 5) ?x681)))))))))
(assert
 (let ((?x215 (bvadd x9_plus x9_minus)))
 (let ((?x583 (bvadd ?x215 x6_plus)))
 (let ((?x615 (bvadd ?x583 x6_minus)))
 (let ((?x644 (bvadd ?x615 x5_plus)))
 (let ((?x680 (bvadd ?x644 x5_minus)))
 (let ((?x681 (bvadd ?x680 x5_minus)))
 (=> (and (bvslt ?x680 (_ bv0 5)) (bvslt x5_minus (_ bv0 5))) (bvslt ?x681 (_ bv0 5))))))))))
(assert
 (let ((?x155 (bvneg (_ bv1 5))))
 (let ((?x712 (bvmul ?x155 x4_plus)))
 (bvsmul_noovfl ?x712 x4_plus))))
(assert
 (let ((?x215 (bvadd x9_plus x9_minus)))
 (let ((?x583 (bvadd ?x215 x6_plus)))
 (let ((?x615 (bvadd ?x583 x6_minus)))
 (let ((?x644 (bvadd ?x615 x5_plus)))
 (let ((?x680 (bvadd ?x644 x5_minus)))
 (let ((?x716 (bvadd ?x680 x4_plus)))
 (let ((?x717 (bvadd ?x716 x4_plus)))
 (=> (and (bvslt (_ bv0 5) ?x716) (bvslt (_ bv0 5) x4_plus)) (bvslt (_ bv0 5) ?x717))))))))))
(assert
 (let ((?x215 (bvadd x9_plus x9_minus)))
 (let ((?x583 (bvadd ?x215 x6_plus)))
 (let ((?x615 (bvadd ?x583 x6_minus)))
 (let ((?x644 (bvadd ?x615 x5_plus)))
 (let ((?x680 (bvadd ?x644 x5_minus)))
 (let ((?x716 (bvadd ?x680 x4_plus)))
 (let ((?x717 (bvadd ?x716 x4_plus)))
 (=> (and (bvslt ?x716 (_ bv0 5)) (bvslt x4_plus (_ bv0 5))) (bvslt ?x717 (_ bv0 5)))))))))))
(assert
 (let ((?x215 (bvadd x9_plus x9_minus)))
 (let ((?x583 (bvadd ?x215 x6_plus)))
 (let ((?x615 (bvadd ?x583 x6_minus)))
 (let ((?x644 (bvadd ?x615 x5_plus)))
 (let ((?x680 (bvadd ?x644 x5_minus)))
 (let ((?x716 (bvadd ?x680 x4_plus)))
 (let ((?x748 (bvadd ?x716 x4_minus)))
 (let ((?x749 (bvadd ?x748 x4_minus)))
 (=> (and (bvslt (_ bv0 5) ?x748) (bvslt (_ bv0 5) x4_minus)) (bvslt (_ bv0 5) ?x749)))))))))))
(assert
 (let ((?x215 (bvadd x9_plus x9_minus)))
 (let ((?x583 (bvadd ?x215 x6_plus)))
 (let ((?x615 (bvadd ?x583 x6_minus)))
 (let ((?x644 (bvadd ?x615 x5_plus)))
 (let ((?x680 (bvadd ?x644 x5_minus)))
 (let ((?x716 (bvadd ?x680 x4_plus)))
 (let ((?x748 (bvadd ?x716 x4_minus)))
 (let ((?x749 (bvadd ?x748 x4_minus)))
 (=> (and (bvslt ?x748 (_ bv0 5)) (bvslt x4_minus (_ bv0 5))) (bvslt ?x749 (_ bv0 5))))))))))))
(assert
 (let ((?x155 (bvneg (_ bv1 5))))
 (let ((?x780 (bvmul ?x155 x3_plus)))
 (bvsmul_noovfl ?x780 x3_plus))))
(assert
 (let ((?x215 (bvadd x9_plus x9_minus)))
 (let ((?x583 (bvadd ?x215 x6_plus)))
 (let ((?x615 (bvadd ?x583 x6_minus)))
 (let ((?x644 (bvadd ?x615 x5_plus)))
 (let ((?x680 (bvadd ?x644 x5_minus)))
 (let ((?x716 (bvadd ?x680 x4_plus)))
 (let ((?x748 (bvadd ?x716 x4_minus)))
 (let ((?x784 (bvadd ?x748 x3_plus)))
 (let ((?x785 (bvadd ?x784 x3_plus)))
 (=> (and (bvslt (_ bv0 5) ?x784) (bvslt (_ bv0 5) x3_plus)) (bvslt (_ bv0 5) ?x785))))))))))))
(assert
 (let ((?x215 (bvadd x9_plus x9_minus)))
 (let ((?x583 (bvadd ?x215 x6_plus)))
 (let ((?x615 (bvadd ?x583 x6_minus)))
 (let ((?x644 (bvadd ?x615 x5_plus)))
 (let ((?x680 (bvadd ?x644 x5_minus)))
 (let ((?x716 (bvadd ?x680 x4_plus)))
 (let ((?x748 (bvadd ?x716 x4_minus)))
 (let ((?x784 (bvadd ?x748 x3_plus)))
 (let ((?x785 (bvadd ?x784 x3_plus)))
 (=> (and (bvslt ?x784 (_ bv0 5)) (bvslt x3_plus (_ bv0 5))) (bvslt ?x785 (_ bv0 5)))))))))))))
(assert
 (let ((?x215 (bvadd x9_plus x9_minus)))
 (let ((?x583 (bvadd ?x215 x6_plus)))
 (let ((?x615 (bvadd ?x583 x6_minus)))
 (let ((?x644 (bvadd ?x615 x5_plus)))
 (let ((?x680 (bvadd ?x644 x5_minus)))
 (let ((?x716 (bvadd ?x680 x4_plus)))
 (let ((?x748 (bvadd ?x716 x4_minus)))
 (let ((?x784 (bvadd ?x748 x3_plus)))
 (let ((?x816 (bvadd ?x784 x3_minus)))
 (let ((?x817 (bvadd ?x816 x3_minus)))
 (=> (and (bvslt (_ bv0 5) ?x816) (bvslt (_ bv0 5) x3_minus)) (bvslt (_ bv0 5) ?x817)))))))))))))
(assert
 (let ((?x215 (bvadd x9_plus x9_minus)))
 (let ((?x583 (bvadd ?x215 x6_plus)))
 (let ((?x615 (bvadd ?x583 x6_minus)))
 (let ((?x644 (bvadd ?x615 x5_plus)))
 (let ((?x680 (bvadd ?x644 x5_minus)))
 (let ((?x716 (bvadd ?x680 x4_plus)))
 (let ((?x748 (bvadd ?x716 x4_minus)))
 (let ((?x784 (bvadd ?x748 x3_plus)))
 (let ((?x816 (bvadd ?x784 x3_minus)))
 (let ((?x817 (bvadd ?x816 x3_minus)))
 (=> (and (bvslt ?x816 (_ bv0 5)) (bvslt x3_minus (_ bv0 5))) (bvslt ?x817 (_ bv0 5))))))))))))))
(assert
 (let ((?x155 (bvneg (_ bv1 5))))
 (let ((?x848 (bvmul ?x155 x1_plus)))
 (bvsmul_noovfl ?x848 x1_plus))))
(assert
 (let ((?x215 (bvadd x9_plus x9_minus)))
 (let ((?x583 (bvadd ?x215 x6_plus)))
 (let ((?x615 (bvadd ?x583 x6_minus)))
 (let ((?x644 (bvadd ?x615 x5_plus)))
 (let ((?x680 (bvadd ?x644 x5_minus)))
 (let ((?x716 (bvadd ?x680 x4_plus)))
 (let ((?x748 (bvadd ?x716 x4_minus)))
 (let ((?x784 (bvadd ?x748 x3_plus)))
 (let ((?x816 (bvadd ?x784 x3_minus)))
 (let ((?x852 (bvadd ?x816 x1_plus)))
 (let ((?x853 (bvadd ?x852 x1_plus)))
 (=> (and (bvslt (_ bv0 5) ?x852) (bvslt (_ bv0 5) x1_plus)) (bvslt (_ bv0 5) ?x853))))))))))))))
(assert
 (let ((?x215 (bvadd x9_plus x9_minus)))
 (let ((?x583 (bvadd ?x215 x6_plus)))
 (let ((?x615 (bvadd ?x583 x6_minus)))
 (let ((?x644 (bvadd ?x615 x5_plus)))
 (let ((?x680 (bvadd ?x644 x5_minus)))
 (let ((?x716 (bvadd ?x680 x4_plus)))
 (let ((?x748 (bvadd ?x716 x4_minus)))
 (let ((?x784 (bvadd ?x748 x3_plus)))
 (let ((?x816 (bvadd ?x784 x3_minus)))
 (let ((?x852 (bvadd ?x816 x1_plus)))
 (let ((?x853 (bvadd ?x852 x1_plus)))
 (=> (and (bvslt ?x852 (_ bv0 5)) (bvslt x1_plus (_ bv0 5))) (bvslt ?x853 (_ bv0 5)))))))))))))))
(assert
 (let ((?x215 (bvadd x9_plus x9_minus)))
 (let ((?x583 (bvadd ?x215 x6_plus)))
 (let ((?x615 (bvadd ?x583 x6_minus)))
 (let ((?x644 (bvadd ?x615 x5_plus)))
 (let ((?x680 (bvadd ?x644 x5_minus)))
 (let ((?x716 (bvadd ?x680 x4_plus)))
 (let ((?x748 (bvadd ?x716 x4_minus)))
 (let ((?x784 (bvadd ?x748 x3_plus)))
 (let ((?x816 (bvadd ?x784 x3_minus)))
 (let ((?x852 (bvadd ?x816 x1_plus)))
 (let ((?x878 (bvadd ?x852 x1_minus)))
 (let ((?x879 (bvadd ?x878 x1_minus)))
 (=> (and (bvslt (_ bv0 5) ?x878) (bvslt (_ bv0 5) x1_minus)) (bvslt (_ bv0 5) ?x879)))))))))))))))
(assert
 (let ((?x215 (bvadd x9_plus x9_minus)))
 (let ((?x583 (bvadd ?x215 x6_plus)))
 (let ((?x615 (bvadd ?x583 x6_minus)))
 (let ((?x644 (bvadd ?x615 x5_plus)))
 (let ((?x680 (bvadd ?x644 x5_minus)))
 (let ((?x716 (bvadd ?x680 x4_plus)))
 (let ((?x748 (bvadd ?x716 x4_minus)))
 (let ((?x784 (bvadd ?x748 x3_plus)))
 (let ((?x816 (bvadd ?x784 x3_minus)))
 (let ((?x852 (bvadd ?x816 x1_plus)))
 (let ((?x878 (bvadd ?x852 x1_minus)))
 (let ((?x879 (bvadd ?x878 x1_minus)))
 (=> (and (bvslt ?x878 (_ bv0 5)) (bvslt x1_minus (_ bv0 5))) (bvslt ?x879 (_ bv0 5))))))))))))))))
(assert
 (bvsge x1_minus (_ bv0 5)))
(assert
 (let ((?x155 (bvneg (_ bv1 5))))
 (let ((?x487 (bvmul ?x155 x8_minus)))
 (bvsmul_noovfl ?x487 x8_minus))))
(assert
 (=> (and (bvslt (_ bv0 5) (bvadd x8_plus x8_minus)) (bvslt (_ bv0 5) x8_minus)) (bvslt (_ bv0 5) (bvadd (bvadd x8_plus x8_minus) x8_minus))))
(assert
 (=> (and (bvslt (bvadd x8_plus x8_minus) (_ bv0 5)) (bvslt x8_minus (_ bv0 5))) (bvslt (bvadd (bvadd x8_plus x8_minus) x8_minus) (_ bv0 5))))
(assert
 (let ((?x155 (bvneg (_ bv1 5))))
 (let ((?x579 (bvmul ?x155 x6_plus)))
 (bvsmul_noovfl ?x579 x6_plus))))
(assert
 (let ((?x904 (bvadd x8_plus x8_minus)))
 (let ((?x930 (bvadd ?x904 x6_plus)))
 (let ((?x931 (bvadd ?x930 x6_plus)))
 (=> (and (bvslt (_ bv0 5) ?x930) (bvslt (_ bv0 5) x6_plus)) (bvslt (_ bv0 5) ?x931))))))
(assert
 (let ((?x904 (bvadd x8_plus x8_minus)))
 (let ((?x930 (bvadd ?x904 x6_plus)))
 (let ((?x931 (bvadd ?x930 x6_plus)))
 (=> (and (bvslt ?x930 (_ bv0 5)) (bvslt x6_plus (_ bv0 5))) (bvslt ?x931 (_ bv0 5)))))))
(assert
 (let ((?x904 (bvadd x8_plus x8_minus)))
 (let ((?x930 (bvadd ?x904 x6_plus)))
 (let ((?x956 (bvadd ?x930 x6_minus)))
 (let ((?x957 (bvadd ?x956 x6_minus)))
 (=> (and (bvslt (_ bv0 5) ?x956) (bvslt (_ bv0 5) x6_minus)) (bvslt (_ bv0 5) ?x957)))))))
(assert
 (let ((?x904 (bvadd x8_plus x8_minus)))
 (let ((?x930 (bvadd ?x904 x6_plus)))
 (let ((?x956 (bvadd ?x930 x6_minus)))
 (let ((?x957 (bvadd ?x956 x6_minus)))
 (=> (and (bvslt ?x956 (_ bv0 5)) (bvslt x6_minus (_ bv0 5))) (bvslt ?x957 (_ bv0 5))))))))
(assert
 (let ((?x210 (bvneg (_ bv2 5))))
 (let ((?x982 (bvmul ?x210 x2_plus)))
 (bvsmul_noovfl ?x982 x2_plus))))
(assert
 (let ((?x904 (bvadd x8_plus x8_minus)))
 (let ((?x930 (bvadd ?x904 x6_plus)))
 (let ((?x956 (bvadd ?x930 x6_minus)))
 (let ((?x986 (bvadd ?x956 x2_plus)))
 (let ((?x987 (bvadd ?x986 x2_plus)))
 (=> (and (bvslt (_ bv0 5) ?x986) (bvslt (_ bv0 5) x2_plus)) (bvslt (_ bv0 5) ?x987))))))))
(assert
 (let ((?x904 (bvadd x8_plus x8_minus)))
 (let ((?x930 (bvadd ?x904 x6_plus)))
 (let ((?x956 (bvadd ?x930 x6_minus)))
 (let ((?x986 (bvadd ?x956 x2_plus)))
 (let ((?x987 (bvadd ?x986 x2_plus)))
 (=> (and (bvslt ?x986 (_ bv0 5)) (bvslt x2_plus (_ bv0 5))) (bvslt ?x987 (_ bv0 5)))))))))
(assert
 (let ((?x1018 (bvmul (_ bv2 5) x2_minus)))
 (bvsmul_noovfl ?x1018 x2_minus)))
(assert
 (let ((?x904 (bvadd x8_plus x8_minus)))
 (let ((?x930 (bvadd ?x904 x6_plus)))
 (let ((?x956 (bvadd ?x930 x6_minus)))
 (let ((?x986 (bvadd ?x956 x2_plus)))
 (let ((?x1020 (bvadd ?x986 x2_minus)))
 (let ((?x1021 (bvadd ?x1020 x2_minus)))
 (=> (and (bvslt (_ bv0 5) ?x1020) (bvslt (_ bv0 5) x2_minus)) (bvslt (_ bv0 5) ?x1021)))))))))
(assert
 (let ((?x904 (bvadd x8_plus x8_minus)))
 (let ((?x930 (bvadd ?x904 x6_plus)))
 (let ((?x956 (bvadd ?x930 x6_minus)))
 (let ((?x986 (bvadd ?x956 x2_plus)))
 (let ((?x1020 (bvadd ?x986 x2_minus)))
 (let ((?x1021 (bvadd ?x1020 x2_minus)))
 (=> (and (bvslt ?x1020 (_ bv0 5)) (bvslt x2_minus (_ bv0 5))) (bvslt ?x1021 (_ bv0 5))))))))))
(assert
 (bvsge x2_minus (_ bv0 5)))
(check-sat)