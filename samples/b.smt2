; 
(set-info :status unknown)
(declare-fun n0 () (_ BitVec 3))
(declare-fun n1 () (_ BitVec 3))
(declare-fun n2 () (_ BitVec 3))
(declare-fun n3 () (_ BitVec 3))
(declare-fun n4 () (_ BitVec 3))
(declare-fun n5 () (_ BitVec 3))
(declare-fun n6 () (_ BitVec 3))
(declare-fun n7 () (_ BitVec 3))
(declare-fun n8 () (_ BitVec 3))
(declare-fun n9 () (_ BitVec 3))
(declare-fun n10 () (_ BitVec 3))
(declare-fun n11 () (_ BitVec 3))
(declare-fun n12 () (_ BitVec 3))
(declare-fun n13 () (_ BitVec 3))
(declare-fun n14 () (_ BitVec 3))
(declare-fun n15 () (_ BitVec 3))
(declare-fun n16 () (_ BitVec 3))
(declare-fun n17 () (_ BitVec 3))
(declare-fun n18 () (_ BitVec 3))
(declare-fun n19 () (_ BitVec 3))
(declare-fun n20 () (_ BitVec 3))
(declare-fun n21 () (_ BitVec 3))
(declare-fun n22 () (_ BitVec 3))
(declare-fun n23 () (_ BitVec 3))
(declare-fun n24 () (_ BitVec 3))
(declare-fun n25 () (_ BitVec 3))
(declare-fun n26 () (_ BitVec 3))
(declare-fun n27 () (_ BitVec 3))
(declare-fun n28 () (_ BitVec 3))
(declare-fun n29 () (_ BitVec 3))
(declare-fun n30 () (_ BitVec 3))
(declare-fun n31 () (_ BitVec 3))
(declare-fun n32 () (_ BitVec 3))
(declare-fun n33 () (_ BitVec 3))
(declare-fun n34 () (_ BitVec 3))
(declare-fun n35 () (_ BitVec 3))
(declare-fun n36 () (_ BitVec 3))
(declare-fun n37 () (_ BitVec 3))
(declare-fun n38 () (_ BitVec 3))
(declare-fun n39 () (_ BitVec 3))
(declare-fun n40 () (_ BitVec 3))
(declare-fun n41 () (_ BitVec 3))
(declare-fun n42 () (_ BitVec 3))
(declare-fun n43 () (_ BitVec 3))
(declare-fun n44 () (_ BitVec 3))
(declare-fun n45 () (_ BitVec 3))
(declare-fun n46 () (_ BitVec 3))
(declare-fun n47 () (_ BitVec 3))
(declare-fun n48 () (_ BitVec 3))
(declare-fun n49 () (_ BitVec 3))
(declare-fun n50 () (_ BitVec 3))
(declare-fun n51 () (_ BitVec 3))
(declare-fun n52 () (_ BitVec 3))
(declare-fun n53 () (_ BitVec 3))
(declare-fun n54 () (_ BitVec 3))
(declare-fun n55 () (_ BitVec 3))
(declare-fun n56 () (_ BitVec 3))
(declare-fun n57 () (_ BitVec 3))
(declare-fun n58 () (_ BitVec 3))
(declare-fun n59 () (_ BitVec 3))
(declare-fun n60 () (_ BitVec 3))
(declare-fun n61 () (_ BitVec 3))
(declare-fun n62 () (_ BitVec 3))
(assert
 (not (= (_ bv0 3) (bvshl (_ bv1 3) (_ bv2 3)))))
(assert
 (bvsge n0 (_ bv0 3)))
(assert
 (not (= (_ bv0 3) (bvshl (_ bv1 3) (_ bv2 3)))))
(assert
 (bvsge n1 (_ bv0 3)))
(assert
 (not (= (_ bv0 3) (bvshl (_ bv1 3) (_ bv2 3)))))
(assert
 (bvsge n2 (_ bv0 3)))
(assert
 (not (= (_ bv0 3) (bvshl (_ bv1 3) (_ bv2 3)))))
(assert
 (bvsge n3 (_ bv0 3)))
(assert
 (not (= (_ bv0 3) (bvshl (_ bv1 3) (_ bv2 3)))))
(assert
 (bvsge n4 (_ bv0 3)))
(assert
 (not (= (_ bv0 3) (bvshl (_ bv1 3) (_ bv2 3)))))
(assert
 (bvsge n5 (_ bv0 3)))
(assert
 (not (= (_ bv0 3) (bvshl (_ bv1 3) (_ bv2 3)))))
(assert
 (bvsge n6 (_ bv0 3)))
(assert
 (not (= (_ bv0 3) (bvshl (_ bv1 3) (_ bv2 3)))))
(assert
 (bvsge n7 (_ bv0 3)))
(assert
 (not (= (_ bv0 3) (bvshl (_ bv1 3) (_ bv2 3)))))
(assert
 (bvsge n8 (_ bv0 3)))
(assert
 (not (= (_ bv0 3) (bvshl (_ bv1 3) (_ bv2 3)))))
(assert
 (bvsge n9 (_ bv0 3)))
(assert
 (not (= (_ bv0 3) (bvshl (_ bv1 3) (_ bv2 3)))))
(assert
 (bvsge n10 (_ bv0 3)))
(assert
 (not (= (_ bv0 3) (bvshl (_ bv1 3) (_ bv2 3)))))
(assert
 (bvsge n11 (_ bv0 3)))
(assert
 (bvsmul_noovfl n7 n6))
(assert
 (= n12 (bvmul n7 n6)))
(assert
 (=> (and (bvslt (_ bv0 3) n6) (bvslt (_ bv0 3) n12)) (bvslt (_ bv0 3) (bvadd n6 n12))))
(assert
 (=> (and (bvslt n6 (_ bv0 3)) (bvslt n12 (_ bv0 3))) (bvslt (bvadd n6 n12) (_ bv0 3))))
(assert
 (let ((?x323 (bvadd n6 n12)))
 (= n13 ?x323)))
(assert
 (bvsmul_noovfl n7 n7))
(assert
 (= n14 (bvmul n7 n7)))
(assert
 (bvsmul_noovfl n9 n6))
(assert
 (= n15 (bvmul n9 n6)))
(assert
 (=> (and (bvslt (_ bv0 3) n8) (bvslt (_ bv0 3) n15)) (bvslt (_ bv0 3) (bvadd n8 n15))))
(assert
 (=> (and (bvslt n8 (_ bv0 3)) (bvslt n15 (_ bv0 3))) (bvslt (bvadd n8 n15) (_ bv0 3))))
(assert
 (let ((?x362 (bvadd n8 n15)))
 (= n16 ?x362)))
(assert
 (bvsmul_noovfl n9 n7))
(assert
 (= n17 (bvmul n9 n7)))
(assert
 (bvsmul_noovfl n9 n10))
(assert
 (= n18 (bvmul n9 n10)))
(assert
 (=> (and (bvslt (_ bv0 3) n8) (bvslt (_ bv0 3) n18)) (bvslt (_ bv0 3) (bvadd n8 n18))))
(assert
 (=> (and (bvslt n8 (_ bv0 3)) (bvslt n18 (_ bv0 3))) (bvslt (bvadd n8 n18) (_ bv0 3))))
(assert
 (let ((?x403 (bvadd n8 n18)))
 (= n19 ?x403)))
(assert
 (bvsmul_noovfl n9 n11))
(assert
 (= n20 (bvmul n9 n11)))
(assert
 (bvsmul_noovfl n5 n8))
(assert
 (= n21 (bvmul n5 n8)))
(assert
 (=> (and (bvslt (_ bv0 3) n4) (bvslt (_ bv0 3) n21)) (bvslt (_ bv0 3) (bvadd n4 n21))))
(assert
 (=> (and (bvslt n4 (_ bv0 3)) (bvslt n21 (_ bv0 3))) (bvslt (bvadd n4 n21) (_ bv0 3))))
(assert
 (let ((?x437 (bvadd n4 n21)))
 (= n22 ?x437)))
(assert
 (bvsmul_noovfl n5 n9))
(assert
 (= n23 (bvmul n5 n9)))
(assert
 (bvsmul_noovfl n3 n13))
(assert
 (= n24 (bvmul n3 n13)))
(assert
 (=> (and (bvslt (_ bv0 3) n2) (bvslt (_ bv0 3) n24)) (bvslt (_ bv0 3) (bvadd n2 n24))))
(assert
 (=> (and (bvslt n2 (_ bv0 3)) (bvslt n24 (_ bv0 3))) (bvslt (bvadd n2 n24) (_ bv0 3))))
(assert
 (let ((?x476 (bvadd n2 n24)))
 (= n25 ?x476)))
(assert
 (bvsmul_noovfl n3 n14))
(assert
 (= n26 (bvmul n3 n14)))
(assert
 (bvsmul_noovfl n1 n19))
(assert
 (= n27 (bvmul n1 n19)))
(assert
 (=> (and (bvslt (_ bv0 3) n0) (bvslt (_ bv0 3) n27)) (bvslt (_ bv0 3) (bvadd n0 n27))))
(assert
 (=> (and (bvslt n0 (_ bv0 3)) (bvslt n27 (_ bv0 3))) (bvslt (bvadd n0 n27) (_ bv0 3))))
(assert
 (let ((?x513 (bvadd n0 n27)))
 (= n28 ?x513)))
(assert
 (bvsmul_noovfl n1 n20))
(assert
 (let ((?x543 (bvmul n1 n20)))
 (= n29 ?x543)))
(assert
 (bvsge n25 n28))
(assert
 (bvsge n26 n29))
(assert
 (bvsmul_noovfl n5 n6))
(assert
 (= n30 (bvmul n5 n6)))
(assert
 (=> (and (bvslt (_ bv0 3) n4) (bvslt (_ bv0 3) n30)) (bvslt (_ bv0 3) (bvadd n4 n30))))
(assert
 (=> (and (bvslt n4 (_ bv0 3)) (bvslt n30 (_ bv0 3))) (bvslt (bvadd n4 n30) (_ bv0 3))))
(assert
 (let ((?x552 (bvadd n4 n30)))
 (= n31 ?x552)))
(assert
 (bvsmul_noovfl n5 n7))
(assert
 (let ((?x579 (bvmul n5 n7)))
 (= n32 ?x579)))
(assert
 (bvsmul_noovfl n1 n10))
(assert
 (= n33 (bvmul n1 n10)))
(assert
 (=> (and (bvslt (_ bv0 3) n0) (bvslt (_ bv0 3) n33)) (bvslt (_ bv0 3) (bvadd n0 n33))))
(assert
 (=> (and (bvslt n0 (_ bv0 3)) (bvslt n33 (_ bv0 3))) (bvslt (bvadd n0 n33) (_ bv0 3))))
(assert
 (let ((?x584 (bvadd n0 n33)))
 (= n34 ?x584)))
(assert
 (bvsmul_noovfl n1 n11))
(assert
 (let ((?x609 (bvmul n1 n11)))
 (= n35 ?x609)))
(assert
 (bvsge n31 n34))
(assert
 (bvsge n32 n35))
(assert
 (bvsmul_noovfl n3 n6))
(assert
 (= n36 (bvmul n3 n6)))
(assert
 (=> (and (bvslt (_ bv0 3) n2) (bvslt (_ bv0 3) n36)) (bvslt (_ bv0 3) (bvadd n2 n36))))
(assert
 (=> (and (bvslt n2 (_ bv0 3)) (bvslt n36 (_ bv0 3))) (bvslt (bvadd n2 n36) (_ bv0 3))))
(assert
 (let ((?x618 (bvadd n2 n36)))
 (= n37 ?x618)))
(assert
 (bvsmul_noovfl n3 n7))
(assert
 (let ((?x643 (bvmul n3 n7)))
 (= n38 ?x643)))
(assert
 (bvsge n22 n37))
(assert
 (bvsge n23 n38))
(assert
 (bvsge n22 n0))
(assert
 (bvsge n23 n1))
(assert
 (bvsmul_noovfl n1 n6))
(assert
 (= n39 (bvmul n1 n6)))
(assert
 (=> (and (bvslt (_ bv0 3) n0) (bvslt (_ bv0 3) n39)) (bvslt (_ bv0 3) (bvadd n0 n39))))
(assert
 (=> (and (bvslt n0 (_ bv0 3)) (bvslt n39 (_ bv0 3))) (bvslt (bvadd n0 n39) (_ bv0 3))))
(assert
 (let ((?x656 (bvadd n0 n39)))
 (= n40 ?x656)))
(assert
 (bvsmul_noovfl n1 n7))
(assert
 (let ((?x681 (bvmul n1 n7)))
 (= n41 ?x681)))
(assert
 (bvsmul_noovfl n1 n16))
(assert
 (= n42 (bvmul n1 n16)))
(assert
 (=> (and (bvslt (_ bv0 3) n0) (bvslt (_ bv0 3) n42)) (bvslt (_ bv0 3) (bvadd n0 n42))))
(assert
 (=> (and (bvslt n0 (_ bv0 3)) (bvslt n42 (_ bv0 3))) (bvslt (bvadd n0 n42) (_ bv0 3))))
(assert
 (let ((?x686 (bvadd n0 n42)))
 (= n43 ?x686)))
(assert
 (bvsmul_noovfl n1 n17))
(assert
 (let ((?x711 (bvmul n1 n17)))
 (= n44 ?x711)))
(assert
 (bvsge n40 n43))
(assert
 (bvsge n41 n44))
(assert
 (bvsmul_noovfl n9 n13))
(assert
 (= n45 (bvmul n9 n13)))
(assert
 (=> (and (bvslt (_ bv0 3) n8) (bvslt (_ bv0 3) n45)) (bvslt (_ bv0 3) (bvadd n8 n45))))
(assert
 (=> (and (bvslt n8 (_ bv0 3)) (bvslt n45 (_ bv0 3))) (bvslt (bvadd n8 n45) (_ bv0 3))))
(assert
 (let ((?x722 (bvadd n8 n45)))
 (= n46 ?x722)))
(assert
 (bvsmul_noovfl n9 n14))
(assert
 (= n47 (bvmul n9 n14)))
(assert
 (bvsmul_noovfl n7 n19))
(assert
 (= n48 (bvmul n7 n19)))
(assert
 (=> (and (bvslt (_ bv0 3) n6) (bvslt (_ bv0 3) n48)) (bvslt (_ bv0 3) (bvadd n6 n48))))
(assert
 (=> (and (bvslt n6 (_ bv0 3)) (bvslt n48 (_ bv0 3))) (bvslt (bvadd n6 n48) (_ bv0 3))))
(assert
 (let ((?x758 (bvadd n6 n48)))
 (= n49 ?x758)))
(assert
 (bvsmul_noovfl n7 n20))
(assert
 (= n50 (bvmul n7 n20)))
(assert
 (bvsge n46 n49))
(assert
 (bvsge n47 n50))
(assert
 (bvsmul_noovfl n11 n6))
(assert
 (= n51 (bvmul n11 n6)))
(assert
 (=> (and (bvslt (_ bv0 3) n10) (bvslt (_ bv0 3) n51)) (bvslt (_ bv0 3) (bvadd n10 n51))))
(assert
 (=> (and (bvslt n10 (_ bv0 3)) (bvslt n51 (_ bv0 3))) (bvslt (bvadd n10 n51) (_ bv0 3))))
(assert
 (let ((?x796 (bvadd n10 n51)))
 (= n52 ?x796)))
(assert
 (bvsmul_noovfl n11 n7))
(assert
 (let ((?x826 (bvmul n11 n7)))
 (= n53 ?x826)))
(assert
 (bvsmul_noovfl n7 n10))
(assert
 (= n54 (bvmul n7 n10)))
(assert
 (=> (and (bvslt (_ bv0 3) n6) (bvslt (_ bv0 3) n54)) (bvslt (_ bv0 3) (bvadd n6 n54))))
(assert
 (=> (and (bvslt n6 (_ bv0 3)) (bvslt n54 (_ bv0 3))) (bvslt (bvadd n6 n54) (_ bv0 3))))
(assert
 (let ((?x833 (bvadd n6 n54)))
 (= n55 ?x833)))
(assert
 (bvsmul_noovfl n7 n11))
(assert
 (= n56 (bvmul n7 n11)))
(assert
 (bvsge n52 n55))
(assert
 (bvsge n53 n56))
(assert
 (bvsmul_noovfl n11 n8))
(assert
 (= n57 (bvmul n11 n8)))
(assert
 (=> (and (bvslt (_ bv0 3) n10) (bvslt (_ bv0 3) n57)) (bvslt (_ bv0 3) (bvadd n10 n57))))
(assert
 (=> (and (bvslt n10 (_ bv0 3)) (bvslt n57 (_ bv0 3))) (bvslt (bvadd n10 n57) (_ bv0 3))))
(assert
 (let ((?x870 (bvadd n10 n57)))
 (= n58 ?x870)))
(assert
 (bvsmul_noovfl n11 n9))
(assert
 (let ((?x432 (bvmul n11 n9)))
 (= n59 ?x432)))
(assert
 (bvsge n58 n16))
(assert
 (bvsge n59 n17))
(assert
 (bvsmul_noovfl n7 n16))
(assert
 (= n60 (bvmul n7 n16)))
(assert
 (=> (and (bvslt (_ bv0 3) n6) (bvslt (_ bv0 3) n60)) (bvslt (_ bv0 3) (bvadd n6 n60))))
(assert
 (=> (and (bvslt n6 (_ bv0 3)) (bvslt n60 (_ bv0 3))) (bvslt (bvadd n6 n60) (_ bv0 3))))
(assert
 (let ((?x905 (bvadd n6 n60)))
 (= n61 ?x905)))
(assert
 (bvsmul_noovfl n7 n17))
(assert
 (= n62 (bvmul n7 n17)))
(assert
 (bvsge n13 n61))
(assert
 (bvsge n14 n62))
(assert
 (let (($x944 (or (or (or (bvsgt n25 n28) (bvsgt n31 n34)) (bvsgt n22 n37)) (bvsgt n22 n0))))
 (or $x944 (bvsgt n40 n43))))
(check-sat)
