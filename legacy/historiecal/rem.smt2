(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :source |Christoph M. Wintersteiger (cwinter@microsoft.com). Randomly generated floating-point testcases.|)
; Rounding mode: to positive
; Precision: double (11/53)
; X = -1.3660645236807684721469513533520512282848358154296875p-125 {- 1648608052442267 -125 (-3.2116e-038)}
; Y = -1.9066224169163008550498261683969758450984954833984375p-869 {- 4083064378989991 -869 (-4.84394e-262)}
; -1.3660645236807684721469513533520512282848358154296875p-125 % -1.9066224169163008550498261683969758450984954833984375p-869 == -1.385143260536116915915272329584695398807525634765625p-869
; [HW: -1.385143260536116915915272329584695398807525634765625p-869] 

; mpf : - 1734531044634714 -869
; mpfd: - 1734531044634714 -869 (-3.51907e-262) class: Neg. norm. non-zero
; hwf : - 1734531044634714 -869 (-3.51907e-262) class: Neg. norm. non-zero

(set-logic QF_FP)
;(set-info :status unsat)
(define-sort FPN () (_ FloatingPoint 11 53))
(declare-fun x () FPN)
(declare-fun y () FPN)
(declare-fun r () FPN)
(assert (= x (fp.add RNA x y)))
(check-sat)
(exit)
