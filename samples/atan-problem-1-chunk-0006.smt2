(set-info :smt-lib-version 2.6)
(set-logic QF_NRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The meti-tarski benchmarks are proof obligations extracted from the
Meti-Tarski project, see:

  B. Akbarpour and L. C. Paulson. MetiTarski: An automatic theorem prover
  for real-valued special functions. Journal of Automated Reasoning,
  44(3):175-205, 2010.

Submitted by Dejan Jovanovic for SMT-LIB.


|)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun skoS3 () Real)
(declare-fun skoSX () Real)
(declare-fun skoX () Real)
(assert (and (= (* (+ 7.1 (/ skoS3 (- 12.9 (- skoX))) skoS3) -3.5654) 9.1) (and (not (<= skoX 0)) (and (not (<= skoSX 0)) (not (<= skoS3 0))))))
(assert (= skoS3 skoS3))
(check-sat)
(exit)
