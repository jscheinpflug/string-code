(in-package #:string-code.cft.presets)

(define-cft-preset free-fermion-10
  (surface sphere :sphere :rational)
  (quantum-number spin10 :ade-irrep :group d5)
  (field psi "psi" :single ((mu :vector-index)) :fermionic
         :quantum-numbers ((spin10 vector)))
  (wick sphere (psi mu z) (psi nu w)
    (* (metric mu nu) (/ 1 (- z w)))))
