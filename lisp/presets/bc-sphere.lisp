(in-package #:string-code.cft.presets)

(define-cft-preset bc-sphere
  (surface sphere :sphere :rational)
  (quantum-number ghost-number :u1)
  (chiral-field b :fermionic
         :quantum-numbers ((ghost-number -1)))
  (chiral-field c :fermionic
         :zero-mode t
         :quantum-numbers ((ghost-number 1)))
  (wick (b z) (c w)
    (/ 1 (- z w)))
  (zero-mode :top-form-fermion (c)))
