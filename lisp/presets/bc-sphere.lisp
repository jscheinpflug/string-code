(in-package #:string-code.cft.presets)

(define-cft-preset bc-sphere
  (surface sphere :sphere :rational)
  (quantum-number ghost-number :u1)
  (field b "b" :single nil :fermionic
         :quantum-numbers ((ghost-number -1)))
  (field c "c" :single nil :fermionic
         :zero-mode t
         :quantum-numbers ((ghost-number 1)))
  (wick sphere (b z) (c w)
    (/ 1 (- z w)))
  (zero-mode sphere :top-form-fermion (c)))
