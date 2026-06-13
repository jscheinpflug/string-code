(in-package #:string-code.cft.presets)

(define-cft-preset bc-sphere
  (:theory-id 4
   :kind-namespace bc
   :basis (:presentation bc
           :backend (:bc)
           :tick-denominator 1
           :quantum-numbers ((ghost-number))
           :seed-bits ((0 :weight -1)
                       (1 :weight 0))))
  (surface sphere :sphere :rational)
  (quantum-number ghost-number (:u1))
  (chiral-field b :fermionic
         :weight (rational 2 1)
         :infinity primary
         :quantum-numbers ((ghost-number -1)))
  (chiral-field c :fermionic
         :zero-mode t
         :weight (rational -1 1)
         :infinity primary
         :quantum-numbers ((ghost-number 1)))
  (wick (b z) (c w)
    (/ 1 (- z w)))
  (zero-mode (grassmann-top-form :field c)))
