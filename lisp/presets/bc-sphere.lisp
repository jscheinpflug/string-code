(in-package #:string-code.cft.presets)

(define-cft-preset bc-sphere
  (:theory-id 4
   :kind-namespace bc
   :basis (:presentation bc
           :backend (:bc)
           :tick-denominator 1
           :quantum-numbers ((ghost-number))
           :seed-bits ((0 :operator c :weight -1)
                       (1 :operator c :weight 0))))
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

(define-cft-preset bc-sphere-full
  (:theory-id 9
   :kind-namespace bc
   :basis (:presentation bc
           :backend (:bc)
           :tick-denominator 1
           :quantum-numbers ((ghost-number))
           :seed-bits ((0 :operator c :weight -1)
                       (1 :operator c :weight 0))))
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
  (anti-chiral-field bt :fermionic
         :weight (rational 2 1)
         :infinity primary
         :quantum-numbers ((ghost-number -1)))
  (anti-chiral-field ct :fermionic
         :zero-mode t
         :weight (rational -1 1)
         :infinity primary
         :quantum-numbers ((ghost-number 1)))
  (wick (b z) (c w)
    (/ 1 (- z w)))
  (wick (bt zbar) (ct wbar)
    (/ 1 (- zbar wbar)))
  (zero-mode (grassmann-top-form :field c))
  (zero-mode (grassmann-top-form :field ct)))
