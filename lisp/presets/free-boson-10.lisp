(in-package #:string-code.cft.presets)

(define-cft-preset free-boson-10
  (parameter alpha-prime "alpha-prime" :scalar-parameter)
  (surface sphere :sphere :rational)
  (quantum-number spin10 :ade-irrep :group d5)
  (field dX "dX" :single ((mu :vector-index)) :bosonic
         :quantum-numbers ((spin10 vector)))
  (field expX "expX" :pair ((k :momentum)) :bosonic
         :zero-mode t
         :weight (* (rational 1 4)
                    (* (parameter alpha-prime)
                       (dot (field-label expX k)
                            (field-label expX k)
                            eta)))
         :anti-weight (* (rational 1 4)
                         (* (parameter alpha-prime)
                            (dot (field-label expX k)
                                 (field-label expX k)
                                 eta))))
  (wick sphere (dX mu z) (dX nu w)
    (* -1/2 alpha-prime
       (metric mu nu)
       (pow (- z w) -2)))
  (wick sphere (dX mu z) (expX k w wb)
    (* -1/2 i alpha-prime
       (momentum-index k mu)
       (/ 1 (- z w)))
    :residuals (:right))
  (wick sphere (expX p z zb) (expX k w wb)
    (* 1/2 alpha-prime
       (momentum-pair p k)
       (green-exp z w)
       (green-exp zb wb))
    :residuals (:left :right))
  (zero-mode sphere :boson-momentum-conservation (expX) :two-pi-power 10))
