(in-package #:string-code.cft.presets)

(define-cft-preset free-boson-10
  (parameter alpha-prime "alpha-prime" :scalar-parameter)
  (surface sphere :sphere :rational)
  (quantum-number spin10 :ade-irrep :group d5)
  (bulk-field X "X" ((mu :vector-index)) :bosonic
         :quantum-numbers ((spin10 vector)))
  (chiral-field dX "dX" ((mu :vector-index)) :bosonic
         :quantum-numbers ((spin10 vector)))
  (chiral-field dXt "dXt" ((mu :vector-index)) :bosonic
         :quantum-numbers ((spin10 vector)))
  (bulk-field expX "expX" ((k :momentum)) :bosonic
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

(wick (dX mu z) (dX nu w)
  (* -1/2 alpha-prime
     (metric mu nu)
     (pow (- z w) -2)))
(wick (dXt mu zbar) (dXt nu wbar)
  (* -1/2 alpha-prime
     (metric mu nu)
     (pow (- zbar wbar) -2)))

(wick (X X)
  (term :scalars ((* -1/2 alpha-prime))
        :coordinates ((:logarithm (:left :holomorphic) (:right :holomorphic)))
        :tensors ((:metric (:left mu) (:right mu))))
  (term :scalars ((* -1/2 alpha-prime))
        :coordinates ((:logarithm (:left :antiholomorphic) (:right :antiholomorphic)))
        :tensors ((:metric (:left mu) (:right mu)))))
(wick (dX mu z) (X nu w wb)
  (* -1/2 alpha-prime
     (metric mu nu)
     (log (- z w))))
(wick (dXt mu zbar) (X nu w wb)
  (* -1/2 alpha-prime
     (metric mu nu)
     (log (- zbar wb))))

(wick (dX mu z) (expX k w wb)
  (* -1/2 i alpha-prime
     (momentum-index k mu)
     (/ 1 (- z w)))
  :residuals (:right))
(wick (dXt mu zbar) (expX k w wb)
  (* -1/2 i alpha-prime
     (momentum-index k mu)
     (/ 1 (- zbar wb)))
  :residuals (:right))

(wick (expX p z zb) (expX k w wb)
  (* 1/2 alpha-prime
     (momentum-pair p k)
     (green-exp z w)
     (green-exp zb wb))
  :residuals (:left :right))

(zero-mode :boson-momentum-conservation (expX) :two-pi-power 10))
