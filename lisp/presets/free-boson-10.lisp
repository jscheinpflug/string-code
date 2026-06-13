(in-package #:string-code.cft.presets)

(define-cft-preset free-boson-10
  (:theory-id 5
   :kind-namespace free_boson
   :basis (:presentation free-boson-10
           :backend (:free-boson :dimension 10)
           :tick-denominator 1
           :quantum-numbers ((spin10))
           :seed-bits nil))
  (parameter alpha-prime "alpha-prime" :scalar-parameter)
  (surface sphere :sphere :rational)
  (quantum-number spin10 (:ade-irrep) :group d5)
  (bulk-field X "X" ((mu :vector-index)) :bosonic
         :kind x
         :quantum-numbers ((spin10 vector)))
  (chiral-field dX "dX" ((mu :vector-index)) :bosonic
         :kind d_x
         :weight (rational 1 1)
         :infinity primary
         :quantum-numbers ((spin10 vector)))
  (anti-chiral-field dXt "dXt" ((mu :vector-index)) :bosonic
         :kind d_xt
         :anti-weight (rational 1 1)
         :infinity primary
         :quantum-numbers ((spin10 vector)))
  (bulk-field expX "expX" ((k :momentum)) :bosonic
         :kind exp_x
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
                                 eta)))
         :infinity (branch-global-exponential :momentum k))
  (bulk-field profile "profile" ((f :profile)) :bosonic
         :kind profile_x
         :zero-mode t)

(wick (dX mu z) (dX nu w)
  (* -1/2 alpha-prime
     (metric mu nu)
     (pow (- z w) -2)))
(wick (dXt mu zbar) (dXt nu wbar)
  (* -1/2 alpha-prime
     (metric mu nu)
     (pow (- zbar wbar) -2)))

(wick (X mu z zb) (X nu w wb)
  (+ (* -1/2 alpha-prime
        (metric mu nu)
        (log (- z w)))
     (* -1/2 alpha-prime
        (metric mu nu)
        (log (- zb wb)))))
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
(wick (dX mu z) (profile f w wb)
  (* -1/2 alpha-prime
     (/ 1 (- z w))
     (profile-derivative f mu))
  :residuals (:right))
(wick (dXt mu zbar) (profile f w wb)
  (* -1/2 alpha-prime
     (/ 1 (- zbar wb))
     (profile-derivative f mu))
  :residuals (:right))

(wick (expX p z zb) (expX k w wb)
  (* 1/2 alpha-prime
     (momentum-pair p k)
     (green-exp z w)
     (green-exp zb wb))
  :residuals (:left :right))

(zero-mode (linear-conservation :fields (expX profile) :normalization (pow (* 2 pi) 10))))
