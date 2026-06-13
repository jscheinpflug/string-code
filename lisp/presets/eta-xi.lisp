(in-package #:string-code.cft.presets)

(define-cft-preset eta-xi-sphere
  (:theory-id 2
   :kind-namespace eta_xi
   :basis (:presentation eta-xi-sphere
           :backend (:eta-xi)
           :tick-denominator 1
           :quantum-numbers ((eta-xi-number))
           :seed-bits ((0 :weight 0))))
  (surface sphere :sphere :rational)
  (quantum-number eta-xi-number (:u1))
  (chiral-field eta :fermionic
         :weight (rational 1 1)
         :infinity primary
         :quantum-numbers ((eta-xi-number 1)))
  (chiral-field xi :fermionic
         :zero-mode t
         :weight (rational 0 1)
         :infinity primary
         :quantum-numbers ((eta-xi-number -1)))
  (wick (eta z) (xi w)
    (/ 1 (- z w)))
  (zero-mode (grassmann-count :field xi)))

(define-cft-preset eta-xi-torus
  (:theory-id 3
   :kind-namespace eta_xi
   :basis (:presentation eta-xi-torus
           :backend (:eta-xi)
           :tick-denominator 1
           :quantum-numbers ((eta-xi-number))
           :seed-bits ((0 :weight 0))))
  (parameter tau "tau" :modular-parameter)
  (surface torus :torus :elliptic :modular-parameter tau)
  (quantum-number eta-xi-number (:u1))
  (chiral-field eta :fermionic
         :weight (rational 1 1)
         :infinity primary
         :quantum-numbers ((eta-xi-number 1)))
  (chiral-field xi :fermionic
         :zero-mode t
         :weight (rational 0 1)
         :infinity primary
         :quantum-numbers ((eta-xi-number -1)))
  (wick (eta z) (xi w)
    (elliptic_prime_form_log_derivative z w))
  (zero-mode (grassmann-count :field xi)))
