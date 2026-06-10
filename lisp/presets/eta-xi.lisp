(in-package #:string-code.cft.presets)

(define-cft-preset eta-xi-sphere
  (surface sphere :sphere :rational)
  (quantum-number eta-xi-number (:u1))
  (chiral-field eta :fermionic
         :quantum-numbers ((eta-xi-number 1)))
  (chiral-field xi :fermionic
         :zero-mode t
         :quantum-numbers ((eta-xi-number -1)))
  (wick (eta z) (xi w)
    (/ 1 (- z w)))
  (zero-mode :constant-fermion (xi)))

(define-cft-preset eta-xi-torus
  (parameter tau "tau" :modular-parameter)
  (surface torus :torus :elliptic :modular-parameter tau)
  (quantum-number eta-xi-number (:u1))
  (chiral-field eta :fermionic
         :quantum-numbers ((eta-xi-number 1)))
  (chiral-field xi :fermionic
         :zero-mode t
         :quantum-numbers ((eta-xi-number -1)))
  (wick (eta z) (xi w)
    (prime-log-d z w))
  (zero-mode :constant-fermion (xi)))
