(in-package #:string-code.cft.presets)

(define-cft-preset eta-xi-sphere
  (surface sphere :sphere :rational)
  (quantum-number ghost-number :u1)
  (field eta "eta" :single nil :fermionic
         :quantum-numbers ((ghost-number 1)))
  (field xi "xi" :single nil :fermionic
         :zero-mode t
         :quantum-numbers ((ghost-number -1)))
  (wick sphere (eta z) (xi w)
    (/ 1 (- z w)))
  (zero-mode sphere :constant-fermion (xi)))

(define-cft-preset eta-xi-torus
  (parameter tau "tau" :modular-parameter)
  (surface torus :torus :elliptic :modular-parameter tau)
  (quantum-number ghost-number :u1)
  (field eta "eta" :single nil :fermionic
         :quantum-numbers ((ghost-number 1)))
  (field xi "xi" :single nil :fermionic
         :zero-mode t
         :quantum-numbers ((ghost-number -1)))
  (wick torus (eta z) (xi w)
    (prime-log-d z w))
  (zero-mode torus :constant-fermion (xi)))
