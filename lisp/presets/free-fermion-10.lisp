(in-package #:string-code.cft.presets)

(define-cft-preset (free-fermion :dimension dimension)
  (:kind-namespace free_fermion
   :basis (:presentation free-fermion
           :backend (:free-fermion :dimension dimension)
           :tick-denominator 2
           :quantum-numbers ((fermion-number)
                             (spin10))
           :seed-bits nil))
  (surface sphere :sphere :rational)
  (quantum-number spin10 (:ade-irrep) :group d5)
  (quantum-number fermion-number (:zn 2))
  (chiral-field psi ((mu :vector-index)) :fermionic
         :weight (rational 1 2)
         :infinity primary
         :quantum-numbers ((spin10 vector)
                           (fermion-number 1)))
  (wick (psi mu z) (psi nu w)
    (* (metric mu nu) (/ 1 (- z w)))))

(instantiate-preset free-fermion
  :dimension 10
  :as free-fermion-10
  :theory-id 1)

(define-cft-preset free-fermion-10-full
  (:theory-id 6
   :kind-namespace free_fermion
   :basis (:presentation free-fermion
           :backend (:free-fermion :dimension 10)
           :tick-denominator 2
           :quantum-numbers ((fermion-number)
                             (spin10))
           :seed-bits nil))
  (surface sphere :sphere :rational)
  (quantum-number spin10 (:ade-irrep) :group d5)
  (quantum-number fermion-number (:zn 2))
  (chiral-field psi ((mu :vector-index)) :fermionic
         :weight (rational 1 2)
         :infinity primary
         :quantum-numbers ((spin10 vector)
                           (fermion-number 1)))
  (anti-chiral-field psit ((mu :vector-index)) :fermionic
         :weight (rational 1 2)
         :infinity primary
         :quantum-numbers ((spin10 vector)
                           (fermion-number 1)))
  (wick (psi mu z) (psi nu w)
    (* (metric mu nu) (/ 1 (- z w))))
  (wick (psit mu zbar) (psit nu wbar)
    (* (metric mu nu) (/ 1 (- zbar wbar)))))
