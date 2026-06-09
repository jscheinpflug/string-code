(defsystem "string-code-cft"
  :description "Lisp CFT presets, descriptor emission, and generated C ABI runtime helpers."
  :serial t
  :depends-on ("uiop")
  :components ((:file "string-code-cft-descriptor")
               (:file "string-code-cft-presets")
               (:module "presets"
                :serial t
                :components
                ((:file "free-fermion-10")
                 (:file "eta-xi")
                 (:file "bc-sphere")
                 (:file "free-boson-10")))
               (:file "string-code-cft-fixtures")))
