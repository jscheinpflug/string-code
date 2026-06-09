(defpackage #:string-code.cft.fixtures
  (:use #:cl #:string-code.cft.descriptor)
  (:export
   #:free-fermion-10
   #:eta-xi-sphere
   #:eta-xi-torus
   #:bc-sphere
   #:free-boson-10
   #:make-free-fermion-runtime
   #:psi
   #:make-eta-xi-sphere-runtime
   #:make-eta-xi-torus-runtime
   #:eta
   #:xi
   #:make-bc-runtime
   #:b-field
   #:c-field
   #:make-free-boson-runtime
   #:dX
   #:expX
   #:with-correlator-context
   #:correlator
   #:corr
   #:ops
   #:R))

(in-package #:string-code.cft.fixtures)

(defun runtime-symbol-id (context value)
  (etypecase value
    (integer value)
    (string (intern-runtime-symbol context value))
    (symbol (intern-runtime-symbol context (string-downcase (string value))))))

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defun fixture-call-symbol (name)
    (if (symbolp name)
        (multiple-value-bind (symbol status)
            (find-symbol (symbol-name name) "STRING-CODE.CFT.FIXTURES")
          (if status symbol name))
        name))

  (defun literal-symbol-form (value)
    (if (symbolp value) `',value value))

  (defun fixture-form-name (form)
    (and (consp form) (symbolp (first form)) (first form)))

  (defun field-form-p (form)
    (and (consp form)
         (not (member (fixture-form-name form) '(ops R)
                      :test #'string-equal))))

  (defun field-call-form (context form)
    (unless (consp form)
      (error "Correlator field form must be a list, got ~S." form))
    `(,(fixture-call-symbol (first form)) ,context
      ,@(mapcar #'literal-symbol-form (rest form))))

  (declaim (ftype function correlator-body-forms correlator-form-forms))

  (defun insertion-count (form)
    (cond
      ((field-form-p form) 1)
      ((and (consp form) (string-equal (fixture-form-name form) 'ops))
       (loop for item in (rest form) sum (insertion-count item)))
      ((and (consp form) (string-equal (fixture-form-name form) 'R))
       (loop for item in (rest form) sum (insertion-count item)))
      (t (error "Unknown correlator form ~S." form))))

  (defun correlator-form-forms (context form)
    (cond
      ((field-form-p form) (list (field-call-form context form)))
      ((and (consp form) (string-equal (fixture-form-name form) 'ops))
       (correlator-body-forms context (rest form)))
      ((and (consp form) (string-equal (fixture-form-name form) 'R))
       (append (correlator-body-forms context (rest form))
               `((normal-order-runtime-field ,context ,(insertion-count form)))))
      (t (error "Unknown correlator form ~S." form))))

  (defun correlator-body-forms (context forms)
    (loop for form in forms append (correlator-form-forms context form))))

(defmacro with-correlator-context ((context (maker &rest runtime-args)) &body body)
  "Bind CONTEXT to a generated runtime and release it after BODY."
  `(let ((,context (,(fixture-call-symbol maker) ,@runtime-args)))
     (unwind-protect
          (progn ,@body)
       (destroy-runtime-context ,context))))

(defmacro correlator ((maker &rest runtime-args) &body fields)
  "Evaluate fixture field forms and return the symbolic correlator expression."
  (let ((context (gensym "CONTEXT-"))
        (frozen (gensym "FROZEN-")))
    `(with-correlator-context (,context (,(fixture-call-symbol maker) ,@runtime-args))
       ,@(correlator-body-forms context fields)
       (let ((,frozen (freeze-runtime-operators ,context)))
         (correlator-expression ,context ,frozen)))))

(defmacro corr ((maker &rest runtime-args) &body fields)
  "Alias for CORRELATOR."
  `(correlator (,maker ,@runtime-args) ,@fields))

(defun free-fermion-10 ()
  (string-code.cft.presets:free-fermion-10))

(defun eta-xi-sphere ()
  (string-code.cft.presets:eta-xi-sphere))

(defun eta-xi-torus ()
  (string-code.cft.presets:eta-xi-torus))

(defun bc-sphere ()
  (string-code.cft.presets:bc-sphere))

(defun free-boson-10 ()
  (string-code.cft.presets:free-boson-10))

(defun make-preset-runtime (name library &key constants)
  (make-runtime-context
   :library library
   :theory-id (string-code.cft.presets:preset-theory-id-for name)
   :constants constants))

(defun make-free-fermion-runtime (&key library)
  (make-preset-runtime 'free-fermion-10 library))

(defun psi (context mu z)
  (insert-runtime-field context 0
                        (list (runtime-symbol-id context z))
                        (list (runtime-symbol-id context mu))))

(defun make-eta-xi-sphere-runtime (&key library)
  (make-preset-runtime 'eta-xi-sphere library))

(defun make-eta-xi-torus-runtime (&key library)
  (make-preset-runtime 'eta-xi-torus library))

(defun eta (context z)
  (insert-runtime-field context 0
                        (list (runtime-symbol-id context z))
                        nil))

(defun xi (context z)
  (insert-runtime-field context 1
                        (list (runtime-symbol-id context z))
                        nil))

(defun make-bc-runtime (&key library)
  (make-preset-runtime 'bc-sphere library))

(defun b-field (context z)
  (insert-runtime-field context 0
                        (list (runtime-symbol-id context z))
                        nil))

(defun c-field (context z)
  (insert-runtime-field context 1
                        (list (runtime-symbol-id context z))
                        nil))

(defun free-boson-constants (alpha-prime constants)
  (acons :alpha-prime alpha-prime constants))

(defun make-free-boson-runtime (&key library (alpha-prime :alpha-prime) constants)
  (make-preset-runtime 'free-boson-10 library
                       :constants (free-boson-constants alpha-prime constants)))

(defun dX (context mu z)
  (insert-runtime-field context 0
                        (list (runtime-symbol-id context z))
                        (list (runtime-symbol-id context mu))))

(defun expX (context k z z-bar)
  (insert-runtime-field context 1
                        (list (runtime-symbol-id context z)
                              (runtime-symbol-id context z-bar))
                        (list (runtime-symbol-id context k))))
