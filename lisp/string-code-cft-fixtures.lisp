(defpackage #:string-code.cft.fixtures
  (:use #:cl #:string-code.cft.descriptor)
  (:export
   #:free-fermion-10
   #:free-fermion-10-full
   #:eta-xi-sphere
   #:eta-xi-sphere-full
   #:eta-xi-torus
   #:eta-xi-torus-full
   #:bc-sphere
   #:bc-sphere-full
   #:free-boson-10
   #:make-free-fermion-runtime
   #:make-free-fermion-full-runtime
   #:psi
   #:psit
   #:make-eta-xi-sphere-runtime
   #:make-eta-xi-sphere-full-runtime
   #:make-eta-xi-torus-runtime
   #:make-eta-xi-torus-full-runtime
   #:eta
   #:xi
   #:etat
   #:xit
   #:make-bc-runtime
   #:make-bc-full-runtime
   #:b-field
   #:c-field
   #:bt
   #:ct
   #:b
   #:c
   #:basis-count
   #:basis
   #:make-product-runtime
   #:make-free-boson-runtime
   #:X
   #:dX
   #:dXt
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

(defun make-preset-runtime (name library &key constants basis-metadata)
  (make-runtime-context
   :library library
   :theory-id (string-code.cft.presets:preset-theory-id-for name)
   :basis-metadata basis-metadata
   :constants constants))

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defun fixture-symbol (symbol)
    (intern (symbol-name symbol) (find-package '#:string-code.cft.fixtures)))

  (defun field-interface-name= (name field)
    (string-equal (symbol-name name)
                  (symbol-name
                   (string-code.cft.presets::preset-field-interface-name field))))

  (defun fixture-field-interface (preset field-name)
    (or (find field-name
              (string-code.cft.presets:preset-field-interfaces preset)
              :test #'field-interface-name=)
        (error "Preset ~S has no generated field ~S." preset field-name)))

  (defun field-label-variables (field)
    (mapcar (lambda (label)
              (fixture-symbol (getf label :name)))
            (string-code.cft.presets::preset-field-interface-labels field)))

  (defun field-coordinate-variables (field)
    (ecase (string-code.cft.presets::preset-field-interface-insertion field)
      (:single (list (fixture-symbol 'z)))
      (:pair (list (fixture-symbol 'z)
                   (fixture-symbol 'z-bar)))))

  (defun runtime-symbol-list-form (context variables)
    `(list ,@(mapcar (lambda (variable)
                       `(runtime-symbol-id ,context ,variable))
                     variables)))

  (defun generated-field-inserter-form (preset alias)
    (destructuring-bind (function-name field-name) alias
      (let* ((field (fixture-field-interface preset field-name))
             (public-name (fixture-symbol function-name))
             (context (fixture-symbol 'context))
             (labels (field-label-variables field))
             (coordinates (field-coordinate-variables field)))
        `(defun ,public-name (,context ,@labels ,@coordinates)
           ,(format nil "~A inserts generated field ~A from preset ~A."
                    function-name field-name preset)
           (insert-runtime-field
            ,context
            ,(string-code.cft.presets::preset-field-interface-id field)
            ,(runtime-symbol-list-form context coordinates)
            ,(if labels
                 (runtime-symbol-list-form context labels)
                 nil))))))

  (defun descriptor-field-aliases (preset)
    (mapcar (lambda (field)
              (let ((name (string-code.cft.presets::preset-field-interface-name field)))
                (list (fixture-symbol name) name)))
            (string-code.cft.presets:preset-field-interfaces preset)))

  (defun normalize-field-aliases (preset fields field-aliases)
    (append (if (eq fields :all)
                (descriptor-field-aliases preset)
                fields)
            field-aliases))

  (defun generated-fixture-export-symbols (preset maker fields)
    (cons (fixture-symbol maker)
          (cons (fixture-symbol preset)
                (mapcar (lambda (field)
                          (fixture-symbol (first field)))
                        fields)))))

(defmacro define-preset-fixture
    (preset maker &key (fields :all) field-aliases constructor-options constants)
  "Generate descriptor, runtime, and field inserter functions for PRESET."
  (let* ((field-forms (normalize-field-aliases preset fields field-aliases))
         (exports (generated-fixture-export-symbols preset maker field-forms)))
    `(progn
       (eval-when (:compile-toplevel :load-toplevel :execute)
         (export ',exports))
       (defun ,preset ()
         ,(format nil "~A returns a fresh generated descriptor." preset)
         (string-code.cft.presets:preset-theory ',preset))
       (defun ,maker (&key library ,@constructor-options)
         ,(format nil "~A creates a generated runtime context." maker)
         (make-preset-runtime ',preset library
                              :basis-metadata (string-code.cft.presets:preset-basis-metadata-for ',preset)
                              :constants ,constants))
       ,@(mapcar (lambda (field)
                   (generated-field-inserter-form preset field))
                 field-forms))))

(defun free-boson-constants (alpha-prime constants)
  (acons :alpha-prime alpha-prime constants))

(define-preset-fixture free-fermion-10 make-free-fermion-runtime)

(define-preset-fixture free-fermion-10-full make-free-fermion-full-runtime
  :fields nil
  :field-aliases ((psit psit)))

(define-preset-fixture eta-xi-sphere make-eta-xi-sphere-runtime)

(define-preset-fixture eta-xi-sphere-full make-eta-xi-sphere-full-runtime
  :fields nil
  :field-aliases ((etat etat)
                  (xit xit)))

(define-preset-fixture eta-xi-torus make-eta-xi-torus-runtime
  :fields nil)

(define-preset-fixture eta-xi-torus-full make-eta-xi-torus-full-runtime
  :fields nil)

(define-preset-fixture bc-sphere make-bc-runtime
  :field-aliases ((b-field b)
                  (c-field c)))

(define-preset-fixture bc-sphere-full make-bc-full-runtime
  :fields nil
  :field-aliases ((bt bt)
                  (ct ct)))

(define-preset-fixture free-boson-10 make-free-boson-runtime
  :constructor-options ((alpha-prime :alpha-prime) constants)
  :constants (free-boson-constants alpha-prime constants))
