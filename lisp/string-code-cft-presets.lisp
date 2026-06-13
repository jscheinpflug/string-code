(eval-when (:compile-toplevel :load-toplevel :execute)
  (require :asdf))

(defpackage #:string-code.cft.presets
  (:use #:cl #:string-code.cft.descriptor)
  (:export
   #:define-cft-preset
   #:preset-theory
   #:preset-theory-id-for
   #:preset-field-interfaces
   #:preset-basis-metadata-for
   #:write-generated-fixtures
   #:write-generated-sources
   #:compile-preset-library
   #:instantiate-preset
   #:free-fermion-10
   #:eta-xi-sphere
   #:eta-xi-torus
   #:bc-sphere
   #:free-boson-10))

(in-package #:string-code.cft.presets)

(defstruct preset name builder theory-name hash theory-id fields basis-metadata)
(defstruct preset-template name parameters forms options)
(defstruct field-shape id insertion labels)

(defparameter *presets* (make-hash-table))
(defparameter *theory-id-owners* (make-hash-table))
(defparameter *preset-templates* (make-hash-table))

(defun make-preset-field-interface (&key name id insertion labels)
  (list :name name :id id :insertion insertion :labels labels))

(defun preset-field-interface-name (field)
  (getf field :name))

(defun preset-field-interface-id (field)
  (getf field :id))

(defun preset-field-interface-insertion (field)
  (getf field :insertion))

(defun preset-field-interface-labels (field)
  (getf field :labels))

(define-condition preset-diagnostic (error)
  ((preset :initarg :preset :reader preset-diagnostic-preset)
   (context :initarg :context :reader preset-diagnostic-context)
   (form :initarg :form :reader preset-diagnostic-form)
   (cause :initarg :cause :reader preset-diagnostic-cause))
  (:report
   (lambda (condition stream)
     (format stream "In CFT preset ~S while parsing ~A form ~S: ~A"
             (preset-diagnostic-preset condition)
             (preset-diagnostic-context condition)
             (preset-diagnostic-form condition)
             (preset-diagnostic-cause condition)))))

(defun preset-options-form-p (form)
  (and (consp form) (keywordp (first form))))

(defun option-present-p (items key)
  (not (null (member key items))))

(defun check-option-keys (items allowed context)
  (loop for tail on items by #'cddr
        for key = (first tail)
        do (progn
             (unless (and (keywordp key) (rest tail))
               (error "Malformed options in ~S." context))
             (unless (member key allowed)
               (error "Unknown option ~S in ~S." key context)))))

(defun split-name-parts (name)
  (let ((text (string-downcase (string name)))
        (start 0)
        (parts nil))
    (loop for index from 0 below (length text)
          when (char= (aref text index) #\-)
            do (progn
                 (when (< start index)
                   (push (subseq text start index) parts))
                 (setf start (1+ index))))
    (when (< start (length text))
      (push (subseq text start) parts))
    (nreverse parts)))

(defun numeric-name-part-p (part)
  (and (> (length part) 0)
       (loop for char across part always (digit-char-p char))))

(defun surface-name-part-p (part)
  (member part '("sphere" "torus" "disk") :test #'string=))

(defun drop-trailing-numeric-parts (parts)
  (loop while (and parts (numeric-name-part-p (car (last parts))))
        do (setf parts (butlast parts)))
  parts)

(defun drop-trailing-surface-part (parts)
  (if (and parts (surface-name-part-p (car (last parts))))
      (butlast parts)
      parts))

(defun join-name-parts (parts separator)
  (with-output-to-string (stream)
    (loop for part in parts
          for first = t then nil
          do (progn
               (unless first
                 (write-string separator stream))
               (write-string part stream)))))

(defun generated-theory-name (name)
  (join-name-parts (drop-trailing-surface-part (split-name-parts name)) "-"))

(defun preset-name-from-spec (spec)
  (if (consp spec) (first spec) spec))

(defun template-parameter-specs (spec)
  (loop for (key value) on (rest spec) by #'cddr
        collect (list key value)))

(defun reserve-theory-id (name id)
  (unless (and (integerp id) (plusp id))
    (error "Preset ~S has invalid :theory-id ~S." name id))
  (let ((owner (gethash id *theory-id-owners*)))
    (when (and owner (not (eq owner name)))
      (error "Duplicate CFT theory id ~D for presets ~S and ~S."
             id owner name))
    (setf (gethash id *theory-id-owners*) name)
    id))

(defun hash-byte (hash byte)
  (logand #xffffffff (* #x01000193 (logxor hash byte))))

(defun generated-theory-hash (name forms)
  (let ((hash #x811c9dc5)
        (text (with-output-to-string (stream)
                (prin1 name stream)
                (prin1 forms stream))))
    (loop for char across text
          do (setf hash (hash-byte hash (char-code char))))
    hash))

(defun descriptor-quantum-by-name (theory name)
  (let ((target (string-downcase (string name)))
        (symbols (string-code.cft.descriptor::theory-symbols theory)))
    (or (find target (string-code.cft.descriptor::theory-quantum-numbers theory)
              :test #'string=
              :key (lambda (number)
                     (aref symbols
                           (string-code.cft.descriptor::quantum-number-symbol
                            number))))
        (error "Basis metadata references unknown quantum number ~S." name))))

(defun descriptor-field-by-name (theory name)
  (let ((target (string-downcase (string name)))
        (symbols (string-code.cft.descriptor::theory-symbols theory)))
    (or (find target (string-code.cft.descriptor::theory-fields theory)
              :test #'string=
              :key (lambda (field)
                     (aref symbols
                           (string-code.cft.descriptor::field-symbol field))))
        (error "Basis metadata references unknown field ~S." name))))

(defun descriptor-field-by-id (theory id)
  (or (find id (string-code.cft.descriptor::theory-fields theory)
            :key #'string-code.cft.descriptor::field-id)
      (error "Basis metadata references unknown field id ~D." id)))

(defun descriptor-field-name (theory field)
  (intern
   (string-upcase
    (aref (string-code.cft.descriptor::theory-symbols theory)
          (string-code.cft.descriptor::field-symbol field)))
   (find-package '#:string-code.cft.presets)))

(defun unique-zero-mode-consume-field (theory)
  (let ((field-id nil)
        (found nil)
        (ambiguous nil))
    (dolist (rule (string-code.cft.descriptor::theory-zero-modes theory))
      (dolist (id (string-code.cft.descriptor::zero-mode-selector-fields rule))
        (cond
          ((not found)
           (setf field-id id
                 found t))
          ((/= field-id id)
           (setf ambiguous t)))))
    (when (and found (not ambiguous))
      (descriptor-field-by-id theory field-id))))

(defun plist-without-keys (properties keys)
  (loop for (key value) on properties by #'cddr
        unless (member key keys)
          append (list key value)))

(defun basis-quantum-properties-from-descriptor (number)
  (ecase (string-code.cft.descriptor::quantum-number-kind number)
    (:u1-charge
     (list :kind :u1))
    (:zn-phase
     (list :kind :zn
           :modulus (string-code.cft.descriptor::quantum-number-modulus number)))
    ((:ade-irrep :tensor-rep)
     (list :kind :rep))))

(defun compact-basis-quantum-p (number)
  (member (string-code.cft.descriptor::quantum-number-kind number)
          '(:u1-charge :zn-phase)))

(defun normalize-basis-quantum-metadata (theory item slot)
  (let* ((name (first item))
         (properties (plist-without-keys (rest item) '(:kind :modulus)))
         (number (descriptor-quantum-by-name theory name)))
    (unless (option-present-p properties :slot)
      (setf (getf properties :slot)
            (when (compact-basis-quantum-p number) slot)))
    (values
     (cons name
           (append properties
                   (basis-quantum-properties-from-descriptor number)))
     (if (and (compact-basis-quantum-p number)
              (integerp (getf properties :slot))
              (= (getf properties :slot) slot))
         (1+ slot)
         slot))))

(defun normalize-basis-quantum-list (theory items)
  (let ((slot 0)
        (result nil))
    (dolist (item items (nreverse result))
      (multiple-value-bind (normalized next-slot)
          (normalize-basis-quantum-metadata theory item slot)
        (push normalized result)
        (setf slot next-slot)))))

(defun descriptor-quantum-name (theory number)
  (aref (string-code.cft.descriptor::theory-symbols theory)
        (string-code.cft.descriptor::quantum-number-symbol number)))

(defun compact-basis-quantum-names (metadata)
  (loop for item in (getf metadata :quantum-numbers)
        when (integerp (getf (rest item) :slot))
          collect (first item)))

(defun descriptor-field-quantum-value (theory field-id quantum-id)
  (let ((item (find-if
               (lambda (candidate)
                 (and (= (string-code.cft.descriptor::field-quantum-number-field
                          candidate)
                         field-id)
                      (= (string-code.cft.descriptor::field-quantum-number-quantum-number
                          candidate)
                         quantum-id)))
               (string-code.cft.descriptor::theory-field-quantum-numbers theory))))
    (and item
         (string-code.cft.descriptor::field-quantum-number-value item))))

(defun field-compact-quantum-record (theory field number)
  (let ((value (descriptor-field-quantum-value
                theory
                (string-code.cft.descriptor::field-id field)
                (string-code.cft.descriptor::quantum-number-id number))))
    (when value
      (ecase (string-code.cft.descriptor::quantum-number-kind number)
        (:u1-charge
         `(u1 ,(intern (string-upcase (descriptor-quantum-name theory number))
                       (find-package '#:string-code.cft.presets))
              ,value))
        (:zn-phase
         `(zn ,(intern (string-upcase (descriptor-quantum-name theory number))
                       (find-package '#:string-code.cft.presets))
              ,(string-code.cft.descriptor::quantum-number-modulus number)
              ,value))
        ((:ade-irrep :tensor-rep) nil)))))

(defun seed-bit-quantum-records (theory metadata operator)
  (let ((field (descriptor-field-by-name theory operator))
        (compact-names (compact-basis-quantum-names metadata)))
    (loop for name in compact-names
          for number = (descriptor-quantum-by-name theory name)
          for record = (field-compact-quantum-record theory field number)
          when record
            collect record)))

(defun seed-bit-operator (theory properties item)
  (if (option-present-p properties :operator)
      (getf properties :operator)
      (let ((field (unique-zero-mode-consume-field theory)))
        (unless field
          (error "Seed bit ~S must declare :operator because the descriptor does not have one unique zero-mode field."
                 item))
        (descriptor-field-name theory field))))

(defun normalize-seed-bit-metadata (theory metadata item)
  (let* ((bit (first item))
         (properties (plist-without-keys (rest item) '(:quantum-number)))
         (operator (seed-bit-operator theory properties item))
         (quantum (seed-bit-quantum-records theory metadata operator)))
    (unless (option-present-p properties :operator)
      (setf (getf properties :operator) operator))
    (cons bit
          (append properties
                  (when quantum
                    (list :quantum-number quantum))))))

(defun normalize-basis-metadata (theory metadata)
  (when metadata
    (let ((normalized (copy-list metadata)))
      (setf (getf normalized :quantum-numbers)
            (normalize-basis-quantum-list
             theory (getf metadata :quantum-numbers)))
      (setf (getf normalized :seed-bits)
            (mapcar (lambda (item)
                      (normalize-seed-bit-metadata theory normalized item))
                    (getf metadata :seed-bits)))
      normalized)))

(defun apply-preset-options-to-theory (theory options)
  (when (getf options :kind-namespace)
    (setf (string-code.cft.descriptor::theory-kind-namespace theory)
          (string-code.cft.descriptor::add-symbol
           theory
           (string-downcase (string (getf options :kind-namespace))))))
  theory)

(defmacro define-cft-preset (name &body body)
  "Define NAME as a descriptor preset from CFT declaration forms."
  (let* ((preset-name (preset-name-from-spec name))
         (user-options (if (preset-options-form-p (first body)) (first body) nil))
         (forms (if user-options (rest body) body)))
    (if (consp name)
        `(progn
           (setf (gethash ',preset-name *preset-templates*)
                 (make-preset-template
                  :name ',preset-name
                  :parameters ',(template-parameter-specs name)
                  :forms ',forms
                  :options ',user-options))
           ',preset-name)
        (let* ((theory-name (or (getf user-options :name)
                                (generated-theory-name preset-name)))
               (hash (or (getf user-options :hash)
                         (generated-theory-hash theory-name forms)))
               (theory-id (if (option-present-p user-options :theory-id)
                              (reserve-theory-id preset-name
                                                 (getf user-options :theory-id))
                              (error "Preset ~S must declare an explicit :theory-id."
                                     preset-name)))
               (theory (apply-preset-options-to-theory
                        (parse-cft-preset preset-name theory-name hash forms)
                        user-options))
               (basis-metadata (normalize-basis-metadata
                                theory (getf user-options :basis)))
               (field-interfaces (preset-field-interfaces-from-theory theory)))
          `(progn
             (defun ,preset-name ()
               (apply-preset-options-to-theory
                (parse-cft-preset ',preset-name ,theory-name ,hash ',forms)
                ',user-options))
             (let ((reserved-theory-id (reserve-theory-id ',preset-name ,theory-id)))
               (setf (gethash ',preset-name *presets*)
                     (make-preset :name ',preset-name
                                  :builder #',preset-name
                                  :theory-name ,theory-name
                                  :hash ,hash
                                  :theory-id reserved-theory-id
                                  :fields ',field-interfaces
                                  :basis-metadata ',basis-metadata)))
             ',preset-name)))))

(defun table-get (table key label)
  (multiple-value-bind (value found) (gethash key table)
    (unless found
      (error "Unknown ~A ~S." label key))
    value))

(defun option-value (items key &optional default)
  (let ((tail (member key items)))
    (if tail (second tail) default)))

(defun field-key (name)
  (string-downcase (string name)))

(defun label-key (field label)
  (list (field-key field) (string-downcase (string label))))

(defun register-field-shape (fields labels field labels-spec)
  (let ((field-name (field-key field))
        (field-id (hash-table-count fields)))
    (setf (gethash field-name fields)
          (make-field-shape :id field-id :insertion nil :labels labels-spec))
    (loop for label in labels-spec
          for slot from 0
          do (setf (gethash (label-key field (first label)) labels) slot))
    field-id))

(defun set-field-shape-insertion (fields field insertion)
  (setf (field-shape-insertion (table-get fields (field-key field) "field"))
        insertion))

(defun current-surface (surfaces)
  (or (gethash :current surfaces)
      (error "No current surface. Declare a SURFACE before surface-less WICK or ZERO-MODE forms.")))

(defun surface-form-id (surfaces value)
  (if (and (symbolp value) (gethash value surfaces))
      (gethash value surfaces)
      (current-surface surfaces)))

(defun starts-with-surface-p (surfaces items)
  (and (symbolp (first items)) (gethash (first items) surfaces)))

(defun field-declaration-parts (form insertion)
  (let* ((id (second form))
         (tail (cddr form))
         (symbol (if (stringp (first tail))
                     (prog1 (first tail) (setf tail (rest tail)))
                     (string-downcase (string id))))
         (labels (if (and tail (consp (first tail)) (not (keywordp (first tail))))
                     (prog1 (first tail) (setf tail (rest tail)))
                     nil))
         (statistics (first tail))
         (options (rest tail)))
    (unless (member statistics '(:bosonic :fermionic))
      (error "Field ~S has invalid statistics ~S." id statistics))
    (values id symbol insertion labels statistics options)))

(defun parse-infinity-behavior (labels field form)
  (cond
    ((null form)
     (values nil nil))
    ((member form '(:infer infer))
     (values :infer nil))
    ((member form '(:none none))
     (values :none nil))
    ((member form '(:primary :primary-from-weight primary primary-from-weight))
     (values :primary-from-weight nil))
    ((and (consp form)
          (member (first form) '(:primary :primary-from-weight primary primary-from-weight)))
     (values :primary-from-weight nil))
    ((and (consp form)
          (member (first form) '(:branch-global-exponential branch-global-exponential
                                 :free-boson-exponential free-boson-exponential)))
     (values :branch-global-exponential
             (parse-label-ref labels field (option-value (rest form) :momentum))))
    (t
     (error "Unknown infinity behavior ~S for field ~S." form field))))

(defun parse-field-support (value)
  (case value
    ((nil) nil)
    ((:infer infer) :infer)
    ((:holomorphic holomorphic) :holomorphic)
    ((:antiholomorphic antiholomorphic :anti-holomorphic anti-holomorphic)
     :antiholomorphic)
    (otherwise (error "Unknown field support ~S." value))))

(defun declare-field
    (theory parameters quantum-numbers fields labels
     id symbol insertion label-spec statistics options)
  (let* ((field-id (register-field-shape fields labels id label-spec))
         (weight-form (option-value options :weight))
         (anti-weight-form (option-value options :anti-weight))
         (weight-id (when weight-form
                      (parse-metadata-id theory parameters fields labels weight-form)))
         (anti-weight-id (cond
                           ((null anti-weight-form) nil)
                           ((equal anti-weight-form weight-form) weight-id)
                           (t (parse-metadata-id theory parameters fields labels
                                                 anti-weight-form)))))
    (set-field-shape-insertion fields id insertion)
    (multiple-value-bind (infinity-behavior infinity-label)
        (parse-infinity-behavior labels id (option-value options :infinity))
      (unless (= field-id
                 (add-field theory symbol insertion label-spec statistics
                            :kind-symbol (or (option-value options :kind-symbol)
                                             (option-value options :kind))
                            :support (parse-field-support
                                      (option-value options :support))
                            :zero-mode (option-value options :zero-mode)
                            :weight weight-id
                            :anti-weight anti-weight-id
                            :infinity-behavior infinity-behavior
                            :infinity-label infinity-label))
        (error "Field table drift while declaring ~S." id))
      (parse-field-quantum-numbers
       theory quantum-numbers field-id
       (option-value options :quantum-numbers nil)))))

(defun parse-parameter-ref (parameters value)
  (etypecase value
    (integer value)
    (symbol (table-get parameters value "parameter"))))

(defun parameter-symbol-ref (theory parameter-id)
  (let ((parameter (find parameter-id
                         (string-code.cft.descriptor::theory-parameters theory)
                         :key #'string-code.cft.descriptor::parameter-id)))
    (unless parameter
      (error "Unknown parameter id ~D." parameter-id))
    (string-code.cft.descriptor::parameter-symbol parameter)))

(defun parse-quantum-number-ref (quantum-numbers value)
  (etypecase value
    (integer value)
    (symbol (table-get quantum-numbers value "quantum number"))))

(defun parse-quantum-number-kind (kind)
  (let ((tag (if (consp kind) (first kind) kind)))
    (ecase tag
      ((:u1 :u1-charge u1 u1-charge) :u1-charge)
      ((:zn :z-n :zn-phase zn z-n zn-phase) :zn-phase)
      ((:ade-irrep ade-irrep) :ade-irrep)
      ((:rep :tensor-rep :representation rep tensor-rep representation) :tensor-rep))))

(defun parse-quantum-number-modulus (kind options)
  (or (option-value options :modulus)
      (when (and (consp kind)
                 (member (first kind) '(:zn :z-n :zn-phase zn z-n zn-phase)))
        (second kind))))

(defun parse-field-ref (fields value)
  (etypecase value
    (integer value)
    (symbol (field-shape-id (table-get fields (field-key value) "field")))))

(defun quantum-number-record (theory id)
  (or (find id (string-code.cft.descriptor::theory-quantum-numbers theory)
            :key #'string-code.cft.descriptor::quantum-number-id)
      (error "Unknown quantum number id ~D." id)))

(defun parse-symbol-quantum-value (theory value)
  (etypecase value
    (string `(:symbol ,(add-symbol theory value)))
    (symbol `(:symbol ,(add-symbol theory (string-downcase (string value)))))))

(defun parse-quantum-value (theory kind value)
  (etypecase value
    (integer
     (if (member kind '(:u1-charge :zn-phase))
         value
         (error "Integer value ~S is not valid for quantum kind ~S." value kind)))
    (rational
     (if (eq kind :u1-charge)
         value
         (error "Rational value ~S is only valid for U(1) quantum numbers." value)))
    (string
     (if (member kind '(:ade-irrep :tensor-rep))
         (parse-symbol-quantum-value theory value)
         (error "Symbolic value ~S is not valid for quantum kind ~S." value kind)))
    (symbol
     (case kind
       ((:ade-irrep :tensor-rep) (parse-symbol-quantum-value theory value))
       (otherwise (error "Symbolic value ~S is not valid for quantum kind ~S." value kind))))
    (cons
     (ecase (first value)
       ((:rational rational)
        (if (eq kind :u1-charge)
            `(:rational ,(second value) ,(third value))
            (error "Rational value ~S is only valid for U(1) quantum numbers." value)))))))

(defun parse-field-quantum-numbers (theory quantum-numbers field-id specs)
  (dolist (spec specs)
    (destructuring-bind (name value) spec
      (let* ((number-id (parse-quantum-number-ref quantum-numbers name))
             (number (quantum-number-record theory number-id)))
        (add-field-quantum-number theory
                                  field-id
                                  number-id
                                  (parse-quantum-value theory (string-code.cft.descriptor::quantum-number-kind number) value))))))

(defun parse-label-ref (labels field value)
  (etypecase value
    (integer value)
    (symbol (table-get labels (label-key field value) "field label"))))

(defun parse-metadata-form (theory parameters fields labels form)
  (etypecase form
    (integer form)
    (cons
     (ecase (first form)
       ((:rational rational)
        `(:rational ,(second form) ,(third form)))
       ((:parameter parameter)
        `(:parameter ,(parse-parameter-ref parameters (second form))))
       ((:field-label field-label)
        `(:field-label ,(parse-field-ref fields (second form))
                       ,(parse-label-ref labels (second form) (third form))))
       ((:add add +)
        `(:add ,(parse-metadata-id theory parameters fields labels (second form))
               ,(parse-metadata-id theory parameters fields labels (third form))))
       ((:mul mul *)
        (parse-metadata-product theory parameters fields labels form))
       ((:bilinear bilinear dot)
        `(:bilinear ,(parse-metadata-id theory parameters fields labels (second form))
                    ,(parse-metadata-id theory parameters fields labels (third form))
                    ,(fourth form)))))))

(defun parse-metadata-id (theory parameters fields labels form)
  (add-metadata theory (parse-metadata-form theory parameters fields labels form)))

(defun i-symbol-p (value)
  (and (symbolp value) (string-equal value 'i)))

(defun rational-factor (value)
  (cond
    ((integerp value) value)
    ((rationalp value) value)
    ((and (consp value) (member (first value) '(:rational rational)))
     (/ (second value) (third value)))
    (t nil)))

(defun scalar-product-factors (form)
  (if (and (consp form) (member (first form) '(* :mul mul)))
      (rest form)
      (list form)))

(defun metadata-product-factors (form)
  (if (and (consp form) (member (first form) '(* :mul mul)))
      (loop for factor in (rest form) append (metadata-product-factors factor))
      (list form)))

(defun scalar-parameter-ref-p (parameters value)
  (etypecase value
    (integer t)
    (symbol (nth-value 1 (gethash value parameters)))))

(defun scalar-atom-factor-p (theory parameters factor)
  (cond
    ((and (consp factor) (member (first factor) '(:parameter parameter)))
     (scalar-parameter-ref-p parameters (second factor)))
    ((and (consp factor) (member (first factor) '(:pow :power pow power expt)))
     (and (integerp (third factor))
          (scalar-atom-factor-p theory parameters (second factor))))
    ((symbolp factor)
     (or (pi-symbol-p factor)
         (scalar-parameter-ref-p parameters factor)))
    (t nil)))

(defun scalar-factor-form-p (theory parameters form)
  (or (rational-factor form)
      (i-symbol-p form)
      (scalar-atom-factor-p theory parameters form)))

(defun scalar-atom-factor (theory parameters factor)
  (cond
    ((and (consp factor) (member (first factor) '(:parameter parameter)))
     (values (parameter-symbol-ref theory (parse-parameter-ref parameters (second factor))) 1))
    ((and (consp factor) (member (first factor) '(:pow :power pow power expt)))
     (unless (integerp (third factor))
       (error "Scalar atom power must be an integer in ~S." factor))
     (let ((power (third factor)))
       (unless (<= -128 power 127)
         (error "Scalar atom power is outside i8 range in ~S." factor))
       (multiple-value-bind (atom atom-power)
           (scalar-atom-factor theory parameters (second factor))
         (values atom (* atom-power power)))))
    ((and (symbolp factor) (pi-symbol-p factor))
     (values (add-symbol theory "pi") 1))
    ((symbolp factor)
     (values (parameter-symbol-ref theory (parse-parameter-ref parameters factor)) 1))
    (t
     (values nil 0))))

(defun scalar-factor-product (theory parameters form)
  (let ((coefficient 1)
        (imaginary-power 0)
        (parameter nil)
        (parameter-power 0))
    (labels ((apply-atom (atom atom-power scale)
               (let ((scaled-power (* atom-power scale)))
                 (cond
                   ((null atom)
                    (error "Unsupported scalar factor in ~S." form))
                   ((and parameter (/= parameter atom))
                    (error "Scalar factor has more than one parameter: ~S." form))
                   (t
                    (setf parameter atom)
                    (incf parameter-power scaled-power)))))
             (apply-factor (factor scale)
               (let ((rational (rational-factor factor)))
                 (cond
                   (rational
                    (setf coefficient (* coefficient (expt rational scale))))
                   ((i-symbol-p factor)
                    (setf imaginary-power (mod (+ imaginary-power scale) 4)))
                   ((and (consp factor)
                         (member (first factor) '(* :mul mul)))
                    (dolist (item (rest factor))
                      (apply-factor item scale)))
                   ((and (consp factor)
                         (member (first factor) '(:pow :power pow power expt))
                         (integerp (third factor)))
                    (apply-factor (second factor) (* scale (third factor))))
                   (t
                    (multiple-value-bind (atom atom-power)
                        (scalar-atom-factor theory parameters factor)
                      (apply-atom atom atom-power scale)))))))
      (apply-factor form 1))
    (unless (<= -128 parameter-power 127)
      (error "Scalar atom power is outside i8 range in ~S." form))
    (values coefficient imaginary-power parameter parameter-power)))

(defun parse-scalar-factor (theory parameters form)
  (if (eq form :one)
      :one
      (multiple-value-bind (coefficient imaginary-power parameter parameter-power)
          (scalar-factor-product theory parameters form)
        (cond
          ((and (null parameter) (zerop imaginary-power) (= coefficient 1))
           :one)
          (t
           `(:monomial ,(numerator coefficient) ,(denominator coefficient)
                       ,imaginary-power ,parameter
                       ,(if parameter parameter-power 0)))))))

(defun scalar-factor-row (coefficient imaginary-power atom atom-power)
  (if (and (null atom) (zerop imaginary-power) (= coefficient 1))
      nil
      `(:monomial ,(numerator coefficient) ,(denominator coefficient)
                  ,imaginary-power ,atom
                  ,(if atom atom-power 0))))

(defun parse-scalar-factors (theory parameters form)
  (if (eq form :one)
      '(:one)
      (let ((coefficient 1)
            (imaginary-power 0)
            (atom-powers nil))
        (labels ((add-atom (atom power)
                   (let ((cell (assoc atom atom-powers)))
                     (if cell
                         (incf (cdr cell) power)
                         (push (cons atom power) atom-powers))))
                 (apply-factor (factor scale)
                   (let ((rational (rational-factor factor)))
                     (cond
                       (rational
                        (setf coefficient (* coefficient (expt rational scale))))
                       ((i-symbol-p factor)
                        (setf imaginary-power (mod (+ imaginary-power scale) 4)))
                       ((and (consp factor)
                             (member (first factor) '(* :mul mul)))
                        (dolist (item (rest factor))
                          (apply-factor item scale)))
                       ((and (consp factor)
                             (member (first factor) '(:pow :power pow power expt))
                             (integerp (third factor)))
                        (apply-factor (second factor) (* scale (third factor))))
                       (t
                        (multiple-value-bind (atom atom-power)
                            (scalar-atom-factor theory parameters factor)
                          (unless atom
                            (error "Unsupported scalar factor in ~S." form))
                          (add-atom atom (* atom-power scale))))))))
          (apply-factor form 1)
          (let ((rows nil)
                (first t))
            (dolist (entry (reverse atom-powers))
              (let ((power (cdr entry)))
                (unless (zerop power)
                  (unless (<= -128 power 127)
                    (error "Scalar atom power is outside i8 range in ~S." form))
                  (push (scalar-factor-row
                         (if first coefficient 1)
                         (if first imaginary-power 0)
                         (car entry)
                         power)
                        rows)
                  (setf first nil))))
            (when first
              (let ((row (scalar-factor-row coefficient imaginary-power nil 0)))
                (when row (push row rows))))
            (or (nreverse rows) '(:one)))))))

(defun pi-symbol-p (value)
  (and (symbolp value) (string-equal value 'pi)))

(defun parse-zero-mode-normalization (theory parameters options)
  (let ((form (option-value options :normalization :one)))
    (let ((factors (parse-scalar-factors theory parameters form)))
      (values (first factors) (rest factors)))))

(defun parse-metadata-scalar-factor (theory parameters factors)
  (multiple-value-bind (coefficient imaginary-power parameter parameter-power)
      (scalar-factor-product theory parameters `(* ,@factors))
    `(:scalar-monomial ,(numerator coefficient) ,(denominator coefficient)
                       ,imaginary-power ,parameter
                       ,(if parameter parameter-power 0))))

(defun metadata-product-id (theory parameters fields labels factors)
  (let ((ids (mapcar (lambda (factor)
                       (parse-metadata-id theory parameters fields labels factor))
                     factors)))
    (unless ids
      (error "Metadata product has no factors."))
    (reduce (lambda (left right)
              (add-metadata theory `(:mul ,left ,right)))
            (rest ids)
            :initial-value (first ids))))

(defun parse-metadata-product (theory parameters fields labels form)
  (let ((scalar-factors nil)
        (metadata-factors nil))
    (dolist (factor (metadata-product-factors form))
      (if (scalar-factor-form-p theory parameters factor)
          (push factor scalar-factors)
          (push factor metadata-factors)))
    (let ((scalar-form (when scalar-factors
                         (parse-metadata-scalar-factor
                          theory parameters
                          (reverse scalar-factors))))
          (metadata-id (when metadata-factors
                         (metadata-product-id
                          theory parameters fields labels
                          (reverse metadata-factors)))))
      (cond
        ((and scalar-form metadata-id)
         `(:mul ,(add-metadata theory scalar-form) ,metadata-id))
        (scalar-form scalar-form)
        (metadata-id metadata-id)
        (t (error "Metadata product has no factors."))))))

(defun parse-coordinate-factor (form)
  (ecase (first form)
    ((:difference-power difference-power)
     `(:difference-power ,(second form)
                         ,(third form)
                         ,(fourth form)
                         ,@(cddddr form)))
    ((:named-kernel named-kernel)
     `(:named-kernel ,(second form)
                     ,(third form)
                     ,(fourth form)
                     ,@(cddddr form)))
    ((:green-exponential green-exponential)
     `(:green-exponential ,(second form)
                          ,(third form)))
    ((:logarithm logarithm)
     `(:logarithm ,(second form)
                  ,(third form)
                  ,@(cdddr form)))))

(defun parse-side-label-ref (labels left-field right-field ref)
  (destructuring-bind (side value) ref
    (ecase side
      (:left `(:left ,(parse-label-ref labels left-field value)))
      (:right `(:right ,(parse-label-ref labels right-field value))))))

(defun parse-tensor-factor (labels left-field right-field form)
  (ecase (first form)
    ((:metric metric)
     `(:metric ,(parse-side-label-ref labels left-field right-field (second form))
               ,(parse-side-label-ref labels left-field right-field (third form))))
    ((:momentum-index momentum-index)
     `(:momentum-index ,(parse-side-label-ref labels left-field right-field (second form))
                       ,(parse-side-label-ref labels left-field right-field (third form))))
    ((:momentum-pair momentum-pair)
     `(:momentum-pair ,(parse-side-label-ref labels left-field right-field (second form))
                      ,(parse-side-label-ref labels left-field right-field (third form))))))

(defun parse-index-constraint-kind (kind)
  (ecase kind
    ((:none none) :none)
    ((:same-sort same-sort) :same-sort)
    ((:conjugate-complex-sort conjugate-complex-sort) :conjugate-complex-sort)))

(defun parse-index-constraint (labels left-field right-field form)
  (destructuring-bind (left-label right-label kind) form
    (list (parse-label-ref labels left-field left-label)
          (parse-label-ref labels right-field right-label)
          (parse-index-constraint-kind kind))))

(defun parse-index-constraints (labels left-field right-field forms)
  (mapcar (lambda (form)
            (parse-index-constraint labels left-field right-field form))
          forms))

(defun insertion-coordinate-slots (insertion)
  (ecase insertion
    (:single '(:position))
    (:pair '(:holomorphic :antiholomorphic))))

(defun coordinate-ref-form (side slot)
  (if (eq slot :position)
      side
      (list side slot)))

(defun bind-field-call (fields side call label-env coordinate-env)
  (destructuring-bind (field &rest args) call
    (let* ((shape (table-get fields (field-key field) "field"))
           (label-count (length (field-shape-labels shape)))
           (slots (insertion-coordinate-slots (field-shape-insertion shape)))
           (labels (subseq args 0 label-count))
           (coordinates (subseq args label-count)))
      (unless (= (length coordinates) (length slots))
        (error "Field call ~S has ~D coordinate arguments; expected ~D."
               call (length coordinates) (length slots)))
      (loop for label in labels
            for slot from 0
            do (setf (gethash label label-env) (list side slot)))
      (loop for coordinate in coordinates
            for slot in slots
            do (setf (gethash coordinate coordinate-env)
                     (coordinate-ref-form side slot)))
      field)))

(defun env-ref (env name label)
  (multiple-value-bind (value found) (gethash name env)
    (unless found
      (error "Unknown ~A variable ~S." label name))
    value))

(defun coordinate-ref-position-p (ref)
  (symbolp ref))

(defun difference-form-p (form)
  (and (consp form) (member (first form) '(- :difference difference))))

(defun lower-difference-power (coordinate-env difference exponent)
  (unless (and (difference-form-p difference)
               (= (length difference) 3))
    (error "Expected coordinate difference, got ~S." difference))
  (let ((left (env-ref coordinate-env (second difference) "coordinate"))
        (right (env-ref coordinate-env (third difference) "coordinate")))
    `(:difference-power ,left ,right ,exponent
                        ,@(when (coordinate-ref-position-p left) '(:derive-left))
                        ,@(when (coordinate-ref-position-p right) '(:derive-right)))))

(defun named-coordinate-kernel-p (form coordinate-env)
  (and (consp form)
       (= (length form) 3)
       (symbolp (first form))
       (gethash (second form) coordinate-env)
       (gethash (third form) coordinate-env)))

(defun parse-expression-coordinate (coordinate-env form)
  (cond
    ((and (consp form) (member (first form) '(/ :div div))
          (= (length form) 3)
          (eql (second form) 1))
     (lower-difference-power coordinate-env (third form) -1))
    ((and (consp form) (member (first form) '(pow expt))
          (= (length form) 3))
     (lower-difference-power coordinate-env (second form) (third form)))
    ((and (consp form) (member (first form) '(green-exp green-exponential))
          (= (length form) 3))
     `(:green-exponential ,(env-ref coordinate-env (second form) "coordinate")
                          ,(env-ref coordinate-env (third form) "coordinate")))
    ((and (consp form) (member (first form) '(log logarithm))
          (= (length form) 2))
     (let ((argument (second form)))
       (unless (and (difference-form-p argument)
                    (= (length argument) 3))
         (error "Expected logarithm of coordinate difference, got ~S." form))
       (let ((left (env-ref coordinate-env (second argument) "coordinate"))
             (right (env-ref coordinate-env (third argument) "coordinate")))
         `(:logarithm ,left ,right
                      ,@(when (coordinate-ref-position-p left) '(:derive-left))
                      ,@(when (coordinate-ref-position-p right) '(:derive-right))))))
    ((named-coordinate-kernel-p form coordinate-env)
     `(:named-kernel ,(first form)
                     ,(env-ref coordinate-env (second form) "coordinate")
                     ,(env-ref coordinate-env (third form) "coordinate")
                     :derive-left))
    (t nil)))

(defun parse-expression-tensor (label-env form)
  (when (consp form)
    (case (first form)
      ((metric)
       `(:metric ,(env-ref label-env (second form) "label")
                 ,(env-ref label-env (third form) "label")))
      ((momentum-index)
       `(:momentum-index ,(env-ref label-env (second form) "label")
                         ,(env-ref label-env (third form) "label")))
      ((momentum-pair)
       `(:momentum-pair ,(env-ref label-env (second form) "label")
                        ,(env-ref label-env (third form) "label"))))))

(defun parse-expression-action (label-env form)
  (when (consp form)
    (case (first form)
      ((profile-derivative)
       `(:profile-derivative ,(env-ref label-env (second form) "label")
                             ,(env-ref label-env (third form) "label"))))))

(defun expression-product-factors (form)
  (if (and (consp form) (member (first form) '(* :mul mul)))
      (loop for factor in (rest form) append (expression-product-factors factor))
      (list form)))

(defun expression-sum-terms (form)
  (if (and (consp form) (member (first form) '(+ :add add)))
      (rest form)
      (list form)))

(defun parse-expression-term (theory parameters label-env coordinate-env expression residuals)
  (let ((scalar-factors nil)
        (coordinates nil)
        (tensors nil)
        (actions nil))
    (dolist (factor (expression-product-factors expression))
      (let ((coordinate (parse-expression-coordinate coordinate-env factor))
            (tensor (parse-expression-tensor label-env factor))
            (action (parse-expression-action label-env factor)))
        (cond
          (coordinate (push coordinate coordinates))
          (tensor (push tensor tensors))
          (action (push action actions))
          (t (push factor scalar-factors)))))
    (make-wick-term
     :scalars (parse-scalar-factors
               theory parameters
               (if scalar-factors
                   `(* ,@(reverse scalar-factors))
                   :one))
     :coordinates (reverse coordinates)
     :tensors (reverse tensors)
     :actions (reverse actions)
     :residuals residuals)))

(defun parse-expression-terms
    (theory parameters label-env coordinate-env expression residuals)
  (mapcar (lambda (term)
            (parse-expression-term theory parameters label-env coordinate-env
                                   term residuals))
          (expression-sum-terms expression)))

(defun parse-term (theory parameters labels left-field right-field form)
  (unless (eq (first form) 'term)
    (error "Expected TERM form, got ~S." form))
  (let ((body (rest form)))
    (make-wick-term
     :scalars (loop for item in (option-value body :scalars '(:one))
                    append (parse-scalar-factors theory parameters item))
     :coordinates (mapcar #'parse-coordinate-factor
                          (option-value body :coordinates nil))
     :tensors (mapcar (lambda (item)
                        (parse-tensor-factor labels left-field right-field item))
                      (option-value body :tensors nil))
     :actions (option-value body :actions nil)
     :residuals (option-value body :residuals nil))))

(defun add-wick-form
    (theory parameters fields labels surface left body)
  (if (and body (consp (first body)) (not (eq (caar body) 'term)))
      (let* ((right (first body))
             (expression (second body))
             (options (cddr body))
             (label-env (make-hash-table))
             (coordinate-env (make-hash-table))
             (left-field (bind-field-call fields :left left label-env coordinate-env))
             (right-field (bind-field-call fields :right right label-env coordinate-env)))
        (add-wick-rule
         theory
         surface
         (parse-field-ref fields left-field)
         (parse-field-ref fields right-field)
         (parse-expression-terms theory parameters label-env coordinate-env
                                 expression
                                 (option-value options :residuals nil))
         :constraints (parse-index-constraints
                       labels left-field right-field
                       (option-value options :index-constraints nil))))
      (destructuring-bind (left-field right-field) left
        (let ((constraints (option-value body :index-constraints nil))
              (terms (loop for item in body
                           when (and (consp item) (eq (first item) 'term))
                           collect item)))
          (add-wick-rule
           theory
           surface
           (parse-field-ref fields left-field)
           (parse-field-ref fields right-field)
           (mapcar (lambda (term)
                     (parse-term theory parameters labels left-field right-field term))
                   terms)
           :constraints (parse-index-constraints
                         labels left-field right-field
                         constraints))))))

(defun parse-zero-mode-saturation (name)
  (case name
    ((grassmann-count :grassmann-count) :grassmann-count)
    ((grassmann-top-form :grassmann-top-form) :grassmann-top-form)
    ((linear-conservation :linear-conservation) :linear-conservation)
    (otherwise (error "Unknown zero-mode saturation ~S." name))))

(defun zero-mode-measure-defaults (saturation)
  (ecase saturation
    (:grassmann-count (values 1 nil nil))
    (:grassmann-top-form (values 3 t t))
    (:linear-conservation (values 0 nil t))))

(defun parse-zero-mode-selector-fields (fields options form)
  (let ((field (option-value options :field))
        (field-list (option-value options :fields)))
    (when (and field field-list)
      (error "Zero-mode measure ~S cannot declare both :field and :fields." form))
    (cond
      (field (list (parse-field-ref fields field)))
      (field-list (mapcar (lambda (item) (parse-field-ref fields item)) field-list))
      (t (error "Zero-mode measure ~S must declare :field or :fields." form)))))

(defun explicit-zero-mode-form-p (body)
  (and (= (length body) 1)
       (consp (first body))
       (not (keywordp (caar body)))))

(defun add-explicit-zero-mode-form (theory parameters fields surface form)
  (let* ((saturation (parse-zero-mode-saturation (first form)))
         (options (rest form)))
    (check-option-keys options
                       '(:field :fields :count :allow-derivatives
                         :allow-infinity :normalization)
                       form)
    (let ((selector-fields (parse-zero-mode-selector-fields fields options form)))
      (multiple-value-bind (default-count default-derivatives default-infinity)
          (zero-mode-measure-defaults saturation)
        (multiple-value-bind (normalization normalization-factors)
            (parse-zero-mode-normalization theory parameters options)
          (add-zero-mode-measure
           theory
           surface
           selector-fields
           saturation
           :exact-count (option-value options :count default-count)
           :allow-derivatives (option-value options :allow-derivatives default-derivatives)
           :allow-infinity (option-value options :allow-infinity default-infinity)
           :normalization normalization
           :normalization-factors normalization-factors))))))

(defun add-legacy-zero-mode-form (theory parameters fields surface body)
  (destructuring-bind (kind consumes &rest options) body
    (check-option-keys options '(:normalization) body)
    (multiple-value-bind (saturation exact-count allow-derivatives allow-infinity)
        (string-code.cft.descriptor::zero-mode-alias-measure kind)
      (multiple-value-bind (normalization normalization-factors)
          (parse-zero-mode-normalization theory parameters options)
        (add-zero-mode-measure
         theory
         surface
         (mapcar (lambda (field) (parse-field-ref fields field)) consumes)
         saturation
         :exact-count exact-count
         :allow-derivatives allow-derivatives
         :allow-infinity allow-infinity
         :normalization normalization
         :normalization-factors normalization-factors)))))

(defun apply-preset-form
    (theory parameters quantum-numbers surfaces fields labels form)
  (ecase (first form)
    (parameter
     (setf (gethash (second form) parameters)
           (add-parameter theory (third form) (or (fourth form) :scalar-parameter))))
    (quantum-number
     (setf (gethash (second form) quantum-numbers)
           (add-quantum-number theory
                               (or (option-value (cdddr form) :symbol)
                                   (string-downcase (string (second form))))
                               (parse-quantum-number-kind (third form))
                               :group (option-value (cdddr form) :group)
                               :modulus (parse-quantum-number-modulus (third form) (cdddr form))
                               :representation-space (or (option-value (cdddr form) :representation-space)
                                                         (option-value (cdddr form) :space)))))
    (surface
     (let ((surface-id
             (add-surface theory (third form) (fourth form)
                          :modular-parameter
                          (when (option-value (cddddr form) :modular-parameter)
                            (parse-parameter-ref
                             parameters
                             (option-value (cddddr form) :modular-parameter))))))
       (setf (gethash (second form) surfaces) surface-id
             (gethash :current surfaces) surface-id)))
    (field
     (destructuring-bind (id symbol insertion label-spec statistics &rest options) (rest form)
       (declare-field theory parameters quantum-numbers fields labels
                      id symbol insertion label-spec statistics options)))
    (chiral-field
     (multiple-value-bind (id symbol insertion label-spec statistics options)
         (field-declaration-parts form :single)
       (declare-field theory parameters quantum-numbers fields labels
                      id symbol insertion label-spec statistics options)))
    (anti-chiral-field
     (multiple-value-bind (id symbol insertion label-spec statistics options)
         (field-declaration-parts form :single)
       (declare-field theory parameters quantum-numbers fields labels
                      id symbol insertion label-spec statistics
                      (append options '(:support :antiholomorphic)))))
    (bulk-field
     (multiple-value-bind (id symbol insertion label-spec statistics options)
         (field-declaration-parts form :pair)
       (declare-field theory parameters quantum-numbers fields labels
                      id symbol insertion label-spec statistics options)))
    (wick
     (let* ((items (rest form))
            (has-surface (starts-with-surface-p surfaces items))
            (surface (surface-form-id surfaces (first items)))
            (left (if has-surface (second items) (first items)))
            (body (if has-surface (cddr items) (rest items))))
       (add-wick-form theory parameters fields labels surface left body)))
    (zero-mode
     (let* ((items (rest form))
            (has-surface (starts-with-surface-p surfaces items))
            (surface (surface-form-id surfaces (first items)))
            (body (if has-surface (rest items) items)))
       (if (explicit-zero-mode-form-p body)
           (add-explicit-zero-mode-form theory parameters fields surface (first body))
           (add-legacy-zero-mode-form theory parameters fields surface body))))))

(defun apply-preset-form-with-diagnostics
    (preset index theory parameters quantum-numbers surfaces fields labels form)
  (handler-case
      (apply-preset-form
       theory parameters quantum-numbers surfaces fields labels form)
    (preset-diagnostic (condition)
      (error condition))
    (error (condition)
      (error 'preset-diagnostic
             :preset preset
             :context (list :index index :kind (and (consp form) (first form)))
             :form form
             :cause condition))))

(defun parse-cft-preset (preset name hash forms)
  (let ((theory (make-theory name hash))
        (parameters (make-hash-table))
        (quantum-numbers (make-hash-table))
        (surfaces (make-hash-table))
        (fields (make-hash-table :test #'equal))
        (labels (make-hash-table :test #'equal)))
    (loop for form in forms
          for index from 0
          do (apply-preset-form-with-diagnostics
              preset index theory parameters quantum-numbers surfaces fields labels form))
    theory))

(defun build-cft-preset (name hash forms)
  (parse-cft-preset name name hash forms))

(defun theory-symbol-text (theory id)
  (aref (string-code.cft.descriptor::theory-symbols theory) id))

(defun field-label-interface (theory label)
  (list :name
        (intern (string-upcase
                 (theory-symbol-text
                  theory
                  (string-code.cft.descriptor::label-schema-symbol label)))
                (find-package '#:string-code.cft.presets))
        :id (string-code.cft.descriptor::label-schema-id label)
        :role (string-code.cft.descriptor::label-schema-role label)))

(defun preset-field-interfaces-from-theory (theory)
  (loop for field in (sort (copy-list (string-code.cft.descriptor::theory-fields theory))
                           #'< :key #'string-code.cft.descriptor::field-id)
        collect
        (make-preset-field-interface
         :name (intern (string-upcase
                        (theory-symbol-text
                         theory
                         (string-code.cft.descriptor::field-symbol field)))
                       (find-package '#:string-code.cft.presets))
         :id (string-code.cft.descriptor::field-id field)
         :insertion (string-code.cft.descriptor::field-insertion field)
         :labels (mapcar (lambda (label)
                            (field-label-interface theory label))
                          (string-code.cft.descriptor::field-labels field)))))

(defun sorted-presets ()
  (sort (loop for preset being the hash-values of *presets*
              collect preset)
        #'< :key #'preset-theory-id))

(defun preset-name-parts (preset)
  (drop-trailing-numeric-parts (split-name-parts (preset-name preset))))

(defun preset-family-parts (preset)
  (drop-trailing-surface-part (preset-name-parts preset)))

(defun same-family-p (left right)
  (equal (preset-family-parts left) (preset-family-parts right)))

(defun preset-family-count (preset presets)
  (loop for item in presets count (same-family-p preset item)))

(defun generated-name-parts (preset presets)
  (if (> (preset-family-count preset presets) 1)
      (preset-name-parts preset)
      (preset-family-parts preset)))

(defun generated-prefix (preset presets)
  (join-name-parts (generated-name-parts preset presets) "_"))

(defun generated-descriptor-name (preset presets)
  (format nil "~A_descriptor" (generated-prefix preset presets)))

(defun capitalized-name-part (part)
  (string-capitalize part))

(defun generated-type-name (preset presets)
  (with-output-to-string (stream)
    (dolist (part (generated-name-parts preset presets))
      (write-string (capitalized-name-part part) stream))))

(defun preset-key (name)
  (etypecase name
    (symbol
     (or (find-symbol (symbol-name name) (find-package '#:string-code.cft.presets))
         name))
    (string
     (find-symbol (string-upcase name) (find-package '#:string-code.cft.presets)))))

(defun registered-preset (name)
  (table-get *presets* (preset-key name) "preset"))

(defun preset-theory (name)
  "Build the descriptor theory declared by preset NAME."
  (funcall (preset-builder (registered-preset name))))

(defun preset-theory-id-for (name)
  "Return the generated ABI theory id for preset NAME."
  (preset-theory-id (registered-preset name)))

(defun preset-field-interfaces (name)
  "Return generated runtime field metadata for preset NAME."
  (copy-list (preset-fields (registered-preset name))))

(defun preset-basis-metadata-for (name)
  "Return compact basis metadata declared by preset NAME."
  (copy-list (preset-basis-metadata (registered-preset name))))

(defun template-binding (bindings key)
  (let ((tail (member key bindings)))
    (if tail
        (values (second tail) t)
        (values nil nil))))

(defun template-substitution-table (template bindings)
  (let ((table (make-hash-table)))
    (dolist (spec (preset-template-parameters template))
      (destructuring-bind (key variable) spec
        (multiple-value-bind (value found) (template-binding bindings key)
          (unless found
            (error "Missing template parameter ~S for preset template ~S."
                   key (preset-template-name template)))
          (setf (gethash variable table) value))))
    table))

(defun substitute-template-form (form substitutions)
  (cond
    ((symbolp form)
     (multiple-value-bind (value found) (gethash form substitutions)
       (if found value form)))
    ((consp form)
     (mapcar (lambda (item)
               (substitute-template-form item substitutions))
             form))
    (t form)))

(defun generated-template-instance-name (template substitutions)
  (let ((parts (list (string-downcase (string (preset-template-name template))))))
    (dolist (spec (preset-template-parameters template))
      (let ((value (gethash (second spec) substitutions)))
        (when (or (integerp value) (symbolp value) (stringp value))
          (push (string-downcase (string value)) parts))))
    (intern (string-upcase (join-name-parts (nreverse parts) "-"))
            (find-package '#:string-code.cft.presets))))

(defun instantiate-options (template bindings)
  (let ((options (copy-list (or (preset-template-options template) nil))))
    (dolist (key '(:theory-id :name :hash))
      (multiple-value-bind (value found) (template-binding bindings key)
        (when found
          (setf (getf options key) value))))
    options))

(defmacro instantiate-preset (template-name &rest bindings)
  "Instantiate a parameterized preset template into one concrete descriptor."
  (let* ((template (table-get *preset-templates* template-name "preset template"))
         (substitutions (template-substitution-table template bindings))
         (instance-name (or (option-value bindings :as)
                            (option-value bindings :preset)
                            (generated-template-instance-name template substitutions)))
         (options (instantiate-options template bindings))
         (forms (mapcar (lambda (form)
                          (substitute-template-form form substitutions))
                        (preset-template-forms template))))
    `(define-cft-preset ,instance-name
       ,@(when options (list options))
       ,@forms)))

(defparameter *generated-source-hash-files*
  '("lisp/string-code-cft.asd"
    "lisp/string-code-cft-descriptor.lisp"
    "lisp/string-code-cft-presets.lisp"
    "lisp/presets/free-fermion-10.lisp"
    "lisp/presets/eta-xi.lisp"
    "lisp/presets/bc-sphere.lisp"
    "lisp/presets/free-boson-10.lisp"))

(defun hash-byte-fnv1a32 (hash byte)
  (logand #xffffffff (* #x01000193 (logxor hash byte))))

(defun source-file-hash (path)
  (with-open-file (stream path :element-type '(unsigned-byte 8))
    (loop with hash = #x811c9dc5
          for byte = (read-byte stream nil nil)
          while byte
          do (setf hash (hash-byte-fnv1a32 hash byte))
          finally (return hash))))

(defun emit-source-hash-manifest (stream)
  (dolist (path *generated-source-hash-files*)
    (format stream "// source-hash ~A ~8,'0X~%" path (source-file-hash path)))
  (format stream "~%"))

(defun emit-fixture-prologue (stream)
  (emit-source-hash-manifest stream)
  (format stream "const std = @import(\"std\");~%")
  (format stream "const descriptor = @import(\"descriptor.zig\");~%~%")
  (format stream "const d = descriptor;~%~%")
  (format stream "fn cref(side: d.Side) d.CoordinateRef {~%")
  (format stream "    return .{ .side = side, .slot = .position };~%")
  (format stream "}~%~%")
  (format stream "fn bulk(side: d.Side, slot: d.CoordinateSlot) d.CoordinateRef {~%")
  (format stream "    return .{ .side = side, .slot = slot };~%")
  (format stream "}~%~%")
  (format stream "fn lref(side: d.Side, slot: d.Id) d.LabelRef {~%")
  (format stream "    return .{ .side = side, .slot = slot };~%")
  (format stream "}~%~%"))

(defun zig-optional-id (value)
  (if value (format nil "~D" value) "null"))

(defun metadata-row-by-id (theory id)
  (nth (- (length (string-code.cft.descriptor::theory-metadata theory)) id 1)
       (string-code.cft.descriptor::theory-metadata theory)))

(defun rational-metadata-row-p (row)
  (and (consp row) (eq (first row) :rational)))

(defun emit-fixture-infinity-test-helpers (stream)
  (format stream "fn expectFieldInfinity(comptime desc: d.Descriptor, comptime field_id: d.Id, comptime behavior: d.InfinityBehavior, comptime support: d.FieldSupport, comptime weight: ?d.Id, comptime anti_weight: ?d.Id, comptime label: ?d.Id) !void {~%")
  (format stream "    const field = desc.fields[field_id];~%")
  (format stream "    try std.testing.expectEqual(behavior, field.infinity_behavior);~%")
  (format stream "    try std.testing.expectEqual(support, field.support);~%")
  (format stream "    try std.testing.expectEqual(weight, field.weight);~%")
  (format stream "    try std.testing.expectEqual(anti_weight, field.anti_weight);~%")
  (format stream "    try std.testing.expectEqual(label, field.infinity_label);~%")
  (format stream "}~%~%")
  (format stream "fn expectRationalMetadata(comptime desc: d.Descriptor, comptime id: d.Id, comptime numerator: i64, comptime denominator: i64) !void {~%")
  (format stream "    switch (desc.metadata[id]) {~%")
  (format stream "        .rational => |value| {~%")
  (format stream "            try std.testing.expectEqual(numerator, value.numerator);~%")
  (format stream "            try std.testing.expectEqual(denominator, value.denominator);~%")
  (format stream "        },~%")
  (format stream "        else => return error.InvalidMetadata,~%")
  (format stream "    }~%")
  (format stream "}~%~%"))

(defun emit-fixture-infinity-metadata-test (stream presets)
  (format stream "test \"generated descriptors carry DSL infinity metadata\" {~%")
  (dolist (preset presets)
    (let* ((theory (funcall (preset-builder preset)))
           (descriptor-name (generated-descriptor-name preset presets)))
      (dolist (field (sort (copy-list (string-code.cft.descriptor::theory-fields theory))
                           #'< :key #'string-code.cft.descriptor::field-id))
        (let ((behavior (string-code.cft.descriptor::field-infinity-behavior field)))
          (when behavior
            (let ((support (or (string-code.cft.descriptor::field-support field) :infer))
                  (weight (string-code.cft.descriptor::field-weight field))
                  (anti-weight (string-code.cft.descriptor::field-anti-weight field)))
              (format stream
                      "    try expectFieldInfinity(~A, ~D, .~A, .~A, ~A, ~A, ~A);~%"
                      descriptor-name
                      (string-code.cft.descriptor::field-id field)
                      (string-code.cft.descriptor::zig-keyword behavior)
                      (string-code.cft.descriptor::zig-keyword support)
                      (zig-optional-id weight)
                      (zig-optional-id anti-weight)
                      (zig-optional-id
                       (string-code.cft.descriptor::field-infinity-label field)))
              (dolist (id (remove nil (list weight anti-weight)))
                (let ((row (metadata-row-by-id theory id)))
                  (when (rational-metadata-row-p row)
                    (format stream
                            "    try expectRationalMetadata(~A, ~D, ~D, ~D);~%"
                            descriptor-name id (second row) (third row)))))))))))
  (format stream "}~%~%"))

(defun emit-fixture-type (stream preset presets)
  (emit-zig-descriptor (funcall (preset-builder preset)) stream
                       :prefix (generated-prefix preset presets)
                       :descriptor-name (generated-descriptor-name preset presets)
                       :basis-metadata (preset-basis-metadata preset))
  (format stream "~%/// ~A is the lowered generated preset.~%"
          (generated-type-name preset presets))
  (format stream "pub const ~A = d.GeneratedTheory(~A);~%~%"
          (generated-type-name preset presets)
          (generated-descriptor-name preset presets)))

(defun emit-fixture-self-test (stream presets)
  (format stream "/// selfTest validates that generated preset descriptors are loadable.~%")
  (format stream "pub fn selfTest() !void {~%")
  (dolist (preset presets)
    (format stream "    try d.validateDescriptor(~A);~%"
            (generated-descriptor-name preset presets)))
  (format stream "}~%"))

(defun write-generated-fixtures
    (&key (path "src/cft-code/correlators/generated_fixtures.zig"))
  "Write the Zig fixture module from registered Lisp presets."
  (with-open-file (stream path :direction :output :if-exists :supersede
                               :if-does-not-exist :create)
    (let ((presets (sorted-presets)))
      (emit-fixture-prologue stream)
      (dolist (preset presets)
        (emit-fixture-type stream preset presets))
      (emit-fixture-infinity-test-helpers stream)
      (emit-fixture-infinity-metadata-test stream presets)
      (emit-fixture-self-test stream presets)))
  path)

(defun emit-dispatch-prologue (stream)
  (emit-source-hash-manifest stream)
  (format stream "const std = @import(\"std\");~%")
  (format stream "const descriptor = @import(\"descriptor.zig\");~%")
  (format stream "const fixtures = @import(\"generated_fixtures.zig\");~%")
  (format stream "const kernel = @import(\"../kernel.zig\");~%~%")
  (format stream "const allocator = std.heap.c_allocator;~%~%"))

(defun emit-theory-id (stream presets)
  (format stream "/// TheoryId selects one generated fixture through the generic ABI.~%")
  (format stream "pub const TheoryId = enum(u32) {~%")
  (dolist (preset presets)
    (format stream "    ~A = ~D,~%"
            (generated-prefix preset presets)
            (preset-theory-id preset)))
  (format stream "};~%~%")
  (format stream "pub const first_theory_id = TheoryId.~A;~%~%"
          (generated-prefix (first presets) presets)))

(defun emit-context-fields (stream presets)
  (format stream "pub const ContextTag = union(TheoryId) {~%")
  (dolist (preset presets)
    (format stream "    ~A: *fixtures.~A.Context,~%"
            (generated-prefix preset presets)
            (generated-type-name preset presets)))
  (format stream "~%"))

(defun emit-create-method (stream presets)
  (format stream "    pub fn create(id: TheoryId) !ContextTag {~%")
  (format stream "        return switch (id) {~%")
  (dolist (preset presets)
    (format stream "            .~A => .{ .~A = try fixtures.~A.contextCreate(allocator) },~%"
            (generated-prefix preset presets)
            (generated-prefix preset presets)
            (generated-type-name preset presets)))
  (format stream "        };~%")
  (format stream "    }~%~%"))

(defun emit-destroy-method (stream presets)
  (format stream "    pub fn destroy(self: ContextTag) void {~%")
  (format stream "        switch (self) {~%")
  (dolist (preset presets)
    (format stream "            .~A => |inner| fixtures.~A.contextDestroy(inner),~%"
            (generated-prefix preset presets)
            (generated-type-name preset presets)))
  (format stream "        }~%")
  (format stream "    }~%~%"))

(defun emit-symbol-intern-method (stream presets)
  (format stream "    pub fn symbolIntern(self: ContextTag, name: []const u8) !u32 {~%")
  (format stream "        return switch (self) {~%")
  (dolist (preset presets)
    (format stream "            .~A => |inner| fixtures.~A.symbolIntern(inner, name),~%"
            (generated-prefix preset presets)
            (generated-type-name preset presets)))
  (format stream "        };~%")
  (format stream "    }~%~%"))

(defun emit-field-insert-method (stream presets)
  (format stream "    pub fn fieldInsert(self: ContextTag, field_id: u16, coords: []const u32, labels: []const u32) !void {~%")
  (format stream "        switch (self) {~%")
  (dolist (preset presets)
    (format stream "            .~A => |inner| try fixtures.~A.fieldInsert(inner, field_id, coords, labels),~%"
            (generated-prefix preset presets)
            (generated-type-name preset presets)))
  (format stream "        }~%")
  (format stream "    }~%~%"))

(defun emit-normal-ordering-method (stream presets)
  (format stream "    pub fn normalOrdering(self: ContextTag, field_count: usize) !void {~%")
  (format stream "        switch (self) {~%")
  (dolist (preset presets)
    (format stream "            .~A => |inner| try fixtures.~A.normalOrdering(inner, field_count),~%"
            (generated-prefix preset presets)
            (generated-type-name preset presets)))
  (format stream "        }~%")
  (format stream "    }~%~%"))

(defun emit-freeze-method (stream presets)
  (format stream "    pub fn freeze(self: ContextTag) !kernel.Call.MultiOp {~%")
  (format stream "        return switch (self) {~%")
  (dolist (preset presets)
    (format stream "            .~A => |inner| fixtures.~A.operatorListFreeze(inner),~%"
            (generated-prefix preset presets)
            (generated-type-name preset presets)))
  (format stream "        };~%")
  (format stream "    }~%~%"))

(defun emit-count-method (stream presets)
  (format stream "    pub fn count(self: ContextTag, ops: kernel.Call.MultiOp) !usize {~%")
  (format stream "        return switch (self) {~%")
  (dolist (preset presets)
    (format stream "            .~A => fixtures.~A.correlatorCount(ops),~%"
            (generated-prefix preset presets)
            (generated-type-name preset presets)))
  (format stream "        };~%")
  (format stream "    }~%~%"))

(defun emit-run-method (stream presets)
  (format stream "    pub fn run(self: ContextTag, ops: kernel.Call.MultiOp, state: anytype, thunk: anytype) !void {~%")
  (format stream "        switch (self) {~%")
  (dolist (preset presets)
    (format stream "            .~A => try fixtures.~A.correlatorRun(ops, state, thunk),~%"
            (generated-prefix preset presets)
            (generated-type-name preset presets)))
  (format stream "        }~%")
  (format stream "    }~%~%"))

(defun emit-context-end (stream)
  (format stream "};~%~%"))

(defun emit-scalar-atom-name-function (stream presets)
  (format stream "pub fn scalarAtomParameterName(id: TheoryId, atom: u32) ?[]const u8 {~%")
  (format stream "    return switch (id) {~%")
  (dolist (preset presets)
    (format stream "        .~A => fixtures.~A.scalarAtomParameterName(atom),~%"
            (generated-prefix preset presets)
            (generated-type-name preset presets)))
  (format stream "    };~%")
  (format stream "}~%~%"))

(defun emit-theory-id-function (stream presets)
  (format stream "pub fn theoryId(raw: u32) !TheoryId {~%")
  (format stream "    return switch (raw) {~%")
  (dolist (preset presets)
    (format stream "        ~D => .~A,~%"
            (preset-theory-id preset)
            (generated-prefix preset presets)))
  (format stream "        else => error.UnknownTheory,~%")
  (format stream "    };~%")
  (format stream "}~%~%"))

(defun emit-descriptor-for-function (stream presets)
  (format stream "fn descriptorFor(comptime id: TheoryId) descriptor.Descriptor {~%")
  (format stream "    return switch (id) {~%")
  (dolist (preset presets)
    (format stream "        .~A => fixtures.~A.descriptor,~%"
            (generated-prefix preset presets)
            (generated-type-name preset presets)))
  (format stream "    };~%")
  (format stream "}~%~%"))

(defun emit-theory-hash-function (stream presets)
  (declare (ignore presets))
  (format stream "pub fn theoryHash(id: TheoryId) u32 {~%")
  (format stream "    return switch (id) {~%")
  (format stream "        inline else => |case| descriptorFor(case).theory_hash,~%")
  (format stream "    };~%")
  (format stream "}~%~%"))

(defun emit-field-metadata-functions (stream presets)
  (declare (ignore presets))
  (format stream "fn coordinateArity(shape: descriptor.InsertionShape) usize {~%")
  (format stream "    return switch (shape) {~%")
  (format stream "        .single => 1,~%")
  (format stream "        .pair => 2,~%")
  (format stream "    };~%")
  (format stream "}~%~%")
  (format stream "fn fieldById(comptime id: TheoryId, field_id: u16) ?descriptor.Field {~%")
  (format stream "    const desc = descriptorFor(id);~%")
  (format stream "    if (field_id >= desc.fields.len) return null;~%")
  (format stream "    return desc.fields[field_id];~%")
  (format stream "}~%~%")
  (format stream "/// fieldName returns the descriptor field name for ABI diagnostics.~%")
  (format stream "pub fn fieldName(id: TheoryId, field_id: u16) ?[]const u8 {~%")
  (format stream "    return switch (id) {~%")
  (format stream "        inline else => |case| {~%")
  (format stream "            const field = fieldById(case, field_id) orelse return null;~%")
  (format stream "            return descriptorFor(case).symbols[field.symbol];~%")
  (format stream "        },~%")
  (format stream "    };~%")
  (format stream "}~%~%")
  (format stream "/// fieldCoordinateArity returns the descriptor coordinate arity for ABI diagnostics.~%")
  (format stream "pub fn fieldCoordinateArity(id: TheoryId, field_id: u16) ?usize {~%")
  (format stream "    return switch (id) {~%")
  (format stream "        inline else => |case| {~%")
  (format stream "            const field = fieldById(case, field_id) orelse return null;~%")
  (format stream "            return coordinateArity(field.insertion);~%")
  (format stream "        },~%")
  (format stream "    };~%")
  (format stream "}~%~%")
  (format stream "/// fieldLabelArity returns the descriptor label arity for ABI diagnostics.~%")
  (format stream "pub fn fieldLabelArity(id: TheoryId, field_id: u16) ?usize {~%")
  (format stream "    return switch (id) {~%")
  (format stream "        inline else => |case| {~%")
  (format stream "            const field = fieldById(case, field_id) orelse return null;~%")
  (format stream "            return field.labels.len;~%")
  (format stream "        },~%")
  (format stream "    };~%")
  (format stream "}~%~%"))

(defun emit-basis-function (stream presets)
  (declare (ignore presets))
  (format stream "/// basisBackend returns compact basis metadata declared by the generated descriptor.~%")
  (format stream "pub fn basisBackend(comptime id: TheoryId) descriptor.BasisBackend {~%")
  (format stream "    return descriptorFor(id).basis.?;~%")
  (format stream "}~%~%")
  (format stream "/// basis returns the compact basis backend declared by the generated descriptor.~%")
  (format stream "pub fn basis(comptime id: TheoryId) type {~%")
  (format stream "    return descriptor.GeneratedBasis(descriptorFor(id));~%")
  (format stream "}~%"))

(defun write-generated-dispatch
    (&key (path "src/cft-code/correlators/generated_dispatch.zig"))
  "Write the generated Zig dispatcher for registered presets."
  (let ((presets (sorted-presets)))
    (with-open-file (stream path :direction :output :if-exists :supersede
                                 :if-does-not-exist :create)
      (emit-dispatch-prologue stream)
      (emit-theory-id stream presets)
      (emit-context-fields stream presets)
      (emit-create-method stream presets)
      (emit-destroy-method stream presets)
      (emit-symbol-intern-method stream presets)
      (emit-field-insert-method stream presets)
      (emit-normal-ordering-method stream presets)
      (emit-freeze-method stream presets)
      (emit-count-method stream presets)
      (emit-run-method stream presets)
      (emit-context-end stream)
      (emit-scalar-atom-name-function stream presets)
      (emit-theory-id-function stream presets)
      (emit-descriptor-for-function stream presets)
      (emit-theory-hash-function stream presets)
      (emit-field-metadata-functions stream presets)
      (emit-basis-function stream presets)))
  path)

(defun write-generated-sources ()
  "Write all generated Zig modules derived from registered Lisp presets."
  (write-generated-fixtures)
  (write-generated-dispatch))

(defun compile-preset-library
    (&key
       (library-path "zig-out/lib/libstring_code_cft_generated.so")
       (global-cache-dir "/tmp/zig-global-cache")
       (zig "zig"))
  "Emit registered presets and compile the generated C ABI shared library."
  (write-generated-sources)
  (uiop:run-program
   (list zig "build-lib" "-OReleaseFast"
         "--dep" "tensor-code"
         "-Mroot=src/cft-code/generated_abi.zig"
         "-Mtensor-code=src/tensor-code/tensor-code.zig"
         "-lc" "--name" "string_code_cft_generated"
         "-dynamic" "--global-cache-dir" global-cache-dir
         "-femit-bin" library-path)
   :output *standard-output*
   :error-output *error-output*)
  library-path)
