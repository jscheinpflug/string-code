(eval-when (:compile-toplevel :load-toplevel :execute)
  (require :asdf))

(defpackage #:string-code.cft.presets
  (:use #:cl #:string-code.cft.descriptor)
  (:export
   #:define-cft-preset
   #:preset-theory
   #:preset-theory-id-for
   #:write-generated-fixtures
   #:write-generated-sources
   #:compile-preset-library
   #:free-fermion-10
   #:eta-xi-sphere
   #:eta-xi-torus
   #:bc-sphere
   #:free-boson-10))

(in-package #:string-code.cft.presets)

(defstruct preset name builder theory-name hash theory-id)
(defstruct field-shape id insertion labels)

(defparameter *presets* (make-hash-table))
(defparameter *next-theory-id* 1)

(defun preset-options-form-p (form)
  (and (consp form) (keywordp (first form))))

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

(defun next-theory-id-form ()
  (prog1 *next-theory-id*
    (incf *next-theory-id*)))

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

(defmacro define-cft-preset (name &body body)
  "Define NAME as a descriptor preset from CFT declaration forms."
  (let* ((user-options (if (preset-options-form-p (first body)) (first body) nil))
         (forms (if user-options (rest body) body))
         (theory-name (or (getf user-options :name)
                          (generated-theory-name name)))
         (hash (or (getf user-options :hash)
                   (generated-theory-hash theory-name forms)))
         (theory-id (or (getf user-options :theory-id)
                        (next-theory-id-form))))
    `(progn
       (defun ,name ()
         (build-cft-preset ,theory-name ,hash ',forms))
       (setf (gethash ',name *presets*)
             (make-preset :name ',name
                          :builder #',name
                          :theory-name ,theory-name
                          :hash ,hash
                          :theory-id ,theory-id))
       ',name)))

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
    (unless (= field-id
               (add-field theory symbol insertion label-spec statistics
                          :zero-mode (option-value options :zero-mode)
                          :weight weight-id
                          :anti-weight anti-weight-id))
      (error "Field table drift while declaring ~S." id))
    (parse-field-quantum-numbers
     theory quantum-numbers field-id
     (option-value options :quantum-numbers nil))))

(defun parse-parameter-ref (parameters value)
  (etypecase value
    (integer value)
    (symbol (table-get parameters value "parameter"))))

(defun parse-quantum-number-ref (quantum-numbers value)
  (etypecase value
    (integer value)
    (symbol (table-get quantum-numbers value "quantum number"))))

(defun parse-quantum-number-kind (kind)
  (ecase kind
    ((:u1 :u1-charge u1 u1-charge) :u1-charge)
    ((:ade-irrep ade-irrep) :ade-irrep)))

(defun parse-field-ref (fields value)
  (etypecase value
    (integer value)
    (symbol (field-shape-id (table-get fields (field-key value) "field")))))

(defun parse-quantum-value (theory value)
  (etypecase value
    (integer value)
    (rational value)
    (string `(:symbol ,(add-symbol theory value)))
    (symbol `(:symbol ,(add-symbol theory (string-downcase (string value)))))
    (cons
     (ecase (first value)
       ((:rational rational)
        `(:rational ,(second value) ,(third value)))))))

(defun parse-field-quantum-numbers (theory quantum-numbers field-id specs)
  (dolist (spec specs)
    (destructuring-bind (name value) spec
      (add-field-quantum-number theory
                                field-id
                                (parse-quantum-number-ref quantum-numbers name)
                                (parse-quantum-value theory value)))))

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
        `(:mul ,(parse-metadata-id theory parameters fields labels (second form))
               ,(parse-metadata-id theory parameters fields labels (third form))))
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

(defun scalar-factor-product (parameters form)
  (let ((coefficient 1)
        (imaginary-power 0)
        (parameter nil))
    (dolist (factor (scalar-product-factors form))
      (let ((rational (rational-factor factor)))
        (cond
          (rational
           (setf coefficient (* coefficient rational)))
          ((i-symbol-p factor)
           (setf imaginary-power (mod (1+ imaginary-power) 4)))
          ((and (consp factor) (member (first factor) '(:parameter parameter)))
           (when parameter
             (error "Scalar factor has more than one parameter: ~S." form))
           (setf parameter (parse-parameter-ref parameters (second factor))))
          ((symbolp factor)
           (when parameter
             (error "Scalar factor has more than one parameter: ~S." form))
           (setf parameter (parse-parameter-ref parameters factor)))
          (t
           (error "Unsupported scalar factor ~S in ~S." factor form)))))
    (values coefficient imaginary-power parameter)))

(defun parse-scalar-factor (parameters form)
  (if (eq form :one)
      :one
      (multiple-value-bind (coefficient imaginary-power parameter)
          (scalar-factor-product parameters form)
        (cond
          ((and (null parameter) (zerop imaginary-power) (= coefficient 1))
           :one)
          ((and (null parameter) (zerop imaginary-power))
           `(:rational ,(numerator coefficient) ,(denominator coefficient)))
          ((and parameter (zerop imaginary-power) (= coefficient 1))
           `(:parameter ,parameter))
          ((and parameter (zerop imaginary-power) (= coefficient 1/2))
           `(:parameter-half ,parameter))
          ((and parameter (zerop imaginary-power) (= coefficient -1/2))
           `(:neg-parameter-half ,parameter))
          ((and parameter (= imaginary-power 1) (= coefficient -1/2))
           `(:neg-i-parameter-half ,parameter))
          (t
           (error "Scalar factor cannot be lowered to the current compact descriptor: ~S."
                  form))))))

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
                          ,(third form)))))

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

(defun expression-product-factors (form)
  (if (and (consp form) (member (first form) '(* :mul mul)))
      (loop for factor in (rest form) append (expression-product-factors factor))
      (list form)))

(defun parse-expression-term (parameters label-env coordinate-env expression residuals)
  (let ((scalar-factors nil)
        (coordinates nil)
        (tensors nil))
    (dolist (factor (expression-product-factors expression))
      (let ((coordinate (parse-expression-coordinate coordinate-env factor))
            (tensor (parse-expression-tensor label-env factor)))
        (cond
          (coordinate (push coordinate coordinates))
          (tensor (push tensor tensors))
          (t (push factor scalar-factors)))))
    (make-wick-term
     :scalars (list (parse-scalar-factor
                     parameters
                     (if scalar-factors
                         `(* ,@(reverse scalar-factors))
                         :one)))
     :coordinates (reverse coordinates)
     :tensors (reverse tensors)
     :residuals residuals)))

(defun parse-term (parameters labels left-field right-field form)
  (unless (eq (first form) 'term)
    (error "Expected TERM form, got ~S." form))
  (let ((body (rest form)))
    (make-wick-term
     :scalars (mapcar (lambda (item) (parse-scalar-factor parameters item))
                      (option-value body :scalars '(:one)))
     :coordinates (mapcar #'parse-coordinate-factor
                          (option-value body :coordinates nil))
     :tensors (mapcar (lambda (item)
                        (parse-tensor-factor labels left-field right-field item))
                      (option-value body :tensors nil))
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
         (list (parse-expression-term parameters label-env coordinate-env
                                      expression
                                      (option-value options :residuals nil)))))
      (destructuring-bind (left-field right-field) left
        (add-wick-rule
         theory
         surface
         (parse-field-ref fields left-field)
         (parse-field-ref fields right-field)
         (mapcar (lambda (term)
                   (parse-term parameters labels left-field right-field term))
                 body)))))

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
                               :group (option-value (cdddr form) :group))))
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
       (destructuring-bind (kind consumes &rest options) body
         (add-zero-mode theory
                        surface
                        kind
                        (mapcar (lambda (field) (parse-field-ref fields field)) consumes)
                        :normalization (option-value options :normalization :one)
                        :two-pi-power (option-value options :two-pi-power 0)))))))

(defun build-cft-preset (name hash forms)
  (let ((theory (make-theory name hash))
        (parameters (make-hash-table))
        (quantum-numbers (make-hash-table))
        (surfaces (make-hash-table))
        (fields (make-hash-table :test #'equal))
        (labels (make-hash-table :test #'equal)))
    (dolist (form forms theory)
      (apply-preset-form
       theory parameters quantum-numbers surfaces fields labels form))))

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

(defun emit-fixture-prologue (stream)
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

(defun emit-fixture-type (stream preset presets)
  (emit-zig-descriptor (funcall (preset-builder preset)) stream
                       :prefix (generated-prefix preset presets)
                       :descriptor-name (generated-descriptor-name preset presets))
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

(defun emit-dispatch-prologue (stream)
  (format stream "const std = @import(\"std\");~%")
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

(defun emit-theory-hash-function (stream presets)
  (format stream "pub fn theoryHash(id: TheoryId) u32 {~%")
  (format stream "    return switch (id) {~%")
  (dolist (preset presets)
    (format stream "        .~A => fixtures.~A.theoryHash(),~%"
            (generated-prefix preset presets)
            (generated-type-name preset presets)))
  (format stream "    };~%")
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
      (emit-theory-hash-function stream presets)))
  path)

(defun write-generated-fixtures
    (&key (path "src/cft-code/correlators/generated_fixtures.zig"))
  "Write the Zig fixture module from registered Lisp presets."
  (with-open-file (stream path :direction :output :if-exists :supersede
                               :if-does-not-exist :create)
    (let ((presets (sorted-presets)))
      (emit-fixture-prologue stream)
      (dolist (preset presets)
        (emit-fixture-type stream preset presets))
      (emit-fixture-self-test stream presets)))
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
