(defpackage #:string-code.cft.descriptor
  (:use #:cl)
  (:export
   #:make-theory
   #:add-symbol
   #:add-parameter
   #:add-quantum-number
   #:add-field-quantum-number
   #:add-surface
   #:add-field
   #:add-metadata
   #:add-wick-rule
   #:add-zero-mode
   #:make-wick-term
   #:emit-zig-descriptor
   #:write-build-manifest
   #:load-generated-library
   #:make-runtime-context
   #:destroy-runtime-context
   #:set-runtime-constant
   #:intern-runtime-symbol
   #:insert-runtime-field
   #:normal-order-runtime-field
   #:freeze-runtime-operators
   #:run-correlator
   #:count-correlator
   #:correlator-expression
   #:collect-correlator
   #:unsupported-basis-filter
   #:make-product-runtime
   #:basis-count
   #:basis))

(in-package #:string-code.cft.descriptor)

(defstruct (theory (:constructor %make-theory))
  name
  hash
  (symbols (make-array 0 :adjustable t :fill-pointer 0))
  (parameters nil)
  (quantum-numbers nil)
  (field-quantum-numbers nil)
  (surfaces nil)
  (fields nil)
  (metadata nil)
  (wick-rules nil)
  (zero-modes nil)
  (result-symbols nil))

(defstruct parameter id symbol role)
(defstruct quantum-number id symbol kind group-symbol modulus representation-space)
(defstruct field-quantum-number field quantum-number value)
(defstruct surface id kind coordinate-model modular-parameter)
(defstruct label-schema id role symbol)
(defstruct field id symbol insertion labels statistics zero-mode weight anti-weight)
(defstruct wick-term scalars coordinates tensors actions residuals)
(defstruct wick-rule surface left right terms constraints)
(defstruct zero-mode surface kind consumes normalization two-pi-power)
(defstruct (runtime-context (:constructor %make-runtime-context))
  handle
  theory-id
  basis-metadata
  constants
  (scalar-atom-names (make-hash-table))
  scalar-monomials
  (symbols (make-array 0 :adjustable t :fill-pointer 0)))

(define-condition unsupported-basis-filter (error)
  ((filter :initarg :filter :reader unsupported-basis-filter-filter))
  (:report (lambda (condition stream)
             (format stream "Unsupported basis filter: ~S."
                     (unsupported-basis-filter-filter condition)))))

(defun descriptor-symbol-name (value)
  (etypecase value
    (string value)
    (symbol (string-downcase (string value)))))

(defun add-symbol (theory name)
  (let ((symbols (theory-symbols theory))
        (text (descriptor-symbol-name name)))
    (or (loop for index below (length symbols)
              when (string= (aref symbols index) text)
                return index)
        (vector-push-extend text symbols))))

(defun make-theory (name hash)
  (let ((theory (%make-theory :name name :hash hash)))
    (add-symbol theory name)
    theory))

(defun add-parameter (theory symbol role)
  (let ((id (length (theory-parameters theory))))
    (push (make-parameter :id id :symbol (add-symbol theory symbol) :role role)
          (theory-parameters theory))
    id))

(defun add-quantum-number (theory symbol kind &key group modulus representation-space)
  (let ((id (length (theory-quantum-numbers theory))))
    (push (make-quantum-number
           :id id
           :symbol (add-symbol theory (descriptor-symbol-name symbol))
           :kind kind
           :group-symbol (when group (add-symbol theory (descriptor-symbol-name group)))
           :modulus (or modulus 0)
           :representation-space (or representation-space 0))
          (theory-quantum-numbers theory))
    id))

(defun add-field-quantum-number (theory field quantum-number value)
  (push (make-field-quantum-number
         :field field
         :quantum-number quantum-number
         :value value)
        (theory-field-quantum-numbers theory)))

(defun add-surface (theory kind coordinate-model &key modular-parameter)
  (let ((id (length (theory-surfaces theory))))
    (push (make-surface :id id :kind kind :coordinate-model coordinate-model
                        :modular-parameter modular-parameter)
          (theory-surfaces theory))
    id))

(defun role-of-label (label)
  (etypecase label
    (label-schema (label-schema-role label))
    (cons (second label))
    (symbol :vector-index)))

(defun label-name (label)
  (etypecase label
    (label-schema (label-schema-symbol label))
    (cons (first label))
    (symbol label)))

(defun make-label-rows (theory labels)
  (loop for label in labels
        for id from 0
        collect (make-label-schema
                 :id id
                 :role (role-of-label label)
                 :symbol (add-symbol theory (string-downcase (string (label-name label)))))))

(defun add-field (theory symbol insertion labels statistics &key zero-mode weight anti-weight)
  (let ((id (length (theory-fields theory))))
    (push (make-field :id id
                      :symbol (add-symbol theory symbol)
                      :insertion insertion
                      :labels (make-label-rows theory labels)
                      :statistics statistics
                      :zero-mode zero-mode
                      :weight weight
                      :anti-weight anti-weight)
          (theory-fields theory))
    id))

(defun metadata-symbol-id (theory value)
  (etypecase value
    (integer value)
    (string (add-symbol theory value))
    (symbol (add-symbol theory (string-downcase (string value))))))

(declaim (ftype function add-metadata))

(defun normalized-metadata-form (theory form)
  (etypecase form
    (integer form)
    (cons
     (case (first form)
       (:rational form)
       (:parameter form)
       (:field-label form)
       (:add (list :add
                   (add-metadata theory (second form))
                   (add-metadata theory (third form))))
       (:mul (list :mul
                   (add-metadata theory (second form))
                   (add-metadata theory (third form))))
       (:bilinear (list :bilinear
                        (add-metadata theory (second form))
                        (add-metadata theory (third form))
                        (metadata-symbol-id theory (fourth form))))
       (otherwise (error "Unknown metadata form ~S." form))))))

(defun metadata-row-id (theory row)
  (let ((count (length (theory-metadata theory))))
    (loop for item in (theory-metadata theory)
          for index from 0
          when (equal item row)
            return (- count index 1))))

(defun add-metadata (theory form)
  (let ((row (normalized-metadata-form theory form)))
    (if (integerp row)
        row
        (or (metadata-row-id theory row)
            (let ((id (length (theory-metadata theory))))
              (push row (theory-metadata theory))
              id)))))

(defun add-wick-rule (theory surface left right terms &key constraints)
  (push (make-wick-rule :surface surface :left left :right right :terms terms
                        :constraints constraints)
        (theory-wick-rules theory)))

(defun add-zero-mode (theory surface kind consumes &key (normalization :one) (two-pi-power 0))
  (push (make-zero-mode :surface surface :kind kind :consumes consumes
                        :normalization normalization :two-pi-power two-pi-power)
        (theory-zero-modes theory)))

(defun by-id (items reader)
  (sort (copy-list items) #'< :key reader))

(defun zig-keyword (value)
  (substitute #\_ #\- (string-downcase (string value))))

(defun emit-id-list (stream ids)
  (format stream "&.{")
  (loop for id in ids for first = t then nil
        do (format stream "~:[, ~;~]~D" first id))
  (format stream "}"))

(defun emit-symbols (stream theory var)
  (format stream "const ~A = [_][]const u8{ " var)
  (loop for index below (length (theory-symbols theory))
        for first = t then nil
        do (format stream "~:[, ~;~]~S" first (aref (theory-symbols theory) index)))
  (format stream " };~%"))

(defun emit-label (stream label)
  (format stream ".{ .id = ~D, .role = .~A, .symbol = ~D }"
          (label-schema-id label)
          (zig-keyword (label-schema-role label))
          (label-schema-symbol label)))

(defun emit-field (stream field)
  (format stream ".{ .id = ~D, .symbol = ~D, .insertion = .~A, .labels = &.{"
          (field-id field) (field-symbol field) (zig-keyword (field-insertion field)))
  (loop for label in (field-labels field) for first = t then nil
        do (progn
             (unless first (format stream ", "))
             (emit-label stream label)))
  (format stream "}, .statistics = .~A"
          (zig-keyword (field-statistics field)))
  (when (field-zero-mode field)
    (format stream ", .zero_mode_consumable = true"))
  (when (field-weight field)
    (format stream ", .weight = ~D" (field-weight field)))
  (when (field-anti-weight field)
    (format stream ", .anti_weight = ~D" (field-anti-weight field)))
  (format stream " }"))

(defun emit-surface (stream surface)
  (format stream ".{ .id = ~D, .kind = .~A, .coordinate_model = .~A"
          (surface-id surface)
          (zig-keyword (surface-kind surface))
          (zig-keyword (surface-coordinate-model surface)))
  (when (surface-modular-parameter surface)
    (format stream ", .modular_parameter = ~D" (surface-modular-parameter surface)))
  (format stream " }"))

(defun emit-parameter (stream parameter)
  (format stream ".{ .id = ~D, .symbol = ~D, .role = .~A }"
          (parameter-id parameter)
          (parameter-symbol parameter)
          (zig-keyword (parameter-role parameter))))

(defun emit-quantum-number (stream number)
  (format stream ".{ .id = ~D, .symbol = ~D, .kind = .~A"
          (quantum-number-id number)
          (quantum-number-symbol number)
          (zig-keyword (quantum-number-kind number)))
  (when (quantum-number-group-symbol number)
    (format stream ", .group_symbol = ~D" (quantum-number-group-symbol number)))
  (unless (zerop (quantum-number-modulus number))
    (format stream ", .modulus = ~D" (quantum-number-modulus number)))
  (unless (zerop (quantum-number-representation-space number))
    (format stream ", .representation_space = ~D" (quantum-number-representation-space number)))
  (format stream " }"))

(defun emit-rational-row (stream numerator denominator)
  (format stream ".{ .numerator = ~D, .denominator = ~D }" numerator denominator))

(defun emit-quantum-value (stream value)
  (etypecase value
    (integer
     (format stream ".{ .integer = ~D }" value))
    (rational
     (format stream ".{ .rational = ")
     (emit-rational-row stream (numerator value) (denominator value))
     (format stream " }"))
    (cons
     (ecase (first value)
       (:symbol
        (format stream ".{ .symbol = ~D }" (second value)))
       (:rational
        (format stream ".{ .rational = ")
        (emit-rational-row stream (second value) (third value))
        (format stream " }"))))))

(defun emit-field-quantum-number (stream item)
  (format stream ".{ .field = ~D, .quantum_number = ~D, .value = "
          (field-quantum-number-field item)
          (field-quantum-number-quantum-number item))
  (emit-quantum-value stream (field-quantum-number-value item))
  (format stream " }"))

(defun emit-metadata (stream form)
  (case (first form)
    (:rational
     (format stream ".{ .rational = ")
     (emit-rational-row stream (second form) (third form))
     (format stream " }"))
    (:parameter
     (format stream ".{ .parameter = ~D }" (second form)))
    (:field-label
     (format stream ".{ .field_label = .{ .field = ~D, .label = ~D } }"
             (second form) (third form)))
    (:add
     (format stream ".{ .add = .{ .left = ~D, .right = ~D } }"
             (second form) (third form)))
    (:mul
     (format stream ".{ .mul = .{ .left = ~D, .right = ~D } }"
             (second form) (third form)))
    (:bilinear
     (format stream ".{ .bilinear = .{ .left = ~D, .right = ~D, .form_symbol = ~D } }"
             (second form) (third form) (fourth form)))
    (otherwise (error "Unknown metadata form ~S." form))))

(defun side-name (value)
  (ecase value
    (:left "left")
    (:right "right")))

(defun coordinate-slot-name (value)
  (ecase value
    (:position "position")
    (:holomorphic "holomorphic")
    (:antiholomorphic "antiholomorphic")))

(defun emit-coordinate-ref (stream value)
  (etypecase value
    (symbol
     (format stream ".{ .side = .~A, .slot = .position }" (side-name value)))
    (cons
     (format stream ".{ .side = .~A, .slot = .~A }"
             (side-name (first value))
             (coordinate-slot-name (second value))))))

(defun emit-label-ref (stream value)
  (format stream ".{ .side = .~A, .slot = ~D }"
          (side-name (first value)) (second value)))

(defun emit-zig-list (stream values printer)
  (format stream "&.{")
  (loop for value in values for first = t then nil
        do (progn
             (unless first (format stream ", "))
             (funcall printer stream value)))
  (format stream "}"))

(defun emit-scalar-factor (stream form)
  (etypecase form
    (symbol
     (ecase form
       (:one (format stream ".one"))))
    (cons
     (ecase (first form)
       (:rational
        (format stream ".{ .rational = ")
        (emit-rational-row stream (second form) (third form))
        (format stream " }"))
       (:parameter
        (format stream ".{ .parameter = ~D }" (second form)))
       (:neg-parameter-half
        (format stream ".{ .neg_parameter_half = ~D }" (second form)))
       (:neg-i-parameter-half
        (format stream ".{ .neg_i_parameter_half = ~D }" (second form)))
       (:parameter-half
        (format stream ".{ .parameter_half = ~D }" (second form)))))))

(defun derive-left-p (value)
  (and (consp value) (member :derive-left value)))

(defun derive-right-p (value)
  (and (consp value) (member :derive-right value)))

(defun emit-coordinate-factor (theory stream form)
  (ecase (first form)
    (:difference-power
     (format stream ".{ .difference_power = .{ .left = ")
     (emit-coordinate-ref stream (second form))
     (format stream ", .right = ")
     (emit-coordinate-ref stream (third form))
     (format stream ", .exponent = ~D" (fourth form))
     (when (derive-left-p form)
       (format stream ", .derive_left = true"))
     (when (derive-right-p form)
       (format stream ", .derive_right = true"))
     (format stream " } }"))
    (:named-kernel
     (format stream ".{ .named_kernel = .{ .symbol = ~D, .left = "
             (metadata-symbol-id theory (second form)))
     (emit-coordinate-ref stream (third form))
     (format stream ", .right = ")
     (emit-coordinate-ref stream (fourth form))
     (when (derive-left-p form)
       (format stream ", .derive_left = true"))
     (when (derive-right-p form)
       (format stream ", .derive_right = true"))
     (format stream " } }"))
    (:green-exponential
     (format stream ".{ .green_exponential = .{ .left = ")
     (emit-coordinate-ref stream (second form))
     (format stream ", .right = ")
     (emit-coordinate-ref stream (third form))
     (format stream " } }"))
    (:logarithm
     (format stream ".{ .logarithm = .{ .left = ")
     (emit-coordinate-ref stream (second form))
     (format stream ", .right = ")
     (emit-coordinate-ref stream (third form))
     (when (derive-left-p form)
       (format stream ", .derive_left = true"))
     (when (derive-right-p form)
       (format stream ", .derive_right = true"))
     (format stream " } }"))))

(defun emit-tensor-factor (stream form)
  (ecase (first form)
    (:metric
     (format stream ".{ .metric = .{ .left = ")
     (emit-label-ref stream (second form))
     (format stream ", .right = ")
     (emit-label-ref stream (third form))
     (format stream " } }"))
    (:momentum-index
     (format stream ".{ .momentum_index = .{ .momentum = ")
     (emit-label-ref stream (second form))
     (format stream ", .index = ")
     (emit-label-ref stream (third form))
     (format stream " } }"))
    (:momentum-pair
     (format stream ".{ .momentum_pair = .{ .left = ")
     (emit-label-ref stream (second form))
     (format stream ", .right = ")
     (emit-label-ref stream (third form))
     (format stream " } }"))))

(defun emit-side (stream side)
  (format stream ".~A" (side-name side)))

(defun emit-index-constraint (stream form)
  (destructuring-bind (left-slot right-slot constraint) form
    (format stream ".{ .left_slot = ~D, .right_slot = ~D, .constraint = .~A }"
            left-slot right-slot (zig-keyword constraint))))

(defun emit-wick-term (theory stream term)
  (format stream ".{ .scalars = ")
  (emit-zig-list stream (or (wick-term-scalars term) '(:one)) #'emit-scalar-factor)
  (format stream ", .coordinates = ")
  (emit-zig-list stream (wick-term-coordinates term)
                 (lambda (out form) (emit-coordinate-factor theory out form)))
  (format stream ", .tensors = ")
  (emit-zig-list stream (wick-term-tensors term) #'emit-tensor-factor)
  (format stream ", .residuals = ")
  (emit-zig-list stream (wick-term-residuals term) #'emit-side)
  (format stream " }"))

(defun emit-wick-rule (stream rule term-var)
  (format stream ".{ .surface = ~D, .left = ~D, .right = ~D, .terms = &~A"
          (wick-rule-surface rule)
          (wick-rule-left rule)
          (wick-rule-right rule)
          term-var)
  (when (wick-rule-constraints rule)
    (format stream ", .index_constraints = ")
    (emit-zig-list stream (wick-rule-constraints rule) #'emit-index-constraint))
  (format stream " }"))

(defun emit-zero-mode (stream rule)
  (format stream ".{ .surface = ~D, .kind = .~A, .consumes = "
          (zero-mode-surface rule)
          (zig-keyword (zero-mode-kind rule)))
  (emit-id-list stream (zero-mode-consumes rule))
  (unless (eq (zero-mode-normalization rule) :one)
    (format stream ", .normalization = ")
    (emit-scalar-factor stream (zero-mode-normalization rule)))
  (unless (zerop (zero-mode-two-pi-power rule))
    (format stream ", .two_pi_power = ~D" (zero-mode-two-pi-power rule)))
  (format stream " }"))

(defun emit-row-array (stream type var rows printer)
  (format stream "const ~A = [_]d.~A{~%" var type)
  (dolist (row rows)
    (format stream "    ")
    (funcall printer stream row)
    (format stream ",~%"))
  (format stream "};~%"))

(defun prepare-coordinate-symbols (theory form)
  (when (eq (first form) :named-kernel)
    (metadata-symbol-id theory (second form))))

(defun prepare-emitter-symbols (theory)
  (dolist (rule (theory-wick-rules theory))
    (dolist (term (wick-rule-terms rule))
      (dolist (factor (wick-term-coordinates term))
        (prepare-coordinate-symbols theory factor)))))

(defun emit-wick-term-arrays (stream theory rules prefix)
  (loop for rule in rules
        for index from 0
        for var = (format nil "~A_terms_~D" prefix index)
        collect var
        do (emit-row-array stream "WickTerm" var (wick-rule-terms rule)
                           (lambda (out term) (emit-wick-term theory out term)))))

(defun emit-zig-descriptor (theory stream &key (descriptor-name "generated_descriptor") (prefix "generated"))
  (prepare-emitter-symbols theory)
  (let ((symbols-var (format nil "~A_symbols" prefix))
        (parameters-var (format nil "~A_parameters" prefix))
        (quantum-numbers-var (format nil "~A_quantum_numbers" prefix))
        (field-quantum-numbers-var (format nil "~A_field_quantum_numbers" prefix))
        (surfaces-var (format nil "~A_surfaces" prefix))
        (fields-var (format nil "~A_fields" prefix))
        (metadata-var (format nil "~A_metadata" prefix))
        (wick-var (format nil "~A_wick" prefix))
        (zero-modes-var (format nil "~A_zero_modes" prefix)))
  (emit-symbols stream theory symbols-var)
  (emit-row-array stream "Parameter" parameters-var
                  (by-id (theory-parameters theory) #'parameter-id)
                  #'emit-parameter)
  (emit-row-array stream "QuantumNumber" quantum-numbers-var
                  (by-id (theory-quantum-numbers theory) #'quantum-number-id)
                  #'emit-quantum-number)
  (emit-row-array stream "FieldQuantumNumber" field-quantum-numbers-var
                  (reverse (theory-field-quantum-numbers theory))
                  #'emit-field-quantum-number)
  (emit-row-array stream "Surface" surfaces-var
                  (by-id (theory-surfaces theory) #'surface-id)
                  #'emit-surface)
  (emit-row-array stream "Field" fields-var
                  (by-id (theory-fields theory) #'field-id)
                  #'emit-field)
  (emit-row-array stream "MetadataExpr" metadata-var
                  (reverse (theory-metadata theory))
                  #'emit-metadata)
  (let* ((rules (reverse (theory-wick-rules theory)))
         (term-vars (emit-wick-term-arrays stream theory rules prefix)))
    (format stream "const ~A = [_]d.WickRule{~%" wick-var)
    (loop for rule in rules
          for term-var in term-vars
          do (progn
               (format stream "    ")
               (emit-wick-rule stream rule term-var)
               (format stream ",~%")))
    (format stream "};~%"))
  (emit-row-array stream "ZeroModeRule" zero-modes-var
                  (reverse (theory-zero-modes theory))
                  #'emit-zero-mode)
  (format stream "pub const ~A = d.Descriptor{~%" descriptor-name)
  (format stream "    .theory_symbol = 0,~%")
  (format stream "    .theory_hash = ~D,~%" (theory-hash theory))
  (format stream "    .symbols = &~A,~%" symbols-var)
  (format stream "    .parameters = &~A,~%" parameters-var)
  (format stream "    .quantum_numbers = &~A,~%" quantum-numbers-var)
  (format stream "    .field_quantum_numbers = &~A,~%" field-quantum-numbers-var)
  (format stream "    .surfaces = &~A,~%" surfaces-var)
  (format stream "    .fields = &~A,~%" fields-var)
  (format stream "    .metadata = &~A,~%" metadata-var)
  (format stream "    .wick_rules = &~A,~%" wick-var)
  (format stream "    .zero_modes = &~A,~%" zero-modes-var)
  (format stream "};~%")))

(defun write-build-manifest (path &key source-hash zig-path library-path)
  (with-open-file (stream path :direction :output)
    (format stream "(:source-hash ~S :zig-path ~S :library-path ~S)~%"
            source-hash zig-path library-path)))

(defvar *abi-bound* nil)
(defvar *abi-callback-pointer* nil)
(defvar *abi-chunk-callback-pointer* nil)
(defvar *abi-basis-callback-pointer* nil)
(defvar *abi-sinks* (make-hash-table))
(defvar *next-abi-sink-id* 0)
(defvar *event-size* 0)
(defvar *factor-size* 0)
(defvar *name-size* 0)
(defvar *name-ptr-offset* 0)
(defvar *name-len-offset* 0)
(defvar *term-size* 0)
(defvar *basis-mode-size* 0)
(defparameter *event-kinds*
  #(:sum-term-begin :sum-term-end :wick-term-begin :wick-term-end
    :scalar :coordinate :tensor :zero-mode :residual-operator))

(declaim
 (ftype function
        set-mem-aref* mem-ref* foreign-slot-value* null-pointer-p*
        set-foreign-slot-value* pointer-address* inc-pointer* foreign-type-size* event-pointer-at
        name-pointer-at term-pointer-at basis-mode-pointer-at term-expression
        %abi-last-error %abi-context-create
        %abi-context-destroy %abi-scalar-atom-name
        %abi-symbol-intern %abi-field-insert
        %abi-normal-ordering %abi-operator-list-freeze
        %abi-correlator-count %abi-correlator-run
        %abi-correlator-run-buffered %abi-correlator-expression-records
        %abi-expression-buffer-free %abi-basis-count
        %abi-basis-run-compact %abi-basis-text
        %abi-basis-text-free))

(declaim
 (ftype function
        factor-name-token-by-id factor-coordinate-expression-values
        factor-tensor-expression-values factor-scalar-expression-values
        factor-zero-mode-expression-values factor-expression-values
        term-product-expression))

(defun cffi-package ()
  (or (find-package '#:cffi)
      (error "CFFI is required to use generated libraries.")))

(defun cffi-symbol (name)
  (intern name (cffi-package)))

(defun foreign-string-to-lisp* (&rest args)
  (apply (symbol-function (cffi-symbol "FOREIGN-STRING-TO-LISP")) args))

(defun foreign-alloc* (&rest args)
  (apply (symbol-function (cffi-symbol "FOREIGN-ALLOC")) args))

(defun foreign-free* (pointer)
  (funcall (symbol-function (cffi-symbol "FOREIGN-FREE")) pointer))

(defun event-from-pointer (pointer)
  (let* ((type '(:struct generated-event))
         (kind (foreign-slot-value* pointer type 'kind))
         (name-pointer (foreign-slot-value* pointer type 'name-ptr))
         (name-length (foreign-slot-value* pointer type 'name-len))
         (name (and (> name-length 0)
                    (not (null-pointer-p* name-pointer))
                    (foreign-string-to-lisp* name-pointer :count name-length))))
    (list :kind (aref *event-kinds* kind)
          :a (foreign-slot-value* pointer type 'a)
          :b (foreign-slot-value* pointer type 'b)
          :c (foreign-slot-value* pointer type 'c)
          :d (foreign-slot-value* pointer type 'd)
          :name name)))

(defun ensure-abi-bindings ()
  (unless *abi-bound*
    (let ((defcstruct (cffi-symbol "DEFCSTRUCT"))
          (defcfun (cffi-symbol "DEFCFUN"))
          (defcallback (cffi-symbol "DEFCALLBACK"))
          (callback (cffi-symbol "CALLBACK"))
          (inc-pointer (cffi-symbol "INC-POINTER"))
          (foreign-type-size (cffi-symbol "FOREIGN-TYPE-SIZE"))
	          (foreign-slot-offset (cffi-symbol "FOREIGN-SLOT-OFFSET"))
	          (with-foreign-slots (cffi-symbol "WITH-FOREIGN-SLOTS"))
	          (mem-aref (cffi-symbol "MEM-AREF"))
          (mem-ref (cffi-symbol "MEM-REF"))
          (foreign-slot-value (cffi-symbol "FOREIGN-SLOT-VALUE"))
          (null-pointer-p (cffi-symbol "NULL-POINTER-P"))
          (pointer-address (cffi-symbol "POINTER-ADDRESS")))
      (eval `(,defcstruct generated-event
               (kind :uint8)
               (a :uint32)
               (b :uint32)
               (c :uint32)
               (d :int32)
               (name-ptr :pointer)
               (name-len :size)))
      (eval `(,defcstruct generated-factor
               (kind :uint8)
               (a :uint32)
               (b :uint32)
               (c :uint32)
               (d :int32)
               (name-id :uint32)))
      (eval `(,defcstruct generated-name
               (ptr :pointer)
               (len :size)))
      (eval `(,defcstruct generated-term
               (first-factor :size)
               (factor-count :size)))
      (eval `(,defcstruct generated-basis-filter
               (slot :uint8)
               (value :int32)))
      (eval `(,defcstruct generated-basis-mode
               (mode-index :uint32)
               (id :uint32)
               (component :uint16)
               (label :uint16)
               (weight-ticks :uint32)
               (body :uint32)
               (name-ptr :pointer)
               (name-len :size)))
      (eval `(,defcstruct generated-basis-record
               (presentation :uint16)
               (seed :uint16)
               (seed-body :uint32)
               (base-weight-ticks :int32)
               (weight-ticks :int32)
               (level-ticks :uint32)
               (base-quantum-ptr :pointer)
               (base-quantum-len :size)
               (quantum-ptr :pointer)
               (quantum-len :size)
               (mode-ptr :pointer)
               (mode-len :size)))
      (eval `(defun set-mem-aref* (pointer type index value)
               (setf (,mem-aref pointer type index) value)))
      (eval `(defun mem-ref* (pointer type)
               (,mem-ref pointer type)))
      (eval `(defun foreign-slot-value* (pointer type slot)
               (,foreign-slot-value pointer type slot)))
      (eval `(defun set-foreign-slot-value* (pointer type slot value)
               (setf (,foreign-slot-value pointer type slot) value)))
      (eval `(defun null-pointer-p* (pointer)
               (,null-pointer-p pointer)))
      (eval `(defun pointer-address* (pointer)
               (,pointer-address pointer)))
      (eval `(defun inc-pointer* (pointer offset)
               (,inc-pointer pointer offset)))
      (eval `(defun foreign-type-size* (type)
               (,foreign-type-size type)))
      (eval `(defun event-pointer-at (events index)
               (,inc-pointer events (* index *event-size*))))
      (eval `(defun name-pointer-at (names index)
               (,inc-pointer names (* index *name-size*))))
      (eval `(defun term-pointer-at (terms index)
               (,inc-pointer terms (* index *term-size*))))
      (eval `(defun basis-mode-pointer-at (modes index)
               (,inc-pointer modes (* index *basis-mode-size*))))
      (setf *event-size* (eval `(,foreign-type-size '(:struct generated-event)))
            *factor-size* (eval `(,foreign-type-size '(:struct generated-factor)))
            *name-size* (eval `(,foreign-type-size '(:struct generated-name)))
            *name-ptr-offset* (eval `(,foreign-slot-offset '(:struct generated-name) 'ptr))
            *name-len-offset* (eval `(,foreign-slot-offset '(:struct generated-name) 'len))
            *term-size* (eval `(,foreign-type-size '(:struct generated-term)))
            *basis-mode-size* (eval `(,foreign-type-size '(:struct generated-basis-mode))))
      (eval `(defun term-expression (builder factors names term)
               (declare (optimize (speed 3) (safety 1) (debug 0)))
               (,with-foreign-slots ((first-factor factor-count) term (:struct generated-term))
                 (let ((items nil)
                       (scalars nil)
                       (greens nil)
                       (momentum-pairs nil)
                       (others nil))
                   (loop for index from first-factor below (+ first-factor factor-count)
                         for factor = (,inc-pointer factors (* index *factor-size*))
                         do (,with-foreign-slots ((kind a b c d name-id) factor (:struct generated-factor))
                              (let ((expr (factor-expression-values builder names kind a b c d name-id)))
                                (when (and expr (not (eql expr 1)))
                                  (push expr items)
                                  (cond
                                    ((= kind 4) (push expr scalars))
                                    ((and (= kind 5) (exp-green-expression-p expr))
                                     (push expr greens))
                                    ((and (= kind 6) (momentum-pair-expression-p expr))
                                     (push expr momentum-pairs))
                                    (t (push expr others)))))))
                   (term-product-expression items scalars greens momentum-pairs others)))))
      (eval `(,defcfun ("sc_generated_last_error" %abi-last-error) :pointer))
      (eval `(,defcfun ("sc_generated_context_create" %abi-context-create) :pointer
               (theory-id :uint32)))
      (eval `(,defcfun ("sc_generated_context_destroy" %abi-context-destroy) :void
               (context :pointer)))
      (eval `(,defcfun ("sc_generated_scalar_atom_name" %abi-scalar-atom-name) :int
               (theory-id :uint32)
               (atom :uint32)
               (out-name :pointer)
               (out-name-len :pointer)))
      (eval `(,defcfun ("sc_generated_symbol_intern" %abi-symbol-intern) :int
               (context :pointer)
               (name :string)
               (name-len :size)
               (out-symbol :pointer)))
      (eval `(,defcfun ("sc_generated_field_insert" %abi-field-insert) :int
               (context :pointer)
               (field-id :uint16)
               (coordinates :pointer)
               (coordinate-count :size)
               (labels :pointer)
               (label-count :size)))
      (eval `(,defcfun ("sc_generated_normal_ordering" %abi-normal-ordering) :int
               (context :pointer)
               (field-count :size)))
      (eval `(,defcfun ("sc_generated_operator_list_freeze" %abi-operator-list-freeze) :int
               (context :pointer)))
      (eval `(,defcfun ("sc_generated_correlator_count" %abi-correlator-count) :int
               (context :pointer)
               (out-count :pointer)))
      (eval `(,defcfun ("sc_generated_correlator_run" %abi-correlator-run) :int
               (context :pointer)
               (payload :pointer)
               (callback :pointer)))
      (eval `(,defcfun ("sc_generated_correlator_run_buffered" %abi-correlator-run-buffered) :int
               (context :pointer)
               (payload :pointer)
               (callback :pointer)))
      (eval `(,defcfun ("sc_generated_correlator_expression_records" %abi-correlator-expression-records) :int
               (context :pointer)
               (out-terms :pointer)
               (out-term-count :pointer)
               (out-factors :pointer)
               (out-factor-count :pointer)
               (out-names :pointer)
               (out-name-count :pointer)))
      (eval `(,defcfun ("sc_generated_expression_buffer_free" %abi-expression-buffer-free) :void
               (terms :pointer)
               (term-count :size)
               (factors :pointer)
               (factor-count :size)
               (names :pointer)
               (name-count :size)))
      (eval `(,defcfun ("sc_generated_basis_count" %abi-basis-count) :int
               (theory-id :uint32)
               (weight-kind :uint8)
               (weight-ticks :int32)
               (max-word-length :uint16)
               (level-match :uint8)
               (filters :pointer)
               (filter-count :size)
               (out-count :pointer)))
      (eval `(,defcfun ("sc_generated_basis_run_compact" %abi-basis-run-compact) :int
               (theory-id :uint32)
               (weight-kind :uint8)
               (weight-ticks :int32)
               (max-word-length :uint16)
               (level-match :uint8)
               (filters :pointer)
               (filter-count :size)
               (payload :pointer)
               (callback :pointer)))
      (eval `(,defcfun ("sc_generated_basis_text" %abi-basis-text) :int
               (theory-id :uint32)
               (weight-kind :uint8)
               (weight-ticks :int32)
               (max-word-length :uint16)
               (level-match :uint8)
               (filters :pointer)
               (filter-count :size)
               (format :uint8)
               (max-states :size)
               (out-text :pointer)
               (out-len :pointer)))
      (eval `(,defcfun ("sc_generated_basis_text_free" %abi-basis-text-free) :void
               (text :pointer)
               (text-len :size)))
      (eval `(,defcallback %abi-event-callback :int
               ((payload :pointer) (event :pointer))
               (let ((sink (gethash (mem-ref* payload :uint64) *abi-sinks*)))
                 (when sink
                   (funcall sink event))
                 0)))
      (eval `(,defcallback %abi-event-chunk-callback :int
               ((payload :pointer) (events :pointer) (event-count :size))
               (let ((sink (gethash (mem-ref* payload :uint64) *abi-sinks*)))
                 (when sink
                   (loop for index below event-count
                         do (funcall sink (event-pointer-at events index))))
                 0)))
      (eval `(,defcallback %abi-basis-callback :int
               ((payload :pointer) (record :pointer))
               (let ((sink (gethash (mem-ref* payload :uint64) *abi-sinks*)))
                 (when sink
                   (funcall sink record))
                 0)))
      (setf *abi-callback-pointer* (eval `(,callback %abi-event-callback)))
      (setf *abi-chunk-callback-pointer* (eval `(,callback %abi-event-chunk-callback)))
      (setf *abi-basis-callback-pointer* (eval `(,callback %abi-basis-callback)))
      (setf *abi-bound* t))))

(defun load-generated-library (path)
  (funcall (symbol-function (cffi-symbol "LOAD-FOREIGN-LIBRARY")) path)
  (ensure-abi-bindings)
  path)

(defun check-abi (status)
  (unless (zerop status)
    (let ((message (%abi-last-error)))
      (error "Generated ABI call failed: ~A"
             (foreign-string-to-lisp* message)))))

(defun keyword-name (name)
  (intern (string-upcase name) '#:keyword))

(defun constant-name (name)
  (etypecase name
    (string (keyword-name name))
    (symbol (keyword-name (string name)))))

(defun normalize-runtime-constants (constants)
  (let ((table (make-hash-table)))
    (dolist (item constants table)
      (etypecase item
        (cons
         (setf (gethash (constant-name (car item)) table) (cdr item)))
        (symbol
         (setf (gethash (constant-name item) table) (constant-name item)))))))

(defun set-runtime-constant (context name value)
  "Set one symbolic scalar constant for later expression construction."
  (setf (gethash (constant-name name) (runtime-context-constants context)) value
        (runtime-context-scalar-monomials context) nil)
  value)

(defun runtime-constant-value (context name)
  (multiple-value-bind (value present)
      (gethash name (runtime-context-constants context))
    (if present value name)))

(defun make-runtime-context (&key library theory-id constants)
  (unless theory-id
    (error "A generated theory id is required."))
  (when library
    (load-generated-library library))
  (ensure-abi-bindings)
  (let ((handle (%abi-context-create theory-id)))
    (when (null-pointer-p* handle)
      (check-abi -1))
    (%make-runtime-context :handle handle :theory-id theory-id
                           :constants (normalize-runtime-constants constants))))

(defun destroy-runtime-context (context)
  (when (runtime-context-handle context)
    (%abi-context-destroy (runtime-context-handle context))
    (setf (runtime-context-handle context) nil)))

(defun runtime-handle (context)
  (or (runtime-context-handle context)
      (error "No generated runtime context is active.")))

(defun remember-runtime-symbol (context id name)
  (let ((symbols (runtime-context-symbols context)))
    (loop while (< (length symbols) id)
          do (vector-push-extend nil symbols))
    (setf (aref symbols (1- id)) (keyword-name name))
    id))

(defun runtime-symbol-name (context id)
  (let ((symbols (runtime-context-symbols context)))
    (if (and (> id 0) (<= id (length symbols)))
        (or (aref symbols (1- id)) `(:symbol ,id))
        `(:symbol ,id))))

(defun intern-runtime-symbol (context name)
  (let ((out (foreign-alloc* :uint32)))
    (unwind-protect
         (progn
           (check-abi
            (%abi-symbol-intern (runtime-handle context) name (length name) out))
           (remember-runtime-symbol context (mem-ref* out :uint32) name))
      (foreign-free* out))))

(defun copy-uint32-values (values)
  (let* ((count (length values))
         (pointer (foreign-alloc* :uint32 :count (max 1 count))))
    (loop for value in values
          for index from 0
          do (set-mem-aref* pointer :uint32 index value))
    (values pointer count)))

(defun insert-runtime-field (context field-id coordinates labels)
  (multiple-value-bind (coord-pointer coord-count) (copy-uint32-values coordinates)
    (multiple-value-bind (label-pointer label-count) (copy-uint32-values labels)
      (unwind-protect
           (check-abi
            (%abi-field-insert (runtime-handle context) field-id coord-pointer coord-count label-pointer label-count))
        (foreign-free* label-pointer)
        (foreign-free* coord-pointer))))
  field-id)

(defun normal-order-runtime-field (context count)
  (check-abi
   (%abi-normal-ordering (runtime-handle context) count))
  count)

(defun freeze-runtime-operators (context)
  (check-abi
   (%abi-operator-list-freeze (runtime-handle context)))
  :generated)

(defun count-correlator (context frozen)
  (declare (ignore frozen))
  (let ((out (foreign-alloc* :size)))
    (unwind-protect
         (progn
           (check-abi
            (%abi-correlator-count (runtime-handle context) out))
           (mem-ref* out :size))
      (foreign-free* out))))

(defparameter *basis-runtime-metadata*
  '((1 :presentation free-fermion-10
     :tick-denominator 2
     :quantum-numbers ((fermion-number :slot 0 :kind :zn :modulus 2)
                       (spin10 :slot nil :kind :rep))
     :seed-bits nil)
    (2 :presentation eta-xi-sphere
     :tick-denominator 1
     :quantum-numbers ((eta-xi-number :slot 0 :kind :u1))
     :seed-bits ((0 :operator xi :weight 0 :quantum-number ((u1 eta-xi-number -1)))))
    (3 :presentation eta-xi-torus
     :tick-denominator 1
     :quantum-numbers ((eta-xi-number :slot 0 :kind :u1))
     :seed-bits ((0 :operator xi :weight 0 :quantum-number ((u1 eta-xi-number -1)))))
    (4 :presentation bc
     :tick-denominator 1
     :quantum-numbers ((ghost-number :slot 0 :kind :u1))
     :seed-bits ((0 :operator c :weight -1 :quantum-number ((u1 ghost-number 1)))
                 (1 :operator c :weight 0 :quantum-number ((u1 ghost-number 1)))))
    (5 :presentation free-boson-10
     :tick-denominator 1
     :quantum-numbers ((spin10 :slot nil :kind :rep))
     :seed-bits nil)
    (100 :presentation product-free-boson-10-free-boson-10
     :tick-denominator 1
     :quantum-numbers nil
     :seed-bits nil)))

(defun basis-runtime-metadata (context)
  (or (runtime-context-basis-metadata context)
      (cdr (assoc (runtime-context-theory-id context) *basis-runtime-metadata*))
      (error "No basis runtime metadata for theory id ~D."
             (runtime-context-theory-id context))))

(defun basis-product-pair-id (left right)
  (+ 1000 (* left 16) right))

(defun supported-quantum-width (metadata)
  (loop for item in (getf metadata :quantum-numbers)
        for slot = (getf (rest item) :slot)
        when (integerp slot)
          maximize (1+ slot) into width
        finally (return (or width 0))))

(defun shifted-quantum-metadata (metadata offset)
  (loop for item in (getf metadata :quantum-numbers)
        for properties = (copy-list (rest item))
        for slot = (getf properties :slot)
        do (when (integerp slot)
             (setf (getf properties :slot) (+ offset slot)))
        collect (cons (first item) properties)))

(defun basis-seed-bit-width (metadata)
  (loop for item in (getf metadata :seed-bits)
        maximize (1+ (first item)) into width
        finally (return (or width 0))))

(defun shifted-seed-bit-metadata (metadata offset component)
  (loop for item in (getf metadata :seed-bits)
        for properties = (copy-list (rest item))
        do (setf (getf properties :component) component)
        collect (cons (+ offset (first item)) properties)))

(defun product-basis-metadata (left right)
  (let* ((left-meta (basis-runtime-metadata left))
         (right-meta (basis-runtime-metadata right))
         (left-denominator (getf left-meta :tick-denominator))
         (right-denominator (getf right-meta :tick-denominator)))
    (unless (= left-denominator right-denominator)
      (error "Cannot build product basis with incompatible backend ticks 1/~D and 1/~D."
             left-denominator right-denominator))
    (let* ((left-width (supported-quantum-width left-meta))
           (numbers (append (shifted-quantum-metadata left-meta 0)
                            (shifted-quantum-metadata right-meta left-width)))
           (left-seed-width (basis-seed-bit-width left-meta))
           (seed-bits (append (shifted-seed-bit-metadata left-meta 0 0)
                              (shifted-seed-bit-metadata right-meta
                                                         left-seed-width
                                                         1))))
      (list :presentation (list :product
                                (getf left-meta :presentation)
                                (getf right-meta :presentation))
            :tick-denominator left-denominator
            :quantum-numbers numbers
            :seed-bits seed-bits))))

(defun make-product-runtime (&rest runtimes)
  "Return a basis-only product runtime backed by a generated product presentation."
  (let ((theory-ids (mapcar #'runtime-context-theory-id runtimes)))
    (cond
      ((and (= (length theory-ids) 2)
            (or (and (= (first theory-ids) 1)
                     (= (second theory-ids) 1))
                (and (member (first theory-ids) '(2 3 4 5))
                     (member (second theory-ids) '(2 3 4 5)))))
       (%make-runtime-context :handle nil
                              :theory-id (basis-product-pair-id
                                          (first theory-ids)
                                          (second theory-ids))
                              :basis-metadata (product-basis-metadata
                                               (first runtimes)
                                               (second runtimes))
                              :constants (normalize-runtime-constants nil)))
      (t
       (error "No generated product basis runtime for theory ids ~S." theory-ids)))))

(defun basis-query-value (query key)
  (getf query key))

(defun basis-weight-ticks (metadata value)
  (let* ((denominator (getf metadata :tick-denominator))
         (ticks (* value denominator)))
    (unless (integerp ticks)
      (error "Basis weight ~S is not representable in backend ticks of 1/~D."
             value denominator))
    ticks))

(defun basis-weight-kind-and-ticks (metadata query)
  (let ((weight (basis-query-value query :weight))
        (max-weight (basis-query-value query :max-weight)))
    (cond
      ((and weight max-weight)
       (error "Basis query cannot contain both :WEIGHT and :MAX-WEIGHT."))
      (weight (values 0 (basis-weight-ticks metadata weight)))
      (max-weight (values 1 (basis-weight-ticks metadata max-weight)))
      (t (error "Basis query requires :WEIGHT or :MAX-WEIGHT.")))))

(defun basis-max-depth (query)
  (or (basis-query-value query :max-depth)
      #xffff))

(defun basis-level-match (query)
  (if (basis-query-value query :level-match) 1 0))

(defun quantum-metadata (metadata name)
  (let ((key (if (symbolp name) name (keyword-name name))))
    (let ((matches (loop for item in (getf metadata :quantum-numbers)
                         when (string-equal (first item) key)
                           collect item)))
      (cond
        ((null matches)
         (error "Unknown basis quantum number ~S." name))
        ((cdr matches)
         (error "Ambiguous product basis quantum number ~S." name))
        (t (first matches))))))

(defun lowered-quantum-filter (metadata spec)
  (unless (consp spec)
    (error "Basis quantum-number filter must be a list, got ~S." spec))
  (let ((kind (string-downcase (string (first spec)))))
    (cond
      ((string= kind "u1")
       (destructuring-bind (_ name value) spec
         (declare (ignore _))
         (let ((number (quantum-metadata metadata name)))
           (unless (eq (getf (rest number) :kind) :u1)
             (error "Quantum number ~S is not U(1)." name))
           (list (getf (rest number) :slot) value))))
      ((string= kind "zn")
       (destructuring-bind (_ name modulus value) spec
         (declare (ignore _))
         (let ((number (quantum-metadata metadata name)))
           (unless (eq (getf (rest number) :kind) :zn)
             (error "Quantum number ~S is not Z_N." name))
           (unless (= modulus (getf (rest number) :modulus))
             (error "Quantum number ~S has modulus ~D, got ~D."
                    name (getf (rest number) :modulus) modulus))
           (list (getf (rest number) :slot) value))))
      ((member kind '("rep" "ade-irrep" "tensor-rep") :test #'string=)
       (let ((name (second spec)))
         (when name (quantum-metadata metadata name))
         (error 'unsupported-basis-filter :filter spec)))
      (t
       (error "Unknown basis quantum-number filter kind in ~S." spec)))))

(defun lowered-basis-filters (metadata query)
  (mapcar (lambda (spec) (lowered-quantum-filter metadata spec))
          (basis-query-value query :quantum-number)))

(defun call-with-basis-filters (filters function)
  (let* ((count (length filters))
         (pointer (foreign-alloc* '(:struct generated-basis-filter)
                                  :count (max 1 count))))
    (unwind-protect
         (progn
           (loop for filter in filters
                 for index from 0
                 for item = (inc-pointer* pointer
                                          (* index
                                             (foreign-type-size*
                                              '(:struct generated-basis-filter))))
                 do (progn
                      (set-foreign-slot-value* item '(:struct generated-basis-filter)
                                               'slot (first filter))
                      (set-foreign-slot-value* item '(:struct generated-basis-filter)
                                               'value (second filter))))
           (funcall function pointer count))
      (foreign-free* pointer))))

(defun run-basis-with-filters (context query function)
  (let ((metadata (basis-runtime-metadata context)))
    (multiple-value-bind (weight-kind weight-ticks)
        (basis-weight-kind-and-ticks metadata query)
      (call-with-basis-filters
       (lowered-basis-filters metadata query)
       (lambda (filters filter-count)
         (funcall function metadata weight-kind weight-ticks
                  (basis-max-depth query) (basis-level-match query)
                  filters filter-count))))))

(defun basis-count (context query)
  "Return the compact backend basis count for QUERY without text rendering."
  (ensure-abi-bindings)
  (run-basis-with-filters
   context query
   (lambda (_ weight-kind weight-ticks max-depth level-match filters filter-count)
     (declare (ignore _))
     (let ((out (foreign-alloc* :size)))
       (unwind-protect
            (progn
              (check-abi
               (%abi-basis-count (runtime-context-theory-id context)
                                 weight-kind weight-ticks max-depth level-match
                                 filters filter-count out))
              (mem-ref* out :size))
         (foreign-free* out))))))

(defun int32-values (pointer count)
  (loop for index below count
        collect (mem-ref* (inc-pointer* pointer (* index 4)) :int32)))

(defun basis-quantum-records (metadata values)
  (loop for number in (getf metadata :quantum-numbers)
        for value in values
        collect (ecase (getf (rest number) :kind)
                  (:u1 `(u1 ,(first number) ,value))
                  (:zn `(zn ,(first number)
                            ,(getf (rest number) :modulus)
                            ,value)))))

(defun basis-weight-value (metadata ticks)
  (let ((denominator (getf metadata :tick-denominator)))
    (if (= denominator 1)
        ticks
        (/ ticks denominator))))

(defun basis-mode-record (metadata mode)
  (let* ((type '(:struct generated-basis-mode))
         (name-pointer (foreign-slot-value* mode type 'name-ptr))
         (name-length (foreign-slot-value* mode type 'name-len))
         (name (and (> name-length 0)
                    (not (null-pointer-p* name-pointer))
                    (keyword-name
                     (foreign-string-to-lisp* name-pointer
                                              :count name-length)))))
    (vector :id (or name `(:id ,(foreign-slot-value* mode type 'id)))
            :component (foreign-slot-value* mode type 'component)
            :label (foreign-slot-value* mode type 'label)
            :weight (basis-weight-value
                     metadata
                     (foreign-slot-value* mode type 'weight-ticks)))))

(defun basis-mode-records (metadata pointer count)
  (let ((modes (make-array count)))
    (loop for index below count
          do (setf (aref modes index)
                   (basis-mode-record metadata
                                      (basis-mode-pointer-at pointer index))))
    modes))

(defun seed-bit-base (metadata bit)
  (cdr (assoc bit (getf metadata :seed-bits))))

(defun basis-base-record (metadata seed-body base-weight base-quantum)
  (let ((quantum (basis-quantum-records metadata base-quantum))
        (bits nil))
    (loop for bit from 0 below 32
          when (not (zerop (logand seed-body (ash 1 bit))))
            do (push bit bits))
    (cond
      ((and (= (length bits) 1) (seed-bit-base metadata (first bits)))
       (let ((base (copy-list (seed-bit-base metadata (first bits)))))
         (setf (getf base :weight) base-weight
               (getf base :quantum-number) quantum)
         base))
      ((zerop seed-body)
       `(:vacuum :weight ,base-weight :quantum-number ,quantum))
      (t
       `(:operators ,(mapcar (lambda (bit)
                               (or (seed-bit-base metadata bit)
                                   `(:seed-bit ,bit)))
                             (nreverse bits))
         :weight ,base-weight
         :quantum-number ,quantum)))))

(defun basis-record-from-pointer (metadata record)
  (let* ((type '(:struct generated-basis-record))
         (base-quantum (int32-values
                        (foreign-slot-value* record type 'base-quantum-ptr)
                        (foreign-slot-value* record type 'base-quantum-len)))
         (quantum (int32-values
                   (foreign-slot-value* record type 'quantum-ptr)
                   (foreign-slot-value* record type 'quantum-len))))
    (list :basis-state
          :presentation (getf metadata :presentation)
          :base (basis-base-record
                 metadata
                 (foreign-slot-value* record type 'seed-body)
                 (basis-weight-value
                  metadata
                  (foreign-slot-value* record type 'base-weight-ticks))
                 base-quantum)
          :weight (basis-weight-value
                   metadata
                   (foreign-slot-value* record type 'weight-ticks))
          :level (basis-weight-value
                  metadata
                  (foreign-slot-value* record type 'level-ticks))
          :quantum-number (basis-quantum-records metadata quantum)
          :modes (basis-mode-records
                  metadata
                  (foreign-slot-value* record type 'mode-ptr)
                  (foreign-slot-value* record type 'mode-len)))))

(defun run-basis-compact (context query)
  (ensure-abi-bindings)
  (let ((records nil))
    (run-basis-with-filters
     context query
     (lambda (metadata weight-kind weight-ticks max-depth level-match filters filter-count)
       (let* ((sink-id (prog1 *next-abi-sink-id*
                         (incf *next-abi-sink-id*)))
              (payload (foreign-alloc* :uint64)))
         (setf (gethash sink-id *abi-sinks*)
               (lambda (record)
                 (push (basis-record-from-pointer metadata record) records)))
         (set-mem-aref* payload :uint64 0 sink-id)
         (unwind-protect
              (check-abi
               (%abi-basis-run-compact
                (runtime-context-theory-id context)
                weight-kind weight-ticks max-depth level-match
                filters filter-count
                payload *abi-basis-callback-pointer*))
           (remhash sink-id *abi-sinks*)
           (foreign-free* payload)))))
    (nreverse records)))

(defun strip-basis-text-line (line)
  (if (and (> (length line) 0) (char= (aref line 0) #\#))
      (let ((space (position #\Space line)))
        (if space (subseq line (1+ space)) line))
      line))

(defun split-basis-lines (text)
  (loop with start = 0
        for index from 0 to (length text)
        when (or (= index (length text)) (char= (aref text index) #\Newline))
          unless (= start index)
            collect (strip-basis-text-line (subseq text start index))
          and do (setf start (1+ index))))

(defun basis-text (context query format)
  (ensure-abi-bindings)
  (run-basis-with-filters
   context query
   (lambda (_ weight-kind weight-ticks max-depth level-match filters filter-count)
     (declare (ignore _))
     (let ((out-text (foreign-alloc* :pointer))
           (out-len (foreign-alloc* :size)))
       (unwind-protect
            (progn
              (check-abi
               (%abi-basis-text
                (runtime-context-theory-id context)
                weight-kind weight-ticks max-depth level-match
                filters filter-count
                (ecase format
                  (:compact 0)
                  (:state 1)
                  (:operator 2))
                (or (basis-query-value query :limit)
                    most-positive-fixnum)
                out-text out-len))
              (let* ((pointer (mem-ref* out-text :pointer))
                     (length (mem-ref* out-len :size))
                     (text (foreign-string-to-lisp* pointer :count length)))
                (%abi-basis-text-free pointer length)
                (let ((lines (split-basis-lines text)))
                  (if (and lines (null (rest lines)))
                      (first lines)
                      lines))))
         (foreign-free* out-len)
         (foreign-free* out-text))))))

(defun basis (context query &key (as :compact))
  "Return basis states for QUERY as :COMPACT records, :STATE text, or :OPERATOR text."
  (ecase as
    (:compact (run-basis-compact context query))
    ((:state :operator) (basis-text context query as))))

(defun run-correlator-raw (context sink)
  (let* ((sink-id (prog1 *next-abi-sink-id*
                    (incf *next-abi-sink-id*)))
         (payload (foreign-alloc* :uint64)))
    (setf (gethash sink-id *abi-sinks*) sink)
    (set-mem-aref* payload :uint64 0 sink-id)
    (unwind-protect
         (check-abi
          (%abi-correlator-run (runtime-handle context) payload *abi-callback-pointer*))
      (remhash sink-id *abi-sinks*)
      (foreign-free* payload))))

(defun run-correlator-buffered (context sink)
  (let* ((sink-id (prog1 *next-abi-sink-id*
                    (incf *next-abi-sink-id*)))
         (payload (foreign-alloc* :uint64)))
    (setf (gethash sink-id *abi-sinks*) sink)
    (set-mem-aref* payload :uint64 0 sink-id)
    (unwind-protect
         (check-abi
          (%abi-correlator-run-buffered (runtime-handle context) payload *abi-chunk-callback-pointer*))
      (remhash sink-id *abi-sinks*)
      (foreign-free* payload))))

(defun run-correlator (context frozen sink)
  (declare (ignore frozen))
  (run-correlator-raw context
                      (lambda (event)
                        (funcall sink (event-from-pointer event)))))

(defstruct (expression-builder (:constructor make-expression-builder (context)))
  context
  terms)

(declaim
 (inline name-ptr name-len name-token product-expression sum-expression))

(defun name-ptr (name)
  (mem-ref* (inc-pointer* name *name-ptr-offset*) :pointer))

(defun name-len (name)
  (mem-ref* (inc-pointer* name *name-len-offset*) :size))

(defun name-token (name)
  (let ((pointer (name-ptr name))
        (length (name-len name)))
    (when (and (> length 0) (not (null-pointer-p* pointer)))
      (keyword-name (foreign-string-to-lisp* pointer :count length)))))

(defun factor-name-token-by-id (names id)
  (and (> id 0) (aref names (1- id))))

(defun product-expression (factors)
  (cond
    ((null factors) 1)
    ((null (cdr factors)) (car factors))
    (t (cons '* factors))))

(defun sum-expression (terms)
  (cond
    ((null terms) 0)
    ((null (cdr terms)) (car terms))
    (t (cons '+ terms))))

(defun exp-green-expression-p (expr)
  (and (consp expr) (eq (first expr) :exp-green)))

(defun momentum-pair-expression-p (expr)
  (and (consp expr) (eq (first expr) :momentum-pair)))

(defun explicit-green-expression (green exponent)
  `(expt (- ,(second green) ,(third green)) ,exponent))

(defun product-factor-list (expr)
  (if (and (consp expr) (eq (first expr) '*))
      (rest expr)
      (list expr)))

(defun momentum-sum-expression (momenta)
  (cond
    ((null momenta) 0)
    ((null (cdr momenta)) (car momenta))
    (t (cons '+ momenta))))

(defun momentum-delta-expression (header momenta)
  (let ((power (second header))
        (sum (momentum-sum-expression momenta)))
    (product-expression
     (remove 1
             (list (if (zerop power) 1 `(expt (* 2 :pi) ,power))
                   `(:momentum-delta ,power ,sum))))))

(defun rewrite-zero-mode-factors (items)
  (let ((rest nil)
        (momenta nil)
        (header nil)
        (has-delta nil))
    (dolist (item items)
      (when (and (consp item) (eq (first item) :momentum-delta-header))
        (setf has-delta t)))
    (dolist (item items)
      (cond
        ((and (consp item) (eq (first item) :momentum-delta-header))
         (setf header item))
        ((and (consp item) (eq (first item) :momentum-delta-momentum))
         (push (second item) momenta))
        ((and has-delta (consp item) (eq (first item) :residual))
         nil)
        (t (push item rest))))
    (if header
        (append (nreverse rest)
                (list (momentum-delta-expression header (nreverse momenta))))
        items)))

(defun term-product-expression (items scalars greens momentum-pairs others)
  (if (and greens momentum-pairs)
      (let ((exponent (product-expression
                       (append
                        (loop for scalar in (nreverse scalars)
                              append (product-factor-list scalar))
                        (nreverse momentum-pairs)))))
        (product-expression
         (append
          (mapcar (lambda (green)
                    (explicit-green-expression green exponent))
                  (nreverse greens))
          (rewrite-zero-mode-factors (nreverse others)))))
      (product-expression (rewrite-zero-mode-factors (nreverse items)))))

(defun factor-coordinate-expression-values (builder names a b d name-id)
  (let* ((context (expression-builder-context builder))
         (left (runtime-symbol-name context a))
         (right (runtime-symbol-name context b))
         (name (factor-name-token-by-id names name-id)))
    (cond
      ((null name) `(expt (- ,left ,right) ,d))
      ((eq name :exp-green) `(:exp-green ,left ,right))
      (t `(,name ,left ,right)))))

(defun factor-tensor-expression-values (builder names a b name-id)
  (let* ((context (expression-builder-context builder))
         (left (runtime-symbol-name context a))
         (right (runtime-symbol-name context b))
         (name (or (factor-name-token-by-id names name-id) :tensor)))
    `(,name ,left ,right)))

(defun scalar-atom-expression (context atom)
  (when (> atom 0)
    (let ((name
            (multiple-value-bind (cached present)
                (gethash atom (runtime-context-scalar-atom-names context))
              (if present
                  cached
                  (let ((out-name (foreign-alloc* :pointer))
                        (out-name-len (foreign-alloc* :size)))
                    (unwind-protect
                         (let ((status (%abi-scalar-atom-name
                                        (runtime-context-theory-id context)
                                        atom out-name out-name-len)))
                           (if (zerop status)
                               (let* ((pointer (mem-ref* out-name :pointer))
                                      (length (mem-ref* out-name-len :size))
                                      (token (keyword-name
                                              (foreign-string-to-lisp*
                                               pointer :count length))))
                                 (setf (gethash atom (runtime-context-scalar-atom-names context))
                                       token))
                               (setf (gethash atom (runtime-context-scalar-atom-names context))
                                     `(:scalar-atom ,atom))))
                      (foreign-free* out-name-len)
                      (foreign-free* out-name)))))))
      (if (keywordp name)
          (runtime-constant-value context name)
          name))))

(defun rational-expression (numerator denominator)
  (cond
    ((= numerator denominator) 1)
    ((= denominator 1) numerator)
    (t `(/ ,numerator ,denominator))))

(defun scalar-atom-power-expression (atom power)
  (cond
    ((or (null atom) (= power 0)) 1)
    ((= power 1) atom)
    (t `(expt ,atom ,power))))

(defun signed-byte8 (value)
  (if (> value 127) (- value 256) value))

(defun scalar-imaginary-factors (power)
  (ecase power
    (0 nil)
    (1 '(:i))
    (2 '(-1))
    (3 '(-1 :i))))

(defun make-scalar-monomial-expression (context atom denominator flags numerator)
  (let* ((imaginary-power (logand flags 3))
         (atom-power (signed-byte8 (ldb (byte 8 8) flags)))
         (atom-expr (scalar-atom-expression context atom))
         (coefficient (if (and (numberp atom-expr) (= atom-power 1))
                          (/ (* numerator atom-expr) denominator)
                          (rational-expression numerator denominator)))
         (atom-factor (unless (and (numberp atom-expr) (= atom-power 1))
                        (scalar-atom-power-expression atom-expr atom-power))))
    (product-expression
     (remove-if (lambda (factor) (or (null factor) (eql factor 1)))
                (append
                 (list coefficient)
                 (scalar-imaginary-factors imaginary-power)
                 (list atom-factor))))))

(defun cached-scalar-monomial-expression (context atom denominator flags numerator)
  (loop for row in (runtime-context-scalar-monomials context)
        when (and (= atom (aref row 0))
                  (= denominator (aref row 1))
                  (= flags (aref row 2))
                  (= numerator (aref row 3)))
          return (aref row 4)
        finally
           (let ((expr (make-scalar-monomial-expression
                        context atom denominator flags numerator)))
             (push (vector atom denominator flags numerator expr)
                   (runtime-context-scalar-monomials context))
             (return expr))))

(defun scalar-monomial-expression (builder atom denominator flags numerator)
  (let ((context (expression-builder-context builder)))
    (cached-scalar-monomial-expression context atom denominator flags numerator)))

(defun factor-scalar-expression-values (builder names a b c d name-id)
  (let ((sign d))
    (cond
      ((and (= sign -1) (= name-id 0)) -1)
      (t
       (let ((name (factor-name-token-by-id names name-id)))
         (cond
           ((eq name :scalar-monomial)
            (scalar-monomial-expression builder a b c d))
           (name
             `(,name
               ,(runtime-symbol-name (expression-builder-context builder) a)
               ,(runtime-symbol-name (expression-builder-context builder) b)))
           (t 1)))))))

(defun factor-zero-mode-expression-values (builder names a b name-id)
  (let ((name (factor-name-token-by-id names name-id)))
    (cond
      ((eq name :momentum-delta)
       `(:momentum-delta-header ,a ,b))
      ((eq name :momentum-delta-momentum)
       `(:momentum-delta-momentum
         ,(runtime-symbol-name (expression-builder-context builder) a)))
      ((eq name :eta-xi-zero-mode)
       `(:eta-xi-zero-mode ,(runtime-symbol-name (expression-builder-context builder) a)))
      ((eq name :bc-top-form)
       '(:bc-top-form))
      (name `(,name))
      (t '(:zero-mode)))))

(defun factor-expression-values (builder names kind a b c d name-id)
  (case kind
    (4 (factor-scalar-expression-values builder names a b c d name-id))
    (5 (factor-coordinate-expression-values builder names a b d name-id))
    (6 (factor-tensor-expression-values builder names a b name-id))
    (7 (factor-zero-mode-expression-values builder names a b name-id))
    (8 `(:residual ,a))
    (otherwise 1)))

(defun expression-name-vector (names count)
  (let ((tokens (make-array count)))
    (loop for index below count
          do (setf (aref tokens index)
                   (name-token (name-pointer-at names index))))
    tokens))

(defun fold-expression-records (context)
  (let ((out-terms (foreign-alloc* :pointer))
        (out-term-count (foreign-alloc* :size))
        (out-factors (foreign-alloc* :pointer))
        (out-factor-count (foreign-alloc* :size))
        (out-names (foreign-alloc* :pointer))
        (out-name-count (foreign-alloc* :size))
        (builder (make-expression-builder context)))
    (unwind-protect
         (progn
           (check-abi
            (%abi-correlator-expression-records
             (runtime-handle context)
             out-terms out-term-count out-factors out-factor-count out-names out-name-count))
           (let ((terms (mem-ref* out-terms :pointer))
                 (term-count (mem-ref* out-term-count :size))
                 (factors (mem-ref* out-factors :pointer))
                 (factor-count (mem-ref* out-factor-count :size))
                 (names (mem-ref* out-names :pointer))
                 (name-count (mem-ref* out-name-count :size)))
             (unwind-protect
                  (let ((name-tokens (expression-name-vector names name-count)))
                    (loop for index below term-count
                          do (push (term-expression builder factors name-tokens
                                                    (term-pointer-at terms index))
                                   (expression-builder-terms builder))))
               (%abi-expression-buffer-free terms term-count factors factor-count names name-count)))
           (sum-expression (nreverse (expression-builder-terms builder))))
      (foreign-free* out-name-count)
      (foreign-free* out-names)
      (foreign-free* out-factor-count)
      (foreign-free* out-factors)
      (foreign-free* out-term-count)
      (foreign-free* out-terms))))

(defun correlator-expression (context frozen)
  (declare (ignore frozen))
  (fold-expression-records context))

(defun collect-correlator (context frozen &key (limit 1024))
  (let ((events nil)
        (count 0))
    (run-correlator context frozen
                    (lambda (event)
                      (when (>= count limit)
                        (error "Result collection limit reached."))
                      (incf count)
                      (push event events)))
    (nreverse events)))
