(require :asdf)

(let* ((script-path (or *load-truename* *compile-file-truename*))
       (lisp-directory (uiop:pathname-directory-pathname script-path)))
  (pushnew lisp-directory asdf:*central-registry* :test #'equal)
  (asdf:load-system :string-code-cft)
  (funcall (find-symbol "WRITE-GENERATED-SOURCES" "STRING-CODE.CFT.PRESETS"))
  (format t "Regenerated CFT generated Zig sources.~%"))
