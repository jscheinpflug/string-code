;;; publish.el --- Project-local static Org/Org-roam publisher -*- lexical-binding: t; -*-

;;; This file intentionally does NOT load org-roam.
;;; It only exports plain Org files into ./public/.
;;;
;;; Expected project layout, either:
;;;
;;;   project/
;;;     publish/
;;;       publish.el
;;;     org/
;;;       note-a.org
;;;       org-roam.db
;;;
;;; or:
;;;
;;;   project/
;;;     publish/
;;;       publish.el
;;;     notes/
;;;       note-a.org
;;;       org-roam.db
;;;
;;; Output:
;;;
;;;   project/
;;;     public/
;;;       index.html
;;;       notes/
;;;         note-a.html
;;;       graph/
;;;         index.html    ; placeholder unless publish-org-roam-ui output is copied here

(require 'ox-publish)
(require 'org)
(require 'org-id)
(require 'subr-x)
(require 'oc)           ; org-cite core
(require 'oc-basic)     ; basic HTML processor (built-in, no extra packages)

;; ---------------------------------------------------------------------
;; Citations (org-cite)
;; HTML: basic processor appends per-page reference list automatically.
;; PDF:  biblatex processor emits \cite{}; \printbibliography at doc end.
;; ---------------------------------------------------------------------

;; Resolved after my/site-source-dir is defined; set lazily via advice.
;; (The actual setq happens after the Paths section below.)

;; ---------------------------------------------------------------------
;; Syntax highlighting: load htmlize + language modes + doom-gruvbox colors
;; so that batch-mode export produces the same colored spans as
;; interactive M-x org-export-dispatch.
;; ---------------------------------------------------------------------

(let* ((straight-dir (expand-file-name "~/.config/emacs/.local/straight"))
       (build-dir (when (file-directory-p straight-dir)
                    (car (sort (seq-filter #'file-directory-p
                                           (directory-files straight-dir t "^build-[0-9]" t))
                               #'string>)))))
  (when build-dir
    (dolist (d (directory-files build-dir t "^[^.]"))
      (when (file-directory-p d) (add-to-list 'load-path d)))))

(when (require 'htmlize nil t)
  (setq org-html-htmlize-output-type 'inline-css)
  (require 'zig-mode nil t)
  (require 'haskell-mode nil t)
  (require 'lua-mode nil t)
  ;; doom-gruvbox colors: set-face-attribute is reliable in batch mode
  ;; whereas load-theme silently drops :foreground on non-graphical frames.
  (set-face-attribute 'default                         nil :foreground "#ebdbb2" :background "#282828")
  (set-face-attribute 'font-lock-keyword-face          nil :foreground "#fb4934" :weight 'bold)
  (set-face-attribute 'font-lock-function-name-face    nil :foreground "#b8bb26" :weight 'bold)
  (set-face-attribute 'font-lock-variable-name-face    nil :foreground "#83a598" :weight 'bold :slant 'italic)
  (set-face-attribute 'font-lock-string-face           nil :foreground "#b8bb26" :slant 'italic)
  (set-face-attribute 'font-lock-type-face             nil :foreground "#fabd2f" :weight 'bold :underline t)
  (set-face-attribute 'font-lock-constant-face         nil :foreground "#d3869b")
  (set-face-attribute 'font-lock-builtin-face          nil :foreground "#fe8019" :weight 'bold)
  (set-face-attribute 'font-lock-preprocessor-face     nil :foreground "#fe8019")
  (set-face-attribute 'font-lock-comment-face          nil :foreground "#ebdbb2" :slant 'italic)
  (set-face-attribute 'font-lock-comment-delimiter-face nil :foreground "#ebdbb2")
  (set-face-attribute 'font-lock-doc-face              nil :foreground "#e0d3b9" :slant 'italic)
  (set-face-attribute 'font-lock-number-face           nil :foreground "#d3869b")
  (set-face-attribute 'font-lock-operator-face         nil :foreground "#ebdbb2")
  (set-face-attribute 'font-lock-warning-face          nil :foreground "#fb4934" :weight 'bold))

;; ---------------------------------------------------------------------
;; Paths
;; ---------------------------------------------------------------------

(defvar my/site-root
  (file-name-directory
   (directory-file-name
    (file-name-directory (or load-file-name buffer-file-name))))
  "Project root directory (parent of the publish/ directory).")

(defvar my/site-source-dir
  (let ((org-dir   (expand-file-name "org/" my/site-root))
        (notes-dir (expand-file-name "notes/" my/site-root)))
    (cond
     ((file-directory-p org-dir) org-dir)
     ((file-directory-p notes-dir) notes-dir)
     (t org-dir)))
  "Directory containing source Org notes.")

;; org-cite: single shared refs.bib; numeric-html for HTML (per-page [N] refs),
;; biblatex for LaTeX (\printbibliography added at end of master org).
(setq org-cite-global-bibliography
      (list (expand-file-name "refs.bib" my/site-source-dir)))

;; ---- Custom numeric HTML citation processor --------------------------------
;; Assigns sequential [1][2]... numbers as citations appear in the document.
;; Uses oc-basic's bib-parsing infrastructure; registers as 'numeric-html.

(defvar my/cite-seq-alist nil
  "Alist of (key . n) built up during a single HTML export.")
(defvar my/cite-seq-counter 0)

(defun my/cite-seq-reset ()
  (setq my/cite-seq-alist nil my/cite-seq-counter 0))

(defun my/cite-seq-num (key)
  "Return the sequence number for KEY, assigning one if not yet seen."
  (or (cdr (assoc key my/cite-seq-alist))
      (let ((n (setq my/cite-seq-counter (1+ my/cite-seq-counter))))
        (push (cons key n) my/cite-seq-alist)
        n)))

(defun my/cite-html-export-citation (citation _style _ info)
  "Render CITATION as linked [N] anchors in HTML."
  (let ((keys (org-cite-get-references citation t)))
    (mapconcat
     (lambda (k)
       (let ((n (my/cite-seq-num k)))
         (format "<a href=\"#ref-%d\" class=\"cite\">[%d]</a>" n n)))
     keys "")))

(defun my/cite-html-export-bibliography (keys _files _style _props _backend info)
  "Render a numbered reference list in HTML.
KEYS is the list of all cited key strings in document order."
  ;; Ensure every key has a number (they should already from inline citations).
  (dolist (k keys) (my/cite-seq-num k))
  (let* ((ordered (sort (copy-sequence my/cite-seq-alist)
                        (lambda (a b) (< (cdr a) (cdr b))))))
    (concat
     "<div class=\"references\"><h2>References</h2><ol>\n"
     (mapconcat
      (lambda (pair)
        (let* ((key   (car pair))
               (entry (org-cite-basic--get-entry key info))
               (fld   (lambda (f) (or (org-cite-basic--get-field f entry nil t) "")))
               (author  (funcall fld 'author))
               (year    (funcall fld 'year))
               (title   (funcall fld 'title))
               (journal (let ((j (funcall fld 'journal)))
                          (if (string= j "") (funcall fld 'booktitle) j)))
               (volume  (funcall fld 'volume))
               (pages   (funcall fld 'pages))
               (doi     (funcall fld 'doi))
               (url     (funcall fld 'url)))
          (format "<li id=\"ref-%d\">%s (%s). <em>%s</em>%s%s%s%s</li>"
                  (cdr pair) author year title
                  (if (not (string= journal "")) (format ", %s" journal) "")
                  (if (not (string= volume "")) (format " <b>%s</b>" volume) "")
                  (if (not (string= pages  "")) (format ", %s" pages)  "")
                  (if (not (string= doi    ""))
                      (format ". doi:<a href=\"https://doi.org/%s\">%s</a>" doi doi)
                    (if (not (string= url ""))
                        (format ". <a href=\"%s\">%s</a>"
                                url
                                (replace-regexp-in-string "^https?://" "" url))
                      ".")))))
      ordered "\n")
     "\n</ol></div>")))

(defun my/cite-html-prepare (_backend)
  "Reset citation counter before each HTML export."
  (my/cite-seq-reset))

(org-cite-register-processor 'numeric-html
  :export-citation    #'my/cite-html-export-citation
  :export-bibliography #'my/cite-html-export-bibliography
  :follow             #'org-cite-basic-follow
  :activate           #'org-cite-basic-activate)

(add-hook 'org-export-before-processing-hook #'my/cite-html-prepare)

(setq org-cite-export-processors
      '((latex . (biblatex))
        (html  . (numeric-html))
        (t     . (basic))))

(defvar my/site-public-dir
  (expand-file-name "public/" my/site-root)
  "Directory where the static site is generated.")

(defvar my/site-public-notes-dir
  (expand-file-name "notes/" my/site-public-dir)
  "Directory where exported note HTML files are generated.")

(defvar my/site-public-graph-dir
  (expand-file-name "graph/" my/site-public-dir)
  "Directory where static org-roam-ui files should be placed.")

(defvar my/site-id-file
  (expand-file-name ".org-id-locations" my/site-source-dir)
  "Project-local Org ID locations file.")

(setq org-id-method 'ts)
(setq org-id-locations-file my/site-id-file)
(setq org-id-track-globally t)

(make-directory my/site-public-dir t)
(make-directory my/site-public-notes-dir t)
(make-directory my/site-public-graph-dir t)

;; ---------------------------------------------------------------------
;; Pub-declaration extraction from zig src blocks
;; ---------------------------------------------------------------------

(defun my/zig-clean-sig (raw)
  "Normalise a Zig signature: collapse whitespace, strip trailing {, fix paren spacing."
  (let ((s (string-trim (replace-regexp-in-string
                         "[[:space:]]+" " "
                         (replace-regexp-in-string "{.*$" "" raw)))))
    (setq s (replace-regexp-in-string "([ \t]+" "(" s))
    (setq s (replace-regexp-in-string "[ \t]+)" ")" s))
    (setq s (replace-regexp-in-string ",)" ")" s))
    s))

(defun my/zig-interface-indent-p (line)
  "Return non-nil when LINE is a module-level declaration.
Struct fields and namespace methods are implementation details of the exported
type and should not become separate module interface entries."
  (and (string-match "^\\([ \t]*\\)" line)
       (= (length (match-string 1 line)) 0)))

(defun my/zig-pub-sigs ()
  "Return ordered (name sig doc kind) lists for pub zig declarations.
Extracts /// doc comments immediately preceding each pub declaration.
kind is one of: \"fn\" \"type\" \"error\" \"const\"."
  (let ((case-fold-search nil)  ; [A-Z] must mean uppercase only
        result seen in-src collecting name-buf parts-buf doc-lines doc-buf)
    (save-excursion
      (goto-char (point-min))
      (while (not (eobp))
        (let ((line (buffer-substring-no-properties
                     (line-beginning-position) (line-end-position))))
          (cond
           ((string-match-p "^[ \t]*#\\+begin_src +zig" line)
            (setq in-src (not (string-match-p ":tangle +no" line)) doc-lines nil))
           ((string-match-p "^[ \t]*#\\+end_src" line)
            (setq in-src nil collecting nil name-buf nil parts-buf nil
                  doc-lines nil doc-buf nil))
           ;; Collect /// doc comment lines
           ((and in-src (string-match "^[ \t]*///[[:space:]]?\\(.*\\)$" line))
            (push (match-string 1 line) doc-lines))
           ;; Collecting a multi-line fn signature
           ((and in-src collecting)
            (push (string-trim line) parts-buf)
            ;; Non-/// non-empty line clears doc accumulator
            (unless (string-match-p "^[ \t]*$" line) (setq doc-lines nil))
            (when (string-match-p "{" line)
              (let* ((sig (my/zig-clean-sig
                           (mapconcat #'identity (nreverse parts-buf) " ")))
                     (doc (when doc-buf
                            (string-trim
                             (mapconcat #'identity (nreverse doc-buf) " ")))))
                (unless (member name-buf seen)
                  (push name-buf seen)
                  (push (list name-buf (concat name-buf sig) doc "fn") result)))
              (setq collecting nil name-buf nil parts-buf nil doc-buf nil)))
           ((and in-src (my/zig-interface-indent-p line))
            (let (name sig kind)
              (cond
               ;; pub [inline] fn — complete on one line
               ((and (string-match
                      "^[ \t]*pub \\(?:inline \\)?fn \\([a-zA-Z_][a-zA-Z0-9_]*\\)\\(.*\\)$"
                      line)
                     (string-match-p ")" line))
                (setq name (match-string 1 line)
                      sig  (concat name (my/zig-clean-sig (match-string 2 line)))
                      kind "fn"))
               ;; pub [inline] fn — multi-line
               ((string-match
                 "^[ \t]*pub \\(?:inline \\)?fn \\([a-zA-Z_][a-zA-Z0-9_]*\\)\\(.*\\)$"
                 line)
                (let ((n (match-string 1 line)))
                  (unless (member n seen)
                    (setq collecting t name-buf n
                          doc-buf (copy-sequence doc-lines)
                          parts-buf (list (string-trim (match-string 2 line)))))
                  (setq doc-lines nil)))
               ;; pub const Type = struct/enum/union/opaque/error
               ((string-match
                 "^[ \t]*pub const \\([A-Z][a-zA-Z0-9_]*\\)[[:space:]]*=[[:space:]]*\\(struct\\|enum\\|union\\|opaque\\|error\\)"
                 line)
                (setq name (match-string 1 line)
                      sig  (format "%s (%s)" name (match-string 2 line))
                      kind (if (string= (match-string 2 line) "error") "error" "type")))
               ;; pub const Name = TypeAlias; (e.g. pub const Variable = f32;)
               ((string-match
                 "^[ \t]*pub const \\([A-Z][a-zA-Z0-9_]*\\)[[:space:]]*=[[:space:]]*\\([^{;\n]+\\);[[:space:]]*$"
                 line)
                (setq name (match-string 1 line)
                      sig  (format "%s = %s" name (string-trim (match-string 2 line)))
                      kind "type"))
               ;; pub const name = value; (module exports and other constants)
               ((string-match
                 "^[ \t]*pub const \\([a-z_][a-zA-Z0-9_]*\\)[[:space:]]*=[[:space:]]*\\([^;\n]+\\);[[:space:]]*$"
                 line)
                (setq name (match-string 1 line)
                      sig  (format "%s = %s" name (string-trim (match-string 2 line)))
                      kind "const"))
               ;; pub const name: Type
               ((string-match
                 "^[ \t]*pub const \\([a-z_][a-zA-Z0-9_]*\\)[[:space:]]*:[[:space:]]*\\([^={(\n]+\\)"
                 line)
                (setq name (match-string 1 line)
                      sig  (format "%s: %s" name (string-trim (match-string 2 line)))
                      kind "const")))
              (cond
               (name
                (unless (member name seen)
                  (let ((doc (when doc-lines
                               (string-trim
                                (mapconcat #'identity (nreverse doc-lines) " ")))))
                    (push name seen)
                    (push (list name sig doc kind) result)))
                (setq doc-lines nil))
               ;; Non-pub non-/// non-blank line: reset doc accumulator
               ((not (string-match-p "^[ \t]*\\(?://\\|$\\)" line))
                (setq doc-lines nil)))))))
        (forward-line 1)))
    (nreverse result)))

(defun my/zig-emit-api-groups (sigs start &optional label)
  "Insert grouped API entries at point START as raw #+html: blocks.
Using raw HTML bypasses org's definition-list parser, which breaks on
links that share a name with a heading and on LaTeX math in descriptions.
SIGS is a list of (name sig doc kind) as returned by `my/zig-pub-sigs'."
  (let ((title (or label "Interface")))
    (goto-char start)
    (insert "#+html: <div class=\"toc-nav api-section\">\n")
    (insert "#+html: <div class=\"toc-section\">\n")
    (insert (format "#+html:   <div class=\"toc-row\"><span class=\"toc-toggle\"></span><span class=\"toc-folder\">%s</span></div>\n" title))
    (insert "#+html:   <div class=\"toc-entries\" hidden>\n")
    (dolist (group '(("fn" . "Functions") ("type" . "Types")
                     ("error" . "Errors") ("const" . "Constants")))
      (let ((entries (seq-filter (lambda (s) (string= (nth 3 s) (car group))) sigs)))
        (when entries
          (insert (format "#+html: <p class=\"api-kind\"><b>%s</b></p>\n" (cdr group)))
          (insert "#+html: <dl>\n")
          (dolist (s entries)
            (insert (format "#+html: <dt><a href=\"#%s\"><code>%s</code></a></dt>\n"
                            (nth 0 s) (my/html-escape (nth 1 s))))
            (when (and (nth 2 s) (not (string-empty-p (nth 2 s))))
              (insert (format "#+html: <dd>%s</dd>\n" (nth 2 s)))))
          (insert "#+html: </dl>\n"))))
    (insert "#+html:   </div>\n")
    (insert "#+html: </div>\n")
    (insert "#+html: </div>\n")))

(defun my/zig-all-pub-names ()
  "Return list of all top-level pub declaration names in the zig block after point."
  (let ((case-fold-search nil)   ; [A-Z] must mean uppercase only
        names)
    (save-excursion
      (forward-line 1)
      (while (not (looking-at "^[ \t]*#\\+end_src"))
        (let ((ln (buffer-substring-no-properties
                   (line-beginning-position) (line-end-position))))
          (when (my/zig-interface-indent-p ln)
            (cond
             ((string-match "^[ \t]*pub \\(?:inline \\)?fn \\([a-zA-Z_][a-zA-Z0-9_]*\\)" ln)
              (push (match-string 1 ln) names))
             ((string-match "^[ \t]*pub const \\([a-zA-Z_][a-zA-Z0-9_]*\\)[[:space:]]*=" ln)
              (push (match-string 1 ln) names)))))
        (forward-line 1)))
    (nreverse names)))

(defun my/zig-inject-html-anchors ()
  "Inject #+name: and #+html: <a id> before pub zig blocks that lack them.
#+name: lets [[name]] links resolve; #+html: <a id> lets /api/ page link by fragment."
  (save-excursion
    (goto-char (point-max))
    (while (re-search-backward "^[ \t]*#\\+begin_src +zig" nil t)
      (let ((block-pos (match-beginning 0)))
        (let ((prev (save-excursion
                      (forward-line -1)
                      (buffer-substring-no-properties
                       (line-beginning-position) (line-end-position)))))
          (let ((block-line (buffer-substring-no-properties
                              (line-beginning-position) (line-end-position))))
            (unless (or (string-match-p ":tangle +no" block-line)
                        (string-match-p "^[ \t]*#\\+html:[[:space:]]*<a id=" prev))
              (let ((pub-names (my/zig-all-pub-names)))
                (when pub-names
                  (goto-char block-pos)
                  ;; One <a id> anchor per pub declaration; #+name for the first.
                  (dolist (n pub-names)
                    (insert (format "#+html: <a id=\"%s\"></a>\n" n)))
                  (insert (format "#+name: %s\n" (car pub-names))))))))))))

;; Before each HTML export: inject anchors then populate API docs.
;; Trigger: either  #+interface:  (keyword, no heading needed)
;;          or      * API / * Interface  (legacy section heading).
(defun my/org-auto-api (backend)
  (when (eq backend 'html)
    (my/zig-inject-html-anchors)
    (save-excursion
      (goto-char (point-min))
      ;; #+api: or #+interface: keyword — delete the line and insert docs inline
      (when (re-search-forward "^#\\+\\(api\\|interface\\):[[:space:]]*$" nil t)
        (let* ((marker (downcase (match-string 1)))
               (sigs (my/zig-pub-sigs))
               (label (if (string= marker "api") "API" "Interface")))
          (when sigs
            (delete-region (line-beginning-position) (1+ (line-end-position)))
            (my/zig-emit-api-groups sigs (point) label)))))))

(add-hook 'org-export-before-processing-hook #'my/org-auto-api)

;; ---------------------------------------------------------------------
;; Helpers
;; ---------------------------------------------------------------------

(defun my/org-files ()
  "Return all Org files in `my/site-source-dir'."
  (when (file-directory-p my/site-source-dir)
    (directory-files-recursively my/site-source-dir "\\.org$")))

(defun my/org-files-direct (dir)
  "Return full paths of org files directly in DIR (non-recursive)."
  (sort (directory-files dir t "\\.org$") #'string<))

(defun my/org-immediate-subdirs ()
  "Return immediate subdirectories of source dir that contain org files."
  (let (result)
    (dolist (entry (directory-files my/site-source-dir t "^[^.]"))
      (when (and (file-directory-p entry)
                 (directory-files entry nil "\\.org$"))
        (push entry result)))
    (sort result #'string<)))


(defun my/file-to-html-path (file)
  "Return the absolute URL path for the HTML version of org FILE."
  (concat "/notes/"
          (file-name-sans-extension
           (file-relative-name file my/site-source-dir))
          ".html"))

(defun my/org-file-title (file)
  "Return #+title from FILE, or the filename base."
  (with-temp-buffer
    (insert-file-contents file)
    (goto-char (point-min))
    (if (re-search-forward "^#\\+title:[ \t]*\\(.+\\)$" nil t)
        (string-trim (match-string 1))
      (file-name-base file))))

(defun my/html-escape (s)
  "Escape S for HTML."
  (let ((s (or s "")))
    (setq s (replace-regexp-in-string "&" "&amp;" s))
    (setq s (replace-regexp-in-string "<" "&lt;" s))
    (setq s (replace-regexp-in-string ">" "&gt;" s))
    (setq s (replace-regexp-in-string "\"" "&quot;" s))
    s))

(defun my/zig-split-tests (code)
  "Return (non-test-code . test-code) from Zig CODE."
  (let ((lines (split-string code "\n"))
        non-test test)
    (while lines
      (let ((line (pop lines)))
        (if (string-match-p "^[[:space:]]*test[[:space:]]+\"" line)
            (let ((block (list line))
                  (done (string= line "}")))
              (while (and lines (not done))
                (let ((next (pop lines)))
                  (push next block)
                  (setq done (string= next "}"))))
              (setq test (append test (nreverse block) '(""))))
          (push line non-test))))
    (cons (string-trim-right (mapconcat #'identity (nreverse non-test) "\n"))
          (string-trim-right (mapconcat #'identity test "\n")))))

(defun my/org-current-title ()
  "Return the current buffer title, or the file base name."
  (save-excursion
    (goto-char (point-min))
    (if (re-search-forward "^#\\+title:[ \t]*\\(.+\\)$" nil t)
        (string-trim (match-string 1))
      (file-name-base (or buffer-file-name "")))))

(defun my/org-section-title (note-title)
  "Return NOTE-TITLE plus the current Org outline path."
  (let (path)
    (save-excursion
      (unless (looking-at "^\\(\\*+\\) +\\(.+\\)$")
        (re-search-backward "^\\(\\*+\\) +\\(.+\\)$" nil t))
      (when (looking-at "^\\(\\*+\\) +\\(.+\\)$")
        (let ((level (length (match-string 1))))
          (push (string-trim (match-string 2)) path)
          (while (re-search-backward "^\\(\\*+\\) +\\(.+\\)$" nil t)
            (let ((candidate-level (length (match-string 1))))
              (when (< candidate-level level)
                (push (string-trim (match-string 2)) path)
                (setq level candidate-level)))))))
    (if path
        (string-join (cons note-title path) " / ")
      note-title)))

(defun my/org-nearest-api-marker-title (note-title pos)
  "Return NOTE-TITLE plus the nearest API or Interface marker before POS."
  (save-excursion
    (goto-char pos)
    (when (re-search-backward "^#\\+\\(api\\|interface\\):[[:space:]]*$" nil t)
      (format "%s / %s"
              note-title
              (if (string= (match-string 1) "api") "API" "Interface")))))

(defun my/org-enclosing-code-section-title (note-title pos)
  "Return the main-text section title for code at POS."
  (save-excursion
    (goto-char pos)
    (if (org-before-first-heading-p)
        (or (my/org-nearest-api-marker-title note-title pos) note-title)
      (org-back-to-heading t)
      (my/org-section-title note-title))))

(defun my/org-previous-code-section-title (note-title pos)
  "Return the previous non-test section title before POS."
  (save-excursion
    (goto-char pos)
    (catch 'title
      (while (re-search-backward "^\\*+ +\\(.+\\)$" nil t)
        (let ((title (string-trim (match-string 1))))
          (unless (string-match-p "\\(Test\\|Checks\\)" title)
            (throw 'title (my/org-section-title note-title)))))
      (or (my/org-nearest-api-marker-title note-title pos) note-title))))

(defun my/test-items-add (items title body)
  "Add BODY under TITLE, preserving source order while scanning backward."
  (let ((entry (assoc title items)))
    (if entry
        (setcar (cdr entry) (concat body "\n\n" (cadr entry)))
      (push (list title body) items)))
  items)

(defun my/org-src-block-content ()
  "Return the current source block content between begin/end lines."
  (let ((beg (save-excursion (forward-line 1) (point)))
        (end (save-excursion
               (re-search-forward "^[[:space:]]*#\\+end_src[[:space:]]*$" nil t)
               (match-beginning 0))))
    (buffer-substring-no-properties beg end)))

(defun my/org-zig-src-blocks-have-only-tests-p (beg end)
  "Return non-nil when every Zig block in BEG..END is empty after test removal."
  (let ((has-test nil)
        (has-non-test nil))
    (save-excursion
      (goto-char beg)
      (while (re-search-forward "^[[:space:]]*#\\+begin_src[[:space:]]+zig\\b.*$" end t)
        (let* ((block-line (buffer-substring-no-properties
                            (line-beginning-position) (line-end-position)))
               (content (my/org-src-block-content))
               (split (my/zig-split-tests content))
               (non-test (car split))
               (tests (cdr split)))
          (unless (string-match-p ":tangle[[:space:]]+no" block-line)
            (when (not (string-empty-p (string-trim tests)))
              (setq has-test t))
            (when (not (string-empty-p (string-trim non-test)))
              (setq has-non-test t))))))
    (and has-test (not has-non-test))))

(defun my/org-extract-test-subtrees (note-title)
  "Remove test-only subtrees and return ((title body) ...)."
  (let (items)
    (save-excursion
      (goto-char (point-max))
      (while (re-search-backward "^\\(\\*+\\)[[:space:]]+\\(.+\\)$" nil t)
        (let* ((title (string-trim (match-string 2)))
               (beg (line-beginning-position))
               (body-beg (save-excursion (forward-line 1) (point)))
               (end (save-excursion (org-end-of-subtree t t)))
               (test-title-p (string-match-p "\\(Test\\|Checks\\)" title)))
          (when (and test-title-p
                     (my/org-zig-src-blocks-have-only-tests-p beg end))
            (let ((body (string-trim
                         (buffer-substring-no-properties body-beg end)))
                  (section-title (my/org-previous-code-section-title note-title beg)))
              (setq items (my/test-items-add items section-title body))
              (delete-region beg end))))))
    (nreverse items)))

(defun my/org-extract-tests-from-src-blocks (note-title)
  "Remove Zig test declarations from mixed source blocks and return test items."
  (let (items)
    (save-excursion
      (goto-char (point-max))
      (while (re-search-backward "^[[:space:]]*#\\+begin_src[[:space:]]+zig\\b.*$" nil t)
        (let* ((block-beg (line-beginning-position))
               (block-line (buffer-substring-no-properties
                            (line-beginning-position) (line-end-position)))
               (content-beg (save-excursion (forward-line 1) (point)))
               (block-end (save-excursion
                            (re-search-forward "^[[:space:]]*#\\+end_src[[:space:]]*$" nil t)
                            (point)))
               (content-end (save-excursion
                              (goto-char content-beg)
                              (re-search-forward "^[[:space:]]*#\\+end_src[[:space:]]*$" nil t)
                              (match-beginning 0)))
               (content (buffer-substring-no-properties content-beg content-end))
               (split (my/zig-split-tests content))
               (non-test (car split))
               (tests (cdr split))
               (section-title (my/org-enclosing-code-section-title note-title block-beg)))
          (unless (or (string-match-p ":tangle[[:space:]]+no" block-line)
                      (string-empty-p (string-trim tests)))
            (setq items
                  (my/test-items-add
                   items section-title
                   (concat "#+begin_src zig\n" tests "\n#+end_src")))
            (if (string-empty-p (string-trim non-test))
                (delete-region block-beg block-end)
              (delete-region content-beg content-end)
              (goto-char content-beg)
              (insert non-test "\n"))))))
    (nreverse items)))

(defun my/org-append-tests-toggle (items)
  "Append ITEMS as a hidden Tests toggle at the bottom of the HTML page."
  (when items
    (goto-char (point-max))
    (insert "\n#+html: <div class=\"toc-nav api-section tests-section\">\n")
    (insert "#+html: <div class=\"toc-section\">\n")
    (insert "#+html:   <div class=\"toc-row\"><span class=\"toc-toggle\"></span><span class=\"toc-folder\">Tests</span></div>\n")
    (insert "#+html:   <div class=\"toc-entries\" hidden>\n")
    (dolist (item items)
      (insert (format "#+html: <p class=\"api-kind\"><b>%s</b></p>\n"
                      (my/html-escape (nth 0 item))))
      (insert (nth 1 item) "\n\n"))
    (insert "#+html:   </div>\n")
    (insert "#+html: </div>\n")
    (insert "#+html: </div>\n")))

(defun my/org-move-tests-to-toggle (backend)
  "Move test-only material to a hidden bottom toggle during HTML export."
  (when (eq backend 'html)
    (let* ((note-title (my/org-current-title))
           (items (append (my/org-extract-test-subtrees note-title)
                          (my/org-extract-tests-from-src-blocks note-title))))
      (my/org-append-tests-toggle items))))

(add-hook 'org-export-before-processing-hook #'my/org-move-tests-to-toggle)

(defun my/update-id-locations ()
  "Update project-local Org ID cache."
  (let ((files (my/org-files)))
    (when files
      (org-id-update-id-locations files))))

(defun my/org-id-link-to-html (id)
  "Return public HTML path for Org ID."
  (let ((file (org-id-find-id-file id)))
    (when file
      (concat "/notes/"
              (file-name-sans-extension
               (file-relative-name file my/site-source-dir))
              ".html"))))

(defun my/org-html-preamble (_plist)
  "HTML preamble for every exported note: nav bar + site sidebar."
  (concat
   "<nav id=\"site-nav\">\n"
   "  <span class=\"site-title\"></span>\n"
   "  <a href=\"/\">Home</a>\n"
   "  <a href=\"/api/\">API</a>\n"
   "  <a href=\"/all-notes.pdf\">PDF</a>\n"
   "  <a href=\"/graph/\">Graph</a>\n"
   "  <button class=\"theme-toggle\" onclick=\"toggleTheme()\">☀</button>\n"
   "</nav>\n"
   (my/gen-site-sidebar)))

;; Export org-roam-style id: links as static HTML links.
(org-link-set-parameters
 "id"
 :export
 (lambda (id desc backend _info)
   (cond
    ((eq backend 'html)
     (let ((path (my/org-id-link-to-html id)))
       (if path
           (format "<a href=\"%s\">%s</a>"
                   path
                   (my/html-escape (or desc id)))
         (my/html-escape (or desc id)))))
    (t
     (or desc id)))))

;; ---------------------------------------------------------------------
;; KaTeX — defined before org-publish-project-alist uses it.
;; Synchronous render, no layout shift, ~200 KB vs ~1 MB for MathJax.
;; ---------------------------------------------------------------------

(setq org-html-with-latex 'verbatim)  ; leave \(...\) for KaTeX, don't inject MathJax

(defconst my/katex-head
  (concat
   "<link rel=\"preconnect\" href=\"https://cdn.jsdelivr.net\">\n"
   "<link rel=\"stylesheet\""
   " href=\"https://cdn.jsdelivr.net/npm/katex@0.16/dist/katex.min.css\">\n"
   "<script defer"
   " src=\"https://cdn.jsdelivr.net/npm/katex@0.16/dist/katex.min.js\"></script>\n"
   "<script defer"
   " src=\"https://cdn.jsdelivr.net/npm/katex@0.16/dist/contrib/auto-render.min.js\""
   " onload=\"renderMathInElement(document.body,{delimiters:["
   "{left:'\\\\(',right:'\\\\)',display:false},"
   "{left:'\\\\[',right:'\\\\]',display:true},"
   "{left:'\\\\begin{equation}',right:'\\\\end{equation}',display:true},"
   "{left:'\\\\begin{align}',right:'\\\\end{align}',display:true},"
   "{left:'\\\\begin{align*}',right:'\\\\end{align*}',display:true}"
   "]})\"></script>")
  "KaTeX CDN scripts — preconnect, stylesheet, renderer.")

;; ---------------------------------------------------------------------
;; Org publish project
;; ---------------------------------------------------------------------

(defun my/org-html-postamble (plist)
  "Show git last-modified date in the page footer."
  (let* ((file (plist-get plist :input-file))
         (date (when file
                 (string-trim
                  (shell-command-to-string
                   (format "git -C %s log -1 --format=%%ad --date=short -- %s 2>/dev/null"
                           (shell-quote-argument my/site-root)
                           (shell-quote-argument file)))))))
    (if (and date (not (string-empty-p date)))
        (format "<p class=\"postamble-date\">Last updated: %s</p>" date)
      "")))

(setq org-publish-project-alist
      `(("roam-notes"
         :base-directory ,my/site-source-dir
         :base-extension "org"
         :publishing-directory ,my/site-public-notes-dir
         :recursive t
         :exclude "\\(^\\|/\\)ordering\\.org$"
         :publishing-function org-html-publish-to-html

         ;; HTML export settings
         :with-author nil
         :with-creator t
         :with-toc t
         :section-numbers nil
         :html-head-include-default-style nil
         :html-head ,(concat "<link rel=\"stylesheet\" href=\"/style.css\">\n"
                             my/katex-head "\n"
                             "<script src=\"/theme.js\"></script>"
                             "<script defer src=\"/sidebar.js\"></script>")
         :html-preamble my/org-html-preamble
         :html-postamble my/org-html-postamble)

        ("roam-site"
         :components ("roam-notes"))))

;; ---------------------------------------------------------------------
;; Index generation
;; ---------------------------------------------------------------------

(defun my/page-shell (title stylesheet &rest body-parts)
  "Return a complete HTML page string with TITLE, STYLESHEET href, and BODY-PARTS."
  (concat
   "<!doctype html>\n<html lang=\"en\">\n<head>\n"
   "  <meta charset=\"utf-8\">\n"
   "  <meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n"
   (format "  <title>%s</title>\n" (my/html-escape title))
   (format "  <link rel=\"stylesheet\" href=\"%s\">\n" stylesheet)
   "  <script src=\"/theme.js\"></script>\n"
   "  <script defer src=\"/sidebar.js\"></script>\n"
   (mapconcat (lambda (l) (concat "  " l "\n"))
              (split-string my/katex-head "\n" t) "")
   "\n"
   "</head>\n<body>\n"
   "<div id=\"preamble\" class=\"status\">\n"
   "<nav id=\"site-nav\">\n"
   "  <span class=\"site-title\"></span>\n"
   "  <a href=\"/\">Home</a>\n"
   "  <a href=\"/api/\">API</a>\n"
   "  <a href=\"/all-notes.pdf\">PDF</a>\n"
   "  <a href=\"/graph/\">Graph</a>\n"
   "  <button class=\"theme-toggle\" onclick=\"toggleTheme()\">☀</button>\n"
   "</nav>\n"
   (my/gen-site-sidebar)
   "</div>\n"
   (apply #'concat body-parts)
   "</body>\n</html>\n"))

(defun my/folder-main-note (dir)
  "Return the primary note for DIR: the .org file named after the directory, or nil."
  (let* ((name      (file-name-nondirectory (directory-file-name dir)))
         (candidate (expand-file-name (concat name ".org") dir)))
    (when (file-exists-p candidate) candidate)))

(defun my/folder-notes (dir)
  "Return notes directly in DIR, excluding ordering/index and the main note."
  (let ((main (my/folder-main-note dir))
        acc)
    (dolist (f (my/org-files-direct dir))
      (unless (or (member (file-name-base f) '("ordering" "index"))
                  (and main (string= (file-truename f) (file-truename main))))
        (push f acc)))
    (nreverse acc)))

(defun my/dir-subdirs (dir)
  "Return immediate subdirectories of DIR that contain org files."
  (let (result)
    (dolist (e (directory-files dir t "^[^.]"))
      (when (and (file-directory-p e)
                 (directory-files e nil "\\.org$"))
        (push e result)))
    (sort result #'string<)))

(defun my/folder-url (dir)
  "Return the URL for DIR's landing page: the main note if present, else the folder."
  (let ((main (my/folder-main-note dir)))
    (if main
        (my/file-to-html-path main)
      (concat "/notes/" (file-relative-name dir my/site-source-dir) "/"))))

(defun my/folder-label (dir)
  "Return display label for DIR: #+title of the main note, or the dir name."
  (let ((main (my/folder-main-note dir)))
    (if main
        (my/org-file-title main)
      (capitalize (replace-regexp-in-string "[-_]" " "
                   (file-name-nondirectory dir))))))

(defun my/landing-section-html (dir)
  "Like `my/sidebar-section-html' but entries are visible by default."
  (let* ((url     (my/folder-url dir))
         (label   (my/html-escape (my/folder-label dir)))
         (subdirs (my/dir-subdirs dir))
         (notes   (my/folder-notes dir)))
    (concat
     "<div class=\"toc-section\">\n"
     "  <div class=\"toc-row\">\n"
     "    <span class=\"toc-toggle open\"></span>\n"
     (format "    <a href=\"%s\" class=\"toc-folder\">%s</a>\n" url label)
     "  </div>\n"
     (when (or notes subdirs)
       (concat
        "  <ul class=\"toc-entries\">\n"   ; no hidden
        (mapconcat #'my/landing-section-html subdirs "")
        (mapconcat
         (lambda (f)
           (format "    <li><a href=\"%s\">%s</a></li>\n"
                   (my/file-to-html-path f)
                   (my/html-escape (my/org-file-title f))))
         notes "")
        "  </ul>\n"))
     "</div>\n")))

(defun my/sidebar-section-html (dir)
  "Return a sidebar section for DIR with toggle support (entries start hidden)."
  (let* ((url     (my/folder-url dir))
         (label   (my/html-escape (my/folder-label dir)))
         (subdirs (my/dir-subdirs dir))
         (notes   (my/folder-notes dir)))
    (concat
     "<div class=\"toc-section\">\n"
     "  <div class=\"toc-row\">\n"
     "    <span class=\"toc-toggle\"></span>\n"
     (format "    <a href=\"%s\" class=\"toc-folder\">%s</a>\n" url label)
     "  </div>\n"
     (when (or notes subdirs)
       (concat
        "  <ul class=\"toc-entries\" hidden>\n"
        (mapconcat #'my/sidebar-section-html subdirs "")
        (mapconcat
         (lambda (f)
           (format "    <li><a href=\"%s\">%s</a></li>\n"
                   (my/file-to-html-path f)
                   (my/html-escape (my/org-file-title f))))
         notes "")
        "  </ul>\n"))
     "</div>\n")))

(defun my/root-note-entry-html (file)
  "Return a toc-section entry for a single root-level note FILE."
  (format
   "<div class=\"toc-section\"><div class=\"toc-row\"><a href=\"%s\" class=\"toc-folder\">%s</a></div></div>\n"
   (my/file-to-html-path file)
   (my/html-escape (my/org-file-title file))))

(defun my/gen-site-sidebar ()
  "Return the <aside id=\"site-sidebar\"> HTML with collapsible sections."
  (let ((root-notes (my/folder-notes my/site-source-dir))
        (subdirs    (my/org-immediate-subdirs)))
    (concat
     "<aside id=\"site-sidebar\" class=\"toc-nav\">\n"
     "<p class=\"toc-nav-label\">Table of Contents</p>\n"
     (mapconcat #'my/root-note-entry-html root-notes "")
     (mapconcat #'my/sidebar-section-html subdirs "")
     "</aside>\n")))

(defun my/generate-index ()
  "Generate public/index.html as a table of contents."
  (let* ((index-file (expand-file-name "index.html" my/site-public-dir))
         (subdirs    (my/org-immediate-subdirs))
         (top-files  (my/folder-notes my/site-source-dir)))
    (with-temp-file index-file
      (insert
       (my/page-shell
        "Home" "style.css"
        "<div class=\"page-content\">\n"
        "<p class=\"toc-intro\">Below you see the table of contents.</p>\n"
        "<div class=\"resources\">\n"
        "  <a href=\"all-notes.pdf\">Combined PDF</a>\n"
        "  <a href=\"graph/\">Knowledge Graph</a>\n"
        "</div>\n"
        "<nav class=\"toc-nav landing-toc\">\n"
        (mapconcat #'my/root-note-entry-html top-files "")
        (mapconcat #'my/landing-section-html subdirs "")
        "</nav>\n"
        "</div>\n")))))


;; ---------------------------------------------------------------------
;; Graph placeholder
;; ---------------------------------------------------------------------

(defun my/generate-graph-placeholder ()
  "Generate public/graph/index.html if org-roam-ui output is not present."
  (let ((graph-index (expand-file-name "index.html" my/site-public-graph-dir)))
    (unless (file-exists-p graph-index)
      (with-temp-file graph-index
        (insert "<!doctype html>\n")
        (insert "<html>\n")
        (insert "<head>\n")
        (insert "  <meta charset=\"utf-8\">\n")
        (insert "  <meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n")
        (insert "  <title>Org-Roam Graph</title>\n")
        (insert "</head>\n")
        (insert "<body>\n")
        (insert "  <h1>Org-Roam Graph</h1>\n")
        (insert "  <p>The static org-roam-ui graph has not been copied here yet.</p>\n")
        (insert "  <p>Generate it with <code>publish-org-roam-ui</code>, then copy its output into <code>public/graph/</code>.</p>\n")
        (insert "  <p><a href=\"../index.html\">Back to index</a></p>\n")
        (insert "</body>\n")
        (insert "</html>\n")))))

;; ---------------------------------------------------------------------
;; API reference page
;; ---------------------------------------------------------------------

(defun my/generate-api-page ()
  "Generate public/api/index.html aggregating pub APIs from all package roots."
  (let* ((api-dir  (expand-file-name "api/" my/site-public-dir))
         (api-file (expand-file-name "index.html" api-dir))
         (parts    (delq nil
                         (mapcar #'my/folder-main-note
                                 (my/org-immediate-subdirs)))))
    (make-directory api-dir t)
    (with-temp-file api-file
      (insert
       (my/page-shell
        "API Reference" "../style.css"
        "<div class=\"page-content\">\n"
        "<h1>API Reference</h1>\n"
        (mapconcat
         (lambda (file)
           (let* ((title (my/org-file-title file))
                  (url   (my/file-to-html-path file))
                  (sigs  (with-temp-buffer
                           (insert-file-contents file)
                           (my/zig-pub-sigs))))
             (when sigs
               (concat
                (format
                 "<div class=\"toc-nav api-section\">\n<div class=\"toc-section\">\n  <div class=\"toc-row\"><span class=\"toc-toggle open\"></span><a href=\"%s\" class=\"toc-folder\">%s</a></div>\n  <div class=\"toc-entries\">\n<dl>\n"
                 url (my/html-escape title))
                (mapconcat
                 (lambda (s)
                   (concat
                    (format "  <dt><a href=\"%s#%s\"><code>%s</code></a></dt>\n"
                            url (my/html-escape (nth 0 s)) (my/html-escape (nth 1 s)))
                    (when (nth 2 s)
                      (format "  <dd>%s</dd>\n" (my/html-escape (nth 2 s))))))
                 sigs "")
                "</dl>\n  </div>\n</div>\n</div>\n"))))
         parts "")
        "</div>\n")))))

;; ---------------------------------------------------------------------
;; Main entry point
;; ---------------------------------------------------------------------

(defun my/publish-site ()
  "Publish project-local Org files as a static site."
  (interactive)

  (unless (file-directory-p my/site-source-dir)
    (error "Source notes directory does not exist: %s" my/site-source-dir))

  (message "Project root: %s" my/site-root)
  (message "Source notes: %s" my/site-source-dir)
  (message "Public site:  %s" my/site-public-dir)

  (my/update-id-locations)
  ;; Incremental mode (--watch rebuilds): only export files newer than cache.
  (org-publish "roam-site" (not (equal (getenv "INCREMENTAL") "1")))
  (my/generate-index)
  (my/generate-api-page)
  (my/generate-graph-placeholder)

  (message "Published site to: %s" my/site-public-dir))

;;; Run automatically in batch mode.
(my/publish-site)
