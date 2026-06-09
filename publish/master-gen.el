;;; master-gen.el — Build all-notes-master.org.
;;;
;;; Two separate files serve different roles:
;;;   overview.org   — project intro prose (optional); becomes the opening section
;;;   ordering.org   — navigation entry point; links determine what's included and in
;;;                    what order; contains no prose of its own
;;;
;;; Paths via environment variables:
;;;   ORDERING_ORG   root ordering.org (required)
;;;   OVERVIEW_ORG   root overview.org (optional, "" if absent)
;;;   NOTES_DIR      root directory of org source files
;;;   MASTER_ORG     output path for the combined master org file
;;;   CLEAN_DIR      scratch directory for sanitized note copies

(require 'org)
(require 'org-id)
(require 'subr-x)

(defvar mgn/test-appendix nil
  "Collected test appendix entries as (source-file title test-path) triples.")

(defvar mgn/current-label-prefix nil
  "Prefix used to namespace generated LaTeX labels for the current note.")

;; ---- helpers ---------------------------------------------------------------

(defun mgn/sanitize-id (id)
  (replace-regexp-in-string "[^a-zA-Z0-9-]" "-" id))

(defun mgn/folder-display-name (dir)
  (capitalize (replace-regexp-in-string "[-_]" " "
               (file-name-nondirectory (directory-file-name dir)))))

(defun mgn/resolve-link (type path index-dir)
  (cond
   ((string= type "file")
    (let ((f (expand-file-name path index-dir)))
      (cond
       ;; Directory link: look for ordering.org inside it
       ((file-directory-p f)
        (let ((sub (expand-file-name "ordering.org" f)))
          (when (file-exists-p sub) sub)))
       ((file-exists-p f) f))))
   ((string= type "id")
    (let ((m (org-id-find path t)))
      (when m (buffer-file-name (marker-buffer m)))))))

(defun mgn/clean-path (file clean-dir notes-dir)
  (let* ((rel  (file-relative-name file notes-dir))
         (safe (replace-regexp-in-string "[/\\\\]" "_" rel)))
    (expand-file-name safe clean-dir)))

(defun mgn/label-prefix (file notes-dir)
  "Return a stable label prefix for FILE relative to NOTES-DIR."
  (let* ((rel (file-name-sans-extension (file-relative-name file notes-dir)))
         (raw (replace-regexp-in-string "[/\\\\]" "--" rel)))
    (mgn/sanitize-id raw)))

(defun mgn/pdf-label (name)
  "Return the namespaced LaTeX label for public declaration NAME."
  (if mgn/current-label-prefix
      (format "decl:%s:%s" mgn/current-label-prefix (mgn/sanitize-id name))
    (mgn/sanitize-id name)))

(defun mgn/latex-escape (text)
  "Escape TEXT for generated LaTeX prose."
  (let ((s (or text "")))
    (setq s (replace-regexp-in-string "\\\\" "\\textbackslash{}" s nil t))
    (setq s (replace-regexp-in-string "{" "\\{" s nil t))
    (setq s (replace-regexp-in-string "}" "\\}" s nil t))
    (setq s (replace-regexp-in-string "%" "\\%" s nil t))
    (setq s (replace-regexp-in-string "&" "\\&" s nil t))
    (setq s (replace-regexp-in-string "#" "\\#" s nil t))
    (setq s (replace-regexp-in-string "_" "\\_" s nil t))
    (setq s (replace-regexp-in-string "\\^" "\\textasciicircum{}" s nil t))
    (setq s (replace-regexp-in-string "~" "\\textasciitilde{}" s nil t))
    s))

(defun mgn/zig-clean-sig (raw)
  (let ((s (string-trim (replace-regexp-in-string
                         "[[:space:]]+" " "
                         (replace-regexp-in-string "{.*$" "" raw)))))
    (setq s (replace-regexp-in-string "([ \t]+" "(" s))
    (setq s (replace-regexp-in-string "[ \t]+)" ")" s))
    (setq s (replace-regexp-in-string ",)" ")" s))
    s))

(defun mgn/zig-all-pub-names ()
  "Return list of all top-level pub declaration names in the zig block after point."
  (let ((case-fold-search nil)   ; [A-Z] must mean uppercase only
        names)
    (save-excursion
      (forward-line 1)
      (while (not (looking-at "^[ \t]*#\\+end_src"))
        (let ((ln (buffer-substring-no-properties
                   (line-beginning-position) (line-end-position))))
          (cond
           ((string-match "^pub \\(?:inline \\)?fn \\([a-zA-Z_][a-zA-Z0-9_]*\\)" ln)
            (push (match-string 1 ln) names))
           ((string-match "^pub const \\([a-zA-Z_][a-zA-Z0-9_]*\\)[[:space:]]*=" ln)
            (push (match-string 1 ln) names))))
        (forward-line 1)))
    (nreverse names)))

(defun mgn/zig-inject-labels ()
  "Inject namespaced #+name: and LaTeX labels before unnamed public Zig blocks.
The labels back the generated PDF API links.  They are namespaced by source note
so common declaration names such as Handle do not collide across modules."
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
                        (string-match-p "^[ \t]*#\\+name:" prev))
              (let ((pub-names (mgn/zig-all-pub-names)))
                (when pub-names
                  (goto-char block-pos)
                  ;; One \phantomsection\label per pub declaration; #+name for the first.
                  (dolist (n pub-names)
                    (insert (format "#+latex: \\phantomsection\\label{%s}\n"
                                    (mgn/pdf-label n))))
                  (insert (format "#+name: %s\n" (mgn/pdf-label (car pub-names)))))))))))))

(defun mgn/zig-pub-sigs ()
  "Extract ordered (name sig doc kind) lists from pub zig declarations in current buffer.
Extracts /// doc comments immediately preceding each pub declaration."
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
           ((and in-src (string-match "^[ \t]*///[[:space:]]?\\(.*\\)$" line))
            (push (match-string 1 line) doc-lines))
           ((and in-src collecting)
            (push (string-trim line) parts-buf)
            (unless (string-match-p "^[ \t]*$" line) (setq doc-lines nil))
            (when (string-match-p "{" line)
              (let* ((sig (mgn/zig-clean-sig
                           (mapconcat #'identity (nreverse parts-buf) " ")))
                     (doc (when doc-buf
                            (string-trim
                             (mapconcat #'identity (nreverse doc-buf) " ")))))
                (unless (member name-buf seen)
                  (push name-buf seen)
                  (push (list name-buf (concat name-buf sig) doc "fn") result)))
              (setq collecting nil name-buf nil parts-buf nil doc-buf nil)))
           (in-src
            (let (name sig kind)
              (cond
               ((and (string-match
                      "^pub \\(?:inline \\)?fn \\([a-zA-Z_][a-zA-Z0-9_]*\\)\\(.*\\)$"
                      line)
                     (string-match-p ")" line))
                (setq name (match-string 1 line)
                      sig  (concat name (mgn/zig-clean-sig (match-string 2 line)))
                      kind "fn"))
               ((string-match
                 "^pub \\(?:inline \\)?fn \\([a-zA-Z_][a-zA-Z0-9_]*\\)\\(.*\\)$"
                 line)
                (let ((n (match-string 1 line)))
                  (unless (member n seen)
                    (setq collecting t name-buf n
                          doc-buf (copy-sequence doc-lines)
                          parts-buf (list (string-trim (match-string 2 line)))))
                  (setq doc-lines nil)))
               ((string-match
                 "^pub const \\([A-Z][a-zA-Z0-9_]*\\)[[:space:]]*=[[:space:]]*\\(struct\\|enum\\|union\\|opaque\\|error\\)"
                 line)
                (setq name (match-string 1 line)
                      sig  (format "%s (%s)" name (match-string 2 line))
                      kind (if (string= (match-string 2 line) "error") "error" "type")))
               ;; Type alias: pub const Name = SomeType; (no block follows)
               ((string-match
                 "^pub const \\([A-Z][a-zA-Z0-9_]*\\)[[:space:]]*=[[:space:]]*\\([^{;\n]+\\);[[:space:]]*$"
                 line)
                (setq name (match-string 1 line)
                      sig  (format "%s = %s" name (string-trim (match-string 2 line)))
                      kind "type"))
               ;; Lowercase constants include module-boundary exports.
               ((string-match
                 "^pub const \\([a-z_][a-zA-Z0-9_]*\\)[[:space:]]*=[[:space:]]*\\([^;\n]+\\);[[:space:]]*$"
                 line)
                (setq name (match-string 1 line)
                      sig  (format "%s = %s" name (string-trim (match-string 2 line)))
                      kind "const"))
               ((string-match
                 "^pub const \\([a-z_][a-zA-Z0-9_]*\\)[[:space:]]*:[[:space:]]*\\([^={(\n]+\\)"
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
               ((not (string-match-p "^[ \t]*\\(?://\\|$\\)" line))
                (setq doc-lines nil)))))))
        (forward-line 1)))
    (nreverse result)))

(defun mgn/latex-escape-sig (sig)
  "Escape underscores in SIG for use inside \\texttt{} in LaTeX."
  (replace-regexp-in-string "_" "\\\\_" sig))

(defun mgn/zig-split-tests (code)
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

(defun mgn/org-heading-path ()
  "Return the current Org outline path from manual heading scans."
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
    path))

(defun mgn/org-nearest-api-marker-path (pos)
  "Return the nearest API or Interface marker before POS as a heading path."
  (save-excursion
    (goto-char pos)
    (when (re-search-backward "^#\\+\\(api\\|interface\\):[[:space:]]*$" nil t)
      (list (if (string= (match-string 1) "api") "API" "Interface")))))

(defun mgn/org-enclosing-code-section-path (pos)
  "Return the main-text section path for code at POS."
  (save-excursion
    (goto-char pos)
    (if (org-before-first-heading-p)
        (or (mgn/org-nearest-api-marker-path pos) (list "Tests"))
      (org-back-to-heading t)
      (mgn/org-heading-path))))

(defun mgn/org-previous-code-section-path (pos)
  "Return the previous non-test section path before POS."
  (save-excursion
    (goto-char pos)
    (catch 'title
      (while (re-search-backward "^\\*+ +\\(.+\\)$" nil t)
        (let ((title (string-trim (match-string 1))))
          (unless (string-match-p "\\(Test\\|Checks\\)" title)
            (throw 'title (mgn/org-heading-path)))))
      (or (mgn/org-nearest-api-marker-path pos) (list "Tests")))))

(defun mgn/test-items-add (items path body)
  "Add BODY under PATH, preserving source order while scanning backward."
  (let ((entry (assoc path items)))
    (if entry
        (setcar (cdr entry) (concat body "\n\n" (cadr entry)))
      (push (list path body) items)))
  items)

(defun mgn/org-src-block-content ()
  "Return the current source block content between begin/end lines."
  (let ((beg (save-excursion (forward-line 1) (point)))
        (end (save-excursion
               (re-search-forward "^[[:space:]]*#\\+end_src[[:space:]]*$" nil t)
               (match-beginning 0))))
    (buffer-substring-no-properties beg end)))

(defun mgn/org-zig-src-blocks-have-only-tests-p (beg end)
  "Return non-nil when every Zig block in BEG..END is empty after test removal."
  (let ((has-test nil)
        (has-non-test nil))
    (save-excursion
      (goto-char beg)
      (while (re-search-forward "^[[:space:]]*#\\+begin_src[[:space:]]+zig\\b.*$" end t)
        (let* ((block-line (buffer-substring-no-properties
                            (line-beginning-position) (line-end-position)))
               (content (mgn/org-src-block-content))
               (split (mgn/zig-split-tests content))
               (non-test (car split))
               (tests (cdr split)))
          (unless (string-match-p ":tangle[[:space:]]+no" block-line)
            (when (not (string-empty-p (string-trim tests)))
              (setq has-test t))
            (when (not (string-empty-p (string-trim non-test)))
              (setq has-non-test t))))))
    (and has-test (not has-non-test))))

(defun mgn/org-extract-test-subtrees ()
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
                     (mgn/org-zig-src-blocks-have-only-tests-p beg end))
            (let ((body (string-trim
                         (buffer-substring-no-properties body-beg end)))
                  (section-path (mgn/org-previous-code-section-path beg)))
              (setq items (mgn/test-items-add items section-path body))
              (delete-region beg end))))))
    (nreverse items)))

(defun mgn/org-extract-tests-from-src-blocks ()
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
               (split (mgn/zig-split-tests content))
               (non-test (car split))
               (tests (cdr split))
               (section-path (mgn/org-enclosing-code-section-path block-beg)))
          (unless (or (string-match-p ":tangle[[:space:]]+no" block-line)
                      (string-empty-p (string-trim tests)))
            (setq items
                  (mgn/test-items-add
                   items section-path
                   (concat "#+begin_src zig\n" tests "\n#+end_src")))
            (if (string-empty-p (string-trim non-test))
                (delete-region block-beg block-end)
              (delete-region content-beg content-end)
              (goto-char content-beg)
              (insert non-test "\n"))))))
    (nreverse items)))

(defun mgn/write-test-appendix-file (_title items clean-path)
  "Write a test-only appendix file for ITEMS next to CLEAN-PATH."
  (let ((test-path (concat clean-path ".tests.org")))
    (with-temp-file test-path
      (dolist (item items)
        (let ((path (or (nth 0 item) '("Tests"))))
          (dotimes (index (length path))
            (insert (make-string (1+ index) ?*) " " (nth index path) "\n\n")))
        (insert (nth 1 item) "\n\n")))
    test-path))

(defun mgn/insert-api-latex (sigs &optional label)
  "Insert LaTeX API listing for SIGS at point, preceded by LABEL (default 'Interface')."
  (let ((title (or label "Interface")))
    (insert (format "#+latex: \\medskip\\noindent{\\textsc{%s}}\\hfill\\rule[0.5ex]{0.75\\linewidth}{0.3pt}\\par\\smallskip\n"
                    title)))
  (dolist (group '(("fn" . "Functions") ("type" . "Types")
                   ("error" . "Errors") ("const" . "Constants")))
    (let ((entries (seq-filter
                    (lambda (s) (string= (nth 3 s) (car group)))
                    sigs)))
      (when entries
        (insert (format (concat "#+latex: \\medskip\\noindent"
                                "{\\small\\textsc{%s}}"
                                "\\par\\nopagebreak"
                                "\\vspace{2pt}\\noindent"
                                "\\rule{\\linewidth}{0.4pt}"
                                "\\par\\nopagebreak\\smallskip\n")
                        (cdr group)))
        (dolist (s entries)
          (insert (format
                   "#+latex: \\noindent\\hyperref[%s]{\\hbox{\\ttfamily %s}}\\par\n"
                   (mgn/pdf-label (nth 0 s))
                   (replace-regexp-in-string
                    ": " ":\\\\hspace{0.25em}"
                    (replace-regexp-in-string "_" "\\\\_" (nth 1 s)))))
          (let ((doc (nth 2 s)))
            (when (and doc (not (string-empty-p doc)))
              (insert (format "#+latex: \\noindent\\hspace{1.5em}{\\small %s}\\par\n"
                              (mgn/latex-escape doc)))))
          (insert "#+latex: \\smallskip\n"))
        (insert "#+latex: \\medskip\n")))))

(defun mgn/populate-api-section ()
  "Populate API docs at #+api: or #+interface: keyword position (LaTeX output)."
  (let ((sigs (mgn/zig-pub-sigs)))
    (when sigs
      (save-excursion
        (goto-char (point-min))
        ;; #+api: → label "API";  #+interface: → label "Interface"
        (when (re-search-forward "^#\\+\\(api\\|interface\\):[[:space:]]*$" nil t)
          (let ((kw (match-string 1)))
            (delete-region (line-beginning-position) (1+ (line-end-position)))
            (mgn/insert-api-latex sigs (if (string= kw "api") "API" "Interface"))))))))

(defun mgn/clean-and-copy (file clean-dir notes-dir)
  "Write a sanitized copy of FILE. Returns (clean-path title file-id)."
  (let (title file-id
        (clean-path (mgn/clean-path file clean-dir notes-dir)))
    (with-temp-buffer
      (insert-file-contents file)
      (goto-char (point-min))
      (when (re-search-forward "^[[:space:]]*#\\+title:[[:space:]]*\\(.*\\)$" nil t)
        (setq title (string-trim (match-string 1))))
      (goto-char (point-min))
      (when (re-search-forward "^[[:space:]]*:ID:[[:space:]]*\\(.+\\)$" nil t)
        (setq file-id (string-trim (match-string 1))))
      ;; Remove :ID: lines but keep :CUSTOM_ID: and other properties
      ;; so that [[#custom-id]] links resolve in the combined PDF.
      (goto-char (point-min))
      (while (re-search-forward "^[[:space:]]*:ID:[[:space:]]+.+$\n?" nil t)
        (replace-match ""))
      ;; Remove property drawers that are now empty.
      (goto-char (point-min))
      (while (re-search-forward
              "^[[:space:]]*:PROPERTIES:[[:space:]]*\n[[:space:]]*:END:[[:space:]]*\n?"
              nil t)
        (replace-match ""))
      (goto-char (point-min))
      (while (re-search-forward
              "^[[:space:]]*#\\+\\(title\\|author\\|options\\|latex_class\\|auto_tangle\\|PROPERTY\\|bibliography\\|print_bibliography\\):.*$"
              nil t)
        (replace-match ""))
      ;; Inject declaration anchors and populate the generated API listing with
      ;; the same note-local namespace, so PDF links do not collide by pub name.
      (let ((mgn/current-label-prefix (mgn/label-prefix file notes-dir)))
        (mgn/zig-inject-labels)
        (mgn/populate-api-section))
      (let ((test-items (append (mgn/org-extract-test-subtrees)
                                (mgn/org-extract-tests-from-src-blocks))))
        (when test-items
          (push (list (file-truename file)
                      (or title (file-name-base file))
                      (mgn/write-test-appendix-file
                       (or title (file-name-base file)) test-items clean-path))
                mgn/test-appendix)))
      (write-region (point-min) (point-max) clean-path nil 'silent))
    (list clean-path (or title (file-name-base file)) file-id)))

;; ---- recursive walker ------------------------------------------------------
;;
;; report class: * → \part, ** → \chapter, *** → \section …
;; depth 0 = root ordering.org; depth 1 folder → * heading → \part
;; depth 1 note  → ** heading → \chapter
;; depth 2 folder → ** heading → \chapter (within parent \part)
;; depth 2 note  → *** heading → \section
;; #+include :minlevel = depth + 2

(defun mgn/walk-ordering (ordering-file clean-dir notes-dir buf seen &optional depth)
  "Follow links in ORDERING-FILE and write sections into BUF.
DEPTH starts at 0 for the root ordering.org.
Returns updated SEEN list."
  (let* ((depth     (or depth 0))
         (index-dir (file-name-directory ordering-file)))
    (with-temp-buffer
      (insert-file-contents ordering-file)
      (org-element-map (org-element-parse-buffer) 'link
        (lambda (link)
          (let* ((type (org-element-property :type link))
                 (path (org-element-property :path link))
                 ;; Capture the link description from the parent ordering file
                 (link-desc (let ((c (org-element-contents link)))
                              (when c (string-trim (org-element-interpret-data c)))))
                 (file (mgn/resolve-link type path index-dir)))
            (when (and file
                       (string-match-p "\\.org\\'" file)
                       (file-exists-p file)
                       (not (string= (file-truename file)
                                     (file-truename ordering-file)))
                       (not (member (file-truename file) seen)))
              (setq seen (cons (file-truename file) seen))
              (if (string= (file-name-nondirectory file) "ordering.org")
                  ;; ---- sub-folder: heading at child-depth stars ----
                  (let* ((child-depth (1+ depth))
                         (stars       (make-string child-depth ?*))
                         (sub-idx     (mgn/parse-ordering file))
                         ;; Prefer the link description from the parent over
                         ;; the sub-ordering.org title (which is always "Ordering")
                         (folder-name (or (and link-desc
                                               (not (string-empty-p link-desc))
                                               link-desc)
                                          (mgn/folder-display-name
                                           (file-name-directory file))))
                         (intro-text  (nth 1 sub-idx))
                         ;; The .org file named after the directory is the
                         ;; main note; include its content directly under the
                         ;; part heading (no extra chapter wrapper).
                         (dir-path    (file-name-directory file))
                         (dir-base    (file-name-nondirectory
                                       (directory-file-name dir-path)))
                         (main-note   (expand-file-name
                                       (concat dir-base ".org") dir-path)))
                    (with-current-buffer buf
                      (insert stars " " folder-name "\n\n")
                      (when intro-text (insert intro-text "\n\n")))
                    ;; Include the main note directly under the part (no heading).
                    (when (and (file-exists-p main-note)
                               (not (member (file-truename main-note) seen)))
                      (setq seen (cons (file-truename main-note) seen))
                      (let* ((info       (mgn/clean-and-copy main-note clean-dir notes-dir))
                             (clean-path (nth 0 info))
                             (file-id    (nth 2 info))
                             (minlevel   (+ depth 2)))
                        (with-current-buffer buf
                          (when file-id
                            (insert (format "#+latex: \\label{orgid:%s}\n"
                                            (mgn/sanitize-id file-id))))
                          (insert (format "#+include: \"%s\" :minlevel %d\n\n"
                                          clean-path minlevel)))))
                    (setq seen (mgn/walk-ordering file clean-dir notes-dir
                                                   buf seen child-depth)))
                ;; ---- regular note ----
                (let* ((info       (mgn/clean-and-copy file clean-dir notes-dir))
                       (clean-path (nth 0 info))
                       (title      (nth 1 info))
                       (file-id    (nth 2 info))
                       (stars      (make-string (1+ depth) ?*))
                       (minlevel   (+ depth 2)))
                  (with-current-buffer buf
                    (insert stars " " title "\n")
                    (when file-id
                      (insert (format "#+latex: \\label{orgid:%s}\n"
                                      (mgn/sanitize-id file-id))))
                    (insert "\n")
                    (insert (format "#+include: \"%s\" :minlevel %d\n\n"
                                    clean-path minlevel))))))))))
	  seen))

(defun mgn/test-entry-for-file (file)
  "Return the collected test appendix entry for FILE, if one exists."
  (let ((truename (file-truename file))
        found)
    (dolist (entry mgn/test-appendix)
      (when (string= truename (nth 0 entry))
        (setq found entry)))
    found))

(defun mgn/insert-test-note (file buf depth)
  "Insert the test appendix section for FILE at DEPTH, if FILE has tests."
  (let ((entry (mgn/test-entry-for-file file)))
    (when entry
      (with-current-buffer buf
        (insert (make-string (1+ depth) ?*) " " (nth 1 entry) "\n\n")
        (insert (format "#+include: \"%s\" :minlevel %d\n\n"
                        (nth 2 entry) (+ depth 2))))
      t)))

(defun mgn/insert-main-note-tests (file buf depth)
  "Insert tests for a folder main note directly under the folder heading."
  (let ((entry (mgn/test-entry-for-file file)))
    (when entry
      (with-current-buffer buf
        (insert (format "#+include: \"%s\" :minlevel %d\n\n"
                        (nth 2 entry) (+ depth 2))))
      t)))

(defun mgn/walk-test-ordering (ordering-file notes-dir buf seen &optional depth)
  "Follow ORDERING-FILE and write only the test appendix hierarchy into BUF.
DEPTH matches `mgn/walk-ordering': root entries are parts, and child entries
become the same chapters and sections as in the main text.  Returns updated
(wrote . seen), where wrote is non-nil when this subtree emitted tests."
  (let* ((depth (or depth 0))
         (index-dir (file-name-directory ordering-file))
         wrote)
    (with-temp-buffer
      (insert-file-contents ordering-file)
      (org-element-map (org-element-parse-buffer) 'link
        (lambda (link)
          (let* ((type (org-element-property :type link))
                 (path (org-element-property :path link))
                 (link-desc (let ((c (org-element-contents link)))
                              (when c (string-trim (org-element-interpret-data c)))))
                 (file (mgn/resolve-link type path index-dir)))
            (when (and file
                       (string-match-p "\\.org\\'" file)
                       (file-exists-p file)
                       (not (string= (file-truename file)
                                     (file-truename ordering-file)))
                       (not (member (file-truename file) seen)))
              (setq seen (cons (file-truename file) seen))
              (if (string= (file-name-nondirectory file) "ordering.org")
                  (let* ((child-depth (1+ depth))
                         (folder-name (or (and link-desc
                                               (not (string-empty-p link-desc))
                                               link-desc)
                                          (mgn/folder-display-name
                                           (file-name-directory file))))
                         (dir-path (file-name-directory file))
                         (dir-base (file-name-nondirectory
                                    (directory-file-name dir-path)))
                         (main-note (expand-file-name
                                     (concat dir-base ".org") dir-path))
                         (child-buf (generate-new-buffer " *test-appendix-subtree*"))
                         child-wrote)
                    (unwind-protect
                        (progn
                          (when (and (file-exists-p main-note)
                                     (not (member (file-truename main-note) seen)))
                            (setq seen (cons (file-truename main-note) seen))
                            (when (mgn/insert-main-note-tests main-note child-buf depth)
                              (setq child-wrote t)))
                          (let ((result (mgn/walk-test-ordering
                                         file notes-dir child-buf seen child-depth)))
                            (when (car result) (setq child-wrote t))
                            (setq seen (cdr result)))
                          (when child-wrote
                            (with-current-buffer buf
                              (insert (make-string child-depth ?*) " " folder-name "\n\n")
                              (insert (with-current-buffer child-buf
                                        (buffer-string))))
                            (setq wrote t)))
                      (kill-buffer child-buf)))
                (when (mgn/insert-test-note file buf depth)
                  (setq wrote t))))))))
    (cons wrote seen)))

(defun mgn/parse-ordering (file)
  "Parse ordering.org FILE, returning (title intro descriptions).
title        — #+title, or nil.
intro        — prose before the first heading, or nil.
descriptions — alist of (heading . body) for annotation (usually empty now)."
  (with-temp-buffer
    (insert-file-contents file)
    (goto-char (point-min))
    (let (title)
      (when (re-search-forward "^[[:space:]]*#\\+title:[[:space:]]*\\(.*\\)$" nil t)
        (setq title (string-trim (match-string 1))))
      (goto-char (point-min))
      (while (re-search-forward "^[[:space:]]*:PROPERTIES:[[:space:]]*$" nil t)
        (let ((beg (match-beginning 0)))
          (if (re-search-forward "^[[:space:]]*:END:[[:space:]]*$" nil t)
              (delete-region beg (min (point-max) (1+ (line-end-position))))
            (goto-char (point-max)))))
      (goto-char (point-min))
      (while (re-search-forward "^[[:space:]]*#\\+[a-zA-Z_]+:.*$" nil t)
        (replace-match ""))
      ;; Collect intro (pre-heading) and heading descriptions
      (goto-char (point-min))
      (let (intro-lines sections cur-heading cur-lines)
        (while (not (eobp))
          (let ((line (buffer-substring-no-properties
                       (line-beginning-position) (line-end-position))))
            (if (string-match "^\\*+ \\(.*\\)$" line)
                (progn
                  (when cur-heading
                    (push (cons cur-heading
                                (string-trim
                                 (mapconcat #'identity (nreverse cur-lines) "\n")))
                          sections))
                  (unless cur-heading
                    (setq intro-lines (nreverse intro-lines)))
                  (setq cur-heading (string-trim (match-string 1 line))
                        cur-lines nil))
              (let ((trimmed (string-trim line)))
                (unless (string= trimmed "")
                  (if cur-heading (push trimmed cur-lines)
                    (push trimmed intro-lines))))))
          (forward-line))
        (when cur-heading
          (push (cons cur-heading
                      (string-trim
                       (mapconcat #'identity (nreverse cur-lines) "\n")))
                sections))
        (list title
              (when intro-lines
                (string-trim (mapconcat #'identity (nreverse intro-lines) "\n")))
              (nreverse sections))))))

;; ---- main ------------------------------------------------------------------

(let* ((ordering-file (getenv "ORDERING_ORG"))
       (overview-file (let ((v (getenv "OVERVIEW_ORG")))
                        (when (and v (not (string= v ""))) v)))
       (notes-dir     (getenv "NOTES_DIR"))
       (master-file   (getenv "MASTER_ORG"))
       (clean-dir     (getenv "CLEAN_DIR")))

  (unless (and ordering-file notes-dir master-file clean-dir)
    (error "master-gen.el: ORDERING_ORG / NOTES_DIR / MASTER_ORG / CLEAN_DIR must be set"))

  (make-directory clean-dir t)

  (let ((buf (get-buffer-create " *master-org*")))
    (with-current-buffer buf
      (erase-buffer)
      (insert "#+title: Combined Notes\n")
      (insert "#+author:\n")
      (insert "#+date:\n")
      (insert "#+options: toc:t num:t H:5 prop:nil d:nil title:nil\n")
      (insert "#+latex_class: report\n")
      ;; Relative path from master .org (project root) to refs.bib
      (insert "#+bibliography: org/refs.bib\n\n"))

    ;; Opening section: overview.org prose (if present)
    (when (and overview-file (file-exists-p overview-file))
      (let* ((ov-info  (mgn/clean-and-copy overview-file clean-dir notes-dir))
             (ov-path  (nth 0 ov-info))
             (ov-title (or (nth 1 ov-info) "Overview")))
        (with-current-buffer buf
          (insert "* " ov-title "\n\n")
          (insert (format "#+include: \"%s\" :minlevel 2\n\n" ov-path)))))

    ;; Walk ordering.org to build the rest
    (mgn/walk-ordering ordering-file clean-dir notes-dir buf
                       (let ((seen (list (file-truename ordering-file))))
                         (when overview-file
                           (push (file-truename overview-file) seen))
                         seen))

    ;; Tests appendix: same note ordering as the main walk, but only branches
    ;; whose notes actually produced tests.
    (when mgn/test-appendix
      (with-current-buffer buf
        (insert "\n#+latex: \\appendix\n")
        ;; The document style resets chapters for each part.  In the appendix
        ;; that would otherwise give each test part a duplicate chapter.A
        ;; hyperlink target, so the appendix anchors include the part counter.
        (insert "#+latex: \\renewcommand{\\theHpart}{appendix.\\arabic{part}}\n")
        (insert "#+latex: \\renewcommand{\\theHchapter}{appendix.\\arabic{part}.\\Alph{chapter}}\n")
        (insert "#+latex: \\renewcommand{\\theHsection}{appendix.\\arabic{part}.\\Alph{chapter}.\\arabic{section}}\n\n")
        (insert "* Tests\n\n"))
      (mgn/walk-test-ordering ordering-file notes-dir buf
                              (let ((seen (list (file-truename ordering-file))))
                                (when overview-file
                                  (push (file-truename overview-file) seen))
                                seen)
                              1))

    ;; Bibliography at the end — biblatex collects all \cite{} from the doc.
    (with-current-buffer buf
      (insert "\n* References\n\n#+print_bibliography:\n"))

    (with-current-buffer buf
      (write-region (point-min) (point-max) master-file nil 'silent))
    (kill-buffer buf))

  (message "master-gen.el: wrote %s" master-file))
