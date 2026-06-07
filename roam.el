;;; roam.el --- Project-isolated Org-roam environment + smart note creation

(let* ((root (file-name-directory (or load-file-name buffer-file-name)))
       (notes-dir (expand-file-name "org/" root))
       (db-file (expand-file-name "org/org-roam.db" root))
       (id-file (expand-file-name "org/.org-id-locations" root)))

  ;; 1. Configure paths explicitly for this local instance
  (setq org-roam-directory notes-dir
        org-roam-db-location db-file)

  ;; 2. Reset database connection to lock onto the project DB file
  (when (and (boundp 'org-roam-db-database) org-roam-db-database)
    (ignore-errors (emacsql-close org-roam-db-database))
    (setq org-roam-db-database nil))

  ;; 3. Force internal IDs to be timestamps
  (setq org-id-method 'ts)
  (setq org-id-locations-file id-file)
  (require 'org-id)
  (setq org-id-track-globally t)

  ;; 4. Default capture template (root-level, plain note)
  (setq org-roam-capture-templates
        '(("d" "default" plain "%?"
           :target (file+head "${slug}.org" "#+title: ${title}\n")
           :unnarrowed t)))

  ;; 5. Force build/sync the database
  (org-roam-db-sync 'force)
  (when (file-directory-p notes-dir)
    (org-id-update-id-locations (directory-files-recursively notes-dir "\\.org$")))

  (message ">>> Isolated Org-roam loaded: %s <<<" (abbreviate-file-name notes-dir)))

;; ---------------------------------------------------------------------------
;; Smart note creation: subdirectory + tangle support
;;
;; Usage: M-x my/roam-new   (or bind to a key, e.g. C-c r n)
;;
;; Prompts:
;;   1. Subdirectory — TAB-completes existing folders; type a new name to create
;;      one; press RET to use the root org/ dir.
;;   2. Title        — the note title (also drives the filename slug).
;;   3. Type         — "note" (blank), "code" (tangle block), "index" (folder index).
;;   For "code": also asks for language and confirms the tangle path.
;; ---------------------------------------------------------------------------

(defun my/roam--subdirs ()
  "Return alist of (relative-path . absolute-path) for all subdirs under notes dir, at any depth."
  (let ((root org-roam-directory)
        result)
    (dolist (abs (directory-files-recursively root "" t))
      (when (file-directory-p abs)
        (push (cons (file-relative-name abs root) abs) result)))
    (nreverse result)))

(defun my/roam--slug (title)
  "Convert TITLE to a safe filename slug."
  (thread-last title
    downcase
    string-trim
    (replace-regexp-in-string "[^a-z0-9]+" "-")
    (replace-regexp-in-string "^-+\\|-+$" "")))

(defconst my/roam--lang-extensions
  '(("zig"    . "zig") ("c"      . "c")   ("cpp"    . "cpp")
    ("rust"   . "rs")  ("go"     . "go")  ("python" . "py")
    ("haskell". "hs")  ("lua"    . "lua") ("js"     . "js")
    ("ts"     . "ts")  ("sh"     . "sh")  ("bash"   . "sh")
    ("nix"    . "nix") ("ocaml"  . "ml")  ("scheme" . "scm"))
  "Map from org src language name to file extension.")

(defun my/roam--tangle-default (subdir slug lang)
  "Suggest a tangle path for SLUG in SUBDIR with LANG.
Path is relative to the .org file being created.
Handles arbitrarily deep SUBDIR like \"programming/concepts\"."
  (let* ((ext      (or (cdr (assoc lang my/roam--lang-extensions)) lang))
         (depth    (if subdir (length (split-string subdir "/" t)) 0))
         (up       (apply #'concat (make-list (1+ depth) "../")))
         (src-path (if subdir
                       (format "%ssrc/%s/%s.%s" up subdir slug ext)
                     (format "../src/%s.%s" slug ext))))
    src-path))

(defun my/roam-new (title subdir type)
  "Create a new org-roam note in SUBDIR (nil = root) with TITLE and TYPE.
TYPE is one of: \"note\", \"code\", \"index\"."
  (interactive
   (let* ((subdir-alist (my/roam--subdirs))
          (subdir-names (cons "(root)" (mapcar #'car subdir-alist)))
          (choice       (completing-read
                         "Folder [TAB = existing, new name = create, RET = root]: "
                         subdir-names nil nil))
          (subdir       (unless (string= choice "(root)") choice))
          (title        (read-string "Title: "))
          (type         (completing-read "Type: " '("note" "code" "ordering")
                                         nil t nil nil "note")))
     (list title subdir type)))

  (let* ((notes-dir   org-roam-directory)
         (target-dir  (if subdir
                          (expand-file-name subdir notes-dir)
                        notes-dir))
         (slug        (my/roam--slug title))
         (ordering-p  (string= type "ordering"))
         ;; ordering.org at any level (root or subfolder); no roam ID
         (filename    (if ordering-p
                          (expand-file-name "ordering.org" target-dir)
                        (expand-file-name (concat slug ".org") target-dir)))
         (node-id     (unless ordering-p (org-id-new))))

    (make-directory target-dir t)

    (if (file-exists-p filename)
        (progn (message "File exists, opening: %s" filename)
               (find-file filename))

      (with-temp-file filename
        ;; Ordering files are plain org files — no roam ID, no properties block.
        (unless ordering-p
          (insert ":PROPERTIES:\n")
          (insert (format ":ID:       %s\n" node-id))
          (insert ":END:\n"))
        (insert (format "#+title: %s\n" title))

        (pcase type
          ;; ------ ordering: pure section ordering, no roam node ------
          ;; ordering.org's only job is to determine the sequence in which
          ;; notes and sub-folders appear in the site TOC and PDF.
          ("ordering"
           (let* ((subdirs
                   (sort (seq-filter #'file-directory-p
                                     (directory-files target-dir t "^[^.]"))
                         #'string<))
                  (org-files
                   (sort (seq-filter
                          (lambda (f)
                            (not (member f '("ordering.org" "overview.org"))))
                          (directory-files target-dir nil "\\.org$"))
                         #'string<)))
             (insert "\n")
             ;; sub-folders: link to ordering.org inside them if it exists,
             ;; otherwise link to the folder path directly
             (dolist (d subdirs)
               (let* ((ord     (expand-file-name "ordering.org" d))
                      (has-ord (file-exists-p ord))
                      (rel     (if has-ord
                                   (file-relative-name ord target-dir)
                                 (concat (file-relative-name d target-dir) "/")))
                      (ttl     (if has-ord
                                   (my/roam--file-title ord)
                                 (capitalize
                                  (replace-regexp-in-string
                                   "[-_]" " " (file-name-nondirectory d))))))
                 (insert (format "* [[file:%s][%s]]\n" rel ttl))))
             ;; then notes in this folder
             (dolist (f org-files)
               (let ((ttl (my/roam--file-title
                           (expand-file-name f target-dir))))
                 (insert (format "* [[file:%s][%s]]\n" f ttl))))
             (insert "\n")))

          ;; ------ code: file-level tangle property, #+interface: marker ------
          ("code"
           (let* ((lang   (completing-read
                           "Language: "
                           (mapcar #'car my/roam--lang-extensions) nil nil))
                  (tangle (read-string
                           (format "Tangle path (relative to %s): " filename)
                           (my/roam--tangle-default subdir slug lang))))
             (insert "#+auto_tangle: t\n")
             (insert (format "#+PROPERTY: header-args:%s :tangle %s :mkdirp yes\n\n"
                             lang tangle))
             (insert "#+interface:\n")))

          ;; ------ note: blank ------
          (_
           (insert "\n"))))

      (find-file filename)
      ;; Ordering files are not roam nodes — skip DB registration entirely.
      (unless ordering-p
        (when (fboundp 'org-roam-db-update-file)
          (org-roam-db-update-file filename))
        (org-id-add-location node-id filename))
      ;; Auto-append to parent ordering.org if it exists.
      (unless ordering-p
        (let* ((ord-file (expand-file-name "ordering.org" target-dir))
               (rel      (file-relative-name filename target-dir))
               (ttl      (my/roam--file-title filename)))
          (when (file-exists-p ord-file)
            (with-current-buffer (find-file-noselect ord-file)
              (goto-char (point-max))
              (unless (bolp) (insert "\n"))
              (insert (format "* [[file:%s][%s]]\n" rel ttl))
              (save-buffer))
            (message "Added to ordering.org: %s" rel))))
      (message "Created: %s" (abbreviate-file-name filename)))))

(defun my/roam-note-to-code (file)
  "Convert an existing note FILE into a code note.
Prompts for language and tangle path (pre-filled via `my/roam--tangle-default').
Adds #+auto_tangle and #+PROPERTY: header-args after the #+title line.
Defaults to the current buffer's file."
  (interactive
   (list (read-file-name "Convert note to code: "
                         (when (buffer-file-name)
                           (file-name-directory (buffer-file-name)))
                         (buffer-file-name)
                         t)))
  (setq file (expand-file-name file))
  (unless (string-match-p "\\.org\\'" file)
    (user-error "Not an org file: %s" file))
  (let* ((notes-dir org-roam-directory)
         ;; Subdir relative to notes root, nil if at root level
         (rel-dir   (file-relative-name (file-name-directory file) notes-dir))
         (subdir    (let ((d (directory-file-name rel-dir)))
                      (if (member d '("." "")) nil d)))
         (slug      (file-name-base file))
         (lang      (completing-read "Language: "
                                     (mapcar #'car my/roam--lang-extensions)
                                     nil nil))
         (tangle    (read-string
                     (format "Tangle path (relative to %s): "
                             (abbreviate-file-name file))
                     (my/roam--tangle-default subdir slug lang))))
    (with-current-buffer (find-file-noselect file)
      (save-excursion
        (goto-char (point-min))
        ;; Remove any pre-existing auto_tangle / header-args lines
        (while (re-search-forward
                "^#\\+\\(auto_tangle\\|PROPERTY:[[:space:]]*header-args\\):.*\n?"
                nil t)
          (replace-match ""))
        ;; Insert the two new lines immediately after #+title:
        (goto-char (point-min))
        (unless (re-search-forward "^#\\+title:.*$" nil t)
          (user-error "No #+title found in %s" file))
        (end-of-line)
        (insert "\n#+auto_tangle: t")
        (insert (format "\n#+PROPERTY: header-args :tangle %s :mkdirp yes" tangle)))
      (save-buffer)
      (pop-to-buffer (current-buffer))
      (message "Converted to code note — tangle → %s" tangle))))

(defun my/roam-rename (new-title)
  "Rename the current org-roam note to NEW-TITLE, updating links and DB."
  (interactive "sNew title: ")
  (unless (and (buffer-file-name) (derived-mode-p 'org-mode))
    (user-error "Not visiting an org-roam file"))
  (let* ((old-file  (buffer-file-name))
         (old-dir   (file-name-directory old-file))
         (new-slug  (my/roam--slug new-title))
         (new-file  (expand-file-name (concat new-slug ".org") old-dir)))
    (when (file-exists-p new-file)
      (user-error "File already exists: %s" new-file))
    ;; Update #+title in the buffer
    (save-excursion
      (goto-char (point-min))
      (if (re-search-forward "^#\\+title:[[:space:]]*.*$" nil t)
          (replace-match (format "#+title: %s" new-title))
        (insert (format "#+title: %s\n" new-title))))
    (save-buffer)
    ;; Rename the file
    (rename-file old-file new-file)
    (set-visited-file-name new-file t t)
    ;; Update roam DB
    (when (fboundp 'org-roam-db-update-file)
      (org-roam-db-update-file new-file))
    (message "Renamed to %s" (abbreviate-file-name new-file))))

(defun my/check-links ()
  "Scan all org files for broken id: and file: links. Report in *Link Check*."
  (interactive)
  (let ((notes-dir org-roam-directory)
        (report    (get-buffer-create "*Link Check*"))
        (broken    0))
    (with-current-buffer report
      (read-only-mode -1)
      (erase-buffer)
      (insert (format "Link check — %s\n%s\n\n" notes-dir
                      (make-string 60 ?-))))
    (dolist (file (directory-files-recursively notes-dir "\\.org$"))
      (with-temp-buffer
        (insert-file-contents file)
        (goto-char (point-min))
        (let ((line 0))
          (while (not (eobp))
            (setq line (1+ line))
            (let ((ln (buffer-substring-no-properties
                       (line-beginning-position) (line-end-position))))
              ;; Check id: links
              (let ((pos 0))
                (while (string-match "\\[\\[id:\\([^]]+\\)\\]" ln pos)
                  (let* ((id  (match-string 1 ln))
                         (loc (org-id-find id)))
                    (unless loc
                      (with-current-buffer report
                        (insert (format "BROKEN id:  %s\n  → %s line %d\n"
                                        id (abbreviate-file-name file) line)))
                      (setq broken (1+ broken))))
                  (setq pos (match-end 0))))
              ;; Check file: links
              (let ((pos 0))
                (while (string-match "\\[\\[file:\\([^]\\[]+\\)\\]" ln pos)
                  (let* ((raw  (match-string 1 ln))
                         (path (expand-file-name
                                (car (split-string raw "::"))
                                (file-name-directory file))))
                    (unless (file-exists-p path)
                      (with-current-buffer report
                        (insert (format "BROKEN file: %s\n  → %s line %d\n"
                                        raw (abbreviate-file-name file) line)))
                      (setq broken (1+ broken))))
                  (setq pos (match-end 0)))))
            (forward-line 1)))))
    (with-current-buffer report
      (insert (format "\n%s\n%d broken link(s) found.\n"
                      (make-string 60 ?-) broken))
      (read-only-mode 1)
      (goto-char (point-min)))
    (pop-to-buffer report)
    (message "Link check complete: %d broken link(s)" broken)))

;; ---------------------------------------------------------------------------
;; API section generation from pub Zig declarations
;;
;; Usage: M-x my/update-api-section
;;
;; Scans zig src blocks in the current org buffer, extracts pub declarations,
;; and writes/updates a * API section with one definition-list entry per
;; symbol.  Existing descriptions are preserved; new symbols get a blank slot.
;; Run again freely after adding new pub items — it only merges, never wipes.
;; ---------------------------------------------------------------------------

(defun my/zig-pub-sigs ()
  "Return ordered (name sig doc kind) lists for pub zig declarations in buffer.
Extracts /// doc comments immediately preceding each pub declaration."
  (let (result seen in-src collecting name-buf parts-buf doc-lines doc-buf)
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
              (let* ((raw (mapconcat #'identity (nreverse parts-buf) " "))
                     (sig (string-trim (replace-regexp-in-string
                                        "[[:space:]]+" " "
                                        (replace-regexp-in-string "{.*$" "" raw))))
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
                      sig  (concat name (string-trim
                                         (replace-regexp-in-string
                                          "[[:space:]]*{[[:space:]]*$" ""
                                          (match-string 2 line))))
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

(defun my/update-api-section ()
  "Regenerate * API/Interface from pub declarations and /// doc comments.
/// comments are the source of truth for descriptions — re-run freely."
  (interactive)
  (unless (derived-mode-p 'org-mode)
    (user-error "Not in an org-mode buffer"))
  (let* ((sigs (my/zig-pub-sigs))
         (body (with-temp-buffer
                 (dolist (group '(("fn" . "Functions") ("type" . "Types")
                                  ("error" . "Errors") ("const" . "Constants")))
                   (let ((entries (seq-filter
                                   (lambda (s) (string= (nth 3 s) (car group)))
                                   sigs)))
                     (when entries
                       (insert (format "*%s*\n\n" (cdr group)))
                       (dolist (s entries)
                         (insert (format "- [[%s][~%s~]] :: %s\n"
                                         (nth 0 s) (nth 1 s) (or (nth 2 s) ""))))
                       (insert "\n"))))
                 (buffer-string))))
    (save-excursion
      (goto-char (point-min))
      (if (re-search-forward "^\\* \\(?:API\\|Interface\\)\\b" nil t)
          (let ((start (progn (forward-line 1) (point)))
                (end   (or (save-excursion
                             (when (re-search-forward "^\\* " nil t)
                               (match-beginning 0)))
                           (point-max))))
            (delete-region start end)
            (insert body))
        (let* ((file     (buffer-file-name))
               (dir-name (file-name-nondirectory
                          (directory-file-name (file-name-directory file))))
               (heading  (if (string= (file-name-base file) dir-name)
                             "API" "Interface")))
          (goto-char (point-min))
          (unless (re-search-forward "^\\* " nil t)
            (goto-char (point-max)))
          (goto-char (match-beginning 0))
          (insert "* " heading "\n" body "\n"))))
    (message "API/Interface updated: %d entries" (length sigs))))

(defun my/roam--file-title (file)
  "Return #+title from FILE, or its base name."
  (with-temp-buffer
    (insert-file-contents file)
    (goto-char (point-min))
    (if (re-search-forward "^#\\+title:[[:space:]]*\\(.+\\)$" nil t)
        (string-trim (match-string 1))
      (file-name-base file))))

(defun my/roam-normalize-orderings ()
  "Clean up all ordering.org files: remove stray headings, convert list links to * headings."
  (interactive)
  (let ((count 0))
    (dolist (file (directory-files-recursively
                   org-roam-directory "\\bordered\\(?:ing\\)\\.org$"))
      (with-temp-buffer
        (insert-file-contents file)
        (let ((original (buffer-string)))
          (goto-char (point-min))
          (while (re-search-forward "^\\*+[[:space:]]+Notes[[:space:]]*\n" nil t)
            (replace-match ""))
          (goto-char (point-min))
          (while (re-search-forward "^-[[:space:]]+\\(\\[\\[.+\\]\\]\\)" nil t)
            (replace-match "* \\1"))
          (unless (string= (buffer-string) original)
            (write-region (point-min) (point-max) file nil 'silent)
            (setq count (1+ count))))))
    (message "my/roam-normalize-orderings: updated %d file(s)" count)))

;; Suggested binding — uncomment or adapt to your taste:
;; (global-set-key (kbd "C-c r n") #'my/roam-new)
