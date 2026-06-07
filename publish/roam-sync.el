;;; roam-sync.el — Force-sync the org-roam database so all nodes appear in the graph.
;;; Reads NOTES_DIR and DB_PATH from environment variables.

(let* ((straight-dir (expand-file-name "~/.config/emacs/.local/straight"))
       (build-dir (when (file-directory-p straight-dir)
                    (car (sort (seq-filter #'file-directory-p
                                           (directory-files straight-dir t "^build-[0-9]" t))
                               #'string>)))))
  (when build-dir
    (dolist (d (directory-files build-dir t "^[^.]"))
      (when (file-directory-p d) (add-to-list 'load-path d)))))

(require 'org-roam)

(let ((notes-dir (getenv "NOTES_DIR"))
      (db-path   (getenv "DB_PATH")))
  (unless (and notes-dir db-path)
    (error "roam-sync.el: NOTES_DIR and DB_PATH must be set"))
  (setq org-roam-directory   notes-dir
        org-roam-db-location db-path)
  (org-id-update-id-locations
   (directory-files-recursively notes-dir "\\.org$"))
  (org-roam-db-sync 'force)
  (message "roam-sync: indexed %d files in %s"
           (length (directory-files-recursively notes-dir "\\.org$"))
           notes-dir))
