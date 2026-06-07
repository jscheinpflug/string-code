;;; pdf-config.el — LaTeX/PDF export: engrave-faces + doom-gruvbox colors

;; Add straight build directory to load-path
(let* ((straight-dir (expand-file-name "~/.config/emacs/.local/straight"))
       (build-dir (when (file-directory-p straight-dir)
                    (car (sort (seq-filter #'file-directory-p
                                           (directory-files straight-dir t "^build-[0-9]" t))
                               #'string>)))))
  (when build-dir
    (dolist (d (directory-files build-dir t "^[^.]"))
      (when (file-directory-p d) (add-to-list 'load-path d)))))

;; Load language modes so font-lock can assign faces to tokens
(require 'zig-mode      nil t)
(require 'haskell-mode  nil t)
(require 'lua-mode      nil t)

;; Tell engrave-faces exactly which colors to use.
;; engrave-faces-current-preset-style is a static alist — it never reads
;; live face attributes, so set-face-attribute has no effect here.
;; Light background for print PDF; doom-gruvbox syntax colors.
(require 'engrave-faces-latex)
;; Colour-only preset: no bold/italic in code blocks so the monospace font
;; renders cleanly without fake oblique or missing bold variants.
(setq engrave-faces-current-preset-style
  '((default
      :short "default" :slug "D"
      :foreground "#1a1a1a" :background "#f2f2f2")
    (font-lock-keyword-face
      :short "fl-keyword" :slug "k"
      :foreground "#fb4934")
    (font-lock-function-name-face
      :short "fl-function" :slug "f"
      :foreground "#b8bb26")
    (font-lock-variable-name-face
      :short "fl-variable" :slug "v"
      :foreground "#83a598")
    (font-lock-string-face
      :short "fl-string" :slug "s"
      :foreground "#b8bb26")
    (font-lock-type-face
      :short "fl-type" :slug "t"
      :foreground "#fabd2f")
    (font-lock-constant-face
      :short "fl-constant" :slug "o"
      :foreground "#d3869b")
    (font-lock-builtin-face
      :short "fl-builtin" :slug "b"
      :foreground "#fe8019")
    (font-lock-preprocessor-face
      :short "fl-preprocessor" :slug "pp"
      :foreground "#fe8019")
    (font-lock-comment-face
      :short "fl-comment" :slug "c"
      :foreground "#928374")
    (font-lock-comment-delimiter-face
      :short "fl-comment-delim" :slug "cd"
      :foreground "#928374")
    (font-lock-doc-face
      :short "fl-doc" :slug "d"
      :foreground "#1a1a1a")
    (font-lock-number-face
      :short "fl-number" :slug "n"
      :foreground "#d3869b")
    (font-lock-operator-face
      :short "fl-operator" :slug "op"
      :foreground "#ebdbb2")
    (font-lock-warning-face
      :short "fl-warning" :slug "wr"
      :foreground "#fb4934")
    (shadow
      :short "shadow" :slug "h"
      :foreground "#928374")
    (variable-pitch
      :short "var-pitch" :slug "vp"
      :foreground "#1a1a1a")))

;; Use engrave-faces backend for src blocks
(require 'ox-latex)
(setq org-latex-src-block-backend 'engraved)

;; Use #+name: values directly as \label{} in LaTeX so that [[name]] links
;; generate \hyperref[name]{} rather than \hyperref[lst:orgXXXX]{}.
(setq org-latex-prefer-user-labels t)

;; Bibliography — biblatex with numeric citations, refs at document end.
;; refs.bib lives at org/refs.bib relative to the project root; the master
;; .tex file is written to the project root, so the relative path is correct.
(require 'oc)
(require 'oc-biblatex)
(setq org-cite-export-processors '((latex . (biblatex)) (t . (basic))))
(add-to-list 'org-latex-packages-alist '("style=numeric,sorting=none" "biblatex" nil) t)

;; Typography and layout improvements
(add-to-list 'org-latex-packages-alist '("a4paper,margin=2.5cm" "geometry" nil) t)
(add-to-list 'org-latex-packages-alist '("" "xcolor" nil) t)
(add-to-list 'org-latex-packages-alist '("" "booktabs" nil) t)
(add-to-list 'org-latex-packages-alist '("" "enumitem" nil) t)
(add-to-list 'org-latex-packages-alist
  "\\setlist[description]{font=\\ttfamily\\bfseries\\color{black},
    labelindent=0pt, leftmargin=1.8em, style=sameline,
    itemsep=0.3ex}"
  t)
(add-to-list 'org-latex-packages-alist '("" "microtype" nil) t)
(add-to-list 'org-latex-packages-alist '("" "titlesec" nil) t)
(add-to-list 'org-latex-packages-alist '("" "titletoc" nil) t)

;; Documentation style: no "Part"/"Chapter" labels, no page breaks.
(add-to-list 'org-latex-packages-alist
  "% Remove word prefixes
\\renewcommand{\\partname}{}
\\renewcommand{\\chaptername}{}
% Parts: inline title with rules, NO page break
\\makeatletter
\\renewcommand\\part{%
  \\@afterindentfalse
  \\secdef\\@part\\@spart}
\\renewcommand\\@part[2][]{%
  \\ifnum\\c@secnumdepth>-2\\relax
    \\refstepcounter{part}%
    \\addcontentsline{toc}{part}{\\thepart\\enspace #1}%
  \\else\\addcontentsline{toc}{part}{#1}\\fi
  \\markboth{}{}%
  \\vspace{2em}%
  {\\color{black!25}\\hrule height 0.5pt}%
  \\smallskip
  {\\centering\\normalfont\\LARGE\\bfseries #2\\par}%
  \\smallskip
  {\\color{black!25}\\hrule height 0.5pt}%
  \\vspace{1em}\\@afterheading}
% Reset chapter numbering at the start of each part
\\@addtoreset{chapter}{part}
\\makeatother
% Chapters: straight class (no page break), number + title
\\titleclass{\\chapter}{straight}
\\titleformat{\\chapter}[hang]
  {\\normalfont\\Large\\bfseries}{\\thechapter}{0.8em}{}
\\titlespacing*{\\chapter}{0pt}{2.5ex}{1ex}"
  t)

