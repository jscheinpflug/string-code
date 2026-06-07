#!/usr/bin/env sh
set -eu

# ---- flags ----
SKIP_GRAPH=0
SKIP_PDF=0
SKIP_HTML=0
WATCH=0
for arg in "$@"; do
  case "$arg" in
    --nograph) SKIP_GRAPH=1 ;;
    --nopdf)   SKIP_PDF=1 ;;
    --nohtml)  SKIP_HTML=1 ;;
    --watch)   WATCH=1; SKIP_GRAPH=1 ;;
    *) echo "Unknown option: $arg"; exit 1 ;;
  esac
done

ROOT="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
PUBLIC="$ROOT/public"
PUBLIC_NOTES="$PUBLIC/notes"
GRAPH="$PUBLIC/graph"
MASTER_ORG="$ROOT/all-notes-master.org"
LOG_DIR="$ROOT/.publish-logs"

NOTES_DIR=""
ORDERING_ORG=""
OVERVIEW_ORG=""

ORUI_DIR="$HOME/.config/emacs/.local/straight/repos/publish-org-roam-ui"
ORUI_LOCAL_SH="$ORUI_DIR/local.sh"

mkdir -p "$LOG_DIR"
cd "$ROOT"

echo "==> Project root: $ROOT"

# ============================================================
# Find notes and database
# ============================================================

if [ -d "$ROOT/org" ]; then
  NOTES_DIR="$ROOT/org"
elif [ -d "$ROOT/notes" ]; then
  NOTES_DIR="$ROOT/notes"
else
  echo "ERROR: expected $ROOT/org or $ROOT/notes"
  exit 1
fi

if [ -f "$NOTES_DIR/ordering.org" ]; then
  ORDERING_ORG="$NOTES_DIR/ordering.org"
elif [ -f "$NOTES_DIR/index.org" ]; then
  ORDERING_ORG="$NOTES_DIR/index.org"
else
  echo "ERROR: neither ordering.org nor index.org found in $NOTES_DIR"
  exit 1
fi

if [ -f "$NOTES_DIR/overview.org" ]; then
  OVERVIEW_ORG="$NOTES_DIR/overview.org"
fi

if [ -f "$NOTES_DIR/org-roam.db" ]; then
  DB_FILE="org-roam.db"
  DB_PATH="$NOTES_DIR/org-roam.db"
elif [ -f "$NOTES_DIR/org-roam.sqlite" ]; then
  DB_FILE="org-roam.sqlite"
  DB_PATH="$NOTES_DIR/org-roam.sqlite"
else
  echo "ERROR: expected org-roam.db or org-roam.sqlite in $NOTES_DIR"
  exit 1
fi

echo "==> Notes:    $NOTES_DIR"
echo "==> Ordering: $ORDERING_ORG"
echo "==> Overview: ${OVERVIEW_ORG:-(none)}"
echo "==> DB:       $DB_PATH"

mkdir -p "$PUBLIC" "$PUBLIC_NOTES" "$GRAPH"


# ============================================================
# Build functions
# ============================================================

build_html() {
  # Pass INCREMENTAL=1 to only export files newer than their cached output.
  local incremental="${1:-0}"
  echo
  echo "==> Publishing HTML..."
  if [ "$incremental" = "0" ]; then
    rm -rf "$PUBLIC_NOTES" "$PUBLIC/api" "$PUBLIC/pagefind"
    mkdir -p "$PUBLIC_NOTES"
  fi
  if ! INCREMENTAL="$incremental" emacs --batch \
      -l "$ROOT/publish/publish.el" \
      > "$LOG_DIR/html.log" 2>&1; then
    echo "ERROR: HTML publish failed. Log: $LOG_DIR/html.log"
    tail -n 40 "$LOG_DIR/html.log" || true
    return 1
  fi
  echo "==> HTML done."
}

audit_html_outputs() {
  if [ "$SKIP_HTML" -eq 1 ]; then
    return 0
  fi

  local stale="$LOG_DIR/stale-html.log"
  : > "$stale"

  if [ -d "$PUBLIC_NOTES" ]; then
    find "$PUBLIC_NOTES" -type f -name '*.html' | while IFS= read -r html; do
      rel="${html#"$PUBLIC_NOTES"/}"
      org="$NOTES_DIR/${rel%.html}.org"
      if [ ! -f "$org" ]; then
        echo "$html" >> "$stale"
      fi
    done
  fi

  if [ -s "$stale" ]; then
    echo "ERROR: stale generated note HTML found. Log: $stale"
    sed -n '1,40p' "$stale"
    return 1
  fi

  echo "  OK: no stale generated note HTML"
}

build_tangle() {
  echo
  echo "==> Tangling code blocks..."
  if ! emacs --batch \
    --eval "(require 'org)" \
    --eval "(require 'ob-tangle)" \
    --eval "(setq org-confirm-babel-evaluate nil)" \
    --eval "(dolist (f (directory-files-recursively \"$NOTES_DIR\" \"\\\\.org\$\"))
              (with-current-buffer (find-file-noselect f t)
                (when (save-excursion
                        (goto-char (point-min))
                        (re-search-forward \"^#[+]auto_tangle:[[:space:]]*t\" nil t))
                  (org-babel-tangle)
                  (kill-buffer))))" \
    > "$LOG_DIR/tangle.log" 2>&1; then
    echo "WARNING: tangle step had errors. See $LOG_DIR/tangle.log"
  else
    echo "==> Tangle done."
  fi
}

sync_db() {
  echo
  echo "==> Syncing org-roam database..."
  if ! NOTES_DIR="$NOTES_DIR" DB_PATH="$DB_PATH" \
       emacs --batch --load "$ROOT/publish/roam-sync.el" \
       > "$LOG_DIR/roam-sync.log" 2>&1; then
    echo "WARNING: org-roam sync failed — graph may be incomplete"
    tail -5 "$LOG_DIR/roam-sync.log" || true
    return 1
  fi
  echo "==> Database synced."
}

build_pdf() {
  echo
  echo "==> Building PDF..."

  rm -f "$MASTER_ORG" "$PUBLIC/all-notes.pdf"
  rm -f "$ROOT"/all-notes-master.{pdf,tex,log,aux,out,toc,fls,fdb_latexmk,bcf,bbl,blg,run.xml}
  rm -f "$ROOT"/all-notes-master.*-SAVE-ERROR
  rm -rf "$LOG_DIR/pdf-notes"
  rm -f "$LOG_DIR/pdf-master.log" "$LOG_DIR/pdf-emacs.log" "$LOG_DIR/pdf-latex.log"

  if ! ORDERING_ORG="$ORDERING_ORG" \
       OVERVIEW_ORG="$OVERVIEW_ORG" \
       NOTES_DIR="$NOTES_DIR" \
       MASTER_ORG="$MASTER_ORG" \
       CLEAN_DIR="$LOG_DIR/pdf-notes" \
    emacs --batch \
      --eval "(require 'org-id)" \
      --eval "(setq org-id-locations-file \"$NOTES_DIR/.org-id-locations\")" \
      --eval "(org-id-update-id-locations (directory-files-recursively \"$NOTES_DIR\" \"\\.org$\"))" \
      --load "$ROOT/publish/master-gen.el" \
    > "$LOG_DIR/pdf-master.log" 2>&1
  then
    echo "ERROR: failed to build master Org file. Log: $LOG_DIR/pdf-master.log"
    tail -n 40 "$LOG_DIR/pdf-master.log" || true
    return 1
  fi

  INCLUDED_COUNT="$(grep -c '^#+include:' "$MASTER_ORG" | tr -d ' ')"
  echo "==> Included in PDF: $INCLUDED_COUNT files"

  if ! emacs --batch "$MASTER_ORG" \
    --eval "(require 'org)" \
    --eval "(require 'ox-latex)" \
    --eval "(require 'org-id)" \
    --load "$ROOT/publish/pdf-config.el" \
    --eval "(setq org-confirm-babel-evaluate nil)" \
    --eval "(setq org-id-locations-file \"$NOTES_DIR/.org-id-locations\")" \
    --eval "(org-id-update-id-locations (directory-files-recursively \"$NOTES_DIR\" \"\\\\.org$\"))" \
	    --eval "(defun my/id-title (id)
	              (let ((m (org-id-find id t)))
	                (unless m
	                  (error \"Unresolved id link: %s\" id))
	                (with-current-buffer (marker-buffer m)
	                  (save-excursion
	                    (goto-char m)
	                    (or
	                     (org-entry-get nil \"ITEM\")
	                     (cdr (assoc \"TITLE\" (org-collect-keywords '(\"TITLE\"))))
	                     id)))))" \
	    --eval "(defun my/pdf-label-present-p (label)
	              (save-excursion
	                (goto-char (point-min))
	                (re-search-forward
	                 (regexp-quote (format \"#+latex: \\\\label{%s}\" label))
	                 nil t)))" \
	    --eval "(org-link-set-parameters
	              \"id\"
	              :export
	              (lambda (path desc backend &rest _)
	                (let ((sanitized (replace-regexp-in-string \"[^a-zA-Z0-9-]\" \"-\" path)))
	                  (cond
	                   ((eq backend 'latex)
	                    (let ((label (format \"orgid:%s\" sanitized))
	                          (text (or desc (my/id-title path))))
	                      (if (my/pdf-label-present-p label)
	                          (format \"\\\\hyperref[%s]{%s}\" label text)
	                        text)))
	                   (t
	                    (org-export-string-as
	                     (or desc (my/id-title path))
                     backend t))))))" \
    --eval "(condition-case err
                (progn
                  (org-latex-export-to-pdf)
                  (when (get-buffer \"*Org PDF LaTeX Output*\")
                    (with-current-buffer \"*Org PDF LaTeX Output*\"
                      (write-region (point-min) (point-max) \"$LOG_DIR/pdf-latex.log\" nil 'silent))))
              (error
               (when (get-buffer \"*Org PDF LaTeX Output*\")
                 (with-current-buffer \"*Org PDF LaTeX Output*\"
                   (write-region (point-min) (point-max) \"$LOG_DIR/pdf-latex.log\")))
               (signal (car err) (cdr err))))" \
    > "$LOG_DIR/pdf-emacs.log" 2>&1
  then
    echo "ERROR: PDF export failed."
    echo "Emacs log: $LOG_DIR/pdf-emacs.log"
    echo "LaTeX log: $LOG_DIR/pdf-latex.log"
    echo
    tail -n 40 "$LOG_DIR/pdf-emacs.log" || true
    if [ -f "$LOG_DIR/pdf-latex.log" ]; then
      echo
      tail -n 80 "$LOG_DIR/pdf-latex.log" || true
    fi
    return 1
  fi

  if [ ! -f "$ROOT/all-notes-master.pdf" ]; then
    echo "ERROR: PDF export succeeded but all-notes-master.pdf was not found."
    return 1
  fi

  mv "$ROOT/all-notes-master.pdf" "$PUBLIC/all-notes.pdf"
  echo "==> PDF done: $PUBLIC/all-notes.pdf"
}

# ============================================================
# Initial full build
# ============================================================

if [ ! -f "$ROOT/publish/publish.el" ]; then
  echo "ERROR: publish.el not found: $ROOT/publish/publish.el"
  exit 1
fi

build_tangle
if [ "$SKIP_HTML" -eq 0 ]; then
  build_html 0
  cp "$ROOT/publish/style.css"  "$PUBLIC/style.css"
  cp "$ROOT/publish/sidebar.js" "$PUBLIC/sidebar.js"
  cp "$ROOT/publish/theme.js"   "$PUBLIC/theme.js"
  if command -v pagefind >/dev/null 2>&1; then
    echo "==> Building search index..."
    pagefind --site "$PUBLIC" --output-path "$PUBLIC/pagefind" \
      > "$LOG_DIR/pagefind.log" 2>&1 \
      && echo "==> Search index done." \
      || echo "WARNING: pagefind failed. See $LOG_DIR/pagefind.log"
  fi
else
  echo
  echo "==> Skipping HTML (--nohtml)."
fi
if [ "$SKIP_PDF" -eq 0 ]; then
  build_pdf
else
  echo
  echo "==> Skipping PDF (--nopdf)."
fi

# ============================================================
# DB sync + graph (skipped with --nograph / --watch)
# ============================================================

if [ "$SKIP_GRAPH" -eq 1 ]; then
  echo
  echo "==> Skipping database sync and graph (--nograph)."
else

sync_db || true

echo
echo "==> Building graph..."

if [ ! -d "$ORUI_DIR" ]; then
  echo "ERROR: publish-org-roam-ui directory not found: $ORUI_DIR"
  exit 1
fi

if [ ! -f "$ORUI_LOCAL_SH" ]; then
  echo "ERROR: local.sh not found: $ORUI_LOCAL_SH"
  exit 1
fi

chmod +x "$ORUI_LOCAL_SH"

cd "$ORUI_DIR"
rm -rf dist out public build .next

if ! printf "%s\n%s\n" "$NOTES_DIR" "$DB_FILE" |
  "$ORUI_LOCAL_SH" "$NOTES_DIR" "$DB_PATH" > "$LOG_DIR/graph.log" 2>&1
then
  echo "ERROR: graph build failed. Log: $LOG_DIR/graph.log"
  tail -n 40 "$LOG_DIR/graph.log" || true
  echo
  echo "Roam path should be: $NOTES_DIR"
  echo "DB filename should be: $DB_FILE"
  exit 1
fi

ORUI_OUTPUT=""

for d in \
  "$ORUI_DIR/dist" \
  "$ORUI_DIR/out" \
  "$ORUI_DIR/public" \
  "$ORUI_DIR/build" \
  "$ORUI_DIR/frontend/out" \
  "$ORUI_DIR/frontend/dist" \
  "$ORUI_DIR/frontend/public" \
  "$ORUI_DIR/frontend/build"
do
  if [ -f "$d/index.html" ]; then
    ORUI_OUTPUT="$d"
    break
  fi
done

if [ -z "$ORUI_OUTPUT" ]; then
  ORUI_INDEX="$(
    find "$ORUI_DIR" -maxdepth 10 -type f -name index.html \
      ! -path "*/node_modules/*" \
      ! -path "*/.git/*" \
      ! -path "*/src/*" \
      ! -path "*/app/*" \
      ! -path "*/pages/*" \
      | sort \
      | head -n 1
  )"

  if [ -n "$ORUI_INDEX" ]; then
    ORUI_OUTPUT="$(dirname "$ORUI_INDEX")"
  fi
fi

if [ -z "$ORUI_OUTPUT" ]; then
  echo "ERROR: could not find graph output. Log: $LOG_DIR/graph.log"
  exit 1
fi

cd "$ROOT"

rm -rf "$GRAPH"
mkdir -p "$GRAPH"
cp -R "$ORUI_OUTPUT"/. "$GRAPH"/

if [ -d "$ORUI_OUTPUT/_next" ]; then
  rm -rf "$PUBLIC/_next"
  cp -R "$ORUI_OUTPUT/_next" "$PUBLIC/_next"
fi

for asset_dir in assets static data; do
  if [ -d "$ORUI_OUTPUT/$asset_dir" ]; then
    rm -rf "$PUBLIC/$asset_dir"
    cp -R "$ORUI_OUTPUT/$asset_dir" "$PUBLIC/$asset_dir"
  fi
done

echo "==> Graph done: $GRAPH"

fi  # end --nograph skip block

# ============================================================
# Report
# ============================================================

echo
echo "==> Checks:"
if [ "$SKIP_HTML" -eq 0 ]; then
  [ -f "$PUBLIC/index.html" ] && echo "  OK: public/index.html" || echo "  MISSING: public/index.html"
  audit_html_outputs
else
  echo "  SKIPPED: public/index.html (--nohtml)"
fi
if [ "$SKIP_PDF" -eq 0 ]; then
  [ -f "$PUBLIC/all-notes.pdf" ] && echo "  OK: public/all-notes.pdf" || echo "  MISSING: public/all-notes.pdf"
else
  echo "  SKIPPED: public/all-notes.pdf (--nopdf)"
fi
if [ "$SKIP_GRAPH" -eq 0 ]; then
  [ -f "$GRAPH/index.html" ] && echo "  OK: public/graph/index.html" || echo "  MISSING: public/graph/index.html"
else
  echo "  SKIPPED: public/graph/ (--nograph)"
fi

echo
echo "==> Logs:"
echo "  $LOG_DIR/tangle.log"
echo "  $LOG_DIR/html.log"
echo "  $LOG_DIR/pdf-master.log"
echo "  $LOG_DIR/pdf-emacs.log"
echo "  $LOG_DIR/pdf-latex.log"
echo "  $LOG_DIR/graph.log"

echo
echo "==> Serve locally with:"
echo "  python3 -m http.server 8000 -d public"
echo
echo "Open:"
echo "  http://localhost:8000"
echo "  http://localhost:8000/graph/"
echo "  http://localhost:8000/all-notes.pdf"

# ============================================================
# Watch loop (--watch only)
# ============================================================

if [ "$WATCH" -eq 0 ]; then
  exit 0
fi

SENTINEL="$LOG_DIR/.watch-sentinel"
touch "$SENTINEL"

echo
echo "==> Watch mode active. Monitoring $NOTES_DIR for .org changes."
echo "    Press Ctrl-C to stop."
echo

while true; do
  sleep 3
  if find "$NOTES_DIR" -name "*.org" -newer "$SENTINEL" -print -quit 2>/dev/null | grep -q .; then
    touch "$SENTINEL"
    echo "$(date '+%H:%M:%S') ==> Change detected — rebuilding..."
    build_tangle                            || true
    build_html 1                            || true
    [ "$SKIP_PDF" -eq 0 ] && build_pdf     || true
    sync_db                                 || true
    echo "$(date '+%H:%M:%S') ==> Ready."
    echo
  fi
done
