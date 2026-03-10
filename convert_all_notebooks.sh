#!/usr/bin/env bash
# Convert all .wlnb files in the repository to .nb files.
# Usage: ./convert_all_notebooks.sh

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
CONVERTER="$SCRIPT_DIR/convert_wlnb_to_nb.py"

if [[ ! -f "$CONVERTER" ]]; then
    echo "Error: converter not found at $CONVERTER" >&2
    exit 1
fi

if ! command -v python3 &>/dev/null; then
    echo "Error: python3 is not installed" >&2
    exit 1
fi

count=0
failures=0

while IFS= read -r -d '' wlnb; do
    if python3 "$CONVERTER" "$wlnb"; then
        ((count++))
    else
        echo "Failed: $wlnb" >&2
        ((failures++))
    fi
done < <(find "$SCRIPT_DIR" -name '*.wlnb' -print0)

echo ""
echo "Converted $count notebook(s), $failures failure(s)."
[[ $failures -eq 0 ]]
