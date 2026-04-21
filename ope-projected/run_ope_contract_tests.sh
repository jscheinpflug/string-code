#!/usr/bin/env bash

set -euo pipefail

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd -- "$script_dir/.." && pwd)"
wl_script="$script_dir/ope_contract_tests.wl"
run_id="$(date -u '+%Y%m%dT%H%M%SZ')"
report_file="$script_dir/ope_contract_tests.report.$run_id.txt"
tmp_file="$report_file.tmp"
wolframscript_bin="${WOLFRAMSCRIPT_BIN:-wolframscript}"

if ! command -v "$wolframscript_bin" >/dev/null 2>&1; then
  {
    printf 'command: %s\n' "$wolframscript_bin"
    printf 'cwd: %s\n' "$repo_root"
    printf 'started_at: %s\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
    echo
    printf 'error: wolframscript not found on PATH\n'
    echo
    printf 'exit_code: 127\n'
    printf 'finished_at: %s\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  } > "$report_file"
  cat "$report_file" >&2
  exit 127
fi

{
  printf 'command: %s -file %s\n' "$wolframscript_bin" "$wl_script"
  printf 'cwd: %s\n' "$repo_root"
  printf 'started_at: %s\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  echo
} > "$tmp_file"

set +e
(
  cd "$repo_root"
  "$wolframscript_bin" -file "$wl_script"
) 2>&1 | tee -a "$tmp_file"
status=${PIPESTATUS[0]}
set -e

{
  echo
  printf 'exit_code: %s\n' "$status"
  printf 'finished_at: %s\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
} >> "$tmp_file"

mv "$tmp_file" "$report_file"

printf '\nreport_file: %s\n' "$report_file"

exit "$status"
