# StringCode Context + Testing Notes

## Context management (what matters)
- Packages use `BeginPackage[...]` and `Begin["Private`"]`; helper functions are intentionally private.
- `R` is the only public normal-ordering symbol from `StringCode`NormalOrdering``.
- In this codebase, tests may still call private helpers as `Private`...` (not exported API).
- `InitStringCode[...]` loads base modules with `Needs[...]`, then appends theory/CFT-specific contexts to `$ContextPath`.
- `StringCode`NormalOrdering`Bosonic`` and `StringCode`NormalOrdering`TypeII`` provide `regcomm` rules needed by `R` reordering.

## Practical test note
- In `math -run '...'`, the whole string is parsed before execution. That means raw `R[...]`, `b[...]`, etc. may bind to `Global`` before `Needs[...]`/`InitStringCode[...]` runs.
- Reliable pattern for headless checks:
  - `Remove["Global`*"]`
  - `Needs["StringCode`"]`
  - `StringCode`InitStringCode[...]`
  - build test expressions after init with `ToExpression[...]` (or use fully-qualified symbols)
- Example:
  - `expr = ToExpression["R[c[0,0],b[0,0]]"];`
  - this resolves against the post-init `$ContextPath` and avoids shadowing ambiguity.

## Running tests quickly
- Notebook tests are `.test.wlnb` JSON notebooks and are normally run in Wolfram notebooks.
- Quick structural check:
  - `node -e "JSON.parse(require('fs').readFileSync('path/to/file.test.wlnb','utf8'))"`
- Fast headless repro for one/few tests:
  - `math -noprompt -run 'Needs["StringCode`..."]; ...; Print[testExpr]; Exit[]'`
- For theory-specific tests, always initialize first:
  - Bosonic: `InitStringCode[<|"theory"->"Bosonic","CFT"->"FlatSpace","conventions"->"Bosonic-Xi","bracket"->"Flat"|>]`
  - TypeII: `InitStringCode[<|"theory"->"TypeII","CFT"->"FlatSpace","conventions"->"TypeII-Xi","bracket"->"Flat"|>]`
