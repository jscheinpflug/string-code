  ## Context and Symbol Rules (StringCode)

  ### 1) Public vs shared-private symbols
  - `BeginPackage["Pkg`"]` creates package scope.
  - `sym::usage` documents symbols (both public and private helpers in this codebase).
  - `Begin["Private`"]` defines symbols in literal `Private``.
  - In this repo, modules intentionally share `Private`` via `Needs[...]`, so private helpers may be reused across modules.

  ### 2) Documentation rule
  - Add `::usage` for **all** nontrivial symbols, including private helpers.
  - Place each `sym::usage = ...` immediately above the corresponding `sym[...] := ...` definition line.
  - Do not leave frequently reused helpers undocumented.

  ### 3) How to reference symbols
  - Inside `Begin["Private`"]`, prefer unqualified names.
  - If qualification is needed, use `Private\`name` (not `Pkg\`Private\`name`).
  - Do not add `StringCode\`...` prefixes for normal internal calls.

  ### 4) Loading and visibility
  - Consumer module must `Needs[...]` producer before using shared helpers.
  - Shared helpers must be defined before rules/guards that depend on them are evaluated.
  - If resolution is unclear, check:
    - `Context[sym]`
    - `Length[DownValues[sym]]`

  ### 5) Shadowing prevention
  - Avoid creating same-named symbols in `Global``.
  - In scripts/headless checks: `Needs[...]` (and init) before building expressions.
  - Use `ToExpression[...]` after init when parse/eval order matters.

  ### 6) Dev loading policy
  - Default to a `$Path`-based checkout load when running code in development, instead of relying on symlink alias package names.
  - If editing `$Path`, prepend only the checkout repo root that contains `StringCode/` (not broad folders like `~/src`).
  - Load with `Needs["StringCode`"]` after setting `$Path` for the desired checkout.
  - If multiple StringCode trees are present, isolate by using one fresh kernel per checkout.
