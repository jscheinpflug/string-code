# StringCode Context + Mathematica Run Notes

## General lessons I wish I knew earlier
- `math -run '...'` parses the entire input string before evaluating anything. Symbols like `R`, `b`, `expX` can bind to `Global`` too early if referenced before init side-effects.
- `InitStringCode[...]` mutates `$ContextPath` by appending theory/CFT-specific contexts. Re-running different inits in one kernel can create mixed-context shadowing (`::shdw`), even if each init is valid in isolation.
- `Remove["Global`*"]` removes symbols, but previously parsed expressions may still carry references such as `Removed["prof"]`. Build expressions after init if you rely on clean symbol identity.
- In this project, private helper access is context-sensitive: `Private\`foo` inside one package is not globally unique unless that package context is active and unambiguous.
- Notebook execution and one-shot headless execution are not equivalent: notebooks evaluate cell-by-cell (safer for context/order), while `math -run` is easiest to misuse due to parse-before-eval.

## Reliable run patterns (project-wide)
- For deterministic headless checks, prefer one fresh kernel per theory/CFT target.
- Initialize first, then construct test expressions.
- Use either fully-qualified symbols or deferred construction (`ToExpression`) in headless scripts when parse order matters.
- Avoid loading Bosonic and TypeII FlatSpace symbols in the same kernel unless you explicitly need cross-theory checks.
- If you see many `::shdw` warnings, restart the kernel and rerun with a single init path.

## Practical templates
- Safe headless skeleton:
  - `math -noprompt -run 'Remove["Global`*"]; Needs["StringCode`"]; StringCode`InitStringCode[...]; expr = ToExpression["R[b[0,z],bt[0,zb]]"]; Print[expr]; Exit[]'`
- Theory init examples:
  - Bosonic: `InitStringCode[<|"theory"->"Bosonic","CFT"->"FlatSpace","conventions"->"Bosonic-Xi","bracket"->"Flat"|>]`
  - TypeII: `InitStringCode[<|"theory"->"TypeII","CFT"->"FlatSpace","conventions"->"TypeII-Xi","bracket"->"Flat"|>]`

## Test-file workflow
- `.test.wlnb` files are JSON notebooks; normal execution path is notebook cell evaluation.
- Keep notebook test cells as Mathematica expressions (do not wrap cells in `ToExpression[...]`).
- Fast structure check:
  - `node -e "JSON.parse(require('fs').readFileSync('path/to/file.test.wlnb','utf8'))"`
- Fast targeted repro:
  - `math -noprompt -run 'Needs["StringCode`"]; StringCode`InitStringCode[...]; Print[testExpr]; Exit[]'`

## Observed issues while running this repo
- Non-exported/internal symbols can silently bind to `Global\`` in headless checks and then stay unevaluated.
  - Build expressions only after `Needs[...]`/`InitStringCode[...]`.
  - Sanity-check symbol binding with `Context[sym]` and `Length[DownValues[sym]]`.
  - Prefer public exported APIs for tests; use internal symbols only for targeted diagnostics.
- The package uses a shared `Private\`` context across modules (by design here), so `StringCode\`...\`Private\`foo` may not resolve as expected in isolation. Use `Private\`foo` once the relevant package is loaded.
- In sandboxed/headless environments you may see:
  - `OMP: Warning #179: Function Can't set size of SHM failed:`
  - This did not affect symbolic test results in practice; treat it as environment noise unless computations fail.
