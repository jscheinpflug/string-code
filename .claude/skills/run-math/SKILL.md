---
name: run-math
description: Run Mathematica/Wolfram Language commands for this StringCode repository with stable initialization and kernel isolation. Use when the user asks to "run mathematica", "run math", execute headless checks, run or debug `.test.wlnb` notebook tests, or reproduce StringCode symbolic evaluations.
---

# Run Math

Run Mathematica commands safely for this repo.

## IMPORTANT: Platform-specific Wolfram execution

- On **Linux**, `math` is typically on `$PATH` and works directly.
- On **macOS**, `math` may not be on `$PATH`. If `which math` fails, use: `/Applications/Wolfram.app/Contents/MacOS/MathKernel`
- On **macOS**, ALWAYS use `dangerouslyDisableSandbox: true` (Claude Code) or escalated sandbox (Codex). Wolfram commands WILL FAIL in the default sandbox. Do not attempt sandbox execution first — escalate before the first attempt.

## Workflow

1. Run from the repo root (the directory containing `StringCode/`).
2. Use one fresh kernel per target:
   - Do not mix Bosonic and TypeII in one kernel unless required.
   - If repeated `::shdw` appears, restart with a fresh kernel.
3. Initialize before building expressions:
   - In `math -run`, parsing happens before evaluation.
   - Call `Needs["StringCode`"]` and `InitStringCode[...]` first.
   - Use `ToExpression[...]` after init when parse order matters.
4. Prefer exported APIs in tests:
   - Use internal/private symbols only for targeted diagnostics.
5. Treat `OMP: Warning #179 ... SHM failed` as environment noise unless results are wrong.

## Command Examples (4)

1. Bosonic headless check:
```bash
math -noprompt -run 'Remove["Global`*"]; Needs["StringCode`"]; StringCode`InitStringCode[<|"theory"->"Bosonic","CFT"->"FlatSpace","conventions"->"Bosonic-Xi","bracket"->"Flat"|>]; expr=ToExpression["R[b[0,z],bt[0,zb]]"]; Print[expr]; Exit[]'
```

2. TypeII headless check:
```bash
math -noprompt -run 'Remove["Global`*"]; Needs["StringCode`"]; StringCode`InitStringCode[<|"theory"->"TypeII","CFT"->"FlatSpace","conventions"->"TypeII-Xi","bracket"->"Flat"|>]; expr=ToExpression["R[b[0,z],bt[0,zb]]"]; Print[expr]; Exit[]'
```

3. Targeted repro template:
```bash
math -noprompt -run 'Needs["StringCode`"]; StringCode`InitStringCode[...]; Print[testExpr]; Exit[]'
```

4. `.test.wlnb` JSON validity check:
```bash
node -e "JSON.parse(require('fs').readFileSync('path/to/file.test.wlnb','utf8'))"
```
