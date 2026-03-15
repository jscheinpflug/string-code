## Lean 4 Workflows

When a task involves `.lean` files, Lean 4 proofs, Lake builds, or mathlib search,
use the local Lean 4 skill in
`/home/scheinpflug/LeanExperiment/tools/lean4-skills/plugins/lean4/skills/lean4/SKILL.md`.

Before running the skill's helper scripts, source the local environment shim:

```bash
source /home/scheinpflug/LeanExperiment/.agents/lean4-env.sh
```

Environment:
- `LEAN4_PLUGIN_ROOT=/home/scheinpflug/LeanExperiment/tools/lean4-skills/plugins/lean4`
- `LEAN4_SCRIPTS=/home/scheinpflug/LeanExperiment/tools/lean4-skills/plugins/lean4/lib/scripts`
- `LEAN4_REFS=/home/scheinpflug/LeanExperiment/tools/lean4-skills/plugins/lean4/skills/lean4/references`
