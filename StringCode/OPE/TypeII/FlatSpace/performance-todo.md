# Todo: Low-Symbolic Rewrite of TypeII FlatSpace `OPEProjected`

Only check a box after the code for that item is in place and the relevant tests for that item pass.

## Guardrails

- [x] Freeze the current line-count baseline: `FlatSpace.m = 1792`, `GammaMatrices.m = 219`, total hot-path baseline `2011`.
- [ ] Keep the final `FlatSpace.m` below `1792` lines.
- [ ] Keep the final total across `FlatSpace.m`, `GammaMatrices.m`, and any new internal kernel file below `2011` lines.
- [ ] Delete replaced hot-path helpers in the same phase they become unused.
- [ ] Keep exactly one canonical compiled IR and one hot evaluation path when the rewrite is complete.

## Phase 1: Extract a clean kernel boundary

- [ ] Add `SpinProjectionKernel.m` under `StringCode/OPE/TypeII/FlatSpace/`.
- [ ] Load the new module from `FlatSpace.m`.
- [ ] Move compiled fast-path ownership into `buildSpinProjectionKernelModel[...]` and `solveSpinProjectionKernelModel[...]`.
- [ ] Leave `FlatSpace.m` with sector splitting, tensor-structure generation, orchestration, and final recombination only.
- [ ] Delete the moved compiled-solver helper bodies from `FlatSpace.m` once the new module is wired.
- [ ] Re-run the existing projected-spin regressions after the extraction.

## Phase 2: Lower everything into one canonical IR

- [ ] Define one compiled model format for free inputs, output families, compiled terms, dummy metadata, and output-state metadata.
- [ ] Lower ground and excited spin fields through the same IR.
- [ ] Lower mode-carried vector labels into ordinary slot references instead of a special execution path.
- [ ] Keep symbolic prefactors attached to terms but outside the inner numeric kernel.
- [ ] Delete the old overlapping descriptor layouts after all call sites switch to the IR.
- [ ] Add parity checks on one ground-spin and one excited-spin example.

## Phase 3: Replace hot-path matrices with gamma action tables

- [ ] Add private action tables in `GammaMatrices.m` for every primitive link used by compiled gamma chains.
- [ ] Add one compiled gamma-chain evaluator that propagates basis states through links instead of constructing product matrices.
- [ ] Use the same action tables for scalar evaluation and output-spin support extraction.
- [ ] Keep the public dense and sparse gamma accessors unchanged.
- [ ] Add regression checks that the action tables reproduce the current dense/sparse matrices exactly.

## Phase 4: Rewrite term evaluation as a low-symbolic kernel

- [ ] Replace the current matrix/descriptor probing path with table-driven factor instructions over packed integer assignments.
- [x] Keep symbolic prefactors outside the dummy loop and multiply them in once per completed term value.
- [ ] Keep candidate spins, candidate vectors, output states, and dummy states as packed integer vectors throughout the kernel.
- [ ] Remove `Association`, `Bosonize`, symbolic pattern dispatch, and generic `SparseArray` indexing from the inner evaluation loop.
- [ ] Delete or demote superseded matrix-oriented hot-path helpers so only one kernel evaluator remains.
- [ ] Re-run projected-spin regressions and compare candidate-row parity on representative inputs.

## Phase 5: Make dummy summation structure-aware

- [ ] Compile dummy-slot usage metadata per term.
- [ ] Add dummy-aware output-spin support summaries before full dummy summation.
- [ ] Skip repeated dummy indices for antisymmetric dummy blocks.
- [ ] Replace ordered tuple loops by increasing combinations when the dummy slots are local to one antisymmetric gamma chain.
- [ ] Keep the generic tuple loop only for mixed-use dummy slots that cannot be collapsed safely.
- [ ] Add regression checks for support parity and antisymmetric-loop parity.

## Phase 6: Compile output-state maps once

- [x] Compile each output family template into a direct state-to-operator-association map.
- [ ] Support excited spin-field templates through the same slot-based lowering.
- [x] Remove per-output-state `Bosonize[...]` from candidate-row generation.
- [x] Delete the superseded per-state output-association helpers from the hot path.
- [ ] Re-run projected-spin regressions and one excited-spin targeted case.

## Phase 7: Add fast row screening and candidate scoring

- [ ] Add cheap candidate scoring from predicted support and active-term patterns.
- [ ] Add cheap numeric screening before exact basis insertion.
- [ ] Keep exact basis insertion authoritative whenever screening is inconclusive.
- [ ] Preserve deterministic seeded behavior for equal-score candidates.
- [ ] Re-run exact-solution parity and seed-independence regressions.

## Phase 8: Delete transition code and tighten the module

- [ ] Remove dead helpers, duplicate descriptors, and transitional wrappers left behind by the rewrite.
- [ ] Collapse wrapper-only helpers that no longer carry real logic.
- [ ] Confirm every remaining nontrivial helper has a `::usage` line immediately above its definition.
- [ ] Recount lines and confirm the final hot-path implementation is below the baseline budget.

## Phase 9: Benchmark and close out

- [ ] Benchmark the 5-chiral-spin stress case end to end.
- [ ] Benchmark one excited spin-field case with mode-carried vector labels.
- [ ] Benchmark one antisymmetric dummy-heavy case.
- [ ] Confirm at least `3x` faster candidate-row generation on the 5-spin stress case.
- [ ] Confirm at least `5x` faster end-to-end solve on the same case unless profiling shows projection dominates.
- [ ] Update `performance.md` with final measurements and the post-rewrite bottleneck summary.
