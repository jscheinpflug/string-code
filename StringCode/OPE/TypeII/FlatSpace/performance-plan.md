# Plan: Low-Symbolic Rewrite of TypeII FlatSpace `OPEProjected`

## Summary

- Rewrite the compiled spin-projection fast path so the hot loop is mostly integer / small-exact kernel code, not repeated symbolic evaluation.
- Keep the public `OPEProjected[...]` interface and exact symbolic output unchanged.
- Keep pure spin-field OPE as the scope, including excited spin fields whose modes carry vector or spinor labels.
- Keep outgoing `dX` / `dXt` states out of scope for the compiled output-state enumerator.

## Clean-Code Guardrails

- Current baseline is `FlatSpace.m = 1792` lines and `GammaMatrices.m = 219` lines, for a hot-path total baseline of `2011` lines.
- The final `FlatSpace.m` must be shorter than `1792` lines.
- The final total across `FlatSpace.m`, `GammaMatrices.m`, and any new internal kernel file must be below `2011` lines.
- Do not keep old and new hot paths alive in parallel after parity is established. Delete replaced helpers in the same phase they become unused.
- Use one canonical compiled IR for the kernel. Do not keep multiple overlapping descriptor formats.
- Use one hot evaluation path. Dense matrices, sparse matrices, and action tables may coexist for compatibility, but only one representation may drive the kernel.
- Push symbolic work to compile time and final exact reconstruction. The inner loop should not call `Bosonize`, `Canonicalize`, symbolic pattern dispatch, or generic sparse-matrix plumbing.

## Implementation Plan

### 1. Extract a dedicated private kernel module

- Add `SpinProjectionKernel.m` under `StringCode/OPE/TypeII/FlatSpace/` and load it from `FlatSpace.m`.
- Move compiled fast-path ownership into two internal entry points:
  `buildSpinProjectionKernelModel[...]`
  `solveSpinProjectionKernelModel[...]`
- Leave `FlatSpace.m` responsible only for sector splitting, tensor-structure generation, high-level orchestration, and final sector recombination.
- Delete the moved compiled-solver helper bodies from `FlatSpace.m` once the new module is wired and tested.

### 2. Replace ad hoc descriptors with one canonical compiled IR

- Lower each compiled sector into one compact model containing:
  free spin slots,
  free vector groups,
  output families,
  compiled term arrays,
  dummy-slot metadata,
  output-state metadata,
  candidate-enumeration metadata.
- Lower ground and excited spin fields through the same IR. Mode-carried vector indices become normal slot references, not a separate execution path.
- Keep symbolic prefactors attached to terms, but keep them outside the inner numeric kernel.
- Remove old overlapping descriptor layouts once all call sites use the new IR.

### 3. Replace matrix-driven gamma evaluation with action tables

- Keep the public dense and sparse gamma APIs unchanged in `GammaMatrices.m`.
- Add one private action-table representation for the primitive gamma links used by the compiled path.
- Represent each primitive link as basis-state transitions with coefficient codes, not as a matrix object inside the hot loop.
- Evaluate gamma chains by propagating basis states through compiled links instead of constructing concrete `16 x 16` product matrices.
- Use the same action tables for:
  scalar factor evaluation,
  support extraction,
  antisymmetry-aware dummy pruning.

### 4. Rewrite term evaluation as a low-symbolic kernel

- Replace the current matrix/descriptor probing path with one table-driven evaluator over packed integer slot assignments.
- Keep symbolic prefactors outside dummy loops and multiply them in once the numeric kernel has produced the exact small coefficient.
- The inner kernel may use:
  packed integer vectors,
  small exact coefficient tables,
  slot lookups,
  table-driven factor instructions.
- The inner kernel may not use:
  `Association`,
  `Bosonize`,
  `Canonicalize`,
  symbolic pattern matching,
  generic `SparseArray` indexing,
  or generic matrix products.
- Any rare unsupported compiled shape must fall back through one isolated cold path, not through layered hot-path wrappers.

### 5. Make dummy summation structure-aware

- Compile dummy-slot usage metadata per term.
- Add dummy-aware support summaries so terms can be rejected before full dummy summation.
- Detect antisymmetric dummy blocks.
- For antisymmetric blocks, always skip repeated dummy indices.
- When a dummy-slot set is local to one antisymmetrized gamma chain, iterate increasing combinations instead of ordered tuples and account for permutation sign analytically.
- Keep the generic tuple loop only for mixed-use dummy slots that cannot be collapsed safely.

### 6. Remove per-output-state bosonization from the search loop

- Compile each output family template into a direct state-to-operator-association map once.
- Support excited spin-field templates with the same slot-based lowering used for ground states.
- Candidate-row generation should consume compiled output-state maps directly.
- No per-output-state `Bosonize[...]` call may remain in the candidate-row loop.

### 7. Add fast row screening without changing the exact answer

- Keep final accepted rows and final coefficients exact.
- Add cheap candidate scoring from predicted support and active-term patterns so better candidates are tried earlier.
- Add cheap numeric screening before exact basis insertion to reject obviously dependent rows or deprioritize weak candidates.
- If screening is inconclusive, fall back to exact acceptance immediately.
- Keep deterministic seeded behavior stable for equal-score candidates.

## Tests And Acceptance

- Keep existing `OPEProjected` regressions exact and unchanged.
- Add action-table equivalence tests against the current dense/sparse gamma data.
- Add one excited-spin regression that exercises mode-carried vector slots through the new IR.
- Add one antisymmetric dummy-heavy regression that verifies combination-based iteration matches the generic exact result.
- Benchmark at least:
  the 5-chiral-spin stress case,
  one excited spin-field case,
  one antisymmetric dummy-heavy case.
- Acceptance targets:
  at least `3x` faster candidate-row generation on the 5-spin stress case,
  at least `5x` faster end-to-end solve on the same case unless profiling proves `spinProjectionProjectInputs` dominates,
  and no exact symbolic output regression.

## Assumptions

- Pure spin-field OPE remains the optimized problem.
- Excited spin fields are in scope because they still factor into spinor data plus vector-labeled mode data.
- Outgoing `dX` / `dXt` states remain out of scope for the compiled fast path.
- The rewrite should delete or relocate current hot-path code rather than layer more helpers onto it.
