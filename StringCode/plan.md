# Refactor: get rid of overengineered `Interacting` and `Op` headers

## Background:
- Currently, we have `R`, `SF`, `MultiOp`, `Interacting`, `Op` as headers into which we can put fields (such as `b`, `c`)
- `Op` is just a packaging of a tuple of `R` and `Interacting`, thus if `Interacting` is removed, it must be removed too
- I want to remove `Interacting` (and things that go with it like `interactingOperators`, `CollapseInteracting`) as I believe it is an overengineered solution to distinguishing between free and interacting operators
- Such a distinguishment is needed since the OPE of universal free fields `b`, `c` (with `eta`, `xi` for Type II) is always done via Wick contractions, whereas OPE of interacting operators has be handled on a case-by-case basis
- Instead of introducing this distinction at the level of OPE, the OPE function only has nontrivial output when `R` is put into it and if `Interacting` is put into it, it simply does not evaluate it, leading to ad-hoc projection rules such as `CollapseInteracting`, using `InteractingProjection`
- This will reduce technical debt by a lot since we will not have to implement every method for `Interacting` and `R` separately

## Task
- Get rid of the distinction between `R` and `Interacting`, simply have all fields sit inside `R` (which can then sit inside `MultiOp`/`SF`, but that's not key)
- The symbols `b`, `c` (or `eta`, `xi`) are to be added to a list name `collapsable` in Symbols
- Now, when OPE is called on `R` of some symbols, it:
 * Commutes (with appropriate Grassmann signs defined by `parity`) all the `collapsable` operators through the rest of operators (say to the left)
 * Performs the OPE defined via Wick contractions on these `collapsable` operators (feel free to introduce say `OPEWick` private helper to capture current OPE Wick contraction logic)
 * Performs the OPE on the rest of these operators. The implementation on such general operators is to be left blank at the moment.
- Make dX, expX, ProfileX `collapsable` too, so their OPE is evaluated via `OPEWick` (but not `psi`, `expphi`)
- Add `OPEProjected`, which takes in normal-ordered products and projects their OPE it onto some particular holo/antiholo weights. After stating its general properties (multilinearity etc.), this is to have an implementation that again separates `collapsable` operators from the rest (which are projected on a case-by-case basis). Reuse `CollapseFree` and `projectOPE` to implement the version on `collapsable` operators (for the free case, the projection is done by rescaling operators by epsilon parameters, then performing `OPE`, then picking out a specific power of epsilon). Reuse `InteractingProjection` to implement the `Bosonic/MinimalModel` version (on non-collapsable operators like 1, V). 
- Take substential care in making sure that the Bracket module retains its function. For example, the collapsing and projection onto a given weight should now be taken care of by the OPE module.

## Implementation Proposal

### Summary
- Remove `Interacting` and `Op` entirely; all local operators are fields inside `R[...]`.
- Introduce `collapsable` classification to control Wick-computable OPE sectors.
- Keep non-collapsable OPE symbolic under `OPE[...]`.
- Move projection ownership to OPE via:
  - `OPEProjected[wH_, wA_][Ra_, Rb_, ...]`.
- Bracket code delegates collapsing/projection to OPE.

### Locked decisions
- Non-collapsable OPE remains under `OPE[...]` head.
- `collapsable` includes mirrors/split fields (e.g. `bt, ct, etat, xit, dXt, expXHolo/AntiHolo, ProfileXHolo/AntiHolo`).
- No generic fallback weight rule for non-simple fields; explicit field-family rules must exist.
- TypeII unresolved non-collapsable projection is a hard failure with message.
- Tests formerly asserting `Op`/`Interacting` wrappers are rewritten to wrapper-free expectations.

### Phase 1: Symbols refactor (`collapsable`, remove interacting/operator lists)
**Files:**
- `StringCode/Symbols/Symbols.m`
- `StringCode/Symbols/Bosonic/FlatSpace/FlatSpace.m`
- `StringCode/Symbols/TypeII/TypeII.m`
- `StringCode/Symbols/TypeII/FlatSpace/FlatSpace.m`
- `StringCode/Symbols/Bosonic/MinimalModel/MinimalModel.m`

**Changes:**
- Add:
  - `collapsable::usage`
  - `isCollapsable::usage`
  - base definition `collapsable = {b, bt, c, ct}` and cached lookup.
- Extend `collapsable` by module:
  - Bosonic FlatSpace: `dX, dXt, expX, expXHolo, expXAntiHolo, ProfileX, ProfileXHolo, ProfileXAntiHolo`
  - TypeII: `\[Eta], \[Eta]t, \[Xi], \[Xi]t`
- Remove:
  - `interactingOperators`, `allOperators`
  - `isInteracting`, `isOperator`
  - all assignments updating interacting/operator lists.
- Keep `V` as a standard field (non-collapsable).
- Ensure explicit `weightHolo`/`weightAntiHolo` rules exist for every non-simple field family (no generic fallback).

### Phase 2: Operators module purge (`Op`/`Interacting` removal)
**File:**
- `StringCode/Operators/Operators.m`

**Changes:**
- Remove `Op`, `Interacting`, and all related tests/helpers.
- Keep `MultiOp`.
- Update helper predicates:
  - `nonOperatorQ[expr_] := FreeQ[expr, R]`
  - `scalarQ[x_] := FreeQ[x, _MultiOp | _R]`
- Restrict `parityOp` and `totalWeight*` logic to `R`, `MultiOp`, numeric/scalar terms.

### Phase 3: OPE core refactor with collapsable/non-collapsable split
**File:**
- `StringCode/OPE/OPE.m`

**Changes:**
- Add private helpers:
  - `splitCollapsable[Ra_]` -> `{Rcoll, Rrest, sign}`
  - `hasCollapsable[Ra_]`
  - `OPEWick[Ra_, Rb_]` (move current Wick-recursive OPE logic here).
- Redefine `OPE[Ra_, Rb_]` (for `RTest` inputs):
  - commute/split collapsable fields with Grassmann sign tracking,
  - evaluate collapsable sector via `OPEWick`,
  - keep non-collapsable sector symbolic via `OPE[RrestA, RrestB]`,
  - recombine in normal-ordered form.
- Preserve multilinearity/nested OPE, but replace any `allOperators` scalar guards with wrapper-free guards.
- Ensure rule ordering avoids non-terminating recursion for non-collapsable symbolic OPEs.

### Phase 4: Add canonical projection API in OPE
**File:**
- `StringCode/OPE/OPE.m`

**Changes:**
- Add public API:
  - `OPEProjected[wH_, wA_][Ra__ /; And @@ (RTest /@ {Ra})]`
- Implement:
  - free/collapsable projection path by reusing existing epsilon-rescaling + `OPE` + Taylor extraction logic (currently in `CollapseFree`/`projectOPE` flow),
  - non-collapsable projection path via a dedicated hook function (see next phase),
  - multilinearity and scalar factorization.

### Phase 5: CFT-specific non-collapsable projection hooks
**Files:**
- `StringCode/OPE/Bosonic/Bosonic.m`
- `StringCode/Brackets/Bosonic/MinimalModel/MinimalModel.m`
- `StringCode/OPE/TypeII/TypeII.m`

**Changes:**
- Move MinimalModel interacting projection logic into OPE-level hook in bosonic OPE module:
  - equivalent behavior of previous `InteractingProjection` for `{0,0}`, `{1,1}`, and higher weights.
- Rewrite correlator rules to use bare `V[...]` (no `Interacting[...]` wrapper).
- Remove `InteractingProjection` definitions from Brackets MinimalModel file.
- Unresolved non-collapsable projection should:
  - emit explicit message (e.g. missing projection rule for non-collapsable sector),
  - hard-fail (`$Failed`/throw) rather than silently pass.

### Phase 6: Brackets refactor to delegate projection to OPE
**Files:**
- `StringCode/Brackets/Brackets.m`
- `StringCode/Brackets/Bosonic/Bosonic.m`
- `StringCode/Brackets/TypeII/TypeII.m`

**Changes:**
- Remove:
  - `CollapseInteracting`
  - `projectOPE` interacting branch logic
  - wrapper-specific branches in `factorizeMultiOp`, `actBGhostMode`, `ApplyPropagator`, ghost-modding helpers.
- Replace projection call path with:
  - `OPEProjected[targetWeightH, targetWeightAH] @@ bracketLocalROps`
  where `bracketLocalROps` is the extracted list of local `R` operators from a bracket term.
- Keep existing BRST/PCO flow; only replace local collapse/projection backend.

### Phase 7: Supporting module cleanup
**Files:**
- `StringCode/StringFields/StringFields.m`
- `StringCode/TeXConversion/TeXConversion.m`
- any remaining modules/tests referencing removed wrappers/lists.

**Changes:**
- Remove `Op`/`Interacting` patterns from mapping and TeX conversion.
- Replace `allOperators` and `isOperator` guards with wrapper-free logic.
- Remove all leftover references to:
  - `Interacting*`
  - `Op*`
  - `allOperators`
  - `interactingOperators`.

### Verification and acceptance criteria
- **OPE behavior**
  - Free/free collapsable OPE matches existing Wick results.
  - Mixed collapsable/non-collapsable preserves signs and leaves non-collapsable part symbolic.
  - Non-collapsable-only OPE does not recurse infinitely.
- **Projection behavior**
  - `OPEProjected[wH,wA][...]` reproduces current free-sector projection outputs.
  - MinimalModel non-collapsable projection reproduces existing correlator-based outputs.
  - TypeII unresolved non-collapsable projection hard-fails with clear message.
- **Brackets behavior**
  - `BracketProjected` still works in Bosonic and TypeII pipelines.
  - BRST and PCO action flows remain functionally unchanged.
- **Tests**
  - Update wrapper-specific tests to wrapper-free equivalents.
  - Run existing `.test.wlnb` notebooks for impacted modules (`OPE`, `Brackets`, `TeXConversion`, theory-specific variants).

## Summary
- Preserved `MultiOp` while removing/avoiding the older `Interacting`-style OPE handling path.
- Updated core OPE behavior in `StringCode/OPE/OPE.m`:
  - one-sided collapsable inputs now use `OPEWick` directly,
  - split/recombine path is restricted to both-sides-collapsable,
  - this prevents sign/order regressions introduced by mixed-sector recombination.
- Kept non-collapsable OPE unevaluated by default (pattern-matching based control; no separate fallback head intended for projection).
- Kept nested OPE behavior intact.
- Added TypeII FlatSpace specialization in `StringCode/OPE/TypeII/FlatSpace/FlatSpace.m`:
  - pure `psi/expphi` sector uses `OPEWick`,
  - `d[Phi]`/`d[Phi]t` included in that Wick-forced sector,
  - module uses `Begin["Private`"]`.
- Added MinimalModel projection implementation in `StringCode/OPE/Bosonic/MinimalModel/MinimalModel.m` for V-sector projection behavior.
- Reorganized OPE tests into CFT-independent vs CFT-specific locations:
  - `StringCode/OPE/Bosonic/Bosonic.test.wlnb`
  - `StringCode/OPE/TypeII/TypeII.test.wlnb`
  - `StringCode/OPE/Bosonic/FlatSpace/FlatSpace.test.wlnb`
  - `StringCode/OPE/TypeII/FlatSpace/FlatSpace.test.wlnb`
  - `StringCode/OPE/Bosonic/MinimalModel/MinimalModel.test.wlnb`
- Revisited Bosonic OPE test 14 and updated its expectation to the full `dX-dX` OPE structure.
- Last reported headless Mathematica results for reorganized OPE notebooks:
  - Bosonic: `6/6`
  - Bosonic FlatSpace: `5/5`
  - Bosonic MinimalModel: `6/6`
  - TypeII: `6/6`
  - TypeII FlatSpace: `6/6`
- Relevant working-tree state:
  - Modified: `StringCode/OPE/OPE.m`, `StringCode/OPE/Bosonic/Bosonic.test.wlnb`, `StringCode/OPE/TypeII/TypeII.test.wlnb`
  - Untracked: `StringCode/OPE/Bosonic/FlatSpace/FlatSpace.test.wlnb`, `StringCode/OPE/Bosonic/MinimalModel/MinimalModel.m`, `StringCode/OPE/Bosonic/MinimalModel/MinimalModel.test.wlnb`, `StringCode/OPE/TypeII/FlatSpace/FlatSpace.m`, `StringCode/OPE/TypeII/FlatSpace/FlatSpace.test.wlnb`
- Follow-up checks:
  - confirm load wiring for new OPE submodule files,
  - re-run impacted non-OPE suites (`Brackets`, `NormalOrdering`),
  - stage/commit new OPE submodule and test files together.
