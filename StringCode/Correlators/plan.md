# Correlators Module Rewrite Plan

## Objective

Rewrite `StringCode/Correlators` into a proper module family that matches the current repository architecture and computes the generic free-sector correlators that are already implied by the existing Wick/OPE infrastructure.

The implementation target is:

- a shared correlator engine in `Correlators/Correlators.m`
- standard theory split modules in `Correlators/Bosonic/Bosonic.m` and `Correlators/TypeII/TypeII.m`
- a `Correlators/TypeII/FlatSpace/FlatSpace.m` extension for the Type II bosonized free-field sector
- integration into `StringCode.m`
- `.test.wlnb` coverage with minimal boilerplate

This rewrite should not try to solve every CFT-specific correlator immediately. It should evaluate the generic free/collapsable sector and leave the rest symbolic in a controlled way.

## Scope And Behavioral Decisions

### Public API

The public surface stays small:

- `Corr[ops__]`
- `Corr[MultiOp[ops__]]`
- `Vev[expr]`

No public `AtInfinity[...]` or `BPZConjugate[...]` wrapper is added in v1. Users continue to write operators with literal `Infinity` in their position slots.

### What Evaluates In V1

The generic correlator engine evaluates:

- universal ghost free sectors
- bosonic flat-space free matter sectors already covered by `Wick`
- Type II flat-space free sectors already covered by `Wick`
- Type II bosonized `H`/`phi` sectors through `Vev`
- pure `psi` / `psit` free correlators through Wick, just as requested

The generic engine intentionally does not try to evaluate arbitrary nonfree sectors such as:

- Bosonic MinimalModel primaries
- general interacting CFT sectors
- raw Type II spin-field correlators involving `S` / `St`

Those should remain as symbolic `Corr[...]` unless a dedicated specialized correlator module adds explicit downvalues later.

### High-Level Evaluation Strategy

`Vev` is part of the correlator engine, not a separate user step.

The evaluation flow is:

1. `Corr` normalizes inputs and handles multilinearity.
2. Each local operator is split into:
   - an evaluable collapsable/free part
   - a residual non-collapsable part
3. The free part is processed by a dedicated `CorrWick` / `CorrWickList` path.
4. That path performs the Wick/OPE-style contractions and reduces the result to a single local operator expression.
5. `Vev` evaluates the remaining zero-mode/background-charge content of that local operator.
6. If residual unsupported operators remain, the result is:
   - `freeFactor * Corr[residualOps...]`
7. If nothing in the input is supported by the generic free-sector engine, `Corr[...]` stays unevaluated.

This mirrors the current `OPE` design rather than introducing a second independent evaluation model.

## Module Layout

### `StringCode/Correlators/Correlators.m`

Shared package responsibilities:

- declare and export `Corr` and `Vev`
- define multilinearity and scalar-factor extraction
- support `Corr[MultiOp[...]]`
- implement shared private helpers for splitting collapsable sectors
- implement `CorrWickList`
- implement internal handling of insertions at `Infinity`
- implement the generic VEV framework
- host the universal `bc` top-form VEV sectors
- provide symbolic fallback behavior for unsupported sectors

### `StringCode/Correlators/Bosonic/Bosonic.m`

Theory module responsibilities:

- `Needs` the shared correlator package and bosonic theory packages
- register or expose Bosonic-specific correlator/Vev logic if needed
- keep the standard module split even if the initial file is thin

The Bosonic theory module exists because the repository expects this structure and future Bosonic-specific correlator rules should land there rather than in the shared package.

### `StringCode/Correlators/TypeII/TypeII.m`

Theory module responsibilities:

- `Needs` the shared correlator package and Type II theory packages
- register the Type II VEV sectors involving superghost / `phi` background charge
- define theory-level helpers that do not depend specifically on a single CFT

### `StringCode/Correlators/TypeII/FlatSpace/FlatSpace.m`

Flat-space Type II extension responsibilities:

- bridge to the existing bosonized `H`-field machinery
- reuse `Bosonize`, `expH`, `expHt`, `dH`, `dHt`, `chargeDot`, `cocycle`, and existing Wick rules
- support the free bosonized VEV path after contractions
- support the pure `psi` free-sector correlator path via Wick

### Optional `StringCode/Correlators/Bosonic/FlatSpace/FlatSpace.m`

Only create this file if the implementation naturally requires Bosonic FlatSpace-specific correlator hooks beyond the shared engine. The standard Bosonic module split is mandatory; the extra Bosonic FlatSpace layer is optional if it would otherwise be empty boilerplate.

## Corr Engine Details

### Input Normalization

`Corr` should support:

- `Corr[] := 1`
- `Corr[..., 0, ...] := 0`
- linearity in every argument
- scalar prefactor extraction when the prefactor contains no registered fields
- `Corr[MultiOp[ops__]] := Corr[ops]`

The generic engine should accept `R[...]` and `MultiOp[...]` inputs. Other operator heads should be preserved as extension points rather than force-converted.

### Reusing The OPE Split Logic

The correlator engine should reuse the same notion of "collapsable" already encoded in the symbol metadata and in `OPE`.

Implementation plan:

- use the same `splitCollapsable` concept as in `OPE`
- for each `R[...]`, separate collapsable fields from residual fields
- collect the collapsable `R[...]` pieces across insertions
- collect the residual `R[...]` pieces across insertions

Behavior:

- if there are no collapsable pieces at all, leave `Corr[...]` unevaluated
- if there are collapsable pieces and no residual pieces, evaluate fully
- if both are present, evaluate the free factor and multiply it by symbolic `Corr[residual...]`

### `CorrWickList`

Add a shared-private helper `CorrWickList` as the correlator analogue of the current free OPE folding helpers.

Its behavior should be:

- take a list of local `R[...]` operators already known to belong to the free-sector engine
- fold the existing Wick/OPE machinery over them
- reduce the result to a single local operator expression
- pass that final local operator expression to `Vev`

This keeps all pairwise contraction combinatorics in one place and makes `Vev` responsible only for final zero-mode/background-charge saturation.

### Pure Type II Free Sector

Type II needs one special supported free-sector path:

- if the input is entirely in the supported free Type II sector, evaluate it even when some heads are not marked collapsable in the generic metadata path
- in particular, pure `psi` / `psit` correlators should evaluate via Wick

Raw spin fields `S` / `St` remain symbolic in v1.

## VEV Architecture

### Design Goal

Encode all VEV logic in one elegant, extensible framework rather than a collection of unrelated replacement rules.

The core idea is:

- `Vev` acts on the final local operator after contractions
- `Vev` evaluates by decomposing the operator into registered sectors
- each sector is responsible for its own saturation rule

This makes the background-charge logic, ghost top-form logic, and future zero-mode sectors all look structurally the same.

### Sector Model

Implement a small private registry of VEV sectors in the shared correlator package.

Each registered sector should specify:

- which field heads belong to the sector
- how to localize those fields at the origin
- how to evaluate the sector contribution on a localized operator
- what counts as unsaturated leftover content

V1 should support two sector kinds.

#### 1. Top-Form Sector

Used for finite Grassmann zero-mode saturation, such as the `bc` ghost system.

Evaluation model:

- localize all fields to the origin
- expand only as far as needed to expose the zero-mode basis
- extract the coefficient of one canonical ordered basis monomial
- return zero unless that top-form basis is saturated exactly

#### 2. Charge Sector

Used for bosonized systems with background charge, such as Type II `phi/H`.

Evaluation model:

- localize all fields to the origin
- bosonize where needed
- sum the sector charges
- compare against a fixed background-charge vector
- return zero unless the charge matches exactly and no forbidden leftover oscillators remain

### Universal `bc` VEV Sector

The shared correlator package should register universal holomorphic and antiholomorphic `bc` sectors.

Canonical basis:

- holomorphic top form: `{c[0,0], c[1,0], c[2,0]}`
- antiholomorphic top form: `{ct[0,0], ct[1,0], ct[2,0]}`

Rules:

- any surviving `b[...]` or `bt[...]` kills the VEV
- localize `c[n,z]` and `ct[n,zbar]` by truncated Taylor expansion around the origin
- extract the coefficient of the canonical ordered top-form monomial

Normalization:

- set `Vev[R[c[0,0], c[1,0], c[2,0]]] = -2`
- set `Vev[R[ct[0,0], ct[1,0], ct[2,0]]] = -2`

This normalization is chosen so that the package reproduces the standard sphere result:

- `<c(z1)c(z2)c(z3)> = (z1-z2)(z1-z3)(z2-z3)`

Once the top-form sector is implemented this way, the usual ghost-number-three selection rule is not hard-coded separately; it follows automatically from top-form saturation.

### Type II `H` / `phi` VEV Sector

The Type II theory module should register bosonized charge sectors for the holomorphic and antiholomorphic `H` systems.

Background charges:

- holomorphic target charge: `{-2, 0, 0, 0, 0, 0}`
- antiholomorphic target charge: `{-2, 0, 0, 0, 0, 0}`

Interpretation:

- the first component is the bosonized `phi` charge
- the remaining components are the matter `H` charges

Rules:

- bosonize surviving local fields using the existing `Bosonize` machinery
- combine same-point exponentials as usual
- the VEV is nonzero only if the total sector charge matches the background vector exactly
- any leftover oscillator-type fields such as `dH`, `dHt`, `d\[Phi]`, `d\[Phi]t`, `\[Eta]`, `\[Xi]`, `\[Beta]`, `\[Gamma]`, and their antiholomorphic partners kill the VEV in v1

Normalization:

- set `Vev[R[expH[{-2,0,0,0,0,0},0]]] = 1`
- set `Vev[R[expHt[{-2,0,0,0,0,0},0]]] = 1`

This makes the background-charge rule explicit and keeps it separate from pairwise Wick contractions.

### VEV Composition

Shared `Vev` behavior:

- expand linearly
- pull out scalar prefactors
- localize to the origin
- canonicalize the resulting normal ordering
- split the operator into the registered sectors
- multiply the sector results
- return `0` when a known sector is unsaturated
- leave `Vev[...]` unevaluated only when the expression still contains unsupported unknown sector content

## Insertions At Infinity

Operators at `Infinity` should be handled internally via the conformal definition of BPZ conjugation, not by inventing special Wick rules at infinity.

Implementation approach:

- replace each `Infinity` insertion by fresh large placeholders
- multiply the correlator by the appropriate weight factor:
  - `u^(2 totalWeightHolo[op])`
  - `ubar^(2 totalWeightAntiHolo[op])`
- evaluate the correlator at finite position
- take the limit sequentially to infinity

Reasons for this choice:

- it matches the standard CFT definition
- it avoids inconsistent effective Wick rules for multiply contractible operators
- it works uniformly for generic free sectors and later specialized sectors

## Integration Into `StringCode.m`

Update the main initializer so correlator modules are loaded like the other subsystems.

Required changes:

- add `Needs["StringCode`Correlators`"]` to the base shared loads
- add `StringCode`Correlators`Bosonic`` to the Bosonic theory context list
- add `StringCode`Correlators`TypeII`` to the Type II theory context list
- add `StringCode`Correlators`TypeII`FlatSpace`` when Type II FlatSpace is selected
- add `StringCode`Correlators`Bosonic`FlatSpace`` only if that module is actually created

## Documentation Rule

All new nontrivial symbols, including shared-private helpers, should receive `::usage` lines immediately above their definitions, following the repository convention in `AGENTS.md`.

In practice this applies at least to:

- `CorrWickList`
- VEV-sector registry helpers
- infinity-handling helpers
- localization helpers
- top-form extraction helpers
- charge-sector helpers

## Test Plan

Write `.test.wlnb` files with minimal boilerplate and cover the following cases.

### Load Path

- `InitStringCode[...]` exposes `Corr` and `Vev` in:
  - Bosonic FlatSpace
  - Bosonic MinimalModel
  - TypeII FlatSpace

### Direct VEV Tests

- `Vev[R[c[0,0], c[1,0], c[2,0]]]` is nonzero with the chosen normalization
- wrong `c`-ghost degree gives `0`
- antiholomorphic `ct` sector behaves analogously
- `Vev[R[expH[{-2,0,0,0,0,0},0]]] == 1`
- wrong total `H` charge gives `0`
- leftover `dH` / `d\[Phi]` / `\[Eta]` / `\[Xi]` content gives `0`

### Correlator Tests

- `<c(z1)c(z2)c(z3)>` reproduces the standard Vandermonde factor
- `<ct(zbar1)ct(zbar2)ct(zbar3)>` reproduces the antiholomorphic analogue
- the same ghost correlators with one insertion at `Infinity` reproduce the BPZ-weighted formulas
- pure `psi` / `psit` two-point and higher free-field Wick correlators evaluate
- Type II `exp\[Phi]` correlators are nonzero only when each chiral sector has total charge `-2`
- mixed free/nonfree inputs factor into a computed free factor times symbolic residual `Corr[...]`
- purely unsupported sectors remain unevaluated

### Regression / Boundary Tests

- `Corr[MultiOp[...]]` agrees with `Corr[...]`
- scalar prefactors and sums distribute correctly
- `Corr[] == 1`
- `Corr[..., 0, ...] == 0`

## Explicit Non-Goals For V1

Do not implement in this pass:

- a full general spin-field correlator engine for `S` / `St`
- target-space zero-mode integration or momentum-conservation delta functions
- migration of Bosonic MinimalModel special correlators into the generic free-sector engine
- a public wrapper syntax for infinity insertions

## Implementation Order

1. Replace the stale correlator prototype with the shared package skeleton.
2. Add the theory split modules and load-path wiring.
3. Build the shared `Corr` normalization and splitting logic.
4. Implement the VEV-sector framework.
5. Register the universal `bc` top-form sectors.
6. Register the Type II `H` / `phi` charge sectors.
7. Add the Type II FlatSpace free-sector bridge.
8. Implement the internal infinity handling.
9. Add tests and validate the load path plus core examples.
