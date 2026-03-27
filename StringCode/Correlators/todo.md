# Correlators Rewrite Todo

## Shared Package

- [x] Replace `StringCode/Correlators/Correlators.m` with the new shared package skeleton.
- [x] Add `Corr` multilinearity, scalar extraction, `Corr[]`, `Corr[..., 0, ...]`, and `Corr[MultiOp[...]]`.
- [x] Reuse the OPE-style collapsable split and add the shared-private `CorrWickList` helper.
- [x] Implement the symbolic fallback for residual unsupported sectors.
- [x] Implement internal handling of insertions at `Infinity` via BPZ-weighted limits.
- [x] Add `::usage` documentation for all new nontrivial shared and shared-private helpers.

## VEV Framework

- [x] Build a private VEV-sector registry in the shared correlator package.
- [x] Implement the generic `TopForm` sector evaluator.
- [x] Implement the generic `Charge` sector evaluator.
- [x] Implement localization-to-origin helpers used by `Vev`.
- [x] Implement sector splitting and sector-product composition inside `Vev`.

## Universal Ghost Sector

- [x] Register the holomorphic `bc` top-form sector with basis `{c[0,0], c[1,0], c[2,0]}`.
- [x] Register the antiholomorphic `bc` top-form sector with basis `{ct[0,0], ct[1,0], ct[2,0]}`.
- [x] Fix the `bc` normalization so `<c(z1)c(z2)c(z3)>` matches the standard sphere result.
- [x] Ensure leftover `b` / `bt` content kills the VEV.

## Theory Modules

- [x] Create `StringCode/Correlators/Bosonic/Bosonic.m`.
- [x] Create `StringCode/Correlators/TypeII/TypeII.m`.
- [x] Create `StringCode/Correlators/TypeII/FlatSpace/FlatSpace.m`.
- [x] Create `StringCode/Correlators/Bosonic/FlatSpace/FlatSpace.m` to preserve the standard Bosonic FlatSpace module split.
- [x] Wire the correlator modules into `StringCode/StringCode.m`.

## Type II VEVs

- [x] Register the holomorphic bosonized `H` charge sector with background charge `{-2, 0, 0, 0, 0, 0}`.
- [x] Register the antiholomorphic bosonized `H` charge sector with background charge `{-2, 0, 0, 0, 0, 0}`.
- [x] Reuse existing `Bosonize` machinery so `exp\[Phi]` and `expH` inputs share one VEV path.
- [x] Make leftover `dH`, `dHt`, `d\[Phi]`, `d\[Phi]t`, `\[Eta]`, `\[Xi]`, `\[Beta]`, `\[Gamma]`, and antiholomorphic partners kill the VEV in v1.

## Type II Free Sector

- [x] Add the supported free-sector correlator path for Type II FlatSpace.
- [x] Ensure pure `\[Psi]` / `\[Psi]t` correlators evaluate through Wick.
- [x] Leave raw `S` / `St` correlators symbolic in v1.

## Tests

- [x] Add correlator test notebooks with minimal boilerplate.
- [x] Test load-path exposure of `Corr` and `Vev` in Bosonic FlatSpace, Bosonic MinimalModel, and TypeII FlatSpace.
- [x] Test direct `bc` VEV saturation and wrong-degree vanishing.
- [x] Test direct Type II background-charge VEV saturation and wrong-charge vanishing.
- [x] Test standard `<c(z1)c(z2)c(z3)>` and antiholomorphic analogues.
- [x] Test correlators with one insertion at `Infinity`.
- [x] Test mixed free/nonfree factorization into computed free part times symbolic residual `Corr[...]`.
- [x] Test `Corr[MultiOp[...]]`, scalar prefactors, sums, and `Corr[]`.
