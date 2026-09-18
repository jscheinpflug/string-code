# Local cocycles and frozen gamma data — convention version 2

Applied 2026-09-05. Restart the Wolfram kernel before using this change. Reloading only one module into an old kernel is not supported: matrix and projection memoizations may still contain the old convention.

## Source change

`NormalOrdering/TypeII/TypeII.m` now includes the ordered pairwise cocycles of local bosonized exponential factors before merging their charges. Factors are grouped by chirality and coordinate. There are no cross-sector phases and no local factors between distinct points. The ordering is the order after `R` canonicalization, including its existing permutation sign.

Mixed local products now preserve point splitting inside every repeated same-point same-sector fermion subgroup. Previously `Bosonize[R[psi,psi]]` used the projected point-split path, while adding a spectator such as `dphi` sent the same fermion pair through direct charge merging. For conjugate vector-charge components this replaced the required `dH` current by spurious charge-plus-or-minus-two exponentials. The `dphi psi psi` terms in the KFFK mass vertex exposed this difference. Point-split subgroup outputs are tagged as already bosonized before being combined with the spectator fields, so their normalization and cocycles are not applied twice.

For a picture-minus-one vector, the ghost/vector-charge cocycles are +i and -i for positive and negative vector charges. In the stored Cartesian basis this gives the rotation

```
V2[i]   =  V1[i+5]    i = 1,...,5
V2[i+5] = -V1[i]
```

`GammaMatrices.m` applies the same rotation to both mixed gamma families before building dense matrices, charge-conjugated matrices, or products. Spinor pairing matrices do not change. The rotation is orthogonal and preserves the Clifford relations.

## Serialized data and cache compatibility

The existing `SpinFieldConventionData.m` and `GammaProductCacheData.m` are retained as version-1 data. They are explicitly imported into version 2; they are not silently treated as new-convention data. Product import includes both vector-rotation signs and antisymmetric permutation signs. Public gamma matrices, direct products, and cache lookups therefore use the same convention.

Untagged data default to version 1 on every load. A future regenerated spin-field data file must declare `spinFieldConventionDataVersion = 2`. The product-cache generator now writes `gammaProductCacheDataConventionVersion = 2`, preventing double rotation when regenerated from the new public matrices. Unknown versions fail closed. Do not add a version-2 tag to unchanged version-1 arrays.

Persistent gamma-kernel cache hashes include the modified matrix source and now also the product-cache implementation and serialized data. Old on-disk caches need not be deleted; they are not selected by the new source hash.

## Test expectations and independent checks

The phase-sensitive local-product snapshots were adjusted using the declared ordered cocycles, including the sign from `R` reordering, not by accepting arbitrary new output. One-mode descendant branches inherit the same +/-i vector-charge phases.

Gamma sign/transpose identities swap their first-five/last-five split under this rotation. The charge-based two-point extraction tests now include the input dressing cocycle and divide by the output dressing cocycle. In particular, the picture-minus-three output basis has the opposite rotation to picture minus one, yielding the corresponding minus sign in the Sdot-Sdot/CIGamma relation.

`LocalCocycles.test.wls` checks both chiral sectors, both original and renamed spin-block inputs, the repeated-index counterexample, deliberately corrupted coefficients, spectator-independence of five representative point-split fermion currents in each sector, and every cached product against a separate recurrence built from public matrices (4 families times 1024 index subsets). It runs with TypeII-Ashoke by default or TypeII-Xi when `STRINGCODE_TEST_CONVENTION=TypeII-Xi`.

The mandatory-validation regression fixture previously expected the physical counterexample to fail. It now injects deliberately doubled fit coefficients to retain explicit rejection tests; the repaired physical block is separately required to pass. No validation budgets or acceptance criteria were relaxed.

## Results and limits

- Local-cocycle and mixed point-splitting regressions: 41/41 under Ashoke; 41/41 under Xi.
- Mandatory-validation regressions: 22/22.
- NormalOrdering: 41/42 after phase-expectation migration; the previously failing multi-mode descendant test 41 remains unresolved.
- GammaMatrices: 35/37 after rotation-expectation migration; previously failing tests 6 and 17 remain unresolved. The new independent all-subset recurrence check passes despite the old test-17 reference failure.
- GammaConventions: 11/11 after dressing the charge-basis extraction. The existing five-spin zero-output/fixed-anchor override remains a coverage limitation, not a general five-spin validation.
- Wick: 10/10, unchanged assertions.
- OPE: 22/45, unchanged assertions. Relative to the previous mandatory-validation run, test 38 changes from fail to pass; the other flags are unchanged. Twenty-three previously failing assertions remain.
- Full termwise KFFK projection: 64/64 mass-vertex terms completed in a fresh kernel; no validation rejection occurred. The combined projected expression and `Vev` result contain no unresolved `OPE`, `OPEProjected`, `Vev`, `$Failed`, or `$Aborted` heads. This run used `$RecursionLimit = 8192` and staged the large expression term by term.

These checks establish the tested convention consistency and successful execution of the current KFFK projection pipeline. They do not prove the physical correctness of the resulting Konishi correlator or its later post-processing. User notebooks and saved correlator exports were not regenerated or overwritten by this patch.
