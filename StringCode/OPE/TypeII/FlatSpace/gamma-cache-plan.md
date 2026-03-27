# Plan: Canonical Gamma-Product Cache for TypeII FlatSpace

## Summary

- Add a committed, preloaded cache of canonical antisymmetrized gamma-product sparse matrices for the legal alternating spinor-chain families up to rank 10.
- Normalize concrete compiled gamma descriptors onto that cache at runtime by family, sorted vector-index tuple, and permutation sign.
- Keep `OPEProjected[...]` behavior unchanged. The gain comes from removing runtime antisymmetrization and runtime sparse matrix products from the compiled hot path.

## Cache Shape

- Cache only the legal alternating families used by the compiled spin path:
  - `{None, 1}`: no leading pairing, vector chain starts with `GammaUD`
  - `{None, 2}`: no leading pairing, vector chain starts with `GammaDU`
  - `{CUDHold, 2}`: leading `CUD`, vector chain starts with `GammaDU`
  - `{CDUHold, 1}`: leading `CDU`, vector chain starts with `GammaUD`
- Precompute all sorted vector-index combinations for ranks `0..10`.
- Canonicalize by sorted tuple, not by raw permutation order.
- Runtime repeated indices for rank `> 1` map to zero immediately.

## Implementation Changes

- Add one internal runtime cache file, loaded with TypeII FlatSpace gamma data.
  Recommended path: [GammaProductCache.m](/home/scheinpflug/Github/string-code/StringCode/OPE/TypeII/FlatSpace/GammaProductCache.m)
- Store compressed sparse-table data for the canonical families and expose internal accessors with `::usage` lines.
- Add one developer regeneration script that rebuilds the committed cache file from the primitive gamma matrices. The script is not used at runtime.
- Update [GammaMatrices.m](/home/scheinpflug/Github/string-code/StringCode/OPE/TypeII/FlatSpace/GammaMatrices.m) to load the cache file during TypeII FlatSpace initialization.
- Update [FlatSpace.m](/home/scheinpflug/Github/string-code/StringCode/OPE/TypeII/FlatSpace/FlatSpace.m) so `spinProjectionConcreteGammaSparseMatrix`:
  - resolves vector sources to integers
  - detects whether the descriptor belongs to one cached family
  - sorts indices and computes the permutation sign
  - fetches the canonical sparse matrix from the cache
  - falls back to the current builder only for unsupported descriptors
- Route both compile-time concrete matrix slots and runtime concrete matrix resolution through the same cache-backed path.

## Tests And Benchmarks

- Add exact equality tests that compare cached products to the current builder for all supported families and all sorted tuples up to rank 10.
- Add repeated-index tests showing rank `> 1` cached lookups return zero.
- Keep current projected-spin regressions unchanged.
- Benchmark at least:
  - the 5-chiral-spin cold `spinProjectionCandidateRows[...]` path
  - the same path warm
  - the isolated heavy rank-3 term
- Acceptance target: the 5-spin hot path must stop performing runtime antisymmetrization and runtime sparse matrix `Dot` for the cached families.

## Assumptions

- The cache is internal only. No public gamma API changes.
- The cache covers only canonical alternating vector-chain families with empty `tailLinks`.
- Unsupported descriptors keep the current runtime builder as fallback.
- The cache is committed to the repo and imported at load time, not regenerated on demand.
