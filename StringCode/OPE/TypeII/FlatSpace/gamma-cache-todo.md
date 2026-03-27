# Todo: Canonical Gamma-Product Cache for TypeII FlatSpace

Only check a box after the code for that item is in place and the relevant tests for that item pass.

## Guardrails

- [x] Keep `FlatSpace.m` below the current `1788` lines.
- [ ] Keep `GammaMatrices.m` plus any new cache file compact enough that the hot-path total stays below the current `2007`-line baseline.
- [x] Use one cache-backed lookup path for supported descriptors. Do not keep a second hot-path builder alive in parallel.
- [x] Keep the public gamma APIs unchanged.

## Phase 1: Add the cache data

- [x] Add `GammaProductCache.m` under `StringCode/OPE/TypeII/FlatSpace/`.
- [x] Define the canonical cached families `{None,1}`, `{None,2}`, `{CUDHold,2}`, `{CDUHold,1}`.
- [x] Store canonical sparse matrices for all sorted index combinations of ranks `0..10`.
- [x] Add internal cache accessors with `::usage` lines immediately above definitions.
- [x] Add one developer regeneration script for the committed cache file.

## Phase 2: Normalize descriptors onto the cache

- [x] Add one internal helper that classifies a concrete descriptor into a cached family or rejects it.
- [x] Add one internal helper that sorts concrete vector indices and returns the permutation sign.
- [x] Treat repeated indices as zero immediately for rank `> 1`.
- [x] Keep unsupported descriptors on the existing fallback builder.

## Phase 3: Wire the compiled hot path to the cache

- [x] Load `GammaProductCache.m` from `GammaMatrices.m`.
- [x] Route compile-time concrete matrix slots through the cache-backed lookup path.
- [x] Route `spinProjectionConcreteGammaSparseMatrix` through the same cache-backed lookup path.
- [x] Remove runtime antisymmetrization and runtime sparse matrix products from supported compiled descriptors.

## Phase 4: Test the cache

- [x] Add exact equality tests between cached matrices and the current builder for all supported families and sorted tuples up to rank 10.
- [x] Add repeated-index zero tests for rank `> 1`.
- [x] Re-run the current projected-spin regressions that hit the compiled path.

## Phase 5: Benchmark and close out

- [x] Benchmark cold `spinProjectionCandidateRows[...]` on the 5-chiral-spin case.
- [x] Benchmark warm `spinProjectionCandidateRows[...]` on the same case.
- [x] Benchmark the isolated heavy rank-3 term.
- [x] Confirm the hot path no longer performs runtime antisymmetrization or runtime sparse matrix `Dot` for cached families.
- [x] Update `performance.md` with the cache measurements and the remaining bottleneck summary.
