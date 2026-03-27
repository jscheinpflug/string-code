# Performance Notes for TypeII FlatSpace `OPEProjected`

## Current State

The compiled spin-field solver is faster than the old dense/direct scan, but the hard cases are still dominated by exact combinatorics rather than by raw gamma-matrix multiplication.

The representative stress case is:

```wl
OPEProjected[0, 0][
  R[S[{a1, "chiral"}, -1/2, {}, 0, z1]],
  R[S[{a2, "chiral"}, -1/2, {}, 0, z2]],
  R[S[{a3, "chiral"}, -1/2, {}, 0, z3]],
  R[S[{a4, "chiral"}, -1/2, {}, 0, z4]],
  R[S[{a5, "chiral"}, -1/2, {}, 0, z5]]
]
```

For this input, the compiled holomorphic model has:

- `1` output family
- `16` coefficient variables
- `16` compiled terms
- `5` free input spin symbols
- no free vectors
- charge-guided candidate enumeration enabled
- exactly `1` unresolved output spin in the only output family

## Improvements Landed

### 1. Sparse gamma backing

Gamma matrices are now stored and probed sparsely in the compiled path instead of forcing dense intermediate matrices.

Effect:

- cheaper matrix storage
- cheaper support extraction
- direct sparse element access in compiled scalar-factor evaluation

This helps, but it is not the dominant win for the 5-spin case.

### 2. Family-level output-spin pruning

For single-output-spin families, the solver computes a candidate-specific allowed output-spin domain from sparse gamma support and only iterates those states.

For the 5-spin example, the family output-spin domain shrinks from `16` basis states to `5` basis states for the sampled deterministic candidates.

### 3. Term-level output-spin gating

This was the missing optimization after sparse-domain pruning.

Previously, even after shrinking the output-spin domain from `16` to `5`, the solver still scanned all `16` compiled terms for each surviving output spin. That meant about `5 * 16 = 80` term/state checks per candidate.

Now, for single-output-spin families, the solver computes each term's supported output-spin set once per candidate and buckets terms by output-spin basis index. During state iteration it evaluates only:

- generic terms with full support
- terms whose support contains the current output spin

For the 5-spin example, every compiled term has singleton support on the sampled candidate, so the inner work drops from about `80` term/state checks to about `16`.

### 4. Canonical gamma-product cache

Canonical alternating gamma products are now loaded from a committed compressed cache instead of being antisymmetrized and multiplied at runtime.

What changed:

- the cache stores the legal alternating families only:
  `{None,1}`, `{None,2}`, `{CUDHold,2}`, `{CDUHold,1}`
- products are indexed by sorted combinations, not raw permutations
- runtime normalizes a supported concrete descriptor to:
  family,
  sorted vector tuple,
  permutation sign
- supported compiled descriptors return from the cache before the fallback antisymmetrized builder is entered

Measured cache-layer result on the rank-3 hot family `{CUDHold, GammaDUHold[i], GammaUDHold[j], GammaDUHold[k]}` over all `Binomial[10,3] = 120` sorted triples:

- cached path: about `0.00068s`
- old uncached builder: about `0.07969s`

That is about a `117x` speedup for the gamma-product construction layer itself. This is the right scale: once the product is preloaded, the gamma piece becomes essentially negligible.

## Measured Example

Measured on the first deterministic compiled candidate for the 5-spin example with `RandomSeed -> 1234`:

- output-spin domain: `{1, 14, 7, 15, 13}`
- term support sizes: all `16` compiled terms have support size `1`
- active terms per surviving output spin: `{3, 3, 3, 4, 3}`

Ad hoc timing result:

- `spinProjectionCandidateRows` before term gating: about `1.115s`
- `spinProjectionCandidateRows` after term gating: about `0.152s`
- `spinProjectionCandidateRows` after the canonical gamma-product cache:
  about `0.416s` cold,
  about `0.146s` warm

This is roughly a `7x` improvement on the hot per-candidate row-building step for this case.

The cold-row improvement from the pre-cache pruned version to the cached version is modest compared to the cache-layer microbenchmark because the remaining time is no longer gamma-product construction. The cache removed that cost, which exposed the next bottleneck more clearly.

## Current Bottlenecks

### 1. Dummy-vector summation

This is the main remaining cost in hard spin-field cases.

`spinProjectionTermValue` explicitly loops over dummy vectors. For the sampled 5-spin candidate:

- `15` terms have dummy count `1`, so each requires a sum over `10` values
- `1` term has dummy count `3`, so it requires a sum over `10^3 = 1000` values

Even when sparse gamma support proves most term/state pairs are zero, any surviving term still pays for its dummy-vector loop.

After the gamma-product cache landed, this is even clearer:

- one isolated rank-3 cached gamma-product sweep over all `120` triples is about `0.00068s`
- one isolated heavy 3-dummy compiled term evaluation on the 5-spin case is still about `0.38s`

So the remaining cost is not gamma products anymore. It is the exact dummy-loop evaluator wrapped around them.

### 2. Exact arithmetic in the hot loop

The solver uses exact symbolic arithmetic throughout:

- exact gamma matrix entries
- exact row accumulation
- exact row reduction
- exact final `LinearSolve`

This is correct and stable, but expensive.

More importantly, the hot path is not just "look up `1000` sparse gamma entries". Today it also does generic tuple iteration, exact factor multiplication, repeated descriptor resolution, exact summation over dummy values, and exact association/row assembly around those lookups. The sparse entry probe itself is cheap; the surrounding symbolic scaffolding is what makes this a performance discussion.

The canonical product cache confirms this diagnosis. Once the gamma products are preloaded, the per-try cost does not collapse to microseconds, because the solver is still spending time in:

- dummy-index iteration
- exact term multiplication and summation
- row assembly
- exact basis insertion

### 3. Candidate search for full rank

Even after optimizing one candidate, the full solve still has to collect enough independent rows to determine all coefficient variables. For the 5-spin case there are `16` unknown coefficients, so the outer solve may still need many candidate assignments before rank `16` is reached.

### 4. LHS projection and bosonization overhead

Per candidate, the solver still has to:

- concretize the input spins
- project the LHS
- bosonize output states
- build output associations

This is smaller than the old term-scan waste, but still part of the steady per-candidate cost.

## What Is Not Yet Optimized

- multi-output-spin family pruning
- dummy-vector-domain pruning
- pairwise or graph-global spin-support propagation
- skipping whole candidates using stronger prechecks
- reusing more per-family exact data across candidates

## Most Likely Next Wins

If more speed is needed, the next high-value targets are below.

The estimates here are relative to the current code after sparse gamma support, family-level output-spin pruning, and term-level output-spin gating. For the 5-spin stress case, the current first-candidate `spinProjectionCandidateRows` cost is about `0.15s`. These gains overlap, so they should not be multiplied together as if they were independent.

### 1. Prune dummy-vector loops before full summation

This is the highest-value next step.

Estimated gain:

- `1.5x` to `3x` on dummy-heavy candidate-row evaluation in the typical case
- up to about `5x` on the specific 5-spin hot path if most active terms can be rejected before entering their `10`- or `1000`-point dummy sums
- likely `1.3x` to `2x` end-to-end on the full solve if the candidate count stays similar

Strategy:

- extend the current support logic so a term can return `0` before calling `spinProjectionLoopDummyVectors`
- for terms with dummy vectors, compute a conservative support summary over the dummy domain instead of falling back immediately to `All`
- start with the easy case:
  one dummy vector index,
  one output spin,
  and gamma factors whose support can be unioned exactly over the `10` dummy-vector values
- only enter the dummy loop if the current output spin survives that precheck

Why this should help:

- the remaining hot terms are expensive because of `10`- and `1000`-point dummy sums
- avoiding even a fraction of those loops is likely more valuable than any further matrix sparsity cleanup

### 2. Strengthen per-term support from “single output spin” to “single output spin plus dummy summary”

The current term support is exact only when the factor support is already concrete in the candidate and does not depend on dummy vectors.

Estimated gain:

- about `1.1x` to `1.5x` on the current 5-spin case after the term-gating fix
- potentially `2x` or better on cases where dummy dependence currently forces many terms into the generic bucket
- lower value than item 1 on this exact example, but a strong complement to it

Strategy:

- keep the current singleton-support machinery for concrete factors
- add a second layer that unions supports over small unresolved domains, especially dummy vectors in `1..10`
- store that widened support back into the same term-bucketing flow used by `spinProjectionCandidateRows`
- treat this as a refinement of the existing term-gating pass, not as a new generalized subsystem

Why this should help:

- the current term buckets are already the right abstraction
- making those buckets tighter directly shrinks the active-term list per output state

### 3. Exploit antisymmetry in dummy-index loops

Right now a term with `k` dummy vector slots still iterates the full ordered `10^k` dummy tuples, even if those slots only feed one antisymmetrized gamma block.

For example:

- a rank-3 antisymmetrized gamma currently still drives `10^3 = 1000` ordered dummy tuples
- simply forbidding repeated indices cuts that to `10 * 9 * 8 = 720`
- when those three dummy slots are local to that one antisymmetric block, collapsing ordered tuples to increasing combinations cuts it further to `Binomial[10, 3] = 120`

Estimated gain:

- about `1.4x` from just skipping repeated indices on a rank-3 antisymmetric dummy block
- up to about `8.3x` on that block when ordered tuples can be replaced by combinations
- likely `1.1x` to `1.8x` end-to-end on hard cases where a small number of antisymmetric dummy-heavy terms dominate

Strategy:

- inspect each compiled term for dummy vector slots that appear only inside one antisymmetrized gamma chain
- first implement the always-safe step:
  skip repeated dummy indices for those slots
- then implement the stronger step only when safe:
  iterate strictly increasing dummy combinations and attach the permutation sign analytically instead of visiting all ordered tuples
- keep the fallback generic dummy loop unchanged for mixed-use dummy slots that also feed deltas or other factors

Why this should help:

- the current loop in `spinProjectionLoopDummyVectors` is completely structure-blind
- antisymmetry is currently used too late, after the ordered dummy tuple has already been chosen
- this is one of the few remaining places where the combinatorics can shrink by a literal factor of `k!`

### 4. Cache more exact work inside one candidate evaluation

`spinProjectionTermValue` still repeats exact work that is stable for the whole candidate or for the whole output state.

Estimated gain:

- about `1.1x` to `1.4x` on the current 5-spin candidate-row hot path
- occasionally up to `2x` if the same concrete gamma descriptors and scalar factors are being rebuilt many times within one candidate
- mostly additive with engineering convenience, not the first place to look for a large asymptotic win

Strategy:

- cache concrete gamma matrices per descriptor per candidate/output-state context instead of rebuilding the same sparse matrix multiple times
- cache scalar-factor values when the same factor is revisited with the same `(candidate, stateSpin, stateVector, dummy)` inputs
- hoist any candidate-only data out of the inner output-state loop in `spinProjectionCandidateRows`
- keep the cache local to one candidate evaluation so memory stays bounded and invalidation stays trivial

Why this should help:

- the remaining cost is exact symbolic arithmetic, not lookup-table setup
- local memoization is low-risk and does not change solver semantics

### 5. Reduce the number of candidates needed to reach full rank

Even a faster inner loop will still struggle if too many candidate assignments are needed before the row basis reaches full rank.

Estimated gain:

- near-linear in the reduction of candidates needed for full rank
- if the solver can reach rank with half as many candidates, the end-to-end solve is roughly `2x` faster
- a realistic first target is `1.5x` to `3x` end-to-end, but this depends heavily on how redundant the current candidate stream is

Strategy:

- improve `spinProjectionAssignmentIterator` so early candidates are more linearly informative, not just deterministically seeded
- exploit charge-guided structure more aggressively:
  prefer candidates that vary the output-support buckets,
  not just the raw spin charges
- add a cheap pre-score for candidate usefulness based on predicted output support and active-term pattern before computing the full projected LHS
- stop treating all charge-compatible candidates as equally good

Why this should help:

- the solver only needs enough independent rows to solve the coefficient system
- fewer good candidates beats many cheap but redundant candidates

### 6. Only after the above, consider broader structural work

Broader solver rewrites are lower priority than the targeted wins above.

Estimated gain:

- highly uncertain; probably only `1.2x` to `2x` until the narrower bottlenecks above are already addressed
- not the best first investment unless profiling shows the local compiled-path fixes have stopped paying off

Strategy:

- defer multi-output-spin support propagation until single-output-spin plus dummy-summary pruning is exhausted
- defer big refactors of the solver model until there is profiling evidence that the current local structure is the blocker
- avoid building a large new support-analysis framework unless the narrower steps above stop paying off

Why this ordering matters:

- the current bottlenecks are already fairly well localized
- the narrow fixes fit the existing compiled path and are much less risky than a solver rewrite
