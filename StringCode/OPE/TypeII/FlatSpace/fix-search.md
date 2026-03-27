Support-driven compiled probe search

Replace the compiled probe iterator with one generic witness search over the existing compiled term factors. Candidate generation must come from actual sparse gamma support plus equality constraints, not from bosonized charge heuristics.

Rules:

- Remove the compiled-path `ChargeGuidedQ` branch entirely.
- Keep the current compiled term format; do not add a second IR.
- Allow free spins, free vectors, output spins, output vectors, and dummy vectors as variables in the witness search.
- Use only the existing factor kinds:
  - delta on vector slots
  - identity on spin slots
  - gamma support from concrete sparse matrices
- Keep `spinProjectionCandidateRows` and term evaluation unchanged in this pass.
- Delete compiled-only charge-guided model fields once unused.

Search algorithm:

1. Flatten the compiled families into a term pool.
2. For one chosen `{family, term}`, build a partial assignment for:
   - free spins
   - free vectors
   - output spins
   - output vectors
   - dummy vectors
3. Repeatedly pick the unresolved factor with the fewest concrete choices.
4. Extend the assignment from actual factor support:
   - delta: enforce equal vector values
   - identity: enforce equal spin values
   - gamma: resolve concrete sparse support and sample only nonzero spin pairs
5. Backtrack on contradictions.
6. When all factor constraints are satisfied, fill any unused free slots by seeded order and return only `{freeSpins, freeVectors}`.
7. Deduplicate yielded candidates in the iterator.

Acceptance:

- No compiled-path branch keyed to ground-spin-only or no-vector-only regimes.
- Candidate generation uses actual sparse factor support.
- The 5-spin compiled search beats the current `11/16` plateau.
- Existing projected-spin symbolic regressions remain unchanged.
