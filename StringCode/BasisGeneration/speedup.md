BasisGeneration Performance Plan With Measured Wins

  Summary

  - I tested improvements in a fresh kernel without editing the repo, by wrapping the current internal `Private`` conversion helpers in scratch code and benchmarking against
    the current operator path.
  - One improvement is already proven safe on the cases I checked: memoizing repeated sub-conversions inside holomorphic operator assembly. A second improvement is also
    fast, but I only proved it correct on the q=0 hot path so far, not universally.
  - Based on the measurements, the implementation order should be: ship sub-conversion caching first, then add a guarded operator-term shortcut, then revisit closed-string
    streaming only after exact-equivalence checks pass.

  Improvements And Proof

  - Sub-conversion caching inside holomorphic operator assembly: cache ghostModesToOperatorFields, superghostExpressionAndFinalPicture, and
    buildMatterOperatorFromModesAtPicture by their actual subsector inputs instead of recomputing them per full basis state.
  - This is justified because the hot bases repeat subsectors heavily. Example counts from the current basis:
      - w=4, q=-1: 345 full states but only 32 distinct bc subsectors, 69 distinct superghost subsectors, and 147 distinct matter subsectors.
      - w=4, q=0: 258 full states but only 28 distinct bc subsectors, 54 distinct superghost subsectors, and 112 distinct matter subsectors.
  - Proven benchmark results for the cache-only prototype:
      - Holomorphic w=3, q=-1: 8.63s -> 4.37s, about 1.98x, exact same output.
      - Holomorphic w=3, q=0: 3.04s -> 2.00s, about 1.52x, exact same output.
      - Holomorphic w=4, q=0: 9.06s -> 4.40s, about 2.06x, exact same output.
      - Holomorphic w=4, q=-1: current path timed out at 20s, cache-only prototype finished in 12.48s.
  - Guarded operator-term shortcut: avoid the full Expand -> split additive terms -> extract R terms path when a converted expression is already a standalone R[...] or a
    scalar-times-R[...] term.
  - Proven benchmark results for the cache-plus-shortcut prototype on the q=0 branch:
      - Holomorphic w=3, q=0: 1.74s -> 0.39s, about 4.5x, exact same output.
      - Holomorphic w=4, q=0: 6.18s -> 2.66s, about 2.3x, exact same output.
  - The same shortcut is not yet correctness-proven for all q=-1 expressions. It is fast there too (w=3, q=-1: 5.92s -> 1.55s), but my scratch collector did not yet
    reproduce exact output on every term shape, so this part must be shipped behind a structural guard only after the mismatch is resolved.
  - Closed-string reuse of the same caches is strongly promising but not yet proven safe. A scratch closed-string cache prototype improved generateBasis[2,0,

  Implementation Order

  - Implement sub-conversion caching first in FlatSpace.m, inside the existing holomorphic and antiholomorphic operator assembly path. This is the safest change and already
    has exact-output proof on multiple cases.
  - After that, tighten the shared operator collector in BasisGeneration.m so it short-circuits simple R[...] and scalar-times-R[...] expressions. Only use the shortcut when
    the expression shape is proven equivalent to the current extractor; otherwise fall back to the current expansion path.
  - Only then touch closed-string operator collection. Reuse the already-proven holomorphic/antiholomorphic caches first; do not ship any closed-string streaming shortcut
    until it passes exact set-equality against the current output on low-weight cases.

  Test Plan

  - Re-run FlatSpace.test.wlnb, especially operator-output tests 21-34.
  - Re-run TypeII.test.wlnb and PartitionFunction.test.wlnb.
  - Re-run the same fresh-kernel timing matrix used above and require, at minimum, the proven cache-only wins to survive in the real codebase before attempting the more
    aggressive collector or closed-string changes.

  Assumptions

  - No public API or option changes.
  - Only improvements with exact output equivalence should land in phase 1.
  - Any new helper must follow the repo rule: ::usage immediately above its definition, with no added module/package boilerplate.