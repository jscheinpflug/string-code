 # Restore Mixed Cocycles Only When Forming Normal-Ordered Products

  ## Summary

  Keep expH and expHt commuting as already-created bosonic exponentials. Do not add any cocycle-dependent swap phase to R sorting.

  Restore the mixed charge cocycle only at the moments a normal-ordered product is formed:

  - in Bosonize[R[...]] for same-point ordered products,
  - in same-sector MWick[...] where the OPE coefficient multiplies a normal-ordered product.

  Fix and validate the mixed rule by demanding associativity of OPE on genuinely composite bosonized operators with RLength > 1.

  Ramond picture convention is locked:

  - never use half-integer expΦ* factors in the implementation or tests,
  - half-integer picture is carried by the charge label on S / St.

  ## Key Changes

  - In TypeII.m:
      - Restore mixed-sector pairs in bosonizedCocycleFactor, using the existing cocycle[q,p] for ordered charge pairs inside Bosonize[R[...]].
      - Leave R sorting unchanged so expH and expHt commute once they already exist.
      - Do not add any bosonized left/right exchange rule to canonicalization.
  - In NormalOrdering.m:
      - Make no bosonized swap-phase changes.
      - Keep canonicalization purely bosonic for expH / expHt.
  - In tests and derived OPE checks:
      - Replace every half-integer expΦf / expΦtf usage with the corresponding S / St carrying that picture in its second argument.
      - For Ramond-sector probes, use S[..., -1/2, ...], St[..., -1/2, ...], S[..., 1/2, ...], St[..., -3/2, ...], etc., and never split those into expΦ times a zero-picture
        spin field.
      - Keep same-sector MWick[expH,expH] / MWick[expHt,expHt] unchanged.

  ## Test Plan

  - In the TypeII normal-ordering tests:
      - Add explicit checks that R[expH[q,z], expHt[p,zb]] canonicalizes with no extra phase.
      - Add a regression showing that mixed factorwise bosonization is not the intended convention.
      - Add deterministic associativity checks on bosonized composite triples with at least one insertion of RLength > 1.
      - Use concrete bosonized composites built from ψ/ψt, S/St, ψ-S, and ψt-St.
      - Keep direct S-S, St-St, ψ-S, and ψt-St bosonized OPE probes, all written with spin-field picture labels and no half-integer expΦ.
  - In SpinField-Cocycle.test.wlnb:
      - Extend the deterministic associativity pool to composite bosonized operators, not just single expH[...] states.
      - Require a fixed set of nontrivial RLength > 1 triples.
      - Keep the gamma/Lorentz-covariance checks, but rewrite any half-integer expΦ formulations into the equivalent S/St picture-label convention.

  ## Assumptions

  - “Exponentials commute” means no cocycle-dependent swap phase is attached to already-created expH / expHt in R.
  - “Only use cocycles when creating a normal-ordered product” includes Bosonize[R[...]] and same-sector MWick, but not R sorting of existing exponentials.
  - Half-integer picture belongs on S / St, not on standalone expΦ* factors, and all new or updated tests will follow that convention.