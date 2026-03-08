  # Minimal Bosonization Layer for Type-II Flat Space

  ## Summary

  - Implement the bosonized free-field sector with the least new structure possible.
  - Put almost all field-level bosonization data and helpers in Symbols\TypeII`FlatSpace; keep Wick contractions in `Wick\`TypeII\`FlatSpace; use NormalOrdering\TypeII``
    only for the normal-ordered bosonization mechanics that genuinely belong there.
  - Keep StringCode\OPE`TypeII`FlatSpace`as a thin public entry point forBosonize`, not as the place where the real logic lives.

  ## Implementation Changes

  - In Symbols\TypeII`FlatSpace`` add dH, dHt, expH, expHt plus the shared-private tables chiralspins, antichiralspins, vectors, and basisChangeM.
  - Use q6 = {qPhi, q1, q2, q3, q4, q5} with the first slot the phi direction and the remaining five the matter bosons.
  - Field metadata:
      - dH/dHt: simple indexed bosons, collapsable, same weight as dX, same-chirality pairings only.
      - expH/expHt: chiral composite bosons mirroring expXHolo/expXAntiHolo, with weight -qPhi (qPhi + 2)/2 + 1/2 Sum[q_i^2, {i,2,6}].
  - In the same Symbols package add the single-field bosonization helpers:
      - expΦb/expΦf -> expH[{q,0,0,0,0,0}], anti-holo analogously.
      - S/St with explicit spin 5-vectors, empty modes, zero derivative -> expH/expHt[Join[{q}, spinVec], ...].
      - ψ/ψt with concrete μ=1..10 -> basisChangeM expansion into the vector-charge basis Join[{0}, vectors[[a]]].
      - For higher derivatives of ψ/ψt, differentiate the symbolic exponential form and replace derivatives of H_i by dH[i,k] or dHt[i,k].
  - In Wick\TypeII`FlatSpace`` add hMetric, chargeDot, the notebook cocycle matrix x[i,j], and cocycle.
  - Add Wick rules:
      - Wick[dH,dH] and Wick[dHt,dHt] with the sign convention that gives -1/(z-w)^2 in the phi direction and +1/(z-w)^2 in matter directions.
      - SWick[dH,expH] and SWick[dHt,expHt] with direct metric coefficients.
      - MWick[expH,expH] := cocycle[q,p] (z-w)^chargeDot[q,p] and similarly for expHt.
      - No holo/anti-holo cross contractions and no BranchPower.
  - Put the normal-ordered bosonization pass in the existing Type-II normal-ordering layer, reusing R semantics instead of creating a second normal-ordering mechanism:
      - expand bosonized factor terms,
      - multiply by Product[cocycle[q_i,q_j], {i<j}] using original factor order,
      - merge same-coordinate same-chirality exponentials by adding their charge vectors,
      - return the expanded sum of R[...].
  - Keep boilerplate low:
      - no new package files,
      - no operator-placement or TeX-conversion support unless an existing test path actually breaks without it,
      - no generic abstraction layer for spin bosons beyond the helpers needed for this task.
  - Update the flat-space random concretization path so symbolic spinor indices are replaced by explicit 5-vectors of the correct chirality, not integers 1..16, before
  ## Verification
  - Add low-level regression checks for Wick[dH,dH], SWick[dH,expH], MWick[expH,expH], and single-field Bosonize on expΦ, S/St, and concrete ψ/ψt.
  - Add Bosonize[R[...]] checks for cocycle insertion, same-coordinate exponential merging, and absence of leftover unevaluated Bosonize after concretization.
  - Reconstruct only the mixed-chirality pairing matrices based on RSAPairing and RASPairing; treat these as the canonical new SA pairings.
  - Do not implement the old SAPairing / ASPairing workflow.
  - Use SSOPE, AAOPE, RSAPairing, and RASPairing to extract gamma matrices, transform with basisChangeM, and verify the ψ-S OPE coefficients including the gamma_μ = gamma_a
    M^a_μ conversion.
  - Add a few deterministic graded-sign and associativity spot checks from the notebook logic, and one sanity check that supported GSO-projected test cases only produce
    integral exponents.

  ## Assumptions

  - Supported v1 inputs remain concrete μ=1..10, numeric picture charge, explicit chirality-compatible spin 5-vectors, and S/St with empty modes and zero derivative.
  - The public Bosonize symbol stays where it already exists, but its implementation should be mostly delegated to Symbols and NormalOrdering helpers.
  - Every new nontrivial helper, including shared-private ones, gets a ::usage immediately above its definition.


    # TypeII Flat-Space Bosonization with Bosonize Owned by Symbols

  ## Summary

  - Move the public Bosonize symbol into StringCode\Symbols`TypeII`FlatSpace`` and remove the duplicate placeholder declaration from the OPE flat-space package.
  - Implement the six-boson bosonization layer with ordinary Mathematica powers only: no BranchPower wrapper in new rules or tests.
  - Keep field/basis/cocycle data in the Symbols flat-space layer, put Bosonize[R[...]] in the TypeII normal-ordering layer, and keep the OPE flat-space module as a consumer
    of the symbol rather than its owner.

  ## Key Changes

  - In StringCode\Symbols`TypeII`FlatSpace``:
      - Add public heads dH, dHt, expH, expHt, and public Bosonize.
      - Define dH[i_, n_, z_], dHt[i_, n_, zbar_], expH[q6_List, z_], expHt[q6_List, zbar_] with TypeII-flat-space metadata matching the existing dX/expXHolo patterns.
      - Use q6 = {qPhi, q1, q2, q3, q4, q5} and weights 1 + n for dH/dHt, -qPhi (qPhi + 2)/2 + 1/2 Sum[q_i^2, {i, 2, 6}] for expH/expHt.
      - Add documented shared-private helpers for chiralspins, antichiralspins, vectors, basisChangeM, hMetric, chargeDot, x, and cocycle so both Wick and bosonization use
        the same data with no load cycle.
      - Implement single-field Bosonize rules only for supported v1 inputs:
          - exp\[Phi]b/f and exp\[Phi]tb/tf map to expH/expHt with only the qPhi slot nonzero.
          - S/St reduce only for explicit 5-vectors of the declared chirality, empty modes, zero derivative.
          - \[Psi]/\[Psi]t reduce only for concrete mu_Integer /; 1 <= mu <= 10; expand through basisChangeM into the vector basis.
          - For n > 0, build the differentiated bosonized fermion by differentiating a temporary exponential Exp[Sum[q_i H_i[x], {i,1,6}]], replacing Derivative[k_][H_i][x]
            with dH[i, k - 1, x] or dHt, then replacing the exponential with expH/expHt.
      - Leave Bosonize unevaluated for unsupported inputs.
  - In StringCode\NormalOrdering`TypeII``:
      - Add Needs["StringCodeSymbolsTypeIIFlatSpace"].
      - Define the Bosonize[Ra_ /; RTest[Ra]] overload on the Symbols-owned symbol.
      - Bosonize each factor into a term list carrying coefficient, net six-charge, chirality, coordinate, derivative factors, and one trailing exponential head.
      - For each tuple of factor terms:
          - multiply coefficients,
          - multiply by Product[cocycle[q_i, q_j], {i, j} with i < j in original factor order],
          - merge same-coordinate same-chirality exponentials by charge addition,
          - keep derivative factors separate,
          - rebuild the result as an expanded sum of R[...].
      - Do not modify global regcomm, oddBosChirFieldQ, or generic bosExpRules; the statistics correction stays local to Bosonize[R[...]].
  - In StringCode\Wick`TypeII`FlatSpace`` and the flat-space operator/OPE consumers:
      - Add Wick/SWick/MWick rules for dH/dHt/expH/expHt using the shared Symbols helpers.
      - Use plain powers:
          - Wick[dH, dH] and Wick[dHt, dHt] from hMetric = DiagonalMatrix[{-1, 1, 1, 1, 1, 1}],
          - SWick[dH, expH] and SWick[dHt, expHt] with direct metric coefficients,
          - MWick[expH[q, z], expH[p, w]] := cocycle[q, p] (z - w)^chargeDot[q, p], similarly for expHt.
      - Add placeOp support for the new heads in the TypeII flat-space operator module.
      - Remove the Bosonize::usage declaration from the OPE flat-space package and keep its existing randomized wrappers pointing at the Symbols-owned symbol.

  ## Test Plan

      - Bosonize on exp\[Phi], S/St, and concrete \[Psi]/\[Psi]t,
  - Extend the existing TypeII flat-space OPE notebook with:
      - Wick[dH,dH], SWick[dH,expH], MWick[expH,expH],
      - Bosonize[R[...]] cocycle insertion and same-point exponential merging,
      - gamma reconstruction from the notebook formulas using ordinary powers and the same M conversion,
      - a small deterministic subset of associativity and graded-sign checks from cocycle-tests.wlnb.
  - Update the current placeholder Bosonize expectations in the flat-space OPE tests so they assert actual bosonized output instead of just the presence of an unevaluated
    wrapper.

  ## Assumptions

  - Bosonize is publicly owned by StringCode\Symbols`TypeII`FlatSpace``; no second public Bosonize symbol remains in OPE.
  - v1 support is limited to concrete mu = 1..10, numeric picture charge, explicit 5-vector spin labels, and S/St with empty modes and zero derivative.
  - Fractional singularities use ordinary Mathematica Power; no BranchPower abstraction is kept.
  - Every new nontrivial helper, including shared-private ones, gets a ::usage line immediately above its definition.