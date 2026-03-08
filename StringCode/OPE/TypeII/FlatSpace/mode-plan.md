 # Excited Spin-Field Bosonization via Same-Point Reduction

  ## Summary

  - Claude’s sketch is correct as a one-mode derivation in the charge basis: it explains why the answer is always (polynomial in dH/dHt) * expH/expHt[shifted charge].
  - It is not sufficient as an implementation recipe for this repo, because it does not settle multi-mode contractions, \[Mu]-basis lifting through basisChangeM,
    antiholomorphic mirroring, or how to read concrete mode entries once both slots are numeric.
  - The safest repo-native implementation is to reuse the existing Bosonize[R[...]] path instead of re-implementing Bell-polynomial recursion: reduce an excited spin field
    to a same-point normal-ordered product of descendant \[Psi]/\[Psi]t fields acting on the empty-mode spin ground state, bosonize that, then strip the outer R so the
    result is again a single local field.
  - Keep Bosonize publicly owned where it already is; add these new downvalues in the later-loaded TypeII normal-ordering layer, exactly as the repo already does for
    Bosonize[Ra_ /; RTest[Ra]]. That avoids package cycles.

  ## Implementation Steps

  1. In NormalOrdering\TypeII, add documented private helpers:
      - concreteSpinBosonizationModeQ[entry_] for {mu_Integer, n_Integer?Positive} with 1 <= mu <= 10.
      - spinModeEntryToLocalPsi[entry_, coord_, chirality_] mapping {mu,n} to \[Psi][mu, n - 1, coord] or \[Psi]t[mu, n - 1, coord].
      - unwrapBosonizedLocalProduct[expr_] replacing R[fields___] with Times[fields] after bosonization.
  2. Add Bosonize rules for S/St with explicit spin vectors, der == 0, and nonempty concrete mode lists:
      - Bosonize[S[{spinVec_List, chirality_}, q_?NumericQ, modes_List, 0, z_]]
      - Bosonize[St[{spinVec_List, chirality_}, q_?NumericQ, modes_List, 0, zbar_]]
        Only fire when every mode passes concreteSpinBosonizationModeQ.
  3. For holomorphic S, preserve stored mode order and build:
      - ground = S[{spinVec, chirality}, q, {}, 0, z]
      - psiFields = spinModeEntryToLocalPsi[#, z, "Holo"] & /@ modes
      - result:

  Expand @ unwrapBosonizedLocalProduct @ Bosonize[R @@ Join[psiFields, {ground}]]

  Mirror this for St with \[Psi]t.
  4. Do not touch the existing empty-mode S/St rules or the existing single-field \[Psi]/\[Psi]t bosonization in the symbols layer. The new behavior should be a strict
  extension.
  5. Keep unsupported cases unevaluated:

  - symbolic or ambiguous mode entries,
  - any all-numeric entry not in index-first {mu,n} form,
  - der != 0.

  6. Add ::usage immediately above every new helper definition.

  ## Acceptance Criteria

  - Existing empty-mode S/St, \[Psi]/\[Psi]t, and Bosonize[R[...]] outputs remain unchanged.
  - Bosonize[S/St] with concrete nonempty mode lists returns an expanded sum of plain products of dH/dHt factors times exactly one trailing expH/expHt; no residual Bosonize,
    S, or St.
  - Concrete mode entries are interpreted as {mu, n}. A regression on {{2,1}} must pin that convention.
  - Bosonize[R[...]] consumes the new single-field outputs without any new global cocycle/sign logic.
  - Under normal Needs["StringCode"]; InitStringCode[...]` initialization, Ramond descendants with one or two matter modes bosonize fully.

  ## Test Plan

  - In the TypeII flat-space symbol tests, add exact holomorphic checks for

  sPlus = {{1/2, 1/2, 1/2, 1/2, 1/2}, "chiral"};

  Bosonize[S[sPlus, -1/2, {{1,1}}, 0, z]]
  == -(expH[{-1/2,-1/2,1/2,1/2,1/2,1/2}, z] + expH[{-1/2,3/2,1/2,1/2,1/2,1/2}, z])/Sqrt[2]

  Bosonize[S[sPlus, -1/2, {{1,2}}, 0, z]]
  == (dH[2,0,z] expH[{-1/2,-1/2,1/2,1/2,1/2,1/2}, z] - dH[2,0,z] expH[{-1/2,3/2,1/2,1/2,1/2,1/2}, z])/Sqrt[2]

  Bosonize[S[sPlus, -1/2, {{1,1},{2,1}}, 0, z]]
  == (expH[{-1/2,-1/2,-1/2,1/2,1/2,1/2}, z] + expH[{-1/2,-1/2,3/2,1/2,1/2,1/2}, z]
     + expH[{-1/2,3/2,-1/2,1/2,1/2,1/2}, z] + expH[{-1/2,3/2,3/2,1/2,1/2,1/2}, z])/2

  Bosonize[S[sPlus, -1/2, {{1,1},{1,2}}, 0, z]]
  == -dH[2,0,z] expH[{-1/2,-3/2,1/2,1/2,1/2,1/2}, z]/2 + dH[2,0,z] expH[{-1/2,5/2,1/2,1/2,1/2,1/2}, z]/2

  - Add antiholomorphic mirrors of the {{1,1}} and {{1,2}} cases with St, dHt, and expHt.
  - Add convention/unsupported tests:
      - Bosonize[S[sPlus, -1/2, {{2,1}}, 0, z]] matches the mu=2, n=1 oracle.
      - Head[Bosonize[S[sPlus, -1/2, {{mu,1}}, 0, z]]] === Bosonize
      - Head[Bosonize[S[sPlus, -1/2, {{1,1}}, 1, z]]] === Bosonize
  - In the TypeII normal-ordering tests, add oracle-equivalence regressions:

  Bosonize[S[sPlus, -1/2, {{1,1}}, 0, z]]
  == Expand[(Bosonize[R[\[Psi][1,0,z], S[sPlus, -1/2, {}, 0, z]]] /. R[a___] :> Times[a])]
  == Expand[(Bosonize[R[\[Psi][1,1,z], S[sPlus, -1/2, {}, 0, z]]] /. R[a___] :> Times[a])]
  Bosonize[S[sPlus, -1/2, {{1,1},{2,1}}, 0, z]]
  == Expand[(Bosonize[R[\[Psi][1,0,z], \[Psi][2,0,z], S[sPlus, -1/2, {}, 0, z]]] /. R[a___] :> Times[a])]

  and the St/\[Psi]t mirrors.

  - Add one smoke test on a Ramond weight-1 descendant operator produced by the existing basis-generation path: after concretizing indices, bosonization must be free of
    _Bosonize | _S | _St.

  ## Assumptions

  - Concrete spin-mode bosonization support is only for the index-first form {mu_Integer, n_Integer?Positive}, because that is what psiModeToSpinMode emits.
  - Spin-field der remains out of scope for this feature.
  - The existing Bosonize[R[...]] cocycle/sign conventions are the repo’s source of truth and should be reused, not rederived.

   # Contour-Defined Bosonization for Excited Spin Fields

  ## Summary

  - Replace the invalid same-point R[ψ, S] idea with actual mode action by contour-coefficient extraction.
  - Use the ordered multi-action kernel as the mathematical spec, but implement it as a sequential one-mode contour action. This is equivalent, and it matches how the repo
    already bosonizes β/γ modes.
  - Keep ground-state Bosonize[S/St[..., {}, 0, ...]] where it is. Add the excited-spin-field Bosonize downvalues in StringCode/BasisGeneration/TypeII/FlatSpace/FlatSpace.m,
    because that package already has the projection machinery and is loaded after OPE/Taylor.

  ## Implementation Changes

  - In StringCode/BasisGeneration/TypeII/FlatSpace/FlatSpace.m:
      - Reuse the existing holomorphic contour-projection path and add the missing antiholomorphic analogs: rescaleAntiHoloFieldByParameter,
        rescaleAntiHoloExpressionByParameter, projectScaledExpressionAtAntiHoloPower, extractAntiHoloPowerCoefficient.
      - Add documented helpers for Ramond spin-mode bosonization:
          - concreteSpinBosonizationModeQ accepts only fully concrete mode entries in the unambiguous form {mu_Integer, n_Integer?NonNegative} with 1 <= mu <= 10.
          - spinModeInsertionField maps one mode entry to the local insertion ψ[mu, 0, ...] or ψt[mu, 0, ...].
          - spinModeExtractionPower returns n - 1/2.
          - applyOneSpinModeBosonizationHolo and applyOneSpinModeBosonizationAntiHolo do one contour action:
              1. bosonize the local insertion with existing Bosonize[R[ψ/ψt[mu,0,...]]];
              2. take the OPE with the current bosonized state at the origin;
              3. project to the required contour power;
              4. set the dummy insertion coordinate to 1.
          - unwrapSinglePointBosonizedField converts the final same-point bosonic R[...] into plain products, so single-field Bosonize stays consistent with existing ψ
            output.
          - restoreBosonizedHoloCoordinate and restoreBosonizedAntiHoloCoordinate move the origin result back to the requested field coordinate.
      - Add new Bosonize downvalues for S/St with explicit spin vectors, der == 0, and nonempty concrete mode lists. The algorithm is:
          1. bosonize the empty-mode ground state at the origin;
          2. fold the one-mode contour action over the stored canonical mode list in order;
          3. expand, unwrap the final bosonic R, and restore the user’s coordinate.
      - Leave unsupported cases unevaluated:
          - symbolic mode entries,
          - fully numeric entries in the ambiguous {n, mu} order,
          - half-integer symbolic mode conventions already used elsewhere in generic algebra tests,
          - der != 0.
  - In StringCode/Taylor/TypeII/FlatSpace/FlatSpace.m:
      - Extend isAtPointHolo/AntiHolo and addHoloDerivatives/addAntiHoloDerivatives to dH, dHt, expH, expHt.
      - For dH/dHt, Taylor shifting just increments the derivative index.
      - For expH/expHt, use the existing bosonizedExponentialDerivative[...] helper to generate the Bell-polynomial prefactor at each Taylor order. Do not introduce a second
        derivative engine.
  - Do not change Bosonize[Ra_ /; RTest[Ra]] in NormalOrdering\TypeII; it should keep working once factor-level Bosonize[S/St] evaluates on excited spin fields.

  ## Test Plan

  - Add Taylor regressions in the TypeII flat-space Taylor tests:
      - TaylorAtOrderHolo[R[dH[2,0,z]], 1, 0] gives z R[dH[2,1,0]].
      - TaylorAtOrderHolo[R[expH[{0,1,0,0,0,0}, z]], 1, 0] gives the first derivative polynomial times expH[{0,1,0,0,0,0},0].
      - TaylorAtOrderHolo at order 2 on that same expH matches the second Bell-polynomial combination.
      - Add the dHt/expHt mirrors.
  - Add exact one-mode excited-spin bosonization regressions in the TypeII flat-space symbol tests for sPlus = {{1/2,1/2,1/2,1/2,1/2}, "chiral"}:
      - Bosonize[S[sPlus, -1/2, {{1,0}}, 0, z]] matches the aligned zero-mode exponential with the existing branch/cocycle phase.
      - Bosonize[S[sPlus, -1/2, {{1,1}}, 0, z]] matches the expected sum of one pure exponential term and one dH[2,0,z] * expH[...] term, with the exact phases fixed by the
        current ψ-S OPE convention.
      - Add the St/dHt/expHt mirrors.
  - Add multi-mode contour-definition tests in the TypeII flat-space symbol or normal-ordering tests:
      - Define a notebook-local oracle that applies modes by repeated OPE[Bosonize[R[ψ/ψt[mu,0,ε x]]], current] plus contour projection, without using the new Bosonize[S/St]
        downvalue.
      - Compare Bosonize[S[sPlus, -1/2, {{1,1},{2,1}}, 0, z]] against that oracle.
      - Compare Bosonize[S[sPlus, -1/2, {{1,1},{1,2}}, 0, z]] against that oracle to force contractions with already-generated dH factors.
      - Add antiholomorphic mirrors.
      - Head[Bosonize[S[sPlus, -1/2, {{1/2, mu}}, 0, z]]] === Bosonize.
  - Add one integration smoke test in the OPE flat-space path:
      - On the first excited Ramond level, a deterministic OPEProjected run that previously produced outgoing Bosonize[S[..., nonemptyModes, ...]] now has no residual
        _Bosonize | _S | _St in the concretized outgoing operators.

  ## Assumptions And Defaults

  - Concrete excited-spin bosonization support is for {mu, n} with mu numeric and n a nonnegative integer. This matches contour-mode semantics and avoids ambiguity when both
    slots are numeric.
  - The closed-form ordered multi-action kernel is the correctness oracle, but code should use sequential contour extraction because it is equivalent and fits the repo’s
    existing architecture.
  - Generic symbolic spin-mode algebra and half-integer mode-list tests stay untouched; this feature only extends Bosonize, not the underlying symbolic S/St canonicalization
    rules.
  - der != 0 stays out of scope for this change.