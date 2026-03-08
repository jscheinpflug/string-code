# Implement Type-II Flat-Space Bosonization

  ## Summary

  - Replace the placeholder Bosonize in StringCode\OPE`TypeII`FlatSpace`` with a real bosonization pipeline for the free-fermion and spin-field sector.
  - Add the six-boson field heads dH, dHt, expH, expHt, plus the notebook-derived charge basis, cocycle matrix, and vector-basis change-of-basis matrix M.
  - Leave tensor-structure generation unchanged; the new work is the bosonized evaluation layer used after indices are concretized.

  ## Public API and behavior

  - Add public heads dH[i_, n_, z_], dHt[i_, n_, zbar_], expH[q6_List, z_], expHt[q6_List, zbar_] in StringCode\Symbols`TypeII`FlatSpace``.
  - Use q6 = {qPhi, q1, q2, q3, q4, q5}, with the first slot carrying the phi charge.
  - Weights:
      - dH/dHt: 1 + n.
      - expH/expHt: -1/2 qPhi (qPhi + 2) + 1/2 Sum[q_i^2, {i, 2, 6}].
  - Bosonize becomes multilinear and evaluates on single fields and on R[...]. It only reduces when:
      - μ is an integer 1..10,
      - spinor indices are explicit 5-vectors with matching chirality,
      - S/St have empty modes and zero derivative.
  - Otherwise Bosonize stays unevaluated.

  ## Implementation changes

  - In the symbol/Wick layer, add documented private helpers for:
      - chargeDot[q_, p_] = -q[[1]] p[[1]] + Sum[q[[i]] p[[i]], {i, 2, 6}],
      - the cocycle matrix x[i,j] from the notebook,
      - chiralspins, antichiralspins, vectors, and the fixed 10x10 matrix M.
  - Add Wick rules in StringCode\Wick`TypeII`FlatSpace``:
      - Wick[dH[i], dH[j]] and Wick[dHt[i], dHt[j]] use metric diag(-1, 1, 1, 1, 1, 1),
      - SWick[dH, expH] and SWick[dHt, expHt] use the same metric componentwise,
      - MWick[expH, expH] and MWick[expHt, expHt] return cocycle[q, p] (z - w)^chargeDot[q, p],
      - no holo/anti-holo cross contractions.
  - Implement bosonization with a private term representation like <|"coeff", "charge", "expr"|> so normal-order phases are applied termwise after basis expansion.
      - expΦb/expΦf[q, z] -> expH[{q, 0, 0, 0, 0, 0}, z]; anti-holo analogues use expHt.
      - S[{spinVec, chirality}, q, {}, 0, z] -> expH[Join[{q}, spinVec], z]; St uses expHt.
      - ψ[μ_Integer, n_, z] and ψt expand in the 10 vector charges Join[{0}, vectors[[a]]] with coefficients M[[μ, a]]; generate the n derivative by differentiating a
        symbolic exponential and replacing ∂^(k+1) H_i with dH[i, k] or dHt[i, k].
  - Bosonize[R[ops___]] must:
      - bosonize each factor into term lists,
      - expand the term product,
      - multiply by Product[cocycle[charge_i, charge_j], {i < j}] using the original factor order,
      - locally merge same-coordinate exponentials into one expH/expHt with summed charge,
      - return the expanded sum of R[...] expressions.
  - Keep the cocycle/statistics correction local to Bosonize[R[...]]; do not change global NormalOrdering grading rules.
  - Add placeOp support for dH, dHt, expH, expHt in the flat-space operator package so bosonized expressions still transform like other CFT fields.
  - Leave SpinFields.wl as reference-only.

      - Wick[dH, dH], SWick[dH, expH], and MWick[expH, expH],
      - Bosonize on expΦ, S/St, and specific ψ/ψt components.
  - Add a dedicated bosonization regression notebook that reproduces the notebook gamma construction:
      - build SSOPE, AAOPE, SAPairing, ASPairing, RSAPairing, RASPairing,
      - reconstruct GammaRMS/GammaRMA, transform with M, and check the ψ-S OPE coefficients against GammaRS/GammaRA,
      - include the raising/lowering step gamma_μ = gamma_a M^a_μ where needed.
  - Include a small deterministic subset of the associativity and graded-commutation checks from cocycle-tests.wlnb to confirm the cocycle handling in Bosonize[R[...]].

  ## Assumptions

  - The anti-holomorphic exponential head is expHt.
  - This v1 does not support symbolic μ, numeric spinor labels 1..16, nonempty S/St modes, or differentiated spin fields.
  - No tensor-structure or basis-generation rules change.
  - Every new nontrivial helper, including private ones, gets a ::usage immediately above its definition.