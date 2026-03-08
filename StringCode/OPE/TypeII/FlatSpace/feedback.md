Implement Bosonization of Free Fermion Sector (Type-II Flat Space)

 Context

 The flat-space OPE code needs to compute OPEs involving spin fields (S, St) alongside fermions (psi, psit) and picture-changing exponentials (expPhi). The strategy is
 bosonization: rewrite all these fields as free bosons (dH, expH) so that OPEWick can evaluate the OPE via standard Wick contractions. Cocycle phases encode the original
 fermionic statistics. This task implements the bosonization layer and new boson fields; OPE pipeline integration (routing via hasSpinFieldQ) is out of scope.

 ---
 1. New field heads: dH, dHt, expH, expHt

 Where: StringCode/Symbols/TypeII/FlatSpace/FlatSpace.m

 dH / dHt (derivative bosons)

 - Arguments: dH[i, n, z], dHt[i, n, zbar] where i = 1..6, n = mode/derivative offset
 - i=1 is the phi (picture) direction; i=2..6 are SO(10) matter bosons H_1..H_5
 - DefineField properties: mirror dX — Boson, Simple, Indexed, Collapsable, Holomorphic (resp. AntiHolomorphic)
 - "PairsWith" -> {dH, expH} (resp. {dHt, expHt})
 - Weight: 1 + n (same as dX)

 expH / expHt (exponential bosons)

 - Arguments: expH[q6_List, z], expHt[q6_List, zbar] where q6 = {qPhi, q1, q2, q3, q4, q5}
 - DefineField properties: Composite, not Simple, Factorizable (mirror expXHolo)
 - "PairsWith" -> {dH, expH} (resp. {dHt, expHt})
 - Weight: -qPhi(qPhi+2)/2 + (1/2) Sum[q_i^2, {i,2,6}]
   - First term is phi-ghost background-charge weight; remaining terms are matter boson weight
 - No holo/anti-holo cross-pairing

 Data tables (also in Symbols/TypeII/FlatSpace/FlatSpace.m)

 - chiralspins: 16 five-vectors (even number of minus signs in {+/-1/2}^5)
 - antichiralspins = -chiralspins
 - vectors: 10 five-vectors from Join[Permutations[{1,0,0,0,0}], Permutations[{-1,0,0,0,0}]]
 - basisChangeM: 10x10 matrix transforming vector-basis index a -> spacetime index mu
 Rows 1-5:  1/Sqrt[2] at (i,i) and (i,i+5)
 Rows 6-10: I/Sqrt[2] at (i,i-5) and -I/Sqrt[2] at (i,i)

 ---
 2. Wick contraction rules

 Where: StringCode/Wick/TypeII/FlatSpace/FlatSpace.m

 Propagator conventions

 The H-boson propagator is <H_i(z) H_j(w)> = hMetric[[i,j]] ln(z-w), where:

 hMetric = DiagonalMatrix[{-1, 1, 1, 1, 1, 1}] (phi direction = -1, matter = +1)

 This gives:
 - <∂φ ∂φ> = -1/(z-w)^2 (matches existing dΦ convention)
 - <∂H_i ∂H_j> = +δ_{ij}/(z-w)^2 for i,j >= 2 (matter bosons, positive)

 The charge dot product (= LDot from notebook):

 chargeDot[q_, p_] := Sum[hMetric[[i,i]] q[[i]] p[[i]], {i, 1, 6}]

 Cocycle (also in Wick module)

 Antisymmetric matrix x[i,j] from notebook:
 x[i_,i_] := 0
 x[i_,j_] /; i<j := -x[j,i]
 x[i_,j_] /; i>j && j!=1 := (-1)^(i j)/2
 x[i_,1] /; i>1 := 1/2

 cocycle[a_List, b_List] := Exp[I Pi Sum[x[i,j] a[[i]] b[[j]], {i,1,6}, {j,1,6}]]

 Contraction rules

 Important sign: The Wick base pattern D[-1/(zd-w)^2, ...] evaluates to -1/(z-w)^2 at n=m=0. Since the actual contraction is hMetric[[i,j]]/(z-w)^2, we need a factor of
 -hMetric to compensate the base sign.

 Wick[dH[i_, n_, z_], dH[j_, m_, w_]] :=
   -hMetric[[i,j]] (-1)^m D[-1/(zd-w)^2, {zd, n+m}] /. zd->z
   (* phi: -(-1)(-1/(z-w)^2) = -1/(z-w)^2  ✓ *)
   (* matter: -(+1)(-1/(z-w)^2) = +1/(z-w)^2  ✓ *)

 Wick[dHt[i_, n_, z_], dHt[j_, m_, w_]] :=
   -hMetric[[i,j]] (-1)^m D[-1/(zd-w)^2, {zd, n+m}] /. zd->z

 SWick uses the propagator coefficient directly (no sign flip needed):
 SWick[dH[i_, n_, z_], expH[q_, w_]] :=
   hMetric[[i,i]] q[[i]] D[1/(zd-w), {zd, n}] /. zd->z
   (* = ∂_z <H_i(z), q_j H_j(w)> = hMetric[[i,i]] q_i / (z-w) *)

 SWick[dHt[i_, n_, z_], expHt[q_, w_]] :=
   hMetric[[i,i]] q[[i]] D[1/(zd-w), {zd, n}] /. zd->z

 MWick uses BranchPower (critical for half-integer exponents in spin-spin OPEs):
 MWick[expH[q_, z_], expH[p_, w_]] :=
   cocycle[q, p] BranchPower[z-w, chargeDot[q, p]]

 MWick[expHt[q_, z_], expHt[p_, w_]] :=
   cocycle[q, p] BranchPower[z-w, chargeDot[q, p]]
 No cross holo/anti-holo contractions.

 ---
 3. Bosonize function

 Where: Split across Symbols/TypeII/FlatSpace/FlatSpace.m (single-field rules) and NormalOrdering/ (R-product rule).

 Preconditions (Bosonize stays unevaluated unless met)

 - mu is Integer 1..10
 - spinor index alpha is an explicit 5-vector matching chirality
 - S/St have empty modes {} and zero derivative
 - picture charge q is numeric

 Single-field bosonization rules

 expPhi bosonic/fermionic:
 Bosonize[expPhib[q_, z_]] := expH[{q, 0, 0, 0, 0, 0}, z]
 Bosonize[expPhif[q_, z_]] := expH[{q, 0, 0, 0, 0, 0}, z]
 (Distinction between b/f is absorbed by cocycles in normal-ordered products.)

 Anti-holo: expPhibt/expPhift -> expHt[{q, 0,0,0,0,0}, zbar]

 Spin fields:
 Bosonize[S[{spinVec_List, chirality_}, q_, {}, 0, z_]] :=
   expH[Join[{q}, spinVec], z]

 Bosonize[St[{spinVec_List, chirality_}, q_, {}, 0, zbar_]] :=
   expHt[Join[{q}, spinVec], zbar]
 Here spinVec is already an explicit 5-vector (element of chiralspins or antichiralspins).

 Fermion psi (key: change-of-basis matrix M):
 Bosonize[psi[mu_Integer, n_, z_]] :=
   Sum[basisChangeM[[mu, a]] bosonizedPsiComponent[a, n, z], {a, 1, 10}]
 where bosonizedPsiComponent[a, n, z] generates the n-th mode of bosonized psi^a:
 - For n=0: expH[Join[{0}, vectors[[a]]], z]
 - For n>0: differentiate symbolic Exp[i H(z)] n times, replacing d^(k+1) H_i -> dH[i, k, z] and Exp -> expH, yielding a sum of terms each being a product of dH factors times
  an expH. E.g. psi^a with n=1 gives i * vectors[[a,j]] * dH[j, 0, z] * expH[Join[{0}, vectors[[a]]], z] (summed over j with nonzero charge).

 Anti-holo: psit[mu, n, zbar] uses basisChangeM, dHt, expHt.

 Normal-ordered product bosonization

 Bosonize[Ra_ /; RTest[Ra]] :=
 1. Bosonize each factor of R[op1, op2, ...] individually into a list of terms. Each term is <|"coeff" -> c, "charges" -> q6List, "expr" -> product_of_dH_and_expH|>.
 2. Form the outer product of all factor term-lists.
 3. For each combined term, multiply by Product[cocycle[charge_i, charge_j], {i < j}] where i,j index the original factor positions (not individual dH/expH pieces).
 4. Merge expH factors at the same coordinate into a single expH with summed charge vector.
 5. Wrap result in R[...] and return expanded sum.

 The cocycle product accounts for the reordering statistics when going from the fermionic normal-ordered product to the bosonic one.

 ---
 4. Operator support

 Where: StringCode/Operators/Operators.m (or the FlatSpace operator submodule)

 Add placeOp rules:
 placeOp[coordHol_, coordAntiHol_][dH[i_, n_, z_]] := dH[i, n, coordHol[z]]
 placeOp[coordHol_, coordAntiHol_][dHt[i_, n_, z_]] := dHt[i, n, coordAntiHol[z]]
 placeOp[coordHol_, coordAntiHol_][expH[q_, z_]] := expH[q, coordHol[z]]
 placeOp[coordHol_, coordAntiHol_][expHt[q_, z_]] := expHt[q, coordAntiHol[z]]

 ---
 5. Verification

 Create a test notebook (e.g. bosonization-tests.wlnb) that:

 5a. Unit checks

 - Wick contractions: Wick[dH[i,0,z], dH[j,0,w]] gives hMetric[[i,j]]/(z-w)^2
 - SWick: SWick[dH[i,0,z], expH[q,w]] gives hMetric[[i,i]] q[[i]] / (z-w)
 - MWick: MWick[expH[q,z], expH[p,w]] gives cocycle[q,p] BranchPower[z-w, chargeDot[q,p]]
 - Bosonize on individual fields: Bosonize[S[...]], Bosonize[psi[mu, 0, z]]

 5b. Gamma matrix reconstruction (main goal)

 1. Define Spic[q, spin, z] = R[expPhif[q, z], S[{spin, chirality}, 0, {}, 0, z]] (as in cocycle-tests.wlnb)
 2. Bosonize to get R[expH[{q, spin...}, z]] (charges merge)
 3. Compute SSOPE, AAOPE: OPEWick on 16x16 tables of bosonized chiral-chiral and antichiral-antichiral spin pairs
 4. Extract SAPairing, ASPairing from chiral-antichiral OPEs at leading singularity
 5. Build gamma matrices in vector basis: gammaMS[a] = Sqrt[2] * Coefficient[SSOPE, R[Spic[-1, vectors[[a]], 0]]] . Inverse[SAPairing]
 6. Transform to spacetime basis: gammaS[mu] = Sum[basisChangeM[[mu,a]] gammaMS[a], {a,1,10}]
 7. Verify Clifford algebra: gammaS[mu].gammaA[nu] + gammaA[nu].gammaS[mu] == 2 eta[[mu,nu]] IdentityMatrix[16]
 8. Include the index-raising subtlety: gamma_mu = gamma_a M^a_mu (i.e., use Inverse[Transpose[M]] if M raises, matching task.md)

 5c. Associativity / graded-commutation spot checks

 - Pick 3-5 triples of bosonized spin operators, check OPE[OPE[a,b],c] == OPE[a,OPE[b,c]]
 - Check graded sign: OPE[a,b] / OPE[b,a] equals expected sign for fermion/boson pairs

 ---
 6. Scope exclusions (v1)

 - No symbolic mu, no numeric spinor labels 1..16
 - No nonempty S/St modes, no differentiated spin fields
 - No changes to tensor-structure or basis-generation rules
 - No OPE pipeline routing changes (hasSpinFieldQ dispatch is separate task)
 - SpinFields.wl left as reference only

 ---
 Files to modify

 ┌────────────────────────────────────────────────────────────┬───────────────────────────────────────────────────────────────────────────────────────────────────────────┐
 │                            File                            │                                                  Changes                                                  │
 ├────────────────────────────────────────────────────────────┼───────────────────────────────────────────────────────────────────────────────────────────────────────────┤
 │ StringCode/Symbols/TypeII/FlatSpace/FlatSpace.m            │ DefineField for dH, dHt, expH, expHt; data tables (chiralspins, antichiralspins, vectors, basisChangeM);  │
 │                                                            │ single-field Bosonize rules                                                                               │
 ├────────────────────────────────────────────────────────────┼───────────────────────────────────────────────────────────────────────────────────────────────────────────┤
 │ StringCode/Wick/TypeII/FlatSpace/FlatSpace.m               │ hMetric, chargeDot, cocycle, x matrix; Wick/SWick/MWick rules for dH/expH                                 │
 ├────────────────────────────────────────────────────────────┼───────────────────────────────────────────────────────────────────────────────────────────────────────────┤
 │ StringCode/NormalOrdering/NormalOrdering.m (or submodule)  │ Bosonize[R[...]] with cocycle insertion                                                                   │
 ├────────────────────────────────────────────────────────────┼───────────────────────────────────────────────────────────────────────────────────────────────────────────┤
 │ StringCode/Operators/Operators.m (or FlatSpace submodule)  │ placeOp rules for dH, dHt, expH, expHt                                                                    │
 ├────────────────────────────────────────────────────────────┼───────────────────────────────────────────────────────────────────────────────────────────────────────────┤
 │ New:                                                       │ Verification notebook                                                                                     │
 │ StringCode/OPE/TypeII/FlatSpace/bosonization-tests.wlnb    │                                                                                                           │
 └────────────────────────────────────────────────────────────┴───────────────────────────────────────────────────────────────────────────────────────────────────────────┘