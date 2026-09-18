(* Run in a fresh Wolfram kernel. No runtime convention overrides. *)
Needs["StringCode`"];
localCocycleTestConvention = If[Environment["STRINGCODE_TEST_CONVENTION"] === "TypeII-Xi", "TypeII-Xi", "TypeII-Ashoke"];
InitStringCode[<|"theory" -> "TypeII", "CFT" -> "FlatSpace", "conventions" -> localCocycleTestConvention, "bracket" -> "Flat"|>];

localCocycleTestResults = {};
localCocycleCheck::usage = "localCocycleCheck[name, condition] records an exact regression assertion.";
localCocycleCheck[name_, condition_] := (
  AppendTo[localCocycleTestResults, {name, TrueQ[condition]}];
  Print[name, ": ", TrueQ[condition]]
);

(* Compare two independent evaluation routes; no fitted coefficient is an oracle. *)
Do[
  current = R[\[Psi][triple[[1]], 0, 1], \[Psi][triple[[2]], 0, 1]];
  dressed = R[exp\[Phi]f[-1, 0], \[Psi][triple[[3]], 0, 0]];
  If[sector === "Anti", {current, dressed} = {current, dressed} /. {\[Psi] -> \[Psi]t, exp\[Phi]f -> exp\[Phi]tf}];
  project = If[sector === "Holo", OPEProjectedHolo, OPEProjectedAntiHolo];
  expected = Bosonize[project[1][current, dressed]] /. \[Delta][i_Integer, j_Integer] :> KroneckerDelta[i, j];
  actual = project[1][Bosonize[current], Bosonize[dressed]];
  localCocycleCheck[{"dressed current", sector, triple}, Expand[actual - expected] === 0],
  {sector, {"Holo", "Anti"}},
  {triple, {{7, 4, 4}, {4, 7, 4}, {4, 10, 4}, {1, 2, 2}, {1, 6, 6}}}
];

(* A spectator must not disable point splitting inside a same-point fermion
   current. This catches the dphi psi psi blocks used by the KFFK pipeline. *)
Do[
  psiHead = If[sector === "Holo", \[Psi], \[Psi]t];
  dphiField = If[sector === "Holo", d\[Phi][0, z], d\[Phi]t[0, z]];
  dhField = If[sector === "Holo", dH[1, 0, z], dHt[1, 0, z]];
  current = Bosonize[R[psiHead[triple[[1]], 0, z], psiHead[triple[[2]], 0, z]]];
  expected = Expand[current /. r_R :> R[dhField, Sequence @@ (List @@ r)]];
  actual = Bosonize[R[dphiField, psiHead[triple[[1]], 0, z], psiHead[triple[[2]], 0, z]]];
  localCocycleCheck[{"dphi spectator preserves point splitting", sector, triple}, Simplify[Expand[actual - expected]] === 0],
  {sector, {"Holo", "Anti"}},
  {triple, {{7, 4}, {4, 7}, {4, 10}, {1, 2}, {1, 6}}}
];

(* Exhaustive cache-to-matrix comparison: four families, all 1024 index subsets.
   The independent recurrence uses public matrices, never the cache lookup. *)
localCocycleAntisym::usage = "localCocycleAntisym[start, indices] builds an antisymmetric product directly from public mixed gamma matrices.";
localCocycleAntisym[start_, {}] := IdentityMatrix[16];
localCocycleAntisym[start_, indices_List] := localCocycleAntisym[start, indices] =
  Sum[(-1)^(pos - 1) If[start === 1, GammaUD[indices[[pos]]], GammaDU[indices[[pos]]]] .
    localCocycleAntisym[3 - start, Delete[indices, pos]], {pos, Length[indices]}]/Length[indices];
Do[
  cacheAgrees = And @@ Table[
    left = Switch[family[[1]], None, IdentityMatrix[16], CUDHold, CUD, CDUHold, CDU];
    Normal[Private`gammaCachedProductMatrix[family, indices]] === left . localCocycleAntisym[family[[2]], indices],
    {indices, Subsets[Range[10]]}
  ];
  localCocycleCheck[{"all cache subsets", family}, cacheAgrees],
  {family, Private`gammaProductCacheFamilies}
];
localCocycleCheck["public charge-conjugated matrices", And @@ Table[
  CGamma[i] === CUD . GammaDU[i] && CIGamma[i] === CDU . GammaUD[i], {i, 10}]];

(* Original repeated-index counterexample, both sectors and two name orderings. *)
base = {R[\[Psi][a, 0, z1], \[Psi][b1, 0, z1]],
  R[S[{s1, "chiral"}, -1/2, {}, 0, -z0]],
  R[exp\[Phi]f[-1, z0], \[Psi][p, 0, z0]],
  R[S[{s2, "chiral"}, -1/2, {}, 0, w]]};
Do[
  input = base;
  If[renamed, input = input /. {a -> m1, b1 -> Private`\[Mu]$123456, p -> p1, s1 -> \[Alpha]1, s2 -> \[Alpha]3}];
  If[sector === "Anti", input = input /. {\[Psi] -> \[Psi]t, exp\[Phi]f -> exp\[Phi]tf, S -> St, z1 -> z1bar, z0 -> z0bar, w -> wbar}];
  artifact = StringCode`OPE`TypeII`FlatSpace`SpinProjection`Compile`buildSectorArtifact[sector, input, 0, 1234];
  solution = StringCode`OPE`TypeII`FlatSpace`SpinProjection`Solve`solveSectorArtifact[artifact, 1234];
  localCocycleCheck[{"spin solve and both gates", sector, renamed}, TrueQ[solution["CompleteQ"]] &&
    TrueQ[solution["Validation"]["FailFast"]["PassedQ"]] && TrueQ[solution["Validation"]["RoutineRegression"]["PassedQ"]]];
  localCocycleCheck[{"relabel gate", sector, renamed}, TrueQ[solution["Validation"]["RoutineRegression"]["Relabel"]["PassedQ"]]];
  If[TrueQ[solution["CompleteQ"]],
    witness = Private`spinProjectionValidationProbe0[artifact, solution["CoeffVector"], {{15, 6}, {7, 7, 7}}, 20];
    localCocycleCheck[{"repeated-index witness", sector, renamed}, TrueQ[witness["PassedQ"]]];
    corrupted = Join[solution, <|"CoeffVector" -> 2 solution["CoeffVector"]|>];
    localCocycleCheck[{"corrupted coefficients still rejected", sector, renamed},
      !TrueQ[Private`spinProjectionValidateSolution0[artifact, corrupted, 1234]["PassedQ"]]]
  ],
  {sector, {"Holo", "Anti"}}, {renamed, {False, True}}
];
Print["SUMMARY ", Count[localCocycleTestResults[[All, 2]], True], "/", Length[localCocycleTestResults]];
Quit[If[And @@ localCocycleTestResults[[All, 2]], 0, 1]];
