Needs["StringCode`"];
StringCode`InitStringCode[<|"theory" -> "TypeII", "CFT" -> "FlatSpace", "conventions" -> "TypeII-Ashoke", "bracket" -> "Flat", "signature" -> "Euclidean"|>];
Needs["StringCode`OPE`TypeII`FlatSpace`SpinProjection`TestSupport`"];

semanticCases = {
  <|
    "Case" -> "projected S-S -> e^-phi psi",
    "Ops" -> {
      R[S[{alpha, "chiral"}, -1/2, {}, 0, z]],
      R[S[{beta, "chiral"}, -1/2, {}, 0, w]]
    },
    "wH" -> 1,
    "wA" -> 0
  |>,
  <|
    "Case" -> "projected psi-S",
    "Ops" -> {
      R[exp\[Phi]f[-1, z], \[Psi][mu, 0, z]],
      R[S[{alpha, "chiral"}, -1/2, {}, 0, w]]
    },
    "wH" -> 1,
    "wA" -> 0
  |>,
  <|
    "Case" -> "projected excited antichiral spin with e^-phi psi [2,0]",
    "Ops" -> {
      R[S[{a1, "antichiral"}, -1/2, {{mu, -1}}, 0, z1]],
      R[exp\[Phi]f[-1, z2], \[Psi][nu, 0, z2]]
    },
    "wH" -> 2,
    "wA" -> 0
  |>,
  <|
    "Case" -> "projected S-S-S",
    "Ops" -> {
      R[S[{alpha, "chiral"}, -1/2, {}, 0, u]],
      R[S[{beta, "chiral"}, -1/2, {}, 0, z]],
      R[S[{gamma, "chiral"}, -1/2, {}, 0, w]]
    },
    "wH" -> 1,
    "wA" -> 0
  |>,
  <|
    "Case" -> "projected psi-psi-S",
    "Ops" -> {
      R[exp\[Phi]f[-1, z1], \[Psi][mu, 0, z1]],
      R[exp\[Phi]f[-1, z2], \[Psi][nu, 0, z2]],
      R[S[{alpha, "chiral"}, -1/2, {}, 0, z3]]
    },
    "wH" -> 0,
    "wA" -> 0
  |>,
  <|
    "Case" -> "projected psi-psi-psi-S",
    "Ops" -> {
      R[exp\[Phi]f[-1, z1], \[Psi][mu, 0, z1]],
      R[exp\[Phi]f[-1, z2], \[Psi][nu, 0, z2]],
      R[exp\[Phi]f[-1, z3], \[Psi][rho, 0, z3]],
      R[S[{alpha, "chiral"}, -1/2, {}, 0, z4]]
    },
    "wH" -> -2,
    "wA" -> 0
  |>,
  <|
    "Case" -> "projected five-spin",
    "Ops" -> {
      R[S[{a1, "chiral"}, -1/2, {}, 0, z1]],
      R[S[{a2, "chiral"}, -1/2, {}, 0, z2]],
      R[S[{a3, "chiral"}, -1/2, {}, 0, z3]],
      R[S[{a4, "chiral"}, -1/2, {}, 0, z4]],
      R[S[{a5, "chiral"}, -1/2, {}, 0, z5]]
    },
    "wH" -> 0,
    "wA" -> 0
  |>
};

semanticSummaries = Table[
  Module[{result, summary},
    result = spinProjectionSemanticCaseCheck[spec["Ops"], spec["wH"], spec["wA"], 1234];
    summary = <|
      "Case" -> spec["Case"],
      "CompleteQ" -> Lookup[result, "CompleteQ", False],
      "WitnessCount" -> Lookup[result, "WitnessCount", 0],
      "CoveredColumns" -> Lookup[result, "CoveredColumns", <||>],
      "AllWitnessesMatchQ" -> Lookup[result, "AllWitnessesMatchQ", False]
    |>;
    Print[summary];
    summary
  ],
  {spec, semanticCases}
];

Exit[If[AllTrue[semanticSummaries, TrueQ[Lookup[#, "CompleteQ", False]] &], 0, 1]];
