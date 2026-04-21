(* OPE contract checks for the rewrite campaign.
   This is a plain Wolfram Language script, not a notebook replay.
   Each section states the behavior we want to preserve and then checks
   the exact output or exact algebraic identity that defines that contract. *)

Needs["StringCode`"];

(* The contract script switches between Bosonic and Type II setups in one kernel.
   Those loads legitimately put same-named symbols on the context path, so we
   suppress shadowing noise and only report contract failures. *)
Off[General::shdw];

ClearAll[failures, report, equalQ, checkEq, checkSame, checkTrue];

failures = {};

report[name_, ok_, details___String] := If[
  TrueQ[ok],
  Print["PASS: " <> name],
  failures = Append[failures, name];
  Print["FAIL: " <> name];
  Scan[Print, {details}]
];

equalQ[actual_, expected_] :=
  TrueQ[actual === expected] ||
  TrueQ[Simplify[actual - expected] === 0] ||
  TrueQ[Simplify[actual == expected]];

checkEq[name_, actual_, expected_] := report[
  name,
  equalQ[actual, expected],
  "  actual: " <> ToString[InputForm[actual]],
  "  expected: " <> ToString[InputForm[expected]]
];

checkSame[name_, actual_, expected_] := report[
  name,
  actual === expected,
  "  actual: " <> ToString[InputForm[actual]],
  "  expected: " <> ToString[InputForm[expected]]
];

checkTrue[name_, condition_] := report[
  name,
  TrueQ[condition],
  "  value: " <> ToString[InputForm[condition]]
];

(* Bosonic flat space gives small exact OPE outputs that are easy to keep stable.
   These also lock down the exported OPE/OPEProjected/OPEProjectedHolo/OPEProjectedAntiHolo symbols. *)
StringCode`InitStringCode[
  <|
    "theory" -> "Bosonic",
    "CFT" -> "FlatSpace",
    "conventions" -> "Bosonic-Xi",
    "bracket" -> "Flat"
  |>
];

Module[{lhs, rhs, expr},
  checkEq[
    "Bosonic OPE unary identity",
    OPE[R[b[0, z]]],
    R[b[0, z]]
  ];

  checkEq[
    "Bosonic OPE b-c",
    OPE[R[b[0, z]], R[c[0, w]]],
    R[b[0, z], c[0, w]] + 1/(z - w)
  ];

  checkEq[
    "Bosonic flat OPE dX-dX",
    OPE[R[dX[\[Mu], 0, z]], R[dX[\[Nu], 0, w]]],
    R[dX[\[Mu], 0, z], dX[\[Nu], 0, w]] - \[Alpha]p \[Delta][\[Mu], \[Nu]]/(2 (z - w)^2)
  ];

  checkEq[
    "OPE annihilates on 0",
    OPE[R[b[0, z]], 0, R[c[0, w]]],
    0
  ];

  lhs = OPEProjected[0, 0][R[dX[\[Mu], 0, z]] + R[dX[\[Rho], 0, z]], R[dX[\[Nu], 0, w]]];
  rhs =
    OPEProjected[0, 0][R[dX[\[Mu], 0, z]], R[dX[\[Nu], 0, w]]] +
    OPEProjected[0, 0][R[dX[\[Rho], 0, z]], R[dX[\[Nu], 0, w]]];
  checkEq["OPEProjected linearity", lhs, rhs];

  expr = OPEProjected[0, 0][R[dX[\[Mu], 0, z]], R[dX[\[Nu], 0, w]]];
  checkTrue[
    "OPEProjected keeps dX singular data",
    !FreeQ[expr, \[Alpha]p] && !FreeQ[expr, \[Delta][\[Mu], \[Nu]]]
  ];

  lhs = OPEProjectedHolo[0][R[b[0, z]] + R[c[0, z]], R[c[0, w]]];
  rhs =
    OPEProjectedHolo[0][R[b[0, z]], R[c[0, w]]] +
    OPEProjectedHolo[0][R[c[0, z]], R[c[0, w]]];
  checkEq["OPEProjectedHolo linearity", lhs, rhs];

  checkEq[
    "OPEProjectedHolo zero law",
    OPEProjectedHolo[0][0, R[b[0, z]]],
    0
  ];

  lhs = OPEProjectedAntiHolo[0][3 R[b[0, z]], R[c[0, w]]];
  rhs = 3 OPEProjectedAntiHolo[0][R[b[0, z]], R[c[0, w]]];
  checkEq["OPEProjectedAntiHolo scalar extraction", lhs, rhs];

  checkEq[
    "OPEProjectedAntiHolo zero law",
    OPEProjectedAntiHolo[0][0, R[c[0, z]]],
    0
  ];
];

(* Bosonic minimal model is where projected OPE is intentionally partial.
   Unsupported projections must stay symbolic rather than silently returning junk. *)
StringCode`InitStringCode[
  <|
    "theory" -> "Bosonic",
    "CFT" -> "MinimalModel",
    "conventions" -> "Bosonic-Xi",
    "bracket" -> "Flat"
  |>
];

Module[{expr, unsupported21, unsupported20},
  expr = OPE[R[V[0, 0, z1, z1Bar]], R[V[0, 0, z2, z2Bar]]];
  checkSame["Minimal-model OPE V-V stays symbolic", Head[expr], OPE];

  unsupported21 = OPEProjected[2, 1][R[V[0, 0, z1, z1Bar]], R[V[0, 0, z2, z2Bar]]];
  checkSame[
    "Minimal-model unsupported projection[2,1] stays symbolic",
    unsupported21,
    OPEProjected[2, 1][R[V[0, 0, z1, z1Bar]], R[V[0, 0, z2, z2Bar]]]
  ];

  unsupported20 = OPEProjected[2, 0][R[V[0, 0, z1, z1Bar]], R[V[0, 0, z2, z2Bar]]];
  checkSame[
    "Minimal-model unsupported projection[2,0] stays symbolic",
    unsupported20,
    OPEProjected[2, 0][R[V[0, 0, z1, z1Bar]], R[V[0, 0, z2, z2Bar]]]
  ];
];

(* Type II flat space is the hard backend-specific contract.
   These are the exact projected outputs that matter for the current implementation.
   The projected basis states are defined here exactly once, matching the notebook setup cell. *)
StringCode`InitStringCode[
  <|
    "theory" -> "TypeII",
    "CFT" -> "FlatSpace",
    "conventions" -> "TypeII-Ashoke",
    "bracket" -> "Flat"
  |>
];

Module[
  {
    lhs, rhs,
    projectedNSOutHolo, projectedNSOutHoloIndex,
    projectedSpinOutHolo, projectedSpinOutHoloIndex,
    projectedNSOutAnti, projectedNSOutAntiIndex,
    projectedSpinOutAnti, projectedSpinOutAntiIndex,
    actual14, expected14, seed1234, seed9876,
    actual15, expected15,
    actual16, expected16,
    actual17, expected17,
    actual22, expected22
  },
  projectedNSOutHolo = First[generateBasisMatterHoloOPE[1, -1]];
  projectedNSOutHoloIndex = First @ Cases[projectedNSOutHolo, \[Psi][idx_, __] :> idx, Infinity];
  projectedSpinOutHolo = First[generateBasisMatterHoloOPE[1, -3/2]];
  projectedSpinOutHoloIndex = First @ Cases[projectedSpinOutHolo, S[{idx_, "antichiral"}, __] :> idx, Infinity];

  projectedNSOutAnti = First[generateBasisMatterAntiHoloOPE[1, -1]];
  projectedNSOutAntiIndex = First @ Cases[projectedNSOutAnti, \[Psi]t[idx_, __] :> idx, Infinity];
  projectedSpinOutAnti = First[generateBasisMatterAntiHoloOPE[1, -3/2]];
  projectedSpinOutAntiIndex = First @ Cases[projectedSpinOutAnti, St[{idx_, "antichiral"}, __] :> idx, Infinity];

  checkEq[
    "Type II OPE \[Eta]-\[Xi]",
    OPE[R[\[Eta][0, z]], R[\[Xi][0, w]]],
    R[\[Eta][0, z], \[Xi][0, w]] + 1/(z - w)
  ];

  checkEq[
    "Type II OPE \[Beta]-\[Gamma]",
    OPE[R[\[Beta][0, z]], R[\[Gamma][0, w]]],
    R[\[Beta][0, z], \[Gamma][0, w]] - 1/(z - w)
  ];

  checkEq[
    "Type II OPE \[Gamma]-\[Beta]",
    OPE[R[\[Gamma][0, z]], R[\[Beta][0, w]]],
    R[\[Gamma][0, z], \[Beta][0, w]] + 1/(z - w)
  ];

  lhs = OPEProjected[0, 0][R[d\[Phi][0, z]] + R[\[Eta][0, z]], R[exp\[Phi]b[a, w]]];
  rhs =
    OPEProjected[0, 0][R[d\[Phi][0, z]], R[exp\[Phi]b[a, w]]] +
    OPEProjected[0, 0][R[\[Eta][0, z]], R[exp\[Phi]b[a, w]]];
  checkEq["Type II OPEProjected linearity", lhs, rhs];

  lhs = OPEProjected[0, 0][2 R[d\[Phi][0, z]], R[exp\[Phi]b[a, w]]];
  rhs = 2 OPEProjected[0, 0][R[d\[Phi][0, z]], R[exp\[Phi]b[a, w]]];
  checkEq["Type II OPEProjected scalar extraction", lhs, rhs];

  expected14 =
    -(GammaAntisymmetricProductHold[{CUDHold, GammaDUHold[projectedNSOutHoloIndex]}, alpha, beta] projectedNSOutHolo)/
      (Sqrt[2] (w - z));
  actual14 =
    OPEProjected[1, 0][
      R[S[{alpha, "chiral"}, -1/2, {}, 0, z]],
      R[S[{beta, "chiral"}, -1/2, {}, 0, w]],
      "RandomSeed" -> 1234
    ];
  checkEq["Projected S-S to e^-phi psi", actual14, expected14];

  expected15 =
    -(GammaAntisymmetricProductHold[{CUDHold, GammaDUHold[projectedNSOutAntiIndex]}, alpha, beta] projectedNSOutAnti)/
      (Sqrt[2] (wb - zb));
  actual15 =
    OPEProjected[0, 1][
      R[St[{alpha, "chiral"}, -1/2, {}, 0, zb]],
      R[St[{beta, "chiral"}, -1/2, {}, 0, wb]],
      "RandomSeed" -> 1234
    ];
  checkEq["Projected St-St to e^-phit psit", actual15, expected15];

  expected16 =
    -(GammaAntisymmetricProductHold[{GammaDUHold[\[Mu]]}, projectedSpinOutHoloIndex, alpha] projectedSpinOutHolo)/
      (Sqrt[2] (w - z));
  actual16 =
    OPEProjected[1, 0][
      R[exp\[Phi]f[-1, z], \[Psi][\[Mu], 0, z]],
      R[S[{alpha, "chiral"}, -1/2, {}, 0, w]],
      "RandomSeed" -> 1234
    ];
  checkEq["Projected e^-phi psi with S", actual16, expected16];

  expected17 =
    -(GammaAntisymmetricProductHold[{GammaDUHold[\[Mu]]}, projectedSpinOutAntiIndex, alpha] projectedSpinOutAnti)/
      (Sqrt[2] (wb - zb));
  actual17 =
    OPEProjected[0, 1][
      R[exp\[Phi]tf[-1, zb], \[Psi]t[\[Mu], 0, zb]],
      R[St[{alpha, "chiral"}, -1/2, {}, 0, wb]],
      "RandomSeed" -> 1234
    ];
  checkEq["Projected e^-phit psit with St", actual17, expected17];

  checkTrue[
    "Projected spin-field branch returns an expression",
    !AssociationQ[actual16]
  ];

  actual22 =
    OPEProjected[1, 0][
      R[exp\[Phi]f[-1, z], \[Psi][1, 0, z]],
      R[S[{alpha, "chiral"}, -1/2, {}, 0, w]],
      "RandomSeed" -> 1234
    ];
  expected22 =
    -(GammaAntisymmetricProductHold[{GammaDUHold[1]}, projectedSpinOutHoloIndex, alpha] projectedSpinOutHolo)/
      (Sqrt[2] (w - z));
  checkEq["Concrete projected e^-phi psi with S", actual22, expected22];

  seed1234 = actual14;
  seed9876 =
    OPEProjected[1, 0][
      R[S[{alpha, "chiral"}, -1/2, {}, 0, z]],
      R[S[{beta, "chiral"}, -1/2, {}, 0, w]],
      "RandomSeed" -> 9876
    ];
  checkEq["RandomSeed does not change canonical result", seed1234, seed9876];
];

If[failures === {},
  Print["All curated OPE contract checks passed."];
  Exit[0];
];

Print["OPE contract check failures:"];
Scan[Print["  - " <> #] &, failures];
Exit[1];
