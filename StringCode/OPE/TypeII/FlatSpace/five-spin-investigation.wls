Remove["Global`*"];
Needs["StringCode`"];
StringCode`InitStringCode[
  <|
    "theory" -> "TypeII",
    "CFT" -> "FlatSpace",
    "conventions" -> "TypeII-Ashoke",
    "bracket" -> "Flat"
  |>
];

pairCoordinate = 7;
tripleCoordinateRules = {u -> 11, z -> 5, w -> 0};
fiveCoordinateRules = {z1 -> 13, z2 -> 11, z3 -> 7, z4 -> 3, z5 -> 0};

chiralBasis[] := Private`chiralspins;
antichiralBasis[] := Private`antichiralspins;
vectorBasis[] := Private`vectors;

stateOperator[charge_List, coord_] :=
  StringCode`NormalOrdering`R[
    StringCode`Symbols`TypeII`FlatSpace`expH[charge, coord]
  ];

chiralSpinField[sym_, coord_] :=
  StringCode`NormalOrdering`R[
    StringCode`Symbols`TypeII`FlatSpace`S[{sym, "chiral"}, -1/2, {}, 0, coord]
  ];

nestedOPE[ops_List] := Fold[StringCode`OPE`OPE, First[ops], Rest[ops]];

probeInputRules[probe_List] := Thread[{a1, a2, a3, a4, a5} -> (chiralBasis[][[#]] & /@ probe)];

fiveSpinOutputStates[probe_List] := stateOperator[Join[{-5/2}, chiralBasis[][[#]]], 0] & /@ probe;

fiveSpinCoefficientVectorFromExpr[expr_, probe_List] := Module[
  {exprWithProbe, outputStates},
  exprWithProbe = Simplify[expr /. probeInputRules[probe]];
  outputStates = fiveSpinOutputStates[probe];
  Simplify[Coefficient[exprWithProbe, #]] & /@ outputStates
];

fiveSpinDirectInputOps[probe_List] := {
  stateOperator[Join[{-1/2}, chiralBasis[][[probe[[1]]]]], z1],
  stateOperator[Join[{-1/2}, chiralBasis[][[probe[[2]]]]], z2],
  stateOperator[Join[{-1/2}, chiralBasis[][[probe[[3]]]]], z3],
  stateOperator[Join[{-1/2}, chiralBasis[][[probe[[4]]]]], z4],
  stateOperator[Join[{-1/2}, chiralBasis[][[probe[[5]]]]], z5]
};

fiveSpinDirectBosonizedExpression[probe_List] :=
  fiveSpinDirectBosonizedExpression[probe] =
    StringCode`Symbols`TypeII`FlatSpace`Bosonize[
      Expand[
        nestedOPE[fiveSpinDirectInputOps[probe]] /. fiveCoordinateRules
      ]
    ];

fiveSpinDirectActualCoefficients[probe_List] :=
  fiveSpinCoefficientVectorFromExpr[fiveSpinDirectBosonizedExpression[probe], probe];

fiveSpinExpectedCoefficients[probe : {a_Integer, b_Integer, c_Integer, d_Integer, e_Integer}] :=
  fiveSpinExpectedCoefficients[probe] = {
    Simplify[
      (
        (-I/2) Sum[
          StringCode`Symbols`TypeII`FlatSpace`CGamma[mu][[b, d]] *
            StringCode`Symbols`TypeII`FlatSpace`CGamma[mu][[c, e]],
          {mu, 1, 10}
        ]/((z2 - z3) (z3 - z4) (z2 - z5) (z4 - z5) (-z1 + z5)) +
        (I/2) Sum[
          StringCode`Symbols`TypeII`FlatSpace`CGamma[mu][[b, c]] *
            StringCode`Symbols`TypeII`FlatSpace`CGamma[mu][[d, e]],
          {mu, 1, 10}
        ]/((z2 - z4) (-z3 + z4) (z2 - z5) (z3 - z5) (-z1 + z5))
      ) /. fiveCoordinateRules
    ],
    Simplify[
      (
        (I/2) Sum[
          StringCode`Symbols`TypeII`FlatSpace`CGamma[mu][[a, d]] *
            StringCode`Symbols`TypeII`FlatSpace`CGamma[mu][[c, e]],
          {mu, 1, 10}
        ]/((z1 - z3) (z3 - z4) (z1 - z5) (z4 - z5) (-z2 + z5)) -
        (I/2) Sum[
          StringCode`Symbols`TypeII`FlatSpace`CGamma[mu][[a, c]] *
            StringCode`Symbols`TypeII`FlatSpace`CGamma[mu][[d, e]],
          {mu, 1, 10}
        ]/((z1 - z4) (-z3 + z4) (z1 - z5) (z3 - z5) (-z2 + z5))
      ) /. fiveCoordinateRules
    ],
    Simplify[
      (
        -(I/2) Sum[
          StringCode`Symbols`TypeII`FlatSpace`CGamma[mu][[a, d]] *
            StringCode`Symbols`TypeII`FlatSpace`CGamma[mu][[b, e]],
          {mu, 1, 10}
        ]/((z1 - z2) (z2 - z4) (z1 - z5) (z4 - z5) (-z3 + z5)) +
        (I/2) Sum[
          StringCode`Symbols`TypeII`FlatSpace`CGamma[mu][[a, b]] *
            StringCode`Symbols`TypeII`FlatSpace`CGamma[mu][[d, e]],
          {mu, 1, 10}
        ]/((z1 - z4) (-z2 + z4) (z1 - z5) (z2 - z5) (-z3 + z5))
      ) /. fiveCoordinateRules
    ],
    Simplify[
      (
        (I/2) Sum[
          StringCode`Symbols`TypeII`FlatSpace`CGamma[mu][[a, c]] *
            StringCode`Symbols`TypeII`FlatSpace`CGamma[mu][[b, e]],
          {mu, 1, 10}
        ]/((z1 - z2) (z2 - z3) (z1 - z5) (z3 - z5) (-z4 + z5)) -
        (I/2) Sum[
          StringCode`Symbols`TypeII`FlatSpace`CGamma[mu][[a, b]] *
            StringCode`Symbols`TypeII`FlatSpace`CGamma[mu][[c, e]],
          {mu, 1, 10}
        ]/((z1 - z3) (-z2 + z3) (z1 - z5) (z2 - z5) (-z4 + z5))
      ) /. fiveCoordinateRules
    ],
    Simplify[
      (
        -(I/2) Sum[
          StringCode`Symbols`TypeII`FlatSpace`CGamma[mu][[a, c]] *
            StringCode`Symbols`TypeII`FlatSpace`CGamma[mu][[b, d]],
          {mu, 1, 10}
        ]/((z1 - z2) (z2 - z3) (z1 - z4) (z3 - z4) (z4 - z5)) +
        (I/2) Sum[
          StringCode`Symbols`TypeII`FlatSpace`CGamma[mu][[a, b]] *
            StringCode`Symbols`TypeII`FlatSpace`CGamma[mu][[c, d]],
          {mu, 1, 10}
        ]/((z1 - z3) (-z2 + z3) (z1 - z4) (z2 - z4) (z4 - z5))
      ) /. fiveCoordinateRules
    ]
  };

fiveSpinPublicInputOps[] := {
  chiralSpinField[a1, z1],
  chiralSpinField[a2, z2],
  chiralSpinField[a3, z3],
  chiralSpinField[a4, z4],
  chiralSpinField[a5, 0]
};

fiveSpinPublicProjectedExpression[] :=
  fiveSpinPublicProjectedExpression[] =
    StringCode`Symbols`TypeII`FlatSpace`Bosonize[
      Expand[
        StringCode`OPE`TypeII`FlatSpace`OPEProjected[0, 0][
          Sequence @@ fiveSpinPublicInputOps[],
          "RandomSeed" -> 1234
        ] /. fiveCoordinateRules
      ]
    ];

fiveSpinPublicProjectedCoefficients[probe_List] :=
  fiveSpinCoefficientVectorFromExpr[fiveSpinPublicProjectedExpression[], probe];

mergedPowerCoefficient[leftCharge_List, rightCharge_List, power_] :=
  mergedPowerCoefficient[leftCharge, rightCharge, power] =
    StringCode`Symbols`TypeII`FlatSpace`Bosonize[
      Expand[
        Coefficient[
          StringCode`OPE`OPE[
            stateOperator[leftCharge, z],
            stateOperator[rightCharge, 0]
          ],
          z,
          power
        ] /. z -> 0
      ]
    ];

spinSpinToVectorMatrices[pLeft_, basisLeft_List, pRight_, basisRight_List, pOut_, zPower_] := Table[
  Table[
    Simplify[
      Coefficient[
        mergedPowerCoefficient[
          Join[{pLeft}, basisLeft[[row]]],
          Join[{pRight}, basisRight[[col]]],
          zPower
        ],
        stateOperator[Join[{pOut}, vectorBasis[][[vec]]], 0]
      ]
    ],
    {row, 1, Length[basisLeft]},
    {col, 1, Length[basisRight]}
  ],
  {vec, 1, Length[vectorBasis[]]}
];

sameChiralGammaMatrices[pLeft_, basisLeft_List, pRight_, basisRight_List, pOut_, zPower_] := Module[{rawMats},
  rawMats = spinSpinToVectorMatrices[pLeft, basisLeft, pRight, basisRight, pOut, zPower];
  Table[
    Simplify[
      Sum[
        Inverse[Private`basisChangeM][[vec, mu]] rawMats[[vec]],
        {vec, 1, Length[vectorBasis[]]}
      ]
    ],
    {mu, 1, Length[vectorBasis[]]}
  ]
];

threeSpinBosonizedExpression[indices : {a_Integer, b_Integer, c_Integer}] :=
  threeSpinBosonizedExpression[indices] =
    StringCode`Symbols`TypeII`FlatSpace`Bosonize[
      Expand[
        nestedOPE[{
          stateOperator[Join[{-1/2}, chiralBasis[][[a]]], u],
          stateOperator[Join[{-1/2}, chiralBasis[][[b]]], z],
          stateOperator[Join[{-1/2}, chiralBasis[][[c]]], 0]
        }] /. tripleCoordinateRules
      ]
    ];

threeSpinActualCoefficient[a_Integer, b_Integer, c_Integer, d_Integer] := Simplify[
  Coefficient[
    threeSpinBosonizedExpression[{a, b, c}],
    stateOperator[Join[{-3/2}, antichiralBasis[][[d]]], 0]
  ]
];

threeSpinExpectedCoefficient[a_Integer, b_Integer, c_Integer, d_Integer] := Simplify[
  (
    -Sum[
      StringCode`Symbols`TypeII`FlatSpace`GammaDU[mu][[d, b]] *
        StringCode`Symbols`TypeII`FlatSpace`CGamma[mu][[a, c]],
      {mu, 1, 10}
    ]/(2 (u - w) (u - z)) +
    Sum[
      StringCode`Symbols`TypeII`FlatSpace`GammaDU[mu][[d, a]] *
        StringCode`Symbols`TypeII`FlatSpace`CGamma[mu][[b, c]],
      {mu, 1, 10}
    ]/(2 (u - z) (w - z))
  ) /. tripleCoordinateRules
];

exitWithStatus[status_String, payload_Association, code_Integer] := Module[{report},
  report = Join[<|"Status" -> status|>, payload];
  Print[report];
  Exit[code];
];

ssPrecheck = TrueQ[
  Simplify[
    sameChiralGammaMatrices[-1/2, chiralBasis[], -1/2, chiralBasis[], -1, -1][[1]] ==
      StringCode`Symbols`TypeII`FlatSpace`CGamma[1]/Sqrt[2]
  ]
];

threeSpinPrecheck = TrueQ[
  Simplify[
    threeSpinActualCoefficient[1, 3, 5, 7] ==
      threeSpinExpectedCoefficient[1, 3, 5, 7]
  ]
];

If[
  !ssPrecheck || !threeSpinPrecheck,
  exitWithStatus[
    "OracleSetupFailed",
    <|
      "SSMatrixIdentity" -> ssPrecheck,
      "ThreeSpinIdentity" -> threeSpinPrecheck
    |>,
    1
  ]
];

fiveSpinAnchorProbes = {
  {5, 2, 7, 8, 16},
  {2, 7, 8, 16, 5},
  {9, 5, 4, 8, 7},
  {1, 3, 5, 7, 9}
};

probeExpectedNonzeroQ[probe_List] :=
  !TrueQ[Simplify[fiveSpinExpectedCoefficients[probe] == ConstantArray[0, 5]]];

probeSlotCoverageCounts[probes_List] := Module[{counts = ConstantArray[0, 5], coeffs},
  Do[
    coeffs = fiveSpinExpectedCoefficients[probe];
    Do[
      If[!TrueQ[Simplify[coeffs[[slot]] == 0]], counts[[slot]]++],
      {slot, 1, 5}
    ],
    {probe, probes}
  ];
  counts
];

probeCorpusReadyQ[probes_List] := Module[{counts},
  counts = probeSlotCoverageCounts[probes];
  Length[probes] >= 12 && Min[counts] >= 3
];

buildFiveSpinProbeCorpus[] := Module[
  {
    probes = DeleteDuplicates[fiveSpinAnchorProbes],
    seeds = {301, 302, 303},
    seed,
    candidate,
    attempts,
    slotCoverage
  },
  Do[
    SeedRandom[seed];
    attempts = 0;
    While[
      Length[probes] < 24 &&
        !probeCorpusReadyQ[probes] &&
        attempts < 2000,
      attempts++;
      candidate = RandomSample[Range[16], 5];
      If[MemberQ[probes, candidate], Continue[]];
      If[probeExpectedNonzeroQ[candidate], probes = Append[probes, candidate]];
    ],
    {seed, seeds}
  ];
  slotCoverage = probeSlotCoverageCounts[probes];
  <|
    "Probes" -> probes,
    "SlotCoverage" -> slotCoverage,
    "ReadyQ" -> (Length[probes] <= 24 && Length[probes] >= 12 && Min[slotCoverage] >= 3)
  |>
];

probeCorpus = buildFiveSpinProbeCorpus[];
If[
  !TrueQ[probeCorpus["ReadyQ"]],
  exitWithStatus[
    "ProbeCorpusBuildFailed",
    <|
      "ProbeCount" -> Length[probeCorpus["Probes"]],
      "SlotCoverage" -> probeCorpus["SlotCoverage"],
      "Anchors" -> fiveSpinAnchorProbes
    |>,
    1
  ]
];

tripleGammaTermQ[term_] := Count[List @@ term, factor_ /; !FreeQ[factor, StringCode`Symbols`TypeII`FlatSpace`CGamma]] >= 3;
publicContainsTripleGammaTermsQ = AnyTrue[List @@ Expand[fiveSpinPublicProjectedExpression[]], tripleGammaTermQ];

probeResultAssociation[probe_List] := Module[{a, b, c, ab, bc, ac, result},
  a = fiveSpinDirectActualCoefficients[probe];
  b = fiveSpinExpectedCoefficients[probe];
  c = fiveSpinPublicProjectedCoefficients[probe];
  ab = TrueQ[Simplify[a == b]];
  bc = TrueQ[Simplify[b == c]];
  ac = TrueQ[Simplify[a == c]];
  result = <|
    "Probe" -> probe,
    "A" -> a,
    "B" -> b,
    "C" -> c,
    "AeqB" -> ab,
    "BeqC" -> bc,
    "AeqC" -> ac
  |>;
  Print[result];
  result
];

probeResults = probeResultAssociation /@ probeCorpus["Probes"];
probeFailureQ[result_Association] := !(TrueQ[result["AeqB"]] && TrueQ[result["BeqC"]] && TrueQ[result["AeqC"]]);
firstFailingResult = SelectFirst[probeResults, probeFailureQ, Missing["NoFailure"]];

summary = <|
  "TotalProbes" -> Length[probeResults],
  "NonzeroProbes" -> Count[
    probeResults,
    result_ /; !TrueQ[Simplify[result["B"] == ConstantArray[0, 5]]]
  ],
  "AeqBCount" -> Count[probeResults, result_ /; TrueQ[result["AeqB"]]],
  "BeqCCount" -> Count[probeResults, result_ /; TrueQ[result["BeqC"]]],
  "AeqCCount" -> Count[probeResults, result_ /; TrueQ[result["AeqC"]]],
  "FirstFailingProbe" -> If[MissingQ[firstFailingResult], Missing["NoFailure"], firstFailingResult["Probe"]],
  "ContainsTripleGammaTerms" -> publicContainsTripleGammaTermsQ
|>;
Print[summary];

classification = Which[
  MissingQ[firstFailingResult], "AllGreen",
  TrueQ[firstFailingResult["AeqB"]] && !TrueQ[firstFailingResult["BeqC"]], "PublicCompiledPathBug",
  !TrueQ[firstFailingResult["AeqB"]] && TrueQ[firstFailingResult["BeqC"]], "DirectOracleBug",
  !TrueQ[firstFailingResult["AeqB"]] && TrueQ[firstFailingResult["AeqC"]], "ExpectedFormulaOrConventionBug",
  True, "MixedMismatch"
];

Print[
  <|
    "Status" -> classification,
    "FirstFailingProbe" -> If[MissingQ[firstFailingResult], Missing["NoFailure"], firstFailingResult["Probe"]]
  |>
];

firstMismatchSlot[left_List, right_List] := SelectFirst[
  Range[Length[left]],
  !TrueQ[Simplify[left[[#]] == right[[#]]]] &,
  Missing["NoMismatch"]
];

findWitnessForKey[artifact_Association, candidate_, key_, seed_] := Module[
  {
    family,
    familyIndex,
    spinDomain,
    termBuckets,
    nextState,
    tuple,
    stateSpins,
    stateVectors,
    terms,
    row,
    assocCoeff
  },
  Do[
    family = artifact["Families"][[familyIndex]];
    {spinDomain, termBuckets} = If[
      Length[family["SpinSymbols"]] == 1,
      StringCode`OPE`TypeII`FlatSpace`SpinProjection`Solve`spinProjectionFamilyOutputSpinDomain[family, candidate, seed, True],
      {StringCode`OPE`TypeII`FlatSpace`SpinProjection`Solve`spinProjectionFamilyOutputSpinDomain[family, candidate, seed], <||>}
    ];
    nextState = StringCode`OPE`TypeII`FlatSpace`SpinProjection`Solve`spinProjectionFamilyStateIterator[family, seed, spinDomain];
    While[True,
      tuple = nextState[];
      If[tuple === EndOfFile, Break[]];
      tuple = Reverse[tuple];
      stateSpins = Developer`ToPackedArray[Take[tuple, Length[family["SpinSymbols"]]]];
      stateVectors = Developer`ToPackedArray[Drop[tuple, Length[family["SpinSymbols"]]]];
      terms = If[
        Length[family["SpinSymbols"]] == 1,
        Join[Lookup[termBuckets, 0, {}], Lookup[termBuckets, stateSpins[[1]], {}]],
        family["Terms"]
      ];
      row = StringCode`OPE`TypeII`FlatSpace`SpinProjection`Solve`spinProjectionFamilyStateRow[
        artifact,
        family,
        candidate,
        stateSpins,
        stateVectors,
        terms
      ];
      If[row === 0 || row === $Failed, Continue[]];
      assocCoeff = Lookup[StringCode`OPE`TypeII`FlatSpace`SpinProjection`Compile`familyOutputAssociation[family, tuple], key, 0];
      If[assocCoeff === 0, Continue[]];
      Return[
        <|
          "Candidate" -> candidate,
          "FamilyIndex" -> familyIndex,
          "Tuple" -> tuple,
          "StateSpins" -> stateSpins,
          "StateVectors" -> stateVectors,
          "Key" -> key,
          "AssocCoeff" -> assocCoeff,
          "Seed" -> seed,
          "CoordinateRules" -> fiveCoordinateRules
        |>
      ]
    ],
    {familyIndex, Length[artifact["Families"]]}
  ];
  Missing["NoWitness"]
];

runPublicCompiledPathDiagnostics[firstFailing_Association] := Module[
  {
    failingProbe,
    failingSlot,
    outputKey,
    artifacts,
    artifact,
    solveResult,
    rawReconstructedExpr,
    rawReconstructedBosonizedExpr,
    rawReconstructedCoeffs,
    publicCoeffs,
    directCoeffs,
    candidateSpins,
    candidate,
    witness,
    familyRows,
    fullKeyRow,
    compiledKeyCoeff,
    lhsAssoc,
    lhsCoeff,
    faithfulnessWitness,
    faithfulnessResults,
    faithfulnessFailures,
    layer
  },
  Needs["StringCode`OPE`TypeII`FlatSpace`SpinProjection`TestSupport`"];

  failingProbe = firstFailing["Probe"];
  failingSlot = firstMismatchSlot[firstFailing["B"], firstFailing["C"]];
  If[MissingQ[failingSlot], failingSlot = firstMismatchSlot[firstFailing["A"], firstFailing["C"]]];
  If[MissingQ[failingSlot], Return[<|"DiagnosticStatus" -> "NoFailingSlotFound"|>]];

  outputKey = fiveSpinOutputStates[failingProbe][[failingSlot]];
  artifacts = StringCode`OPE`TypeII`FlatSpace`SpinProjection`Compile`buildProjectedArtifacts[
    fiveSpinPublicInputOps[],
    0,
    0,
    1234
  ];
  artifact = artifacts["Holo"];
  If[Lookup[artifact, "Mode", None] =!= "SpinProjection",
    Return[<|"DiagnosticStatus" -> "NoSpinProjectionArtifact", "ArtifactMode" -> Lookup[artifact, "Mode", None]|>]
  ];
  solveResult = StringCode`OPE`TypeII`FlatSpace`SpinProjection`Solve`solveSectorArtifact[artifact, 1234];
  If[!TrueQ[solveResult["CompleteQ"]],
    Return[<|"DiagnosticStatus" -> "SolveIncomplete", "SolveResult" -> solveResult|>]
  ];

  rawReconstructedExpr = If[
    artifact["Columns"] === {},
    artifact["Expr"],
    Total@Table[
      solveResult["CoeffVector"][[i]] artifact["Columns"][[i, "RepresentativeExpr"]],
      {i, Length[artifact["Columns"]]}
    ]
  ];
  rawReconstructedBosonizedExpr = StringCode`Symbols`TypeII`FlatSpace`Bosonize[
    Expand[rawReconstructedExpr /. fiveCoordinateRules]
  ];
  rawReconstructedCoeffs = fiveSpinCoefficientVectorFromExpr[rawReconstructedBosonizedExpr, failingProbe];
  publicCoeffs = fiveSpinPublicProjectedCoefficients[failingProbe];
  directCoeffs = fiveSpinDirectActualCoefficients[failingProbe];

  candidateSpins = Lookup[
    AssociationThread[{a1, a2, a3, a4, a5} -> failingProbe],
    artifact["FreeSpinSymbols"],
    Missing["NoSpinAssignment"]
  ];
  If[MemberQ[candidateSpins, _Missing],
    Return[<|"DiagnosticStatus" -> "CandidateBuildFailed", "FreeSpinSymbols" -> artifact["FreeSpinSymbols"]|>]
  ];
  candidate = {
    Developer`ToPackedArray[candidateSpins],
    Developer`ToPackedArray[ConstantArray[1, Length[artifact["FreeVectorGroups"]]]]
  };

  witness = findWitnessForKey[artifact, candidate, outputKey, 1234];
  If[MissingQ[witness], Return[<|"DiagnosticStatus" -> "WitnessNotFound", "FailingProbe" -> failingProbe, "FailingSlot" -> failingSlot|>]];

  familyRows = Table[
    StringCode`OPE`TypeII`FlatSpace`SpinProjection`TestSupport`Private`spinProjectionFamilyKeyRow0[
      artifact,
      familyIndex,
      candidate,
      outputKey,
      1234
    ],
    {familyIndex, Length[artifact["Families"]]}
  ];
  fullKeyRow = Total[familyRows];
  compiledKeyCoeff = StringCode`OPE`TypeII`FlatSpace`SpinProjection`TestSupport`Private`spinProjectionEvaluateSummedTensorScalars0[
    (fullKeyRow . solveResult["CoeffVector"]) /. fiveCoordinateRules
  ];
  lhsAssoc = StringCode`OPE`TypeII`FlatSpace`SpinProjection`TestSupport`Private`spinProjectionLHSAssociationForCandidate0[artifact, candidate];
  lhsCoeff = StringCode`OPE`TypeII`FlatSpace`SpinProjection`TestSupport`Private`spinProjectionEvaluateSummedTensorScalars0[
    Lookup[lhsAssoc, outputKey, 0] /. fiveCoordinateRules
  ];

  faithfulnessWitness = <|
    "Name" -> "FailingWitness",
    "FreeSpins" -> candidate[[1]],
    "FreeVectors" -> candidate[[2]],
    "StateSpins" -> witness["StateSpins"],
    "StateVectors" -> witness["StateVectors"],
    "Key" -> outputKey,
    "CoordinateRules" -> fiveCoordinateRules
  |>;
  faithfulnessResults = StringCode`OPE`TypeII`FlatSpace`SpinProjection`TestSupport`spinProjectionColumnFaithfulnessCheck[
    artifact,
    {faithfulnessWitness}
  ];
  faithfulnessFailures = Select[faithfulnessResults, !TrueQ[Lookup[#, "MatchQ", False]] &];

  layer = Which[
    !TrueQ[Simplify[rawReconstructedCoeffs[[failingSlot]] == publicCoeffs[[failingSlot]]]],
      "PublicGlueOrReconstruction",
    TrueQ[Simplify[compiledKeyCoeff == directCoeffs[[failingSlot]]]] &&
      !TrueQ[Simplify[publicCoeffs[[failingSlot]] == directCoeffs[[failingSlot]]]],
      "SymbolicRepresentativeConstruction",
    TrueQ[Simplify[compiledKeyCoeff == publicCoeffs[[failingSlot]]]] &&
      !TrueQ[Simplify[compiledKeyCoeff == directCoeffs[[failingSlot]]]],
      "SolveCoefficients",
    !TrueQ[Simplify[compiledKeyCoeff == directCoeffs[[failingSlot]]]] &&
      !TrueQ[Simplify[publicCoeffs[[failingSlot]] == directCoeffs[[failingSlot]]]] &&
      faithfulnessFailures =!= {},
      "CompiledTermConstructionOrRepresentativeMismatch",
    True,
      "MixedOrInconclusive"
  ];

  <|
    "DiagnosticStatus" -> "PublicPathDiagnosticComplete",
    "FailingProbe" -> failingProbe,
    "FailingSlot" -> failingSlot,
    "FailingKey" -> outputKey,
    "DirectCoeff" -> directCoeffs[[failingSlot]],
    "ExpectedCoeff" -> firstFailing["B"][[failingSlot]],
    "PublicCoeff" -> publicCoeffs[[failingSlot]],
    "RawReconstructedCoeff" -> rawReconstructedCoeffs[[failingSlot]],
    "CompiledFamilyKeyCoeff" -> compiledKeyCoeff,
    "LHSCoeff" -> lhsCoeff,
    "RawEqualsPublic" -> TrueQ[Simplify[rawReconstructedCoeffs[[failingSlot]] == publicCoeffs[[failingSlot]]]],
    "CompiledEqualsPublic" -> TrueQ[Simplify[compiledKeyCoeff == publicCoeffs[[failingSlot]]]],
    "CompiledEqualsDirect" -> TrueQ[Simplify[compiledKeyCoeff == directCoeffs[[failingSlot]]]],
    "LHSMatchesCompiled" -> TrueQ[Simplify[lhsCoeff == compiledKeyCoeff]],
    "FaithfulnessFailureCount" -> Length[faithfulnessFailures],
    "FirstFaithfulnessFailure" -> If[faithfulnessFailures === {}, Missing["NoFailure"], First[faithfulnessFailures]],
    "InferredLayer" -> layer
  |>
];

If[
  classification === "PublicCompiledPathBug",
  publicDiagnostics = runPublicCompiledPathDiagnostics[firstFailingResult];
  Print[publicDiagnostics];
];

If[classification === "AllGreen",
  Exit[0],
  Exit[1]
];
