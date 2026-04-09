(* ::Package:: *)

BeginPackage["StringCode`OPE`TypeII`FlatSpace`SpinProjection`Solve`"];
Needs["StringCode`OPE`TypeII`FlatSpace`SpinProjection`Compile`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];
Needs["StringCode`Symbols`TypeII`FlatSpace`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`TypeII`"];
Needs["StringCode`Operators`"];
Needs["StringCode`OPE`"];
Needs["StringCode`OPE`TypeII`FlatSpace`GammaMatrices`"];
Needs["StringCode`OPE`TypeII`FlatSpace`GammaMatrices`GammaKernelEngine`"];
Needs["StringCode`OPE`TypeII`FlatSpace`GammaMatrices`GammaProductGrammar`"];

solveSectorArtifact::usage =
  "solveSectorArtifact[artifact, seed] solves one spin-projection artifact exactly and returns coefficient data, pivot metadata, and witness assignments.";

traceSectorArtifact::usage =
  "traceSectorArtifact[artifact, candidate, seed] returns artifact-native row-trace diagnostics for one candidate assignment.";


Begin["Private`"];

spinProjectionSpinBasisChargeTable::usage =
  "spinProjectionSpinBasisChargeTable[chirality, q] returns the bosonized charge vectors for one fixed picture and chirality, indexed in spin-basis order.";
spinProjectionSpinBasisChargeTable[chirality_String, q_?NumericQ] :=
  spinProjectionSpinBasisChargeTable[chirality, q] = (Prepend[#, q] & /@ spinProjectionSpinBasisState[chirality]);

spinProjectionSpinorBasisAssociation::usage =
  "spinProjectionSpinorBasisAssociation[chirality] returns the exact ordered spin-state lookup used for probe gamma-matrix evaluation.";
spinProjectionSpinorBasisAssociation["chiral"] :=
  spinProjectionSpinorBasisAssociation["chiral"] = AssociationThread[chiralspins -> Range[Length[chiralspins]]];
spinProjectionSpinorBasisAssociation["antichiral"] :=
  spinProjectionSpinorBasisAssociation["antichiral"] = AssociationThread[antichiralspins -> Range[Length[antichiralspins]]];

spinProjectionSpinorBasisIndex::usage =
  "spinProjectionSpinorBasisIndex[spin, chirality] returns the canonical basis index for one explicit spin vector or Missing if absent.";
spinProjectionSpinorBasisIndex[spin_, chirality_String] := Module[{assoc},
  assoc = spinProjectionSpinorBasisAssociation[chirality];
  If[KeyExistsQ[assoc, spin], assoc[spin], Missing["UnknownSpinor"]]
];

spinProjectionConcreteSpinChirality::usage =
  "spinProjectionConcreteSpinChirality[spin] returns the concrete chirality label of one explicit spin basis vector when known.";
spinProjectionConcreteSpinChirality[spin_List] := Which[
  IntegerQ[spinProjectionSpinorBasisIndex[spin, "chiral"]], "chiral",
  IntegerQ[spinProjectionSpinorBasisIndex[spin, "antichiral"]], "antichiral",
  True, Missing["UnknownChirality"]
];
spinProjectionConcreteSpinChirality[_] := Missing["UnknownChirality"];

spinProjectionGammaFactorValue::usage =
  "spinProjectionGammaFactorValue[factor] evaluates one concrete GammaAntisymmetricProductHold factor to its exact scalar matrix element when possible.";
spinProjectionGammaFactorValue[factor_GammaAntisymmetricProductHold] := Module[
  {links = factor[[1]], spinors = {factor[[2]], factor[[3]]}, chiralities, concreteChiralities, indices, matrix},
  chiralities = gammaProductSpinorChiralities[links];
  concreteChiralities = spinProjectionConcreteSpinChirality /@ spinors;
  If[links === {} && AllTrue[concreteChiralities, StringQ] && SameQ @@ concreteChiralities,
    chiralities = concreteChiralities;
  ];
  indices = MapThread[spinProjectionSpinorBasisIndex, {spinors, chiralities}];
  If[!AllTrue[indices, IntegerQ], Return[factor]];
  matrix = If[
    links === {} && AllTrue[concreteChiralities, StringQ] && SameQ @@ concreteChiralities,
    IdentityMatrix[Length[CUD]],
    spinProjectionGammaFactorMatrix[links]
  ];
  If[!MatrixQ[matrix], Return[factor]];
  matrix[[indices[[1]], indices[[2]]]]
];

spinProjectionGammaFactorVector::usage =
  "spinProjectionGammaFactorVector[factor, sym] returns the exact row or column associated with symbolic spinor sym when the opposite spinor slot is concrete.";
spinProjectionGammaFactorVector[factor_GammaAntisymmetricProductHold, sym_Symbol] := Module[
  {links = factor[[1]], s1 = factor[[2]], s2 = factor[[3]], chiralities, matrix, index, concreteChirality},
  chiralities = gammaProductSpinorChiralities[links];
  Which[
    s1 === sym,
    concreteChirality = spinProjectionConcreteSpinChirality[s2];
    If[links === {} && StringQ[concreteChirality],
      chiralities = {concreteChirality, concreteChirality};
      matrix = IdentityMatrix[Length[CUD]],
      matrix = spinProjectionGammaFactorMatrix[links]
    ];
    If[!MatrixQ[matrix], Return[factor]];
    index = spinProjectionSpinorBasisIndex[s2, chiralities[[2]]];
    If[IntegerQ[index], matrix[[All, index]], factor],
    s2 === sym,
    concreteChirality = spinProjectionConcreteSpinChirality[s1];
    If[links === {} && StringQ[concreteChirality],
      chiralities = {concreteChirality, concreteChirality};
      matrix = IdentityMatrix[Length[CUD]],
      matrix = spinProjectionGammaFactorMatrix[links]
    ];
    If[!MatrixQ[matrix], Return[factor]];
    index = spinProjectionSpinorBasisIndex[s1, chiralities[[1]]];
    If[IntegerQ[index], matrix[[index, All]], factor],
    True,
    factor
  ]
];

spinProjectionDeltaValue::usage =
  "spinProjectionDeltaValue[factor] evaluates one concrete inert delta factor to 0 or 1 when both endpoints are explicit vector slots.";
spinProjectionDeltaValue[factor_ /; Head[factor] === \[Delta] && Length[factor] == 2] := KroneckerDelta[factor[[1]], factor[[2]]];
spinProjectionDeltaValue[factor_] := factor;

spinProjectionEvaluateTensorScalars::usage =
  "spinProjectionEvaluateTensorScalars[expr] replaces concrete gamma/delta tensor factors by exact scalar values inside one randomized probe expression.";
spinProjectionEvaluateTensorScalars[expr_] := Expand[expr /. {
  factor_GammaAntisymmetricProductHold :> spinProjectionGammaFactorValue[factor],
  factor_ /; Head[factor] === \[Delta] && Length[factor] == 2 :> spinProjectionDeltaValue[factor]
}];

spinProjectionOperatorAssociation::usage =
  "spinProjectionOperatorAssociation[expr] expands a bosonized operator expression into an operator-key association.";
spinProjectionOperatorAssociation[expr_] := basisExpressionToOperatorAssociation[Canonicalize[Expand[expr]]];

spinProjectionWeightFilteredExpression::usage =
  "spinProjectionWeightFilteredExpression[expr, sector, weight] keeps only operator terms whose chiral weight matches the requested projected weight.";
spinProjectionWeightFilteredExpression[expr_, sector_String, weight_] := Module[{assoc},
  assoc = spinProjectionOperatorAssociation[expr];
  Total @ KeyValueMap[
    Function[{op, coeff},
      Which[
        op === 1 && weight === 0, coeff,
        op === 1, 0,
        sector === "Holo" && totalWeightHolo[op] === weight, coeff op,
        sector === "Anti" && totalWeightAntiHolo[op] === weight, coeff op,
        True, 0
      ]
    ],
    assoc
  ]
];

spinProjectionExpressionWeight::usage =
  "spinProjectionExpressionWeight[expr, sector] returns the common chiral weight carried by a bosonized probe expression.";
spinProjectionExpressionWeight[expr_, sector : ("Holo" | "Anti")] := Module[{assoc, ops, weights, spec},
  spec = spinProjectionSectorSpec[sector];
  assoc = spinProjectionOperatorAssociation[expr];
  ops = DeleteCases[Keys[assoc], 1];
  If[ops === {}, Return[0]];
  weights = DeleteDuplicates[spec["Weight"] /@ ops];
  First[weights]
];

spinProjectionRescaleInputExpression::usage =
  "spinProjectionRescaleInputExpression[expr, scale] rescales every top-level R[...] contribution inside one expanded bosonized input expression.";
spinProjectionRescaleInputExpression[expr_, scale_] := Expand[expr /. ra_ /; RTest[ra] :> rescaleR[scale][ra]];

spinProjectionProjectInputs::usage =
  "spinProjectionProjectInputs[sector, weight, targetWeight, inputs] evaluates one projected bosonized OPE sector when the insertion target weight is already known.";
spinProjectionProjectInputs[sector : ("Holo" | "Anti"), weight_, targetWeight_, inputs_List] := Module[
  {spec},
  spec = spinProjectionSectorSpec[sector];
  If[inputs === {}, Return[If[weight === 0, 1, 0]]];
  spinProjectionWeightFilteredExpression[
    spec["Project"][
      opeOfRList[spinProjectionRescaleInputExpression[#, spec["ScaleSymbol"]] & /@ inputs],
      targetWeight,
      spec["ScaleSymbol"]
    ],
    sector,
    weight
  ]
];

spinProjectionSectorEvaluation::usage =
  "spinProjectionSectorEvaluation[sector, weight, inputs] evaluates one randomized projected OPE sector on bosonized inputs.";
spinProjectionSectorEvaluation[sector : ("Holo" | "Anti"), weight_, inputs_List] := Module[
  {insertionWeight, targetWeight},
  If[inputs === {}, Return[If[weight === 0, 1, 0]]];
  insertionWeight = Total[spinProjectionExpressionWeight[#, sector] & /@ inputs];
  targetWeight = weight - insertionWeight;
  spinProjectionProjectInputs[sector, weight, targetWeight, inputs]
];

spinProjectionCompiledCandidateLimit::usage =
  "Maximum number of deterministic compiled probe assignments enumerated before falling back to the legacy symbolic solver.";
spinProjectionCompiledCandidateLimit = 800;

spinProjectionFamilyTupleAssociation0::usage =
  "spinProjectionFamilyTupleAssociation0[family, tuple] resolves one family output tuple through the lazy output-association key.";
spinProjectionFamilyTupleAssociation0[family_Association, tuple_List] := familyOutputAssociation[family, tuple];

spinProjectionArtifactCandidateRows0::usage =
  "spinProjectionArtifactCandidateRows0[artifact, candidate, basis, seed] scans concrete family states and returns only rank-increasing exact rows.";
spinProjectionArtifactCandidateRows0[
  artifact_Association,
  candidate : {freeSpins_List, freeVectors_List},
  basis_Association,
  seed_
] := Module[
  {state = basis, row, assoc, familyRows, insert, nextState, tuple, stateSpins, stateVectors, spinDomain, termBuckets, terms, reaped, collected},
  reaped = Reap[
    Do[
      familyRows = <||>;
      {spinDomain, termBuckets} = If[
        Length[family["SpinSymbols"]] == 1,
        spinProjectionFamilyOutputSpinDomain[family, candidate, seed, True],
        {spinProjectionFamilyOutputSpinDomain[family, candidate, seed], <||>}
      ];
      nextState = spinProjectionFamilyStateIterator[family, seed, spinDomain];
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
        row = spinProjectionFamilyStateRow[artifact, family, candidate, stateSpins, stateVectors, terms];
        If[row === $Failed || !AnyTrue[row, # =!= 0 &], Continue[]];
        assoc = spinProjectionFamilyTupleAssociation0[family, tuple];
        Scan[
          Function[pair,
            familyRows[pair[[1]]] =
              Lookup[familyRows, pair[[1]], ConstantArray[0, artifact["VarCount"]]] + pair[[2]] row
          ],
          Normal[assoc]
        ];
      ];
      Scan[
        Function[pair,
          insert = spinProjectionExactBasisInsertRow[state, pair[[2]]];
          If[insert[[2]],
            state = insert[[1]];
            Sow[pair[[2]], "Rows"];
            Sow[pair[[1]], "Keys"]
          ]
        ],
        SortBy[Normal[familyRows], First]
      ];
      If[Length[state["Pivots"]] >= artifact["VarCount"], Break[]],
      {family, artifact["Families"]}
    ],
    _,
    Rule
  ];
  collected = Association[reaped[[2]]];
  <|
    "Basis" -> state,
    "Rows" -> Lookup[collected, "Rows", {}],
    "Keys" -> Lookup[collected, "Keys", {}]
  |>
];

spinProjectionCoeffVectorFromRows0::usage =
  "spinProjectionCoeffVectorFromRows0[varCount, rows, rhs, pivots] returns the full coefficient vector from accepted pivot rows.";
spinProjectionCoeffVectorFromRows0[varCount_Integer?NonNegative, rows_List, rhs_List, pivots_List] := Module[
  {coeffs = ConstantArray[0, varCount], solved},
  If[pivots === {}, Return[coeffs]];
  solved = LinearSolve[rows[[All, pivots]], rhs];
  coeffs[[pivots]] = solved;
  coeffs
];

spinProjectionSolveResult0::usage =
  "spinProjectionSolveResult0[varCount, coeffVector, pivots, acceptedKeys, witnesses, visited, acceptedCandidates, acceptedRows, completeQ] builds the standard solve-result association.";
spinProjectionSolveResult0[
  varCount_Integer?NonNegative,
  coeffVector_List,
  pivots_List,
  acceptedKeys_List,
  witnesses_List,
  visited_Integer?NonNegative,
  acceptedCandidates_Integer?NonNegative,
  acceptedRows_Integer?NonNegative,
  completeQ_
] := <|
  "CoeffVector" -> coeffVector,
  "Pivots" -> pivots,
  "AcceptedKeys" -> acceptedKeys,
  "WitnessAssignments" -> witnesses,
  "VisitedCandidates" -> visited,
  "AcceptedCandidates" -> acceptedCandidates,
  "AcceptedRows" -> acceptedRows,
  "PivotCount" -> Length[pivots],
  "VarCount" -> varCount,
  "CompleteQ" -> TrueQ[completeQ],
  "Attempts" -> visited
|>;

spinProjectionArtifactExhaustiveFamilyRows0::usage =
  "spinProjectionArtifactExhaustiveFamilyRows0[artifact, family, candidate] exhaustively evaluates one artifact family state space and returns state/family rows.";
spinProjectionArtifactExhaustiveFamilyRows0[
  artifact_Association,
  family_Association,
  candidate : {freeSpins_List, freeVectors_List}
] := Module[
  {nextState, tuple, stateSpins, stateVectors, row, assoc, stateRows = <||>, familyRows = <||>},
  nextState = spinProjectionFamilyStateIterator[family, None];
  While[True,
    tuple = nextState[];
    If[tuple === EndOfFile, Break[]];
    tuple = Reverse[tuple];
    stateSpins = Developer`ToPackedArray[Take[tuple, Length[family["SpinSymbols"]]]];
    stateVectors = Developer`ToPackedArray[Drop[tuple, Length[family["SpinSymbols"]]]];
    row = spinProjectionFamilyStateRow[artifact, family, candidate, stateSpins, stateVectors];
    If[row === 0, Continue[]];
    AssociateTo[stateRows, tuple -> row];
    If[row === $Failed, Continue[]];
    assoc = spinProjectionFamilyTupleAssociation0[family, tuple];
    Scan[
      Function[pair,
        familyRows[pair[[1]]] = Lookup[familyRows, pair[[1]], ConstantArray[0, artifact["VarCount"]]] + pair[[2]] row
      ],
      Normal[assoc]
    ];
  ];
  <|
    "StateRows" -> stateRows,
    "FamilyRows" -> SortBy[Normal[familyRows], First]
  |>
];

spinProjectionArtifactCandidateRowsTrace0::usage =
  "spinProjectionArtifactCandidateRowsTrace0[artifact, candidate, basis, seed] mirrors artifact row selection with per-family diagnostics.";
spinProjectionArtifactCandidateRowsTrace0[
  artifact_Association,
  candidate : {freeSpins_List, freeVectors_List},
  basis_Association,
  seed_
] := Module[
  {
    state = basis,
    row,
    assoc,
    familyRows,
    insert,
    nextState,
    tuple,
    stateSpins,
    stateVectors,
    spinDomain,
    termBuckets,
    visitedTuples,
    nonzeroStateRows,
    bucketColumns,
    familyVisitedReap,
    collected,
    reaped
  },
  reaped = Reap[
    Do[
      familyRows = <||>;
      nonzeroStateRows = <||>;
      {spinDomain, termBuckets} = If[
        Length[family["SpinSymbols"]] == 1,
        spinProjectionFamilyOutputSpinDomain[family, candidate, seed, True],
        {spinProjectionFamilyOutputSpinDomain[family, candidate, seed], <||>}
      ];
      nextState = spinProjectionFamilyStateIterator[family, seed, spinDomain];
      familyVisitedReap = Reap[
        While[True,
          tuple = nextState[];
          If[tuple === EndOfFile, Break[]];
          tuple = Reverse[tuple];
          Sow[tuple, "VisitedTuples"];
          stateSpins = Developer`ToPackedArray[Take[tuple, Length[family["SpinSymbols"]]]];
          stateVectors = Developer`ToPackedArray[Drop[tuple, Length[family["SpinSymbols"]]]];
          row = spinProjectionFamilyStateRow[
            artifact,
            family,
            candidate,
            stateSpins,
            stateVectors,
            If[
              Length[family["SpinSymbols"]] == 1,
              Join[Lookup[termBuckets, 0, {}], Lookup[termBuckets, stateSpins[[1]], {}]],
              family["Terms"]
            ]
          ];
          If[row === 0, Continue[]];
          AssociateTo[nonzeroStateRows, tuple -> row];
          If[row === $Failed, Continue[]];
          assoc = spinProjectionFamilyTupleAssociation0[family, tuple];
          Scan[
            Function[pair,
              familyRows[pair[[1]]] = Lookup[familyRows, pair[[1]], ConstantArray[0, artifact["VarCount"]]] + pair[[2]] row
            ],
            Normal[assoc]
          ];
        ],
        _,
        Rule
      ];
      visitedTuples = Lookup[Association[familyVisitedReap[[2]]], "VisitedTuples", {}];
      Scan[
        Function[pair,
          insert = spinProjectionExactBasisInsertRow[state, pair[[2]]];
          If[insert[[2]],
            state = insert[[1]];
            Sow[pair[[2]], "Rows"];
            Sow[pair[[1]], "Keys"]
          ]
        ],
        SortBy[Normal[familyRows], First]
      ];
      bucketColumns = Association @ KeyValueMap[#1 -> (Lookup[#, "Column"] & /@ #2) &, termBuckets];
      Sow[
        <|
          "Template" -> family["Template"],
          "SpinDomain" -> spinDomain,
          "BucketColumns" -> bucketColumns,
          "VisitedTuples" -> visitedTuples,
          "NonzeroStateRows" -> nonzeroStateRows,
          "FamilyRows" -> SortBy[Normal[familyRows], First]
        |>,
        "Families"
      ];
      If[Length[state["Pivots"]] >= artifact["VarCount"], Break[]],
      {family, artifact["Families"]}
    ],
    _,
    Rule
  ];
  collected = Association[reaped[[2]]];
  <|
    "Basis" -> state,
    "Rows" -> Lookup[collected, "Rows", {}],
    "Keys" -> Lookup[collected, "Keys", {}],
    "Families" -> Lookup[collected, "Families", {}]
  |>
];

traceSectorArtifact[artifact_Association, candidate : {freeSpins_List, freeVectors_List}, seed_] := Module[
  {trace, exhaustive},
  trace = spinProjectionArtifactCandidateRowsTrace0[artifact, candidate, <|"Rows" -> {}, "Pivots" -> {}|>, seed];
  exhaustive = If[
    Lookup[artifact, "Families", {}] === {},
    <|"StateRows" -> <||>, "FamilyRows" -> {}|>,
    spinProjectionArtifactExhaustiveFamilyRows0[artifact, artifact["Families"][[1]], candidate]
  ];
  <|"Trace" -> trace, "Exhaustive" -> exhaustive|>
];

solveSectorArtifact::usage =
  "solveSectorArtifact[artifact, seed] solves one spin-projection artifact exactly and returns coefficient data, pivot metadata, and witness assignments.";
solveSectorArtifact[artifact_Association, seed_] := Module[
  {
    varCount = Lookup[artifact, "VarCount", Length[Lookup[artifact, "Vars", {}]]],
    mode = Lookup[artifact, "Mode", None],
    sector = Lookup[artifact, "Sector", Missing["NotAvailable"]],
    weight = Lookup[artifact, "Weight", Missing["NotAvailable"]],
    targetWeight = Lookup[artifact, "TargetWeight", None],
    nextCandidate,
    basis = <|"Rows" -> {}, "Pivots" -> {}|>,
    rows = {},
    rhs = {},
    acceptedKeys = {},
    witnesses = {},
    visitedCandidates = 0,
    acceptedCandidates = 0,
    acceptedRows = 0,
    candidate,
    accepted,
    inputs,
    lhs,
    lhsAssoc,
    coeffs = {},
    pivots = {},
    completeQ = True
  },
  If[mode =!= "SpinProjection",
    Return[spinProjectionSolveResult0[varCount, ConstantArray[0, varCount], {}, {}, {}, 0, 0, 0, True]]
  ];
  If[sector === Missing["NotAvailable"] || weight === Missing["NotAvailable"],
    Return[spinProjectionSolveResult0[varCount, ConstantArray[0, varCount], {}, {}, {}, 0, 0, 0, False]]
  ];
  If[varCount == 0,
    Return[spinProjectionSolveResult0[0, {}, {}, {}, {}, 0, 0, 0, True]]
  ];
  If[targetWeight === None,
    targetWeight = weight - Total[
      spinProjectionExpressionWeight[#, sector] & /@ spinProjectionConcreteInputs[
        artifact,
        {
          Developer`ToPackedArray[ConstantArray[1, Length[Lookup[artifact, "FreeSpinSymbols", {}]]]],
          Developer`ToPackedArray[ConstantArray[1, Length[Lookup[artifact, "FreeVectorGroups", {}]]]]
        }
      ]
    ]
  ];
  nextCandidate = spinProjectionAssignmentIterator[artifact, seed];
  If[nextCandidate === $Failed,
    Return[spinProjectionSolveResult0[varCount, ConstantArray[0, varCount], {}, {}, {}, 0, 0, 0, False]]
  ];
  While[
    Length[basis["Pivots"]] < varCount && (candidate = nextCandidate[]) =!= EndOfFile,
    visitedCandidates++;
    accepted = spinProjectionArtifactCandidateRows0[artifact, candidate, basis, seed];
    If[accepted["Rows"] === {}, Continue[]];
    acceptedCandidates++;
    acceptedRows += Length[accepted["Rows"]];
    basis = accepted["Basis"];
    inputs = spinProjectionConcreteInputs[artifact, candidate];
    lhs = spinProjectionProjectInputs[sector, weight, targetWeight, inputs];
    lhsAssoc = spinProjectionOperatorAssociation[lhs];
    rows = Join[rows, accepted["Rows"]];
    acceptedKeys = Join[acceptedKeys, accepted["Keys"]];
    rhs = Join[rhs, Lookup[lhsAssoc, #, 0] & /@ accepted["Keys"]];
    witnesses = Join[witnesses, ConstantArray[candidate, Length[accepted["Keys"]]]];
  ];
  pivots = basis["Pivots"];
  completeQ = Length[pivots] == varCount;
  coeffs = If[
    completeQ,
    spinProjectionCoeffVectorFromRows0[varCount, rows, rhs, pivots],
    ConstantArray[0, varCount]
  ];
  spinProjectionSolveResult0[
    varCount,
    coeffs,
    pivots,
    acceptedKeys,
    witnesses,
    visitedCandidates,
    acceptedCandidates,
    acceptedRows,
    completeQ
  ]
];


(* legacy solve core migrated from LegacyCore.m *)

spinProjectionTupleStep::usage =
  "spinProjectionTupleStep[total, seed, tag] returns a seeded step size coprime to total for streaming tuple permutations.";
spinProjectionTupleStep[total_Integer?Positive, None, _] := 1;
spinProjectionTupleStep[total_Integer?Positive, Automatic, tag_] := spinProjectionTupleStep[total, 0, tag];
spinProjectionTupleStep[1, _, _] := 1;
spinProjectionTupleStep[total_Integer?Positive, seed_, tag_] := Module[{step},
  step = 1 + Mod[Hash[{seed, tag, "step"}], total - 1];
  While[!CoprimeQ[step, total], step++];
  step
];

spinProjectionTupleAt::usage =
  "spinProjectionTupleAt[domains, lengths, index] decodes one mixed-radix tuple index without materializing the full Cartesian product.";
spinProjectionTupleAt[domains_List, lengths_List, index_Integer?NonNegative] := Module[
  {digits = ConstantArray[1, Length[domains]], q = index},
  Do[
    digits[[i]] = Mod[q, lengths[[i]]] + 1;
    q = Quotient[q, lengths[[i]]],
    {i, Length[domains], 1, -1}
  ];
  MapThread[Part, {domains, digits}]
];

spinProjectionTupleIterator::usage =
  "spinProjectionTupleIterator[domains, seed, tag] returns a zero-argument iterator over the Cartesian product of domains without materializing all tuples.";
spinProjectionTupleIterator[domains_List, seed_: Automatic, tag_: None] := Module[
  {lengths = Length /@ domains, total, index = 0, start, step},
  total = Times @@ Replace[lengths, {} -> {1}];
  If[MemberQ[lengths, 0], Return[Function[{}, EndOfFile]]];
  start = If[
    seed === None || total == 0,
    0,
    Mod[Hash[{Replace[seed, Automatic -> 0], tag, "start"}], total]
  ];
  step = spinProjectionTupleStep[total, seed, tag];
  Function[{},
    If[index >= total,
      EndOfFile,
      With[{tupleIndex = Mod[start + step index, total]},
        index++;
        If[domains === {}, {}, spinProjectionTupleAt[domains, lengths, tupleIndex]]
      ]
    ]
  ]
];

spinProjectionFactorOutputSpinSupport::usage =
  "spinProjectionFactorOutputSpinSupport[factor, outputSpinSlot, freeSpins, freeVectors] returns All or the allowed output-spin basis indices for one compiled factor under one candidate assignment.";
spinProjectionFactorOutputSpinSupport[factor_, outputSpinSlot_Integer?Positive, freeSpins_List, freeVectors_List] := Module[
  {left = factor[[2]], right = factor[[3]], desc, matrix, sourceTypes, dummyCount, tuples, matrixSupport, supports},
  Switch[factor[[1]],
    0, All,
    1, Which[left[[1]] === 2 && left[[2]] === outputSpinSlot && right[[1]] === 1, {freeSpins[[right[[2]]]]}, right[[1]] === 2 && right[[2]] === outputSpinSlot && left[[1]] === 1, {freeSpins[[left[[2]]]]}, True, All],
    2,
    desc = factor[[4]];
    matrixSupport = Function[m,
      Which[
        left[[1]] === 2 && left[[2]] === outputSpinSlot && right[[1]] === 1,
          Flatten[Position[Normal[Unitize[m[[All, freeSpins[[right[[2]]]]]]]], 1]],
        right[[1]] === 2 && right[[2]] === outputSpinSlot && left[[1]] === 1,
          Flatten[Position[Normal[Unitize[m[[freeSpins[[left[[2]]]], All]]]], 1]],
        True,
          Range[16]
      ]
    ];
    sourceTypes = First /@ desc[[3]];
    If[MemberQ[sourceTypes, 2], Return[All]];
    dummyCount = Replace[Max @ Join[{0}, Cases[desc[[3]], {3, idx_Integer} :> idx, Infinity]], _Missing -> 0];
    If[dummyCount > 2, Return[All]];
    tuples = If[dummyCount == 0, {{}}, Tuples[Range[10], dummyCount]];
    supports = DeleteCases[
      Module[{m = spinProjectionConcreteGammaSparseMatrix[desc, freeVectors, {}, #]},
        If[m === $Failed, {}, matrixSupport[m]]
      ] & /@ tuples,
      {}
    ];
    If[supports === {}, Return[All]];
    supports = Union @@ supports;
    If[supports === Range[16], All, supports],
    _, All
  ]
];

spinProjectionFamilyOutputSpinDomain::usage =
  "spinProjectionFamilyOutputSpinDomain[family, candidate, seed, includeTerms] returns Automatic or the seeded subset of output-spin basis states allowed by concrete factor supports, and optionally the active term buckets.";
spinProjectionFamilyOutputSpinDomain[family_Association, {freeSpins_List, freeVectors_List}, seed_, includeTerms_: False] := Module[
  {fullDomain, seededDomain, familySupport = {}, termBuckets = <|0 -> {}|>, support, result},
  If[Length[family["SpinSymbols"]] =!= 1, Return[If[TrueQ[includeTerms], {Automatic, termBuckets}, Automatic]]];
  fullDomain = Range[Length[spinProjectionSpinBasisState[First[family["SpinChiralities"]]]]];
  seededDomain = spinProjectionSeededOrder[fullDomain, seed, First[family["SpinSymbols"]]];
  Scan[
    Function[term,
      support = With[
        {supports = Select[spinProjectionFactorOutputSpinSupport[#, 1, freeSpins, freeVectors] & /@ term["Parts"], ListQ]},
        If[
          supports === {},
          If[
            Lookup[family, "VectorSymbols", {}] === {},
            With[
              {exact = Select[
                fullDomain,
                !TrueQ @ PossibleZeroQ @ spinProjectionTermValue[
                  term,
                  freeSpins,
                  freeVectors,
                  {#},
                  {}
                ] &
              ]},
              If[exact === {}, fullDomain, exact]
            ],
            fullDomain
          ],
          Intersection @@ supports
        ]
      ];
      If[support =!= {},
        If[support === fullDomain,
          familySupport = fullDomain;
          termBuckets[0] = Append[termBuckets[0], term],
          familySupport = Union[familySupport, support];
          Scan[Function[idx, termBuckets[idx] = Append[Lookup[termBuckets, idx, {}], term]], support]
        ]
      ]
    ],
    family["Terms"]
  ];
  result = If[familySupport === {} || familySupport === fullDomain, Automatic, Select[seededDomain, MemberQ[familySupport, #] &]];
  If[TrueQ[includeTerms], {result, termBuckets}, result]
];

spinProjectionFamilyStateIterator::usage =
  "spinProjectionFamilyStateIterator[family, seed, spinDomainOverride] returns a lazy iterator over concrete output states for one compiled output family, optionally restricting the unique output-spin domain.";
spinProjectionFamilyStateIterator[family_Association, seed_, spinDomainOverride_: Automatic] := Module[{spinDomains, vectorDomains},
  spinDomains = If[
    Length[family["SpinSymbols"]] == 1 && ListQ[spinDomainOverride],
    {spinDomainOverride},
    MapThread[
      spinProjectionSeededOrder[Range[Length[spinProjectionSpinBasisState[#1]]], seed, #2] &,
      {family["SpinChiralities"], family["SpinSymbols"]}
    ]
  ];
  vectorDomains = spinProjectionSeededOrder[Range[10], seed, #] & /@ family["VectorSymbols"];
  spinProjectionTupleIterator[Reverse@Join[spinDomains, vectorDomains], seed, {"outputStates", family["Template"]}]
];

spinProjectionFamilyStateRow::usage =
  "spinProjectionFamilyStateRow[model, family, candidate, stateSpins, stateVectors, terms] evaluates one compiled family on one concrete output state and returns the exact coefficient row, 0, or $Failed.";
spinProjectionFamilyStateRow[
  model_Association,
  family_Association,
  {freeSpins_List, freeVectors_List},
  stateSpins_List,
  stateVectors_List,
  terms_List : Automatic
] := Module[{row = ConstantArray[0, model["VarCount"]], localTerms, value},
  localTerms = Replace[terms, Automatic :> family["Terms"]];
  Scan[
    Function[term,
      value = spinProjectionTermValue[term, freeSpins, freeVectors, stateSpins, stateVectors];
      If[value === $Failed,
        row = $Failed,
        If[value =!= 0, row[[term["Column"]]] += value]
      ]
    ],
    localTerms
  ];
  Which[
    row === $Failed, $Failed,
    !AnyTrue[row, # =!= 0 &], 0,
    True, row
  ]
];

spinProjectionExactBasisInsertRow::usage =
  "spinProjectionExactBasisInsertRow[state, row] inserts one exact coefficient row into the reduced exact row basis.";
spinProjectionExactBasisInsertRow[state_Association, rawRow_List] := Module[
  {basisRows = state["Rows"], pivots = state["Pivots"], row = rawRow, coeff, pivotPos, pivot, insertPos},
  If[!AnyTrue[row, # =!= 0 &], Return[{state, False}]];
  Do[
    coeff = row[[pivots[[j]]]];
    If[coeff =!= 0, row = row - coeff basisRows[[j]]],
    {j, Length[basisRows]}
  ];
  pivotPos = FirstPosition[row, x_ /; x =!= 0, Missing["NoPivot"], {1}, Heads -> False];
  If[MissingQ[pivotPos], Return[{state, False}]];
  pivot = First[pivotPos];
  row = row/row[[pivot]];
  Do[
    coeff = basisRows[[j, pivot]];
    If[coeff =!= 0, basisRows[[j]] = basisRows[[j]] - coeff row],
    {j, Length[basisRows]}
  ];
  insertPos = 1 + Count[pivots, _?(# < pivot &)];
  {
    <|"Rows" -> Insert[basisRows, row, insertPos], "Pivots" -> Insert[pivots, pivot, insertPos]|>,
    True
  }
];

spinProjectionConcreteInputs::usage =
  "spinProjectionConcreteInputs[ops, assignment] substitutes one compiled probe assignment into sector inputs and bosonizes them.";
spinProjectionConcreteInputs[model_Association, {freeSpins_List, freeVectors_List}] := Module[
  {
    spinRules,
    vectorRules
  },
  spinRules = MapThread[
    #1 -> spinProjectionSpinBasisState[#2][[#3]] &,
    {model["FreeSpinSymbols"], model["FreeSpinChiralities"], freeSpins}
  ];
  vectorRules = Flatten @ MapThread[Thread[#1 -> #2] &, {model["FreeVectorGroups"], freeVectors}];
  Bosonize /@ (model["Ops"] /. Join[vectorRules, spinRules])
];

spinProjectionProbeTermPool::usage =
  "spinProjectionProbeTermPool[model] flattens compiled output families into the term pool used by support-driven witness search.";
spinProjectionProbeTermPool[model_Association] := Flatten[
  Thread[{ConstantArray[#, Length[#["Terms"]]], #["Terms"]}] & /@ model["Families"],
  1
];

spinProjectionWitnessAssignment::usage =
  "spinProjectionWitnessAssignment[model, family, term, seed, serial] returns one support-driven witness assignment for a compiled term, or $Failed.";
spinProjectionWitnessAssignment[model_Association, family_Association, term_Association, seed_, serial_Integer?Positive] := Module[
  {
    assignment = {
      ConstantArray[None, Length[model["FreeSpinSymbols"]]],
      ConstantArray[None, Length[model["FreeVectorGroups"]]],
      ConstantArray[None, Length[family["SpinSymbols"]]],
      ConstantArray[None, Length[family["VectorSymbols"]]],
      ConstantArray[None, term["DummyCount"]]
    },
    freeSpinDomains,
    stateSpinDomains,
    freeVectorDomains,
    stateVectorDomains,
    dummyDomains
  },
  freeSpinDomains = MapThread[
    spinProjectionSeededOrder[Range[Length[spinProjectionSpinBasisState[#1]]], {seed, serial}, {"freeSpin", #2}] &,
    {model["FreeSpinChiralities"], model["FreeSpinSymbols"]}
  ];
  stateSpinDomains = MapThread[
    spinProjectionSeededOrder[Range[Length[spinProjectionSpinBasisState[#1]]], {seed, serial}, {"stateSpin", #2}] &,
    {family["SpinChiralities"], family["SpinSymbols"]}
  ];
  freeVectorDomains = spinProjectionSeededOrder[Range[10], {seed, serial}, {"freeVector", #}] & /@ model["FreeVectorGroups"];
  stateVectorDomains = spinProjectionSeededOrder[Range[10], {seed, serial}, {"stateVector", #}] & /@ family["VectorSymbols"];
  dummyDomains = spinProjectionSeededOrder[Range[10], {seed, serial}, {"dummyVector", #}] & /@ Range[term["DummyCount"]];
  With[
    {
      spinValue = Function[{src, state}, Switch[src[[1]], 1, state[[1, src[[2]]]], 2, state[[3, src[[2]]]], _, $Failed]],
      vectorValue = Function[{src, state}, Switch[src[[1]], 1, state[[2, src[[2]]]], 2, state[[4, src[[2]]]], 3, state[[5, src[[2]]]], 4, src[[2]], _, $Failed]],
      spinDomain = Function[src, Switch[src[[1]], 1, freeSpinDomains[[src[[2]]]], 2, stateSpinDomains[[src[[2]]]], _, {}]],
      vectorDomain = Function[src, Switch[src[[1]], 1, freeVectorDomains[[src[[2]]]], 2, stateVectorDomains[[src[[2]]]], 3, dummyDomains[[src[[2]]]], 4, {src[[2]]}, _, {}]]
    },
    Module[{setSpin, setVector, fillFree, factorChoices, search},
      setSpin[state_, src_, value_] := Module[{current = spinValue[src, state]},
        Which[
          current === value, state,
          current =!= None, $Failed,
          src[[1]] === 1, ReplacePart[state, {1, src[[2]]} -> value],
          src[[1]] === 2, ReplacePart[state, {3, src[[2]]} -> value],
          True, $Failed
        ]
      ];
      setVector[state_, src_, value_] := Module[{current = vectorValue[src, state]},
        Which[
          current === value, state,
          current =!= None, $Failed,
          src[[1]] === 1, ReplacePart[state, {2, src[[2]]} -> value],
          src[[1]] === 2, ReplacePart[state, {4, src[[2]]} -> value],
          src[[1]] === 3, ReplacePart[state, {5, src[[2]]} -> value],
          src[[1]] === 4 && src[[2]] === value, state,
          True, $Failed
        ]
      ];
      fillFree[state_] := {
        Developer`ToPackedArray @ MapThread[If[#1 === None, First[#2], #1] &, {state[[1]], freeSpinDomains}],
        Developer`ToPackedArray @ MapThread[If[#1 === None, First[#2], #1] &, {state[[2]], freeVectorDomains}]
      };
      factorChoices[factor_, state_, tag_] := Module[
        {left, right, desc, matrix, unresolved, pairs},
        Switch[factor[[1]],
          0,
          left = vectorValue[factor[[2]], state];
          right = vectorValue[factor[[3]], state];
          Which[
            left === right && left =!= None, None,
            left =!= None && right =!= None, $Failed,
            left =!= None, {setVector[state, factor[[3]], left]},
            right =!= None, {setVector[state, factor[[2]], right]},
            factor[[2]] === factor[[3]], None,
            True, DeleteCases[setVector[setVector[state, factor[[2]], #], factor[[3]], #] & /@ spinProjectionSeededOrder[Intersection[vectorDomain[factor[[2]]], vectorDomain[factor[[3]]]], {seed, serial}, tag], $Failed]
          ],
          1,
          left = spinValue[factor[[2]], state];
          right = spinValue[factor[[3]], state];
          Which[
            left === right && left =!= None, None,
            left =!= None && right =!= None, $Failed,
            left =!= None, {setSpin[state, factor[[3]], left]},
            right =!= None, {setSpin[state, factor[[2]], right]},
            factor[[2]] === factor[[3]], None,
            True, DeleteCases[setSpin[setSpin[state, factor[[2]], #], factor[[3]], #] & /@ spinProjectionSeededOrder[Intersection[spinDomain[factor[[2]]], spinDomain[factor[[3]]]], {seed, serial}, tag], $Failed]
          ],
          2,
          desc = factor[[4]];
          matrix = spinProjectionConcreteGammaSparseMatrix[desc, state[[2]], state[[4]], state[[5]]];
          If[matrix === $Failed,
            unresolved = DeleteDuplicates @ Select[desc[[3]], vectorValue[#, state] === None &];
            If[unresolved === {}, Return[$Failed]];
            With[{src = First @ spinProjectionSeededOrder[unresolved, {seed, serial}, {"gammaVector", tag}]},
              DeleteCases[setVector[state, src, #] & /@ vectorDomain[src], $Failed]
            ],
            left = spinValue[factor[[2]], state];
            right = spinValue[factor[[3]], state];
            Which[
              IntegerQ[left] && IntegerQ[right], If[matrix[[left, right]] === 0, $Failed, None],
              IntegerQ[left], DeleteCases[setSpin[state, factor[[3]], #] & /@ spinProjectionSeededOrder[Flatten[Position[Normal[Unitize[matrix[[left, All]]]], 1]], {seed, serial}, {"gammaRight", tag, left}], $Failed],
              IntegerQ[right], DeleteCases[setSpin[state, factor[[2]], #] & /@ spinProjectionSeededOrder[Flatten[Position[Normal[Unitize[matrix[[All, right]]]], 1]], {seed, serial}, {"gammaLeft", tag, right}], $Failed],
              True,
              pairs = First /@ Most[ArrayRules[matrix]];
              DeleteCases[
                Map[
                  Function[pair, setSpin[setSpin[state, factor[[2]], pair[[1]]], factor[[3]], pair[[2]]]],
                  spinProjectionSeededOrder[pairs, {seed, serial}, {"gammaPair", tag}]
                ],
                $Failed
              ]
            ]
          ],
          _, None
        ]
      ];
      search[state_] := Catch[Module[{choices, active, best, result},
        choices = MapIndexed[{First[#2], factorChoices[#1, state, First[#2]]} &, term["Parts"]];
        If[AnyTrue[choices, Last[#] === $Failed &], Return[$Failed]];
        active = Select[choices, ListQ[Last[#]] &];
        If[active === {}, Return[fillFree[state]]];
        best = First @ MinimalBy[active, Length[Last[#]] &];
        Do[
          result = search[nextState];
          If[result =!= $Failed, Throw[result]],
          {nextState, best[[2]]}
        ];
        $Failed
      ]];
      search[assignment]
    ]
  ]
];

spinProjectionAssignmentIterator::usage =
  "spinProjectionAssignmentIterator[model, seed] returns a zero-argument function that lazily enumerates compiled probe assignments without replacement, or $Failed when the search space is too large.";
spinProjectionAssignmentIterator[model_Association, seed_] := Module[
  {
    maxCount = spinProjectionCompiledCandidateLimit,
    termPool = spinProjectionProbeTermPool[model],
    termOrder,
    yielded = 0,
    seen = <||>,
    serial = 0,
    maxTrials,
    next,
    choice,
    candidate,
    key
  },
  If[termPool === {}, Return[Function[{}, EndOfFile]]];
  termOrder = spinProjectionSeededOrder[Range[Length[termPool]], seed, "probeTerms"];
  maxTrials = maxCount Length[termPool];
  next[] := Module[{},
    While[yielded < maxCount && serial < maxTrials,
      choice = termPool[[termOrder[[1 + Mod[serial, Length[termPool]]]]]];
      candidate = spinProjectionWitnessAssignment[model, choice[[1]], choice[[2]], seed, 1 + Quotient[serial, Length[termPool]]];
      serial++;
      If[candidate === $Failed, Continue[]];
      key = HoldComplete @@ (Normal /@ candidate);
      If[KeyExistsQ[seen, key], Continue[]];
      seen[key] = True;
      yielded++;
      Return[candidate]
    ];
    EndOfFile
  ];
  next
];

End[];


EndPackage[];
