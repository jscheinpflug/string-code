(* ::Package:: *)

BeginPackage["StringCode`OPE`TypeII`FlatSpace`SpinProjection`TestSupport`"];
Needs["StringCode`OPE`TypeII`FlatSpace`SpinProjection`Compile`"];
Needs["StringCode`OPE`TypeII`FlatSpace`SpinProjection`Solve`"];
Needs["StringCode`OPE`TypeII`FlatSpace`GammaMatrices`GammaProductGrammar`"];

spinProjectionSemanticSectorCheck::usage =
  "spinProjectionSemanticSectorCheck[artifact, seed, opts] runs solve/pool/select/witness semantic checks for one sector artifact and returns detailed diagnostics.";
spinProjectionSemanticSectorCheck[artifact_, seed_, opts___Rule] := Private`spinProjectionSemanticSectorCheck0[artifact, seed, opts];

spinProjectionSemanticCaseCheck::usage =
  "spinProjectionSemanticCaseCheck[ops, wH, wA, seed, opts] builds artifacts, solves spin sectors, selects sparse witnesses, and returns detailed semantic regression results.";
spinProjectionSemanticCaseCheck[ops_, wH_, wA_, seed_, opts___Rule] := Private`spinProjectionSemanticCaseCheck0[ops, wH, wA, seed, opts];

spinProjectionWitnessPool::usage =
  "spinProjectionWitnessPool[artifact, seed, opts] builds a sparse nonzero witness pool using the artifact support machinery.";
spinProjectionWitnessPool[artifact_, seed_, opts___Rule] := Private`spinProjectionWitnessPool0[artifact, seed, opts];

spinProjectionSelectCoverageWitnesses::usage =
  "spinProjectionSelectCoverageWitnesses[artifact, pool, opts] greedily selects a small witness set that covers all reachable columns and all families.";
spinProjectionSelectCoverageWitnesses[artifact_, pool_, opts___Rule] := Private`spinProjectionSelectCoverageWitnesses0[artifact, pool, opts];

spinProjectionColumnFaithfulnessCheck::usage =
  "spinProjectionColumnFaithfulnessCheck[artifact, witnesses] compares symbolic columns against compiled term semantics on fixed witnesses.";
spinProjectionColumnFaithfulnessCheck[artifact_, witnesses_List] := Private`spinProjectionColumnFaithfulnessCheck0[artifact, witnesses];

Begin["Private`"];

(* ===== Scalar Evaluation ===== *)

spinProjectionTestCoordinateRules::usage =
  "spinProjectionTestCoordinateRules[n] returns the deterministic coordinate substitution rules used by semantic witness tests.";
spinProjectionTestCoordinateRules[n_Integer?NonNegative] := Module[
  {width = Max[n, 10], baseSymbols, numberedSymbols, values},
  baseSymbols = {z, w, u, v, t, zb, wb, ub, vb, tb};
  numberedSymbols = Join[
    Table[Symbol["z" <> ToString[i]], {i, width}],
    Table[Symbol["w" <> ToString[i]], {i, width}],
    Table[Symbol["u" <> ToString[i]], {i, width}]
  ];
  values = Prime /@ Range[Length[baseSymbols] + Length[numberedSymbols]];
  Thread[Join[baseSymbols, numberedSymbols] -> values]
];

spinProjectionConcreteGammaFactorValue0::usage =
  "spinProjectionConcreteGammaFactorValue0[factor] resolves one concrete GammaAntisymmetricProductHold factor to its exact scalar value when possible.";
spinProjectionConcreteGammaFactorValue0[factor_] := Module[{value},
  If[SymbolName[Head[factor]] =!= "GammaAntisymmetricProductHold", Return[factor]];
  value = spinProjectionGammaFactorValue[factor];
  If[SymbolName[Head[value]] =!= "GammaAntisymmetricProductHold", value, factor]
];

spinProjectionEvaluateTensorScalars0::usage =
  "spinProjectionEvaluateTensorScalars0[expr] evaluates concrete gamma factors and deltas in one tensor scalar expression.";
spinProjectionEvaluateTensorScalars0[expr_] := Expand[expr /. {
  factor_ /; SymbolName[Head[factor]] === "GammaAntisymmetricProductHold" :> spinProjectionConcreteGammaFactorValue0[factor],
  factor_ /; SymbolName[Head[factor]] === "\[Delta]" && Length[factor] == 2 :> KroneckerDelta[factor[[1]], factor[[2]]]
}];

spinProjectionEvaluateSummedTensorScalars0::usage =
  "spinProjectionEvaluateSummedTensorScalars0[expr] sums dummy vectors over 1..10 and evaluates remaining concrete tensor scalars.";
spinProjectionEvaluateSummedTensorScalars0[expr_] := Module[{dummySyms, summed},
  dummySyms = SortBy[
    DeleteDuplicates @ Cases[
      expr,
      sym_Symbol /; TrueQ[generatedDummyVectorSymbolQ[sym]],
      Infinity
    ],
    SymbolName
  ];
  summed = Expand @ Fold[Sum[#1, {#2, 1, 10}] &, expr, dummySyms];
  spinProjectionEvaluateTensorScalars0[summed]
];

(* ===== Witness Pool And Coverage ===== *)

Seeds::usage =
  "Seeds is an option for spinProjectionWitnessPool0 that sets the deterministic candidate-seed list for sparse witness generation.";
MaxCandidatesPerSeed::usage =
  "MaxCandidatesPerSeed is an option for spinProjectionWitnessPool0 that sets the candidate cap per seed.";
MaxTuplesPerFamilyPerCandidate::usage =
  "MaxTuplesPerFamilyPerCandidate is an option for spinProjectionWitnessPool0 that sets the per-family tuple scan cap for each candidate.";
MaxWitnessesPerSeed::usage =
  "MaxWitnessesPerSeed is an option for spinProjectionWitnessPool0 that sets the witness cap per seed.";
MaxSelectedWitnesses::usage =
  "MaxSelectedWitnesses is an option for spinProjectionSelectCoverageWitnesses0 that caps greedy selected witnesses before fallback.";
FallbackSeed::usage =
  "FallbackSeed is an option for spinProjectionSelectCoverageWitnesses0 that sets the deterministic seed used by uncovered-column fallback witness generation.";
FallbackSerialLimit::usage =
  "FallbackSerialLimit is an option for spinProjectionSelectCoverageWitnesses0 that sets the serial-attempt cap per uncovered column.";

spinProjectionWitnessPoolDefaultOptions0::usage =
  "spinProjectionWitnessPoolDefaultOptions0[varCount, seed] resolves deterministic default witness-pool bounds from one artifact variable count and primary seed.";
spinProjectionWitnessPoolDefaultOptions0[varCount_Integer?NonNegative, seed_] := <|
  "Seeds" -> {seed},
  "MaxCandidatesPerSeed" -> Min[6, Max[3, varCount]],
  "MaxTuplesPerFamilyPerCandidate" -> 3,
  "MaxWitnessesPerSeed" -> Min[10, Max[5, varCount]]
|>;

spinProjectionSelectWitnessDefaultOptions0::usage =
  "spinProjectionSelectWitnessDefaultOptions0[varCount] resolves deterministic default witness-selection bounds from one artifact variable count.";
spinProjectionSelectWitnessDefaultOptions0[varCount_Integer?NonNegative] := <|
  "MaxSelectedWitnesses" -> Min[16, Max[8, 2 varCount]],
  "FallbackSeed" -> 1234,
  "FallbackSerialLimit" -> 512
|>;

spinProjectionCandidateKey0::usage =
  "spinProjectionCandidateKey0[candidate] returns a deterministic held key for one concrete {freeSpins, freeVectors} assignment.";
spinProjectionCandidateKey0[{freeSpins_List, freeVectors_List}] := HoldComplete[Normal[freeSpins], Normal[freeVectors]];

spinProjectionWitnessIdentity0::usage =
  "spinProjectionWitnessIdentity0[witness] returns the dedup identity key built from candidate, family index, tuple, and operator key.";
spinProjectionWitnessIdentity0[witness_Association] := HoldComplete[
  spinProjectionCandidateKey0[witness["Candidate"]],
  witness["FamilyIndex"],
  Normal[witness["Tuple"]],
  witness["Key"]
];

spinProjectionWitnessColumns0::usage =
  "spinProjectionWitnessColumns0[row] returns the nonzero coefficient-column indices of one compiled row.";
spinProjectionWitnessColumns0[row_List] := Flatten @ Position[row, x_ /; x =!= 0, {1}, Heads -> False];

spinProjectionStateTupleData0::usage =
  "spinProjectionStateTupleData0[family, tuple] splits one concrete tuple into packed output spin and vector state components.";
spinProjectionStateTupleData0[family_Association, tuple_List] := Module[{spinCount, stateSpins, stateVectors},
  spinCount = Length[family["SpinSymbols"]];
  stateSpins = Developer`ToPackedArray[Take[tuple, spinCount]];
  stateVectors = Developer`ToPackedArray[Drop[tuple, spinCount]];
  <|"StateSpins" -> stateSpins, "StateVectors" -> stateVectors|>
];

spinProjectionFamilyTermsForState0::usage =
  "spinProjectionFamilyTermsForState0[family, stateSpins, termBuckets] returns the active compiled terms for one family state, using support buckets when available.";
spinProjectionFamilyTermsForState0[family_Association, stateSpins_List, termBuckets_Association] := If[
  Length[family["SpinSymbols"]] == 1,
  Join[Lookup[termBuckets, 0, {}], Lookup[termBuckets, stateSpins[[1]], {}]],
  family["Terms"]
];

spinProjectionWitnessFromRow0::usage =
  "spinProjectionWitnessFromRow0[artifact, family, familyIndex, candidate, tuple, stateSpins, stateVectors, row, seed] builds one deterministic witness association from one nonzero row.";
spinProjectionWitnessFromRow0[
  artifact_Association,
  family_Association,
  familyIndex_Integer?Positive,
  candidate : {freeSpins_List, freeVectors_List},
  tuple_List,
  stateSpins_List,
  stateVectors_List,
  row_List,
  seed_
] := Module[{assoc, keyOrder, key},
  assoc = familyOutputAssociation[family, tuple];
  keyOrder = spinProjectionSeededOrder[Keys[assoc], seed, {"witnessKeys", familyIndex, tuple}];
  key = SelectFirst[keyOrder, Lookup[assoc, #, 0] =!= 0 &, Missing["NoNonzeroKey"]];
  If[MissingQ[key], Return[$Failed]];
  <|
    "Candidate" -> candidate,
    "Seed" -> seed,
    "FamilyIndex" -> familyIndex,
    "Tuple" -> tuple,
    "StateSpins" -> stateSpins,
    "StateVectors" -> stateVectors,
    "Key" -> key,
    "AssocCoeff" -> assoc[key],
    "Row" -> row,
    "CoveredColumns" -> spinProjectionWitnessColumns0[row]
  |>
];

spinProjectionFamilyKeyTupleWitnesses0::usage =
  "spinProjectionFamilyKeyTupleWitnesses0[artifact, family, familyIndex, candidate, key, coordRules, seed] enumerates all nonzero tuple witnesses in one family that contribute to the requested output key.";
spinProjectionFamilyKeyTupleWitnesses0[
  artifact_Association,
  family_Association,
  familyIndex_Integer?Positive,
  candidate : {freeSpins_List, freeVectors_List},
  key_,
  coordRules_List,
  seed_
] := Module[
  {
    nextState,
    tuple,
    tupleData,
    row,
    assoc,
    assocCoeff,
    terms,
    spinDomain,
    termBuckets,
    reaped
  },
  {spinDomain, termBuckets} = If[
    Length[family["SpinSymbols"]] == 1,
    spinProjectionFamilyOutputSpinDomain[family, candidate, seed, True],
    {spinProjectionFamilyOutputSpinDomain[family, candidate, seed], <||>}
  ];
  nextState = spinProjectionFamilyStateIterator[family, seed, spinDomain];
  reaped = Reap[
    While[True,
      tuple = nextState[];
      If[tuple === EndOfFile, Break[]];
      tuple = Reverse[tuple];
      tupleData = spinProjectionStateTupleData0[family, tuple];
      terms = spinProjectionFamilyTermsForState0[family, tupleData["StateSpins"], termBuckets];
      row = spinProjectionFamilyStateRow[
        artifact,
        family,
        candidate,
        tupleData["StateSpins"],
        tupleData["StateVectors"],
        terms
      ];
      If[row === 0 || row === $Failed, Continue[]];
      assoc = familyOutputAssociation[family, tuple];
      assocCoeff = Lookup[assoc, key, 0];
      If[assocCoeff === 0, Continue[]];
      Sow[
        <|
          "Candidate" -> candidate,
          "Seed" -> seed,
          "FamilyIndex" -> familyIndex,
          "Tuple" -> tuple,
          "StateSpins" -> tupleData["StateSpins"],
          "StateVectors" -> tupleData["StateVectors"],
          "Key" -> key,
          "AssocCoeff" -> assocCoeff,
          "Row" -> row,
          "CoveredColumns" -> spinProjectionWitnessColumns0[row],
          "CoordinateRules" -> coordRules
        |>,
        "TupleWitnesses"
      ];
    ],
    _,
    Rule
  ];
  Lookup[Association[reaped[[2]]], "TupleWitnesses", {}]
];

spinProjectionScanFamilyWitnesses0::usage =
  "spinProjectionScanFamilyWitnesses0[artifact, family, familyIndex, candidate, seed, maxTuples] scans one family lazily and returns deterministic nonzero witnesses up to the tuple cap.";
spinProjectionScanFamilyWitnesses0[
  artifact_Association,
  family_Association,
  familyIndex_Integer?Positive,
  candidate : {freeSpins_List, freeVectors_List},
  seed_,
  maxTuples_
] := Module[
  {
    nextState,
    tuple,
    tupleData,
    row,
    terms,
    spinDomain,
    termBuckets,
    tupleCount = 0,
    tupleCap = maxTuples,
    witness,
    reaped
  },
  {spinDomain, termBuckets} = If[
    Length[family["SpinSymbols"]] == 1,
    spinProjectionFamilyOutputSpinDomain[family, candidate, seed, True],
    {spinProjectionFamilyOutputSpinDomain[family, candidate, seed], <||>}
  ];
  nextState = spinProjectionFamilyStateIterator[family, seed, spinDomain];
  reaped = Reap[
    While[True,
      If[tupleCap =!= Infinity && tupleCount >= tupleCap, Break[]];
      tuple = nextState[];
      If[tuple === EndOfFile, Break[]];
      tupleCount++;
      tuple = Reverse[tuple];
      tupleData = spinProjectionStateTupleData0[family, tuple];
      terms = spinProjectionFamilyTermsForState0[family, tupleData["StateSpins"], termBuckets];
      row = spinProjectionFamilyStateRow[
        artifact,
        family,
        candidate,
        tupleData["StateSpins"],
        tupleData["StateVectors"],
        terms
      ];
      If[row === 0 || row === $Failed, Continue[]];
      witness = spinProjectionWitnessFromRow0[
        artifact,
        family,
        familyIndex,
        candidate,
        tuple,
        tupleData["StateSpins"],
        tupleData["StateVectors"],
        row,
        seed
      ];
      If[witness =!= $Failed, Sow[witness, "Witnesses"]];
    ],
    _,
    Rule
  ];
  Lookup[Association[reaped[[2]]], "Witnesses", {}]
];

spinProjectionWitnessPool0::usage =
  "spinProjectionWitnessPool0[artifact, seed, opts] builds a sparse nonzero witness pool using the artifact support machinery.";
Options[spinProjectionWitnessPool0] = {
  Seeds -> Automatic,
  MaxCandidatesPerSeed -> Automatic,
  MaxTuplesPerFamilyPerCandidate -> Automatic,
  MaxWitnessesPerSeed -> Automatic
};
spinProjectionWitnessPool0[artifact_Association, seed_, opts : OptionsPattern[]] := Module[
  {
    defaults,
    seeds,
    maxCandidates,
    maxTuples,
    maxWitnesses,
    nextCandidate,
    candidate,
    candidateCount,
    witnessCount,
    family,
    familyWitnesses,
    familyIndex,
    witnessKey,
    witnessPool = <||>
  },
  If[Lookup[artifact, "Mode", None] =!= "SpinProjection", Return[{}]];
  defaults = spinProjectionWitnessPoolDefaultOptions0[Lookup[artifact, "VarCount", 0], seed];
  seeds = Replace[
    OptionValue[Seeds],
    Automatic :> defaults["Seeds"]
  ];
  maxCandidates = Replace[OptionValue[MaxCandidatesPerSeed], Automatic -> defaults["MaxCandidatesPerSeed"]];
  maxTuples = Replace[OptionValue[MaxTuplesPerFamilyPerCandidate], Automatic -> defaults["MaxTuplesPerFamilyPerCandidate"]];
  maxWitnesses = Replace[OptionValue[MaxWitnessesPerSeed], Automatic -> defaults["MaxWitnessesPerSeed"]];
  Do[
    nextCandidate = spinProjectionAssignmentIterator[artifact, localSeed];
    If[nextCandidate === $Failed, Continue[]];
    candidateCount = 0;
    witnessCount = 0;
    While[candidateCount < maxCandidates && witnessCount < maxWitnesses,
      candidate = nextCandidate[];
      If[candidate === EndOfFile, Break[]];
      candidateCount++;
      Do[
        family = artifact["Families"][[familyIndex]];
        familyWitnesses = spinProjectionScanFamilyWitnesses0[
          artifact,
          family,
          familyIndex,
          candidate,
          localSeed,
          maxTuples
        ];
        Scan[
          Function[witness,
            witnessKey = spinProjectionWitnessIdentity0[witness];
            If[!KeyExistsQ[witnessPool, witnessKey] && witnessCount < maxWitnesses,
              witnessPool[witnessKey] = witness;
              witnessCount++;
            ]
          ],
          familyWitnesses
        ];
        If[witnessCount >= maxWitnesses, Break[]],
        {familyIndex, Length[artifact["Families"]]}
      ];
    ],
    {localSeed, seeds}
  ];
  Values[witnessPool]
];

spinProjectionCoverageCounts0::usage =
  "spinProjectionCoverageCounts0[varCount, witnesses] returns per-column witness coverage counts over the selected witness list.";
spinProjectionCoverageCounts0[varCount_Integer?NonNegative, witnesses_List] := Module[{counts},
  counts = Counts[Flatten[Lookup[witnesses, "CoveredColumns", {}]]];
  AssociationThread[Range[varCount], Lookup[counts, Range[varCount], 0]]
];

spinProjectionAddWitness0::usage =
  "spinProjectionAddWitness0[state, witness] adds one witness to the selection state if it is new and recomputes coverage counts.";
spinProjectionAddWitness0[state_Association, witness_Association] := Module[
  {id, selectedWitnesses, selectedIds},
  id = spinProjectionWitnessIdentity0[witness];
  If[KeyExistsQ[state["SelectedIDs"], id], Return[state]];
  selectedWitnesses = Append[state["SelectedWitnesses"], witness];
  selectedIds = Append[state["SelectedIDs"], id -> True];
  <|
    "VarCount" -> state["VarCount"],
    "SelectedWitnesses" -> selectedWitnesses,
    "SelectedIDs" -> selectedIds,
    "CoverageCounts" -> spinProjectionCoverageCounts0[state["VarCount"], selectedWitnesses]
  |>
];

spinProjectionWitnessScore0::usage =
  "spinProjectionWitnessScore0[witness, coverage, threshold, missingFamilies] computes deterministic greedy selection metrics for one witness.";
spinProjectionWitnessScore0[
  witness_Association,
  coverage_Association,
  threshold_Integer?Positive,
  missingFamilies_List
] := <|
  "Witness" -> witness,
  "FamilyBonus" -> If[MemberQ[missingFamilies, witness["FamilyIndex"]], 1, 0],
  "NewColumns" -> Count[witness["CoveredColumns"], col_ /; Lookup[coverage, col, 0] < threshold],
  "Width" -> Length[witness["CoveredColumns"]],
  "TieKey" -> ToString[InputForm[spinProjectionWitnessIdentity0[witness]]]
|>;

spinProjectionBestWitnessRecord0::usage =
  "spinProjectionBestWitnessRecord0[pool, selectedIds, coverage, threshold, missingFamilies] returns the best available witness-score record for one greedy step.";
spinProjectionBestWitnessRecord0[
  pool_List,
  selectedIds_Association,
  coverage_Association,
  threshold_Integer?Positive,
  missingFamilies_List
] := Module[{available, records},
  available = Select[pool, !KeyExistsQ[selectedIds, spinProjectionWitnessIdentity0[#]] &];
  records = spinProjectionWitnessScore0[#, coverage, threshold, missingFamilies] & /@ available;
  If[records === {}, Return[Missing["NoCandidate"]]];
  First @ SortBy[
    records,
    {
      -#["FamilyBonus"] &,
      -#["NewColumns"] &,
      #["Width"] &,
      #["TieKey"] &
    }
  ]
];

spinProjectionColumnTermLookup0::usage =
  "spinProjectionColumnTermLookup0[artifact, column] finds one {family, term} pair that generates the requested compiled column index.";
spinProjectionColumnTermLookup0[artifact_Association, column_Integer?Positive] := Module[{term},
  Do[
    term = SelectFirst[
      artifact["Families"][[familyIndex, "Terms"]],
      Lookup[#, "Column", 0] == column &,
      Missing["NotFound"]
    ];
    If[term =!= Missing["NotFound"],
      Return[<|"FamilyIndex" -> familyIndex, "Family" -> artifact["Families"][[familyIndex]], "Term" -> term|>]
    ],
    {familyIndex, Length[Lookup[artifact, "Families", {}]]}
  ];
  Missing["NotFound"]
];

spinProjectionFallbackWitnessForColumn0::usage =
  "spinProjectionFallbackWitnessForColumn0[artifact, column, seed, serialLimit, selectedIds] attempts targeted witness synthesis for one uncovered column and returns the first new matching witness.";
spinProjectionFallbackWitnessForColumn0[
  artifact_Association,
  column_Integer?Positive,
  seed_,
  serialLimit_Integer?Positive,
  selectedIds_Association
] := Module[
  {familyIndex = Missing["NotFound"], family = Missing["NotFound"], term = Missing["NotFound"], candidate, witnesses, witness},
  Do[
    term = SelectFirst[
      artifact["Families"][[fi, "Terms"]],
      Lookup[#, "Column", 0] == column &,
      Missing["NotFound"]
    ];
    If[term =!= Missing["NotFound"],
      familyIndex = fi;
      family = artifact["Families"][[fi]];
      Break[]
    ],
    {fi, Length[Lookup[artifact, "Families", {}]]}
  ];
  If[term === Missing["NotFound"] || MissingQ[familyIndex] || MissingQ[family], Return[Missing["NoColumnTerm"]]];
  Do[
    candidate = spinProjectionWitnessAssignment[artifact, family, term, seed, serial];
    If[candidate === $Failed, Continue[]];
    witnesses = spinProjectionScanFamilyWitnesses0[artifact, family, familyIndex, candidate, seed, Infinity];
    witness = SelectFirst[
      witnesses,
      MemberQ[Lookup[#, "CoveredColumns", {}], column] &&
        !KeyExistsQ[selectedIds, spinProjectionWitnessIdentity0[#]] &,
      Missing["NotFound"]
    ];
    If[witness =!= Missing["NotFound"], Return[witness]],
    {serial, serialLimit}
  ];
  Missing["NoFallbackWitness"]
];

spinProjectionSelectCoverageWitnesses0::usage =
  "spinProjectionSelectCoverageWitnesses0[artifact, pool, opts] greedily selects a small witness set that covers all reachable columns and all families.";
Options[spinProjectionSelectCoverageWitnesses0] = {
  MaxSelectedWitnesses -> Automatic,
  FallbackSeed -> Automatic,
  FallbackSerialLimit -> Automatic
};
spinProjectionSelectCoverageWitnesses0[artifact_Association, pool_List, opts : OptionsPattern[]] := Module[
  {
    varCount = Lookup[artifact, "VarCount", 0],
    defaults,
    maxSelected,
    fallbackSeed,
    fallbackSerialLimit,
    state,
    missingFamilies,
    missingColumns,
    record,
    fallbackWitness,
    fallbackTerm,
    fallbackFamily,
    fallbackFamilyIndex,
    fallbackCandidate,
    fallbackWitnesses,
    fallbackSelected
  },
  defaults = spinProjectionSelectWitnessDefaultOptions0[varCount];
  maxSelected = Replace[OptionValue[MaxSelectedWitnesses], Automatic -> defaults["MaxSelectedWitnesses"]];
  fallbackSeed = Replace[OptionValue[FallbackSeed], Automatic -> defaults["FallbackSeed"]];
  fallbackSerialLimit = Replace[OptionValue[FallbackSerialLimit], Automatic -> defaults["FallbackSerialLimit"]];
  state = <|
    "VarCount" -> varCount,
    "SelectedWitnesses" -> {},
    "SelectedIDs" -> <||>,
    "CoverageCounts" -> AssociationThread[Range[varCount], ConstantArray[0, varCount]]
  |>;
  missingFamilies = Complement[
    Range[Length[Lookup[artifact, "Families", {}]]],
    DeleteDuplicates[Lookup[state["SelectedWitnesses"], "FamilyIndex", {}]]
  ];
  While[missingFamilies =!= {} && Length[state["SelectedWitnesses"]] < maxSelected,
    record = spinProjectionBestWitnessRecord0[
      pool,
      state["SelectedIDs"],
      state["CoverageCounts"],
      1,
      missingFamilies
    ];
    If[MissingQ[record] || record["FamilyBonus"] == 0, Break[]];
    state = spinProjectionAddWitness0[state, record["Witness"]];
    missingFamilies = Complement[
      Range[Length[Lookup[artifact, "Families", {}]]],
      DeleteDuplicates[Lookup[state["SelectedWitnesses"], "FamilyIndex", {}]]
    ];
  ];
  missingColumns = Select[Range[varCount], Lookup[state["CoverageCounts"], #, 0] < 1 &];
  While[missingColumns =!= {} && Length[state["SelectedWitnesses"]] < maxSelected,
    record = spinProjectionBestWitnessRecord0[
      pool,
      state["SelectedIDs"],
      state["CoverageCounts"],
      1,
      {}
    ];
    If[MissingQ[record] || record["NewColumns"] == 0, Break[]];
    state = spinProjectionAddWitness0[state, record["Witness"]];
    missingColumns = Select[Range[varCount], Lookup[state["CoverageCounts"], #, 0] < 1 &];
  ];
  While[Length[state["SelectedWitnesses"]] < maxSelected,
    record = spinProjectionBestWitnessRecord0[
      pool,
      state["SelectedIDs"],
      state["CoverageCounts"],
      2,
      {}
    ];
    If[MissingQ[record] || record["NewColumns"] == 0, Break[]];
    state = spinProjectionAddWitness0[state, record["Witness"]];
  ];
  missingColumns = Select[Range[varCount], Lookup[state["CoverageCounts"], #, 0] < 1 &];
  Do[
    fallbackWitness = Missing["NoFallbackWitness"];
    fallbackTerm = Missing["NotFound"];
    fallbackFamily = Missing["NotFound"];
    fallbackFamilyIndex = Missing["NotFound"];
    Do[
      fallbackTerm = SelectFirst[
        artifact["Families"][[fi, "Terms"]],
        Lookup[#, "Column", 0] == column &,
        Missing["NotFound"]
      ];
      If[fallbackTerm =!= Missing["NotFound"],
        fallbackFamilyIndex = fi;
        fallbackFamily = artifact["Families"][[fi]];
        Break[]
      ],
      {fi, Length[Lookup[artifact, "Families", {}]]}
    ];
    If[fallbackTerm =!= Missing["NotFound"] && !MissingQ[fallbackFamilyIndex],
      Do[
        fallbackCandidate = spinProjectionWitnessAssignment[
          artifact,
          fallbackFamily,
          fallbackTerm,
          fallbackSeed,
          serial
        ];
        If[fallbackCandidate === $Failed, Continue[]];
        fallbackWitnesses = spinProjectionScanFamilyWitnesses0[
          artifact,
          fallbackFamily,
          fallbackFamilyIndex,
          fallbackCandidate,
          fallbackSeed,
          Infinity
        ];
        fallbackSelected = SelectFirst[
          fallbackWitnesses,
          MemberQ[Lookup[#, "CoveredColumns", {}], column] &&
            !KeyExistsQ[state["SelectedIDs"], spinProjectionWitnessIdentity0[#]] &,
          Missing["NotFound"]
        ];
        If[fallbackSelected =!= Missing["NotFound"],
          fallbackWitness = fallbackSelected;
          Break[]
        ],
        {serial, fallbackSerialLimit}
      ]
    ];
    If[!MissingQ[fallbackWitness], state = spinProjectionAddWitness0[state, fallbackWitness]],
    {column, missingColumns}
  ];
  missingColumns = Select[Range[varCount], Lookup[state["CoverageCounts"], #, 0] < 1 &];
  <|
    "SelectedWitnesses" -> state["SelectedWitnesses"],
    "CoverageCounts" -> state["CoverageCounts"],
    "CoveredColumns" -> Select[Range[varCount], Lookup[state["CoverageCounts"], #, 0] > 0 &],
    "DoublyCoveredColumns" -> Select[Range[varCount], Lookup[state["CoverageCounts"], #, 0] > 1 &],
    "MissingColumns" -> missingColumns,
    "CoverageCompleteQ" -> (missingColumns === {})
  |>
];

spinProjectionConcreteWitnessRules0::usage =
  "spinProjectionConcreteWitnessRules0[artifact, family, candidate, tuple, coordRules] returns free/state spin and vector substitution rules for one witness.";
spinProjectionConcreteWitnessRules0[
  artifact_Association,
  family_Association,
  candidate : {freeSpins_List, freeVectors_List},
  tuple_List,
  coordRules_List
] := Module[
  {tupleData, freeSpinRules, freeVectorRules, stateSpinRules, stateVectorRules},
  tupleData = spinProjectionStateTupleData0[family, tuple];
  freeSpinRules = MapThread[
    #1 -> spinProjectionSpinBasisState[#2][[#3]] &,
    {artifact["FreeSpinSymbols"], artifact["FreeSpinChiralities"], Normal[freeSpins]}
  ];
  freeVectorRules = Flatten @ MapThread[
    Thread[#1 -> #2] &,
    {artifact["FreeVectorGroups"], Normal[freeVectors]}
  ];
  stateSpinRules = MapThread[
    #1 -> spinProjectionSpinBasisState[#2][[#3]] &,
    {family["SpinSymbols"], family["SpinChiralities"], Normal[tupleData["StateSpins"]]}
  ];
  stateVectorRules = Thread[family["VectorSymbols"] -> Normal[tupleData["StateVectors"]]];
  Join[coordRules, freeSpinRules, freeVectorRules, stateSpinRules, stateVectorRules]
];

(* ===== Semantic Regression ===== *)

spinProjectionLHSAssociationCache0::usage =
  "spinProjectionLHSAssociationCache0 stores candidate-keyed LHS operator associations for semantic witness checks.";
spinProjectionLHSAssociationCache0 = <||>;

spinProjectionLHSAssociationCacheKey0::usage =
  "spinProjectionLHSAssociationCacheKey0[artifact, candidate] returns the memoization key used by spinProjectionLHSAssociationForCandidate0.";
spinProjectionLHSAssociationCacheKey0[artifact_Association, candidate : {freeSpins_List, freeVectors_List}] := HoldComplete[
  Lookup[artifact, "Sector", None],
  Lookup[artifact, "Weight", None],
  Lookup[artifact, "TargetWeight", None],
  Lookup[artifact, "Ops", {}],
  spinProjectionCandidateKey0[candidate]
];

spinProjectionLHSAssociationForCandidate0::usage =
  "spinProjectionLHSAssociationForCandidate0[artifact, candidate] bosonizes/projects one concrete input assignment and returns the operator association.";
spinProjectionLHSAssociationForCandidate0[artifact_Association, candidate : {freeSpins_List, freeVectors_List}] := Module[
  {cacheKey, inputs, targetWeight, lhsAssoc},
  cacheKey = spinProjectionLHSAssociationCacheKey0[artifact, candidate];
  If[KeyExistsQ[spinProjectionLHSAssociationCache0, cacheKey],
    Return[spinProjectionLHSAssociationCache0[cacheKey]]
  ];
  inputs = spinProjectionConcreteInputs[artifact, candidate];
  targetWeight = artifact["Weight"] - Total[spinProjectionExpressionWeight[#, artifact["Sector"]] & /@ inputs];
  lhsAssoc = spinProjectionOperatorAssociation[
    spinProjectionProjectInputs[artifact["Sector"], artifact["Weight"], targetWeight, inputs]
  ];
spinProjectionLHSAssociationCache0[cacheKey] = lhsAssoc;
  lhsAssoc
];

spinProjectionFamilyKeyRowCache0::usage =
  "spinProjectionFamilyKeyRowCache0 memoizes exact compiled family/key witness rows used by semantic RHS checks.";
spinProjectionFamilyKeyRowCache0 = <||>;

spinProjectionFamilyKeyRowCacheKey0::usage =
  "spinProjectionFamilyKeyRowCacheKey0[artifact, familyIndex, candidate, key, seed] returns the memoization key used by spinProjectionFamilyKeyRow0.";
spinProjectionFamilyKeyRowCacheKey0[
  artifact_Association,
  familyIndex_Integer?Positive,
  candidate : {freeSpins_List, freeVectors_List},
  key_,
  seed_
] := HoldComplete[
  Lookup[artifact, "Sector", None],
  Lookup[artifact, "Weight", None],
  Lookup[artifact, "TargetWeight", None],
  Lookup[artifact, "Ops", {}],
  familyIndex,
  spinProjectionCandidateKey0[candidate],
  key,
  seed
];

spinProjectionFamilyKeyRow0::usage =
  "spinProjectionFamilyKeyRow0[artifact, familyIndex, candidate, key, seed] returns one exact compiled coefficient row summed over all family tuples that contribute to one output key.";
spinProjectionFamilyKeyRow0[
  artifact_Association,
  familyIndex_Integer?Positive,
  candidate : {freeSpins_List, freeVectors_List},
  key_,
  seed_
] := Module[
  {
    cacheKey,
    family,
    varCount,
    nextState,
    tuple,
    tupleData,
    row,
    terms,
    assocCoeff,
    spinDomain,
    termBuckets,
    reaped,
    rowContribs,
    summedRow
  },
  cacheKey = spinProjectionFamilyKeyRowCacheKey0[artifact, familyIndex, candidate, key, seed];
  If[KeyExistsQ[spinProjectionFamilyKeyRowCache0, cacheKey],
    Return[spinProjectionFamilyKeyRowCache0[cacheKey]]
  ];
  family = artifact["Families"][[familyIndex]];
  varCount = Lookup[artifact, "VarCount", 0];
  {spinDomain, termBuckets} = If[
    Length[family["SpinSymbols"]] == 1,
    spinProjectionFamilyOutputSpinDomain[family, candidate, seed, True],
    {spinProjectionFamilyOutputSpinDomain[family, candidate, seed], <||>}
  ];
  nextState = spinProjectionFamilyStateIterator[family, seed, spinDomain];
  reaped = Reap[
    While[True,
      tuple = nextState[];
      If[tuple === EndOfFile, Break[]];
      tuple = Reverse[tuple];
      tupleData = spinProjectionStateTupleData0[family, tuple];
      terms = spinProjectionFamilyTermsForState0[family, tupleData["StateSpins"], termBuckets];
      row = spinProjectionFamilyStateRow[
        artifact,
        family,
        candidate,
        tupleData["StateSpins"],
        tupleData["StateVectors"],
        terms
      ];
      If[row === 0 || row === $Failed, Continue[]];
      assocCoeff = Lookup[familyOutputAssociation[family, tuple], key, 0];
      If[assocCoeff === 0, Continue[]];
      Sow[assocCoeff row, "Rows"];
    ],
    _,
    Rule
  ];
  rowContribs = Lookup[Association[reaped[[2]]], "Rows", {}];
  summedRow = If[rowContribs === {}, ConstantArray[0, varCount], Total[rowContribs]];
  spinProjectionFamilyKeyRowCache0[cacheKey] = summedRow;
  summedRow
];

spinProjectionColumnWitnessCoeff0::usage =
  "spinProjectionColumnWitnessCoeff0[artifact, column, family, witness] evaluates one symbolic column coefficient on one concrete witness.";
spinProjectionColumnWitnessCoeff0[
  artifact_Association,
  column_Association,
  family_Association,
  witness_Association
] := Module[{witnessRules},
  witnessRules = spinProjectionConcreteWitnessRules0[
    artifact,
    family,
    witness["Candidate"],
    witness["Tuple"],
    Lookup[witness, "CoordinateRules", {}]
  ];
  witness["AssocCoeff"] spinProjectionEvaluateSummedTensorScalars0[column["TensorExpr"] /. witnessRules]
];

spinProjectionColumnFaithfulnessCheck0::usage =
  "spinProjectionColumnFaithfulnessCheck0[artifact, witnesses] compares symbolic columns against compiled term semantics on fixed witnesses.";
spinProjectionColumnFaithfulnessCheck0[artifact_Association, witnesses_List] := Module[
  {defaultCoordRules, columns},
  defaultCoordRules = spinProjectionArtifactCoordinateRules0[artifact];
  columns = Lookup[artifact, "Columns", {}];
  Flatten @ Table[
    Module[
      {
        familyIndex,
        family,
        term,
        key,
        freeSpinsRaw,
        freeSpins,
        freeVectors,
        stateSpinsRaw,
        stateSpins,
        stateSpinIndices,
        stateVectors,
        tuple,
        candidate,
        assocCoeff,
        witnessRules,
        compiledCoeff,
        symbolicCoeff
      },
      familyIndex = Lookup[column, "FamilyIndex", 1];
      family = artifact["Families"][[familyIndex]];
      term = family["Terms"][[Lookup[column, "CandidateIndex", 1]]];
      key = Lookup[witness, "Key", Missing["NoKey"]];
      freeSpinsRaw = Lookup[witness, "FreeSpins", Lookup[witness, "Indices", {}]];
      freeSpins = spinProjectionConcreteSpinBasisIndex /@ freeSpinsRaw;
      freeVectors = Lookup[witness, "FreeVectors", ConstantArray[1, Length[artifact["FreeVectorGroups"]]]];
      stateSpinsRaw = Lookup[witness, "StateSpins", Lookup[witness, "State", {}]];
      stateSpins = If[
        Length[family["SpinSymbols"]] == 1 &&
          stateSpinsRaw =!= {} &&
          (!ListQ[stateSpinsRaw] || !AllTrue[stateSpinsRaw, ListQ[#] || IntegerQ[#] &]),
        {stateSpinsRaw},
        stateSpinsRaw
      ];
      stateSpinIndices = spinProjectionConcreteSpinBasisIndex /@ stateSpins;
      stateVectors = Lookup[witness, "StateVectors", ConstantArray[1, Length[family["VectorSymbols"]]]];
      tuple = Join[stateSpinIndices, stateVectors];
      candidate = {
        Developer`ToPackedArray[freeSpins],
        Developer`ToPackedArray[freeVectors]
      };
      If[
        key === Missing["NoKey"] ||
          MemberQ[Join[freeSpins, stateSpinIndices], $Failed] ||
          Length[freeSpins] =!= Length[artifact["FreeSpinSymbols"]] ||
          Length[stateSpinIndices] =!= Length[family["SpinSymbols"]] ||
          Length[freeVectors] =!= Length[artifact["FreeVectorGroups"]] ||
          Length[stateVectors] =!= Length[family["VectorSymbols"]],
        Return[
          <|
            "Index" -> Lookup[column, "Index", Missing["NoColumn"]],
            "Witness" -> Lookup[witness, "Name", Missing["Unnamed"]],
            "Compiled" -> $Failed,
            "Symbolic" -> $Failed,
            "MatchQ" -> False
          |>
        ]
      ];
      assocCoeff = Lookup[familyOutputAssociation[family, tuple], key, 0];
      witnessRules = spinProjectionConcreteWitnessRules0[
        artifact,
        family,
        candidate,
        tuple,
        Lookup[witness, "CoordinateRules", defaultCoordRules]
      ];
      compiledCoeff = assocCoeff spinProjectionTermValue[term, freeSpins, freeVectors, stateSpins, stateVectors];
      symbolicCoeff = assocCoeff spinProjectionEvaluateSummedTensorScalars0[column["TensorExpr"] /. witnessRules];
      <|
        "Index" -> Lookup[column, "Index", Missing["NoColumn"]],
        "Witness" -> Lookup[witness, "Name", Missing["Unnamed"]],
        "Compiled" -> compiledCoeff,
        "Symbolic" -> symbolicCoeff,
        "MatchQ" -> TrueQ[Simplify[compiledCoeff == symbolicCoeff]]
      |>
    ],
    {column, columns},
    {witness, witnesses}
  ]
];

spinProjectionRHSCoeffForWitness0::usage =
  "spinProjectionRHSCoeffForWitness0[artifact, solveResult, witness] returns the exact RHS coefficient on one witness using solved coefficients and cached compiled family/key rows.";
spinProjectionRHSCoeffForWitness0[
  artifact_Association,
  solveResult_Association,
  witness_Association
] := Module[{coordRules, familyKeyRow},
  coordRules = Lookup[witness, "CoordinateRules", {}];
  familyKeyRow = spinProjectionFamilyKeyRow0[
    artifact,
    witness["FamilyIndex"],
    witness["Candidate"],
    witness["Key"],
    Lookup[witness, "Seed", 1234]
  ];
  spinProjectionEvaluateSummedTensorScalars0[(familyKeyRow . solveResult["CoeffVector"]) /. coordRules]
];

spinProjectionSemanticWitnessCheck0::usage =
  "spinProjectionSemanticWitnessCheck0[artifact, solveResult, witness] compares exact LHS and RHS coefficients for one witness and returns a detailed association.";
spinProjectionSemanticWitnessCheck0[
  artifact_Association,
  solveResult_Association,
  witness_Association
] := Module[{lhsAssoc, lhsCoeff, familyKeyRow, rhsCoeff, matchQ},
  lhsAssoc = spinProjectionLHSAssociationForCandidate0[artifact, witness["Candidate"]];
  lhsCoeff = spinProjectionEvaluateSummedTensorScalars0[
    Lookup[lhsAssoc, witness["Key"], 0] /. Lookup[witness, "CoordinateRules", {}]
  ];
  familyKeyRow = spinProjectionFamilyKeyRow0[
    artifact,
    witness["FamilyIndex"],
    witness["Candidate"],
    witness["Key"],
    Lookup[witness, "Seed", 1234]
  ];
  rhsCoeff = spinProjectionEvaluateSummedTensorScalars0[
    (familyKeyRow . solveResult["CoeffVector"]) /. Lookup[witness, "CoordinateRules", {}]
  ];
  matchQ = TrueQ[Simplify[lhsCoeff == rhsCoeff]];
  <|
    "FamilyIndex" -> witness["FamilyIndex"],
    "Key" -> witness["Key"],
    "Candidate" -> witness["Candidate"],
    "Tuple" -> witness["Tuple"],
    "LHSCoeff" -> lhsCoeff,
    "RHSCoeff" -> rhsCoeff,
    "MatchQ" -> matchQ
  |>
];

spinProjectionArtifactCoordinateRules0::usage =
  "spinProjectionArtifactCoordinateRules0[artifact] builds deterministic coordinate substitutions for the symbols used as insertion points in one artifact.";
spinProjectionArtifactCoordinateRules0[artifact_Association] := Module[
  {coords, templateRules, templateAssoc, missing, extraAssoc},
  coords = SortBy[
    DeleteDuplicates @ Cases[
      Lookup[artifact, "Ops", {}],
      field_[___, coord_Symbol] :> coord,
      Infinity
    ],
    SymbolName
  ];
  If[coords === {}, Return[{}]];
  templateRules = spinProjectionTestCoordinateRules[Length[coords]];
  templateAssoc = Association[templateRules];
  missing = Select[coords, !KeyExistsQ[templateAssoc, #] &];
  extraAssoc = AssociationThread[missing -> (Prime /@ Range[200, 199 + Length[missing]])];
  Thread[coords -> Lookup[Join[templateAssoc, extraAssoc], coords]]
];

spinProjectionSemanticSectorCheck0::usage =
  "spinProjectionSemanticSectorCheck0[artifact, seed, opts] runs solve/pool/select/witness semantic checks for one sector artifact and returns detailed diagnostics.";
spinProjectionSemanticSectorCheck0[artifact_, seed_, opts___Rule] := Module[
  {
    solveResult,
    pool,
    extraPool = {},
    selection,
    witnessResults,
    witnesses,
    allWitnessesMatchQ,
    coordRules,
    poolOpts,
    poolOptsNoSeeds,
    selectOpts,
    selectOptsNoFallback
  },
  If[artifact === None || Lookup[artifact, "Mode", None] === "ClosedForm",
    Return[<|
      "Mode" -> Lookup[artifact, "Mode", "ClosedForm"],
      "SolveCompleteQ" -> True,
      "CoverageCompleteQ" -> True,
      "AllWitnessesMatchQ" -> True,
      "WitnessCount" -> 0,
      "CoveredColumns" -> {},
      "CoverageCounts" -> <||>,
      "MissingColumns" -> {},
      "WitnessPool" -> {},
      "SelectedWitnesses" -> {},
      "WitnessResults" -> {}
    |>]
  ];
  If[Lookup[artifact, "Mode", None] =!= "SpinProjection",
    Return[<|
      "Mode" -> Lookup[artifact, "Mode", None],
      "SolveCompleteQ" -> False,
      "CoverageCompleteQ" -> False,
      "AllWitnessesMatchQ" -> False,
      "WitnessCount" -> 0,
      "CoveredColumns" -> {},
      "CoverageCounts" -> <||>,
      "MissingColumns" -> {},
      "WitnessPool" -> {},
      "SelectedWitnesses" -> {},
      "WitnessResults" -> {}
    |>]
  ];
  poolOpts = FilterRules[{opts}, Options[spinProjectionWitnessPool0]];
  poolOptsNoSeeds = DeleteCases[poolOpts, HoldPattern[Seeds -> _]];
  selectOpts = FilterRules[{opts}, Options[spinProjectionSelectCoverageWitnesses0]];
  selectOptsNoFallback = Join[
    DeleteCases[selectOpts, HoldPattern[FallbackSerialLimit -> _]],
    {FallbackSerialLimit -> 0}
  ];
  solveResult = solveSectorArtifact[artifact, seed];
  pool = spinProjectionWitnessPool0[
    artifact,
    seed,
    Seeds -> {seed},
    Sequence @@ poolOptsNoSeeds
  ];
  selection = spinProjectionSelectCoverageWitnesses0[
    artifact,
    pool,
    Sequence @@ selectOptsNoFallback
  ];
  If[!TrueQ[selection["CoverageCompleteQ"]],
    extraPool = spinProjectionWitnessPool0[
      artifact,
      4321,
      Seeds -> {4321},
      Sequence @@ poolOptsNoSeeds
    ];
    pool = DeleteDuplicatesBy[Join[pool, extraPool], spinProjectionWitnessIdentity0];
    selection = spinProjectionSelectCoverageWitnesses0[
      artifact,
      pool,
      Sequence @@ selectOptsNoFallback
    ];
  ];
  If[!TrueQ[selection["CoverageCompleteQ"]],
    selection = spinProjectionSelectCoverageWitnesses0[
      artifact,
      pool,
      Sequence @@ selectOpts
    ];
  ];
  If[!TrueQ[solveResult["CompleteQ"]],
    Return[<|
      "Mode" -> "SpinProjection",
      "SolveResult" -> solveResult,
      "SolveCompleteQ" -> False,
      "CoverageCompleteQ" -> False,
      "AllWitnessesMatchQ" -> False,
      "WitnessCount" -> 0,
      "CoveredColumns" -> {},
      "CoverageCounts" -> Lookup[selection, "CoverageCounts", <||>],
      "MissingColumns" -> Lookup[selection, "MissingColumns", Range[Lookup[artifact, "VarCount", 0]]],
      "WitnessPool" -> pool,
      "SelectedWitnesses" -> {},
      "WitnessResults" -> {}
    |>]
  ];
  If[!TrueQ[selection["CoverageCompleteQ"]],
    Return[<|
      "Mode" -> "SpinProjection",
      "SolveResult" -> solveResult,
      "SolveCompleteQ" -> True,
      "CoverageCompleteQ" -> False,
      "AllWitnessesMatchQ" -> False,
      "WitnessCount" -> Length[selection["SelectedWitnesses"]],
      "CoveredColumns" -> selection["CoveredColumns"],
      "CoverageCounts" -> selection["CoverageCounts"],
      "MissingColumns" -> selection["MissingColumns"],
      "WitnessPool" -> pool,
      "SelectedWitnesses" -> selection["SelectedWitnesses"],
      "WitnessResults" -> {}
    |>]
  ];
  coordRules = spinProjectionArtifactCoordinateRules0[artifact];
  witnesses = (Append[#, "CoordinateRules" -> coordRules] &) /@ selection["SelectedWitnesses"];
  witnessResults = spinProjectionSemanticWitnessCheck0[artifact, solveResult, #] & /@ witnesses;
  allWitnessesMatchQ = AllTrue[witnessResults, TrueQ[Lookup[#, "MatchQ", False]] &];
  <|
    "Mode" -> "SpinProjection",
    "SolveResult" -> solveResult,
    "SolveCompleteQ" -> True,
    "CoverageCompleteQ" -> True,
    "AllWitnessesMatchQ" -> allWitnessesMatchQ,
    "WitnessCount" -> Length[witnesses],
    "CoveredColumns" -> selection["CoveredColumns"],
    "CoverageCounts" -> selection["CoverageCounts"],
    "MissingColumns" -> {},
    "WitnessPool" -> pool,
    "SelectedWitnesses" -> witnesses,
    "WitnessResults" -> witnessResults
  |>
];

spinProjectionSemanticCaseCheck0::usage =
  "spinProjectionSemanticCaseCheck0[ops, wH, wA, seed, opts] builds artifacts, solves spin sectors, selects sparse witnesses, and returns detailed semantic regression results.";
Options[spinProjectionSemanticCaseCheck0] = Join[
  Options[spinProjectionWitnessPool0],
  Options[spinProjectionSelectCoverageWitnesses0]
];
spinProjectionSemanticCaseCheck0[ops_List, wH_, wA_, seed_, opts : OptionsPattern[]] := Module[
  {artifacts, sectors, solveCompleteQ, coverageCompleteQ, allWitnessesMatchQ, witnessCount, coveredColumns},
  spinProjectionLHSAssociationCache0 = <||>;
  spinProjectionFamilyKeyRowCache0 = <||>;
  artifacts = buildProjectedArtifacts[ops, wH, wA, seed];
  sectors = <|
    "Holo" -> spinProjectionSemanticSectorCheck0[
      artifacts["Holo"],
      seed,
      Sequence @@ FilterRules[{opts}, Options[spinProjectionSemanticCaseCheck0]]
    ],
    "Anti" -> spinProjectionSemanticSectorCheck0[
      artifacts["Anti"],
      seed,
      Sequence @@ FilterRules[{opts}, Options[spinProjectionSemanticCaseCheck0]]
    ]
  |>;
  solveCompleteQ = And @@ Lookup[Values[sectors], "SolveCompleteQ", True];
  coverageCompleteQ = And @@ Lookup[Values[sectors], "CoverageCompleteQ", True];
  allWitnessesMatchQ = And @@ Lookup[Values[sectors], "AllWitnessesMatchQ", True];
  witnessCount = Total[Lookup[Values[sectors], "WitnessCount", 0]];
  coveredColumns = Association @ KeyValueMap[#1 -> Lookup[#2, "CoveredColumns", {}] &, sectors];
  <|
    "Artifacts" -> artifacts,
    "Sectors" -> sectors,
    "SolveCompleteQ" -> solveCompleteQ,
    "CoverageCompleteQ" -> coverageCompleteQ,
    "AllWitnessesMatchQ" -> allWitnessesMatchQ,
    "WitnessCount" -> witnessCount,
    "CoveredColumns" -> coveredColumns,
    "CompleteQ" -> (solveCompleteQ && coverageCompleteQ && allWitnessesMatchQ)
  |>
];

End[];

EndPackage[];
