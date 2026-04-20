(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`OPE`TypeII`FlatSpace`TensorStructures`IndependentTensorStructuresSelector`"];
Needs["StringCode`OPE`TypeII`FlatSpace`TensorStructures`CountSinglet`"];
Needs["StringCode`OPE`TypeII`FlatSpace`GammaMatrices`GammaKernelEngine`"];
Needs["StringCode`OPE`TypeII`FlatSpace`GammaMatrices`GammaProductGrammar`"];


(* ::Section:: *)
(*Logic*)


Begin["Private`"];

selectorParsedCandidateQ::usage =
  "selectorParsedCandidateQ[data] is True when data already carries the parsed selector fields used for lazy exact selection.";
selectorParsedCandidateQ[data_Association] := And @@ (KeyExistsQ[data, #] & /@ {"Expression", "Key", "ScalarFactor", "Parsed", "SpinSymbols", "SpinChiralities", "VectorSymbols", "FamilyData"});
selectorParsedCandidateQ[_] := False;

selectorParsedCandidateAnnotatedQ0::usage =
  "selectorParsedCandidateAnnotatedQ0[data] is True when one parsed selector candidate already carries stable flat-order and group-position annotations.";
selectorParsedCandidateAnnotatedQ0[data_Association] :=
  selectorParsedCandidateQ[data] && And @@ (KeyExistsQ[data, #] & /@ {"Position", "GroupIndex", "GroupMemberIndex"});
selectorParsedCandidateAnnotatedQ0[_] := False;

selectorScalarFactorQ::usage =
  "selectorScalarFactorQ[expr] is True when expr contains only scalar prefactors and no raw tensor-structure heads that must be parsed explicitly.";
selectorScalarFactorQ[expr_] := FreeQ[
  expr,
  _GammaAntisymmetricProductHold | _GammaUDHold | _GammaDUHold | CUDHold | CDUHold | _\[Delta]
];

selectorCandidateMetadata::usage =
  "selectorCandidateMetadata[candidates] returns lightweight metadata used for target-rank inference and exact probe-bank setup.";
selectorCandidateMetadata[candidates_List] := Module[{parsed},
  parsed = Which[
    candidates === {}, {},
    AllTrue[candidates, selectorParsedCandidateQ], candidates,
    True, selectorParseCandidates[candidates]
  ];
  If[parsed === $Failed, Return[$Failed]];
  Map[
    <|
      "Expression" -> #["Expression"],
      "Key" -> #["Key"],
      "SpinorChiralities" -> AssociationThread[#["SpinSymbols"] -> #["SpinChiralities"]],
      "ExternalVectors" -> #["VectorSymbols"]
    |>&,
    parsed
  ]
];

selectorPartStructuralSortKey::usage =
  "selectorPartStructuralSortKey[part] returns the structural factor key used to canonicalize one parsed candidate independently of concrete boundary labels.";
selectorPartStructuralSortKey[part_Association] := Switch[
  part["Kind"],
  "Delta",
  {0, Replace[part["VectorSymbols"], sym_Symbol /; generatedDummyVectorSymbolQ[sym] :> 0, 1]},
  "Gamma",
  {
    1,
    Replace[part["CTag"], None -> 0],
    Replace[Head /@ part["VectorLinks"], {GammaUDHold -> 1, GammaDUHold -> 2}, 1],
    Replace[part["VectorSymbols"], sym_Symbol /; generatedDummyVectorSymbolQ[sym] :> 0, 1],
    part["TailLinks"],
    part["SpinorChiralities"]
  },
  _,
  {2}
];

selectorDummySymbolSignature::usage =
  "selectorDummySymbolSignature[sym, orderedParts] returns the canonical occurrence signature used to rename selector dummy vectors consistently across equivalent explicit candidates.";
selectorDummySymbolSignature[sym_Symbol, orderedParts_List] := Cases[
  MapIndexed[
    Function[{part, factorIndex},
      Cases[
        Position[Lookup[part, "VectorSymbols", {}], sym, {1}],
        {pos_Integer} :> {
          First[factorIndex],
          pos,
          If[
            part["Kind"] === "Gamma" && pos <= Length[part["VectorLinks"]],
            Replace[Head[part["VectorLinks"][[pos]]], {GammaUDHold -> 1, GammaDUHold -> 2}],
            0
          ]
        }
      ]
    ],
    orderedParts
  ],
  {_Integer, _Integer, _Integer},
  Infinity
];

selectorCanonicalFamilySymbols::usage =
  "selectorCanonicalFamilySymbols[orderedParts] returns canonical spin, external-vector, and dummy-vector renamings for one structurally sorted parsed candidate.";
selectorCanonicalFamilySymbols[orderedParts_List] := Module[
  {spinSymbols, externalVectors, dummyVectors},
  spinSymbols = DeleteDuplicates @ Flatten[Lookup[orderedParts, "Spinors", {}], 1];
  externalVectors = DeleteDuplicates @ Select[
    Flatten[Lookup[orderedParts, "VectorSymbols", {}], 1],
    Head[#] === Symbol && !generatedDummyVectorSymbolQ[#] &
  ];
  dummyVectors = SortBy[
    DeleteDuplicates @ Select[
      Flatten[Lookup[orderedParts, "VectorSymbols", {}], 1],
      generatedDummyVectorSymbolQ
    ],
    selectorDummySymbolSignature[#, orderedParts] &
  ];
  <|
    "SpinRules" -> AssociationThread[
      spinSymbols,
      Table[Symbol["StringCode`OPE`TypeII`FlatSpace`TensorStructures`IndependentTensorStructuresSelector`selectorSpin" <> ToString[i]], {i, Length[spinSymbols]}]
    ],
    "VectorRules" -> AssociationThread[
      externalVectors,
      Table[Symbol["StringCode`OPE`TypeII`FlatSpace`TensorStructures`IndependentTensorStructuresSelector`selectorVector" <> ToString[i]], {i, Length[externalVectors]}]
    ],
    "DummyRules" -> AssociationThread[
      dummyVectors,
      Table[Symbol["StringCode`OPE`TypeII`FlatSpace`TensorStructures`IndependentTensorStructuresSelector`selectorDummy" <> ToString[i]], {i, Length[dummyVectors]}]
    ]
  |>
];

selectorCanonicalFamilyData::usage =
  "selectorCanonicalFamilyData[parsed] canonicalizes one parsed tensor-factor candidate to a representative family expression plus actual-to-representative symbol maps.";
selectorCanonicalFamilyData[parsed_Association] := Module[
  {orderedParts, symbolData, rules, canonicalParts, canonicalFactors, spinRules, vectorRules, canonicalExpr},
  orderedParts = SortBy[parsed["FactorParts"], selectorPartStructuralSortKey];
  symbolData = selectorCanonicalFamilySymbols[orderedParts];
  spinRules = symbolData["SpinRules"];
  vectorRules = Join[symbolData["VectorRules"], symbolData["DummyRules"]];
  rules = Join[spinRules, vectorRules];
  canonicalParts = orderedParts /. Normal[rules];
  canonicalFactors = syntheticFactorFromParts /@ canonicalParts;
  If[MemberQ[canonicalFactors, $Failed], Return[$Failed]];
  canonicalExpr = If[canonicalFactors === {}, 1, Times @@ canonicalFactors];
  <|
    "Expression" -> canonicalExpr,
    "Parsed" -> <|
      "Expression" -> canonicalExpr,
      "Key" -> candidateCacheKey[canonicalExpr],
      "Factors" -> canonicalFactors,
      "FactorParts" -> canonicalParts,
      "SpinorChiralities" -> candidateSpinorChiralities[canonicalParts],
      "ExternalVectors" -> SortBy[Values[symbolData["VectorRules"]], SymbolName]
    |>,
    "CanonicalToActualSpin" -> Association[Reverse /@ Normal[spinRules]],
    "CanonicalToActualVector" -> Association[Reverse /@ Normal[symbolData["VectorRules"]]]
  |>
];

selectorCandidateParseData::usage =
  "selectorCandidateParseData[expr] parses one tensor-structure candidate without compiling gamma kernels, returning the data needed for lazy exact selection.";
selectorCandidateParseData[data_Association] /; selectorParsedCandidateQ[data] := data;
selectorCandidateParseData[candidate_Association, spinorHints_: <||>] := If[
  KeyExistsQ[candidate, "Expression"],
  selectorCandidateParseData[candidate["Expression"], spinorHints],
  $Failed
];

selectorApplySpinorChiralityHints::usage =
  "selectorApplySpinorChiralityHints[parsed, spinorHints] rewrites ambiguous zero-link gamma metadata using known external spinor chiralities.";
selectorApplySpinorChiralityHints[parsed_Association, spinorHints_Association] := Module[{parts},
  If[spinorHints === <||>, Return[parsed]];
  parts = parsed["FactorParts"] /. part_Association /; Lookup[part, "Kind", None] === "Gamma" &&
      Lookup[part, "CTag", None] === None &&
      Lookup[part, "VectorLinks", {}] === {} &&
      Lookup[part, "TailLinks", {}] === {} &&
      AllTrue[Lookup[part, "Spinors", {}], Head[#] === Symbol && KeyExistsQ[spinorHints, #] &] :>
    Join[part, <|"SpinorChiralities" -> (Lookup[spinorHints, #] & /@ part["Spinors"])|>];
  Join[
    parsed,
    <|
      "FactorParts" -> parts,
      "SpinorChiralities" -> candidateSpinorChiralities[parts]
    |>
  ]
];

selectorCandidateParseData[expr_, spinorHints_: <||>] := Module[
  {
    factors,
    tensorFactors,
    scalarFactor,
    parsed,
    factorSymbols,
    spinSymbols,
    spinChiralities,
    vectorSymbols,
    familyData
  },
  factors = If[Head[expr] === Times, List @@ expr, {expr}];
  tensorFactors = Select[factors, candidateFactorQ];
  scalarFactor = Times @@ Select[factors, !candidateFactorQ[#] &];
  If[tensorFactors === {} && !AtomQ[expr] && !MemberQ[{Plus, Times, Power}, Head[expr]], Return[$Failed]];
  If[!selectorScalarFactorQ[scalarFactor], Return[$Failed]];
  parsed = If[tensorFactors === {}, parseCandidate[1], parseCandidate[Times @@ tensorFactors]];
  If[parsed === $Failed, Return[$Failed]];
  parsed = selectorApplySpinorChiralityHints[parsed, spinorHints];
  factorSymbols = DeleteDuplicates @ Select[
    Join[
      Flatten[Lookup[parsed["FactorParts"], "VectorSymbols", {}]],
      Flatten[Lookup[parsed["FactorParts"], "Spinors", {}]]
    ],
    Head[#] === Symbol &
  ];
  If[factorSymbols =!= {} && !FreeQ[scalarFactor, Alternatives @@ factorSymbols], Return[$Failed]];
  spinSymbols = SortBy[Keys[parsed["SpinorChiralities"]], SymbolName];
  spinChiralities = Lookup[parsed["SpinorChiralities"], spinSymbols];
  vectorSymbols = SortBy[Lookup[parsed, "ExternalVectors", {}], SymbolName];
  familyData = selectorCanonicalFamilyData[parsed];
  If[familyData === $Failed, Return[$Failed]];
  <|
    "Expression" -> expr,
    "Key" -> candidateCacheKey[expr],
    "ScalarFactor" -> scalarFactor,
    "Parsed" -> parsed,
    "SpinSymbols" -> spinSymbols,
    "SpinChiralities" -> spinChiralities,
    "VectorSymbols" -> vectorSymbols,
    "FamilyData" -> familyData
  |>
];

selectorParseCandidates::usage =
  "selectorParseCandidates[candidates] parses one explicit candidate list without compiling gamma kernels.";
selectorParseCandidates[candidates_List, spinorHints_: <||>] := Module[{parsed},
  parsed = selectorCandidateParseData[#, spinorHints] & /@ candidates;
  If[MemberQ[parsed, $Failed], $Failed, parsed]
];

selectorCandidates::usage =
  "selectorCandidates[candidates] parses one explicit candidate list into reusable selector data.";
selectorCandidates[candidates_List, spinorHints_: <||>] := selectorParseCandidates[candidates, spinorHints];

selectorSpinorMap::usage =
  "selectorSpinorMap[candidates] returns the merged spinor chirality assignment carried by one parsed selector candidate list.";
selectorSpinorMap[candidates_List] := If[
  candidates === {},
  <||>,
  Merge[
    Flatten[Map[MapThread[Rule, {#["SpinSymbols"], #["SpinChiralities"]}] &, candidates], 1],
    First
  ]
];

selectorSpinorMapFromParsed::usage =
  "selectorSpinorMapFromParsed[candidates] returns the merged spinor chirality assignment carried by parsed selector candidates.";
selectorSpinorMapFromParsed[candidates_List] := selectorSpinorMap[candidates];

automaticCandidateTargetRank::usage =
  "automaticCandidateTargetRank[candidates] infers an exact singlet-count upper bound from candidate spinor chiralities and external vectors.";
automaticCandidateTargetRank[candidates_List, spinorHints_: <||>] := Module[{parsed, chiralityMap, nVectors, counts, flipped},
  parsed = selectorCandidates[candidates, spinorHints];
  If[parsed === $Failed || parsed === {}, Return[0]];
  chiralityMap = selectorSpinorMap[parsed];
  nVectors = Length[DeleteDuplicates[Flatten[parsed[[All, "VectorSymbols"]], 1]]];
  counts = {
    countSinglets[Count[Values[chiralityMap], "chiral"], Count[Values[chiralityMap], "antichiral"], nVectors]
  };
  counts = Join[
    counts,
    Table[
      flipped = Join[chiralityMap, <|sym -> If[chiralityMap[sym] === "chiral", "antichiral", "chiral"]|>];
      countSinglets[Count[Values[flipped], "chiral"], Count[Values[flipped], "antichiral"], nVectors],
      {sym, Keys[chiralityMap]}
    ]
  ];
  counts = Select[counts, Positive];
  If[counts === {}, 0, Min[counts]]
];

automaticParsedCandidateTargetRank::usage =
  "automaticParsedCandidateTargetRank[candidates] infers the exact target rank directly from parsed candidate metadata without further compilation.";
automaticParsedCandidateTargetRank[candidates_List] := Module[{chiralityMap, nVectors, counts, flipped},
  If[candidates === {}, Return[0]];
  chiralityMap = selectorSpinorMapFromParsed[candidates];
  nVectors = Length[DeleteDuplicates[Flatten[candidates[[All, "VectorSymbols"]], 1]]];
  counts = {
    countSinglets[Count[Values[chiralityMap], "chiral"], Count[Values[chiralityMap], "antichiral"], nVectors]
  };
  counts = Join[
    counts,
    Table[
      flipped = Join[chiralityMap, <|sym -> If[chiralityMap[sym] === "chiral", "antichiral", "chiral"]|>];
      countSinglets[Count[Values[flipped], "chiral"], Count[Values[flipped], "antichiral"], nVectors],
      {sym, Keys[chiralityMap]}
    ]
  ];
  counts = Select[counts, Positive];
  If[counts === {}, 0, Min[counts]]
];

selectorProbeChoices::usage =
  "selectorProbeChoices[] returns the small exact component values used in deterministic dense selector probes.";
selectorProbeChoices[] := {-2 - I, -2 + I, -1 - I, -1 + I, 1 - I, 1 + I, 2 - I, 2 + I, -3, 3};

selectorKSparseProbeChoices::usage =
  "selectorKSparseProbeChoices[] returns the integer-only component values used in deterministic k-sparse selector probes.";
selectorKSparseProbeChoices[] := {-2, -1, 1, 2};

buildDeterministicDenseProbe::usage =
  "buildDeterministicDenseProbe[spinorSymbols, externalVectors, baseSeed, probeIndex, salt] builds one deterministic dense probe stream distinguished by salt.";
buildDeterministicDenseProbe[spinorSymbols_List, externalVectors_List, baseSeed_, probeIndex_Integer?Positive, salt_String] := BlockRandom[
  SeedRandom[Hash[{Replace[baseSeed, Automatic -> 0], probeIndex, spinorSymbols, externalVectors, salt}]];
  <|
    "SpinorComponents" -> AssociationThread[
      spinorSymbols,
      Table[RandomChoice[selectorProbeChoices[], 16], {Length[spinorSymbols]}]
    ],
    "VectorComponents" -> AssociationThread[
      externalVectors,
      Table[RandomChoice[selectorProbeChoices[], 10], {Length[externalVectors]}]
    ]
  |>
];

buildDenseProbe::usage =
  "buildDenseProbe[spinorSymbols, externalVectors, baseSeed, probeIndex] builds one deterministic dense selector probe in the default dense stream.";
buildDenseProbe[spinorSymbols_List, externalVectors_List, baseSeed_, probeIndex_Integer?Positive] :=
  buildDeterministicDenseProbe[spinorSymbols, externalVectors, baseSeed, probeIndex, "selectorDenseProbe"];

buildWideDenseProbe::usage =
  "buildWideDenseProbe[spinorSymbols, externalVectors, baseSeed, probeIndex] builds one deterministic dense selector probe in the fallback dense stream.";
buildWideDenseProbe[spinorSymbols_List, externalVectors_List, baseSeed_, probeIndex_Integer?Positive] :=
  buildDeterministicDenseProbe[spinorSymbols, externalVectors, baseSeed, probeIndex, "selectorWideDenseProbe"];

buildKSparseSpinVector::usage =
  "buildKSparseSpinVector[kValue] builds one exact 16-component spin vector with exactly kValue nonzero entries, capped at 16.";
buildKSparseSpinVector[kValue_Integer?Positive] := Module[{effectiveK, positions, values, vec},
  effectiveK = Min[kValue, 16];
  vec = ConstantArray[0, 16];
  positions = RandomSample[Range[16], effectiveK];
  values = RandomChoice[selectorKSparseProbeChoices[], effectiveK];
  vec[[positions]] = values;
  vec
];

buildKSparseProbe::usage =
  "buildKSparseProbe[spinorSymbols, externalVectors, baseSeed, probeIndex, kValue] builds one deterministic sparse-first selector probe.";
buildKSparseProbe[spinorSymbols_List, externalVectors_List, baseSeed_, probeIndex_Integer?Positive, kValue_Integer?Positive] := BlockRandom[
  SeedRandom[Hash[{Replace[baseSeed, Automatic -> 0], probeIndex, spinorSymbols, externalVectors, "selectorKSparseProbe"}]];
  <|
    "SpinorComponents" -> AssociationThread[
      spinorSymbols,
      Table[buildKSparseSpinVector[kValue], {Length[spinorSymbols]}]
    ],
    "VectorComponents" -> AssociationThread[
      externalVectors,
      Table[RandomChoice[selectorProbeChoices[], 10], {Length[externalVectors]}]
    ]
  |>
];

selectorProbeAssignment::usage =
  "selectorProbeAssignment[spinorSymbols, externalVectors, baseSeed, probeIndex, kValue, prefixCount, denseCount] builds one deterministic selector probe from the sparse-first schedule.";
selectorProbeAssignment[
  spinorSymbols_List,
  externalVectors_List,
  baseSeed_,
  probeIndex_Integer?Positive,
  kValue_Integer?Positive,
  prefixCount_Integer?NonNegative,
  denseCount_Integer?NonNegative
] := Which[
  probeIndex <= prefixCount,
  buildKSparseProbe[spinorSymbols, externalVectors, baseSeed, probeIndex, kValue],
  probeIndex <= prefixCount + denseCount,
  buildDenseProbe[spinorSymbols, externalVectors, baseSeed, probeIndex],
  True,
  buildWideDenseProbe[spinorSymbols, externalVectors, baseSeed, probeIndex]
];

buildProbeBank::usage =
  "buildProbeBank[spinorSymbols, externalVectors, count, seed, kValue, prefixCount, denseCount] builds a deterministic list of scheduled selector probes.";
buildProbeBank[
  spinorSymbols_List,
  externalVectors_List,
  count_Integer?NonNegative,
  seed_,
  kValue_Integer?Positive : 4,
  prefixCount_Integer?NonNegative : 0,
  denseCount_Integer?NonNegative : 50
] := Table[
  selectorProbeAssignment[spinorSymbols, externalVectors, seed, i, kValue, prefixCount, denseCount],
  {i, 1, count}
];

initialPivotState::usage =
  "initialPivotState[] constructs an empty incremental exact pivot state.";
initialPivotState[] := <|"Rows" -> {}, "PivotColumns" -> {}|>;

incrementalPivotInsert::usage =
  "incrementalPivotInsert[state, row] inserts one exact signature row into an incremental row-echelon state.";
incrementalPivotInsert[state_Association, row_List] := Module[
  {reducedRow, rows, pivots, pivotPos, pivotValue, insertPos, newRows, newPivots, i, rowLength, existingLength},
  reducedRow = row;
  rows = state["Rows"];
  pivots = state["PivotColumns"];
  rowLength = Length[reducedRow];
  If[rows =!= {},
    existingLength = Length[rows[[1]]];
    If[existingLength < rowLength, rows = (PadRight[#, rowLength] &) /@ rows];
    If[existingLength > rowLength, reducedRow = PadRight[reducedRow, existingLength]];
  ];
  For[i = 1, i <= Length[rows], i++,
    If[reducedRow[[pivots[[i]]]] =!= 0, reducedRow = Expand[reducedRow - reducedRow[[pivots[[i]]]] rows[[i]]]];
  ];
  pivotPos = FirstCase[Range[Length[reducedRow]], j_ /; reducedRow[[j]] =!= 0 :> j, Missing["NoPivot"]];
  If[pivotPos === Missing["NoPivot"], Return[<|"State" -> <|"Rows" -> rows, "PivotColumns" -> pivots|>, "RankIncreased" -> False|>]];
  pivotValue = reducedRow[[pivotPos]];
  reducedRow = Expand[reducedRow/pivotValue];
  newRows = rows;
  For[i = 1, i <= Length[newRows], i++,
    If[newRows[[i, pivotPos]] =!= 0, newRows[[i]] = Expand[newRows[[i]] - newRows[[i, pivotPos]] reducedRow]];
  ];
  insertPos = Count[pivots, _?(# < pivotPos &)] + 1;
  newRows = Insert[newRows, reducedRow, insertPos];
  newPivots = Insert[pivots, pivotPos, insertPos];
  <|"State" -> <|"Rows" -> newRows, "PivotColumns" -> newPivots|>, "RankIncreased" -> True|>
];

selectionRuntimeFromMetadata::usage =
  "selectionRuntimeFromMetadata[candidateMetadataList, optsAssoc, targetRank] initializes exact selector runtime state from metadata only.";
selectionRuntimeFromMetadata[candidateMetadataList_List, optsAssoc_Association, targetRank_Integer?NonNegative] := Module[
  {
    spinorMap,
    spinorSymbols,
    spinorSymbolIndex,
    vectorSymbols,
    probeCount,
    verificationCount,
    seed,
    sparseProbeKValue,
    sparseProbePrefixCount,
    denseFallbackProbeCount
  },
  spinorMap = If[candidateMetadataList === {}, <||>, Merge[Lookup[candidateMetadataList, "SpinorChiralities", <||>], First]];
  spinorSymbols = SortBy[Keys[spinorMap], SymbolName];
  spinorSymbolIndex = AssociationThread[spinorSymbols -> Range[Length[spinorSymbols]]];
  vectorSymbols = If[candidateMetadataList === {}, {}, SortBy[DeleteDuplicates[Flatten[Lookup[candidateMetadataList, "ExternalVectors", {}], 1]], SymbolName]];
  probeCount = Max[Lookup[optsAssoc, "ProbeCount", 5], targetRank];
  verificationCount = Max[0, Lookup[optsAssoc, "VerificationProbeCount", 3]];
  seed = Lookup[optsAssoc, "RandomSeed", Automatic];
  sparseProbeKValue = Lookup[optsAssoc, "SparseProbeKValue", 4];
  sparseProbePrefixCount = Replace[Lookup[optsAssoc, "SparseProbePrefixCount", Automatic], Automatic -> (3 targetRank + 20)];
  denseFallbackProbeCount = Replace[Lookup[optsAssoc, "DenseFallbackProbeCount", 50], Automatic -> 50];
  <|
    "SpinorSymbols" -> spinorSymbols,
    "SpinorSymbolIndex" -> spinorSymbolIndex,
    "SpinorChiralities" -> spinorMap,
    "SpinorBanksByIndex" -> ConstantArray[{}, Length[spinorSymbols]],
    "VectorSymbols" -> vectorSymbols,
    "BaseSeed" -> seed,
    "Assignments" -> {},
    "AssignmentCount" -> 0,
    "SignatureCache" -> <||>,
    "GroupRecords" -> <||>,
    "GroupProbeCache" -> <||>,
    "TargetRank" -> targetRank,
    "SparseProbeKValue" -> sparseProbeKValue,
    "SparseProbePrefixCount" -> sparseProbePrefixCount,
    "DenseFallbackProbeCount" -> denseFallbackProbeCount,
    "InitialBankSize" -> probeCount,
    "ExtensionBankSize" -> Max[1, verificationCount],
    "VerificationBankSize" -> verificationCount
  |>
];

selectionRuntime::usage =
  "selectionRuntime[candidates, optsAssoc, targetRank] initializes exact selector runtime for one parsed candidate list.";
selectionRuntime[candidates_List, optsAssoc_Association, targetRank_Integer?NonNegative] := selectionRuntimeFromMetadata[selectorCandidateMetadata[candidates], optsAssoc, targetRank];

selectionRuntimeFromParsedCandidates::usage =
  "selectionRuntimeFromParsedCandidates[candidates, optsAssoc, targetRank] initializes exact selector runtime directly from parsed candidate metadata.";
selectionRuntimeFromParsedCandidates[candidates_List, optsAssoc_Association, targetRank_Integer?NonNegative] := Module[
  {metadata},
  metadata = Map[
    <|
      "SpinorChiralities" -> AssociationThread[#["SpinSymbols"] -> #["SpinChiralities"]],
      "ExternalVectors" -> #["VectorSymbols"]
    |>&,
    candidates
  ];
  selectionRuntimeFromMetadata[metadata, optsAssoc, targetRank]
];

selectorCandidateActualVectorSources::usage =
  "selectorCandidateActualVectorSources[candidate, compiled, ref] maps one compiled family ref to the actual candidate vector-source list used by the selector fast path.";
selectorCandidateActualVectorSources[candidate_Association, compiled_Association, ref_Association] := Module[
  {actualVectors},
  actualVectors = Lookup[candidate["FamilyData", "CanonicalToActualVector"], compiled["VectorSymbols"], Missing["Unassigned"]];
  Replace[
    ref["VectorSlots"],
    {
      {1, pos_Integer} :> actualVectors[[pos]],
      {4, pos_Integer} :> pos
    },
    1
  ]
];

selectorCandidateActualSpinSymbols::usage =
  "selectorCandidateActualSpinSymbols[candidate, compiled, ref] maps one compiled family ref to the actual candidate spin symbols used by the selector fast path.";
selectorCandidateActualSpinSymbols[candidate_Association, compiled_Association, ref_Association] := Replace[
  ref["SpinSlots"],
  {
    {1, pos_Integer} :> Lookup[
      candidate["FamilyData", "CanonicalToActualSpin"],
      compiled["SpinSymbols"][[pos]],
      Missing["Unassigned"]
    ]
  },
  1
];

selectorGroupBatchEligibleQ0::usage =
  "selectorGroupBatchEligibleQ0[groupRecord] is True when one shared-kernel selector group can extend signatures through the batched pair-matrix probe path.";
selectorGroupBatchEligibleQ0[groupRecord_Association] :=
  Lookup[groupRecord, "Mode", None] === "SharedKernelGroup" && TrueQ[Lookup[groupRecord, "BatchEligible", False]];
selectorGroupBatchEligibleQ0[_] := False;

selectorGroupSharedKernelRecord::usage =
  "selectorGroupSharedKernelRecord[group, spinorSymbolIndex] builds one selector group record for lazy group-probe reuse when every member shares the same compiled family kernel layout.";
selectorGroupSharedKernelRecord[group_List, spinorSymbolIndex_Association] := Module[
  {
    familyKeys,
    compiled,
    groupVectorSymbols,
    vectorTuples,
    memberKeys,
    memberPositions,
    memberScalars,
    memberSpinSymbolsByRef,
    uniqueSpinSymbolsByRef,
    uniqueSpinSlotIndicesByRef,
    spinPatternIndexByRef,
    memberPatternIndices,
    memberRecords,
    refModes,
    pairFactorSlotIndicesByRef,
    batchEligible
  },
  familyKeys = DeleteDuplicates[group[[All, "FamilyData", "Parsed", "Key"]]];
  If[Length[familyKeys] =!= 1, Return[<|"Mode" -> "PerCandidate"|>]];
  compiled = spinProjectionSelectorCompiledFamilyData[group[[1, "FamilyData", "Parsed"]]];
  If[
    compiled === $Failed ||
    compiled["Mode"] =!= "sharedKernel" ||
    compiled["DeltaFactors"] =!= {},
    Return[<|"Mode" -> "PerCandidate"|>]
  ];
  groupVectorSymbols = DeleteDuplicates @ Flatten[Lookup[group, "VectorSymbols", {}], 1];
  If[SortBy[groupVectorSymbols, SymbolName] =!= SortBy[compiled["VectorSymbols"], SymbolName], Return[<|"Mode" -> "PerCandidate"|>]];
  vectorTuples = selectorCandidateActualVectorSources[group[[1]], compiled, #] & /@ compiled["GammaKernelRefs"];
  If[!FreeQ[vectorTuples, Missing["Unassigned"], Infinity], Return[<|"Mode" -> "PerCandidate"|>]];
  memberKeys = group[[All, "Key"]];
  memberPositions = group[[All, "Position"]];
  memberScalars = group[[All, "ScalarFactor"]];
  memberSpinSymbolsByRef = Map[
    Function[candidate, selectorCandidateActualSpinSymbols[candidate, compiled, #] & /@ compiled["GammaKernelRefs"]],
    group
  ];
  If[!FreeQ[memberSpinSymbolsByRef, Missing["Unassigned"], Infinity], Return[<|"Mode" -> "PerCandidate"|>]];
  uniqueSpinSymbolsByRef = Table[
    DeleteDuplicates[memberSpinSymbolsByRef[[All, refIndex]]],
    {refIndex, Length[compiled["GammaKernelRefs"]]}
  ];
  uniqueSpinSlotIndicesByRef = Map[Lookup[spinorSymbolIndex, #, Missing["Unassigned"]] &, uniqueSpinSymbolsByRef, {2}];
  If[!FreeQ[uniqueSpinSlotIndicesByRef, Missing["Unassigned"], Infinity], Return[<|"Mode" -> "PerCandidate"|>]];
  spinPatternIndexByRef = AssociationThread[candidateCacheKey /@ #, Range[Length[#]]] & /@ uniqueSpinSymbolsByRef;
  memberPatternIndices = Map[
    Function[spinSymbolsByRef,
      Table[
        Lookup[spinPatternIndexByRef[[refIndex]], candidateCacheKey[spinSymbolsByRef[[refIndex]]], Missing["Unassigned"]],
        {refIndex, Length[spinSymbolsByRef]}
      ]
    ],
    memberSpinSymbolsByRef
  ];
  If[!FreeQ[memberPatternIndices, Missing["Unassigned"], Infinity], Return[<|"Mode" -> "PerCandidate"|>]];
  refModes = Map[
    Module[{kernel},
      kernel = spinProjectionGammaKernelRegistry[# ["Key"]];
      Which[
        spinProjectionGammaKernelPairMatrixQ[kernel], "paired2x2",
        Length[kernel["Factors"]] === 1 && Length[kernel["Factors"][[1, "SpinSlots"]]] === 2, "singleFactor2",
        True, "fallback"
      ]
    ]&,
    compiled["GammaKernelRefs"]
  ];
  pairFactorSlotIndicesByRef = Map[
    Module[{kernel},
      kernel = spinProjectionGammaKernelRegistry[# ["Key"]];
      If[spinProjectionGammaKernelPairMatrixQ[kernel], kernel["Factors"][[All, "SpinSlots"]], {}]
    ]&,
    compiled["GammaKernelRefs"]
  ];
  memberRecords = MapThread[
    <|
      "Key" -> #1,
      "Position" -> #2,
      "ScalarFactor" -> #3,
      "SpinSymbolsByRef" -> #4,
      "PatternIndicesByRef" -> #5
    |>&,
    {memberKeys, memberPositions, memberScalars, memberSpinSymbolsByRef, memberPatternIndices}
  ];
  batchEligible = True;
  <|
    "Mode" -> "SharedKernelGroup",
    "BatchEligible" -> batchEligible,
    "Compiled" -> compiled,
    "VectorTuples" -> vectorTuples,
    "MemberKeys" -> memberKeys,
    "MemberPositions" -> memberPositions,
    "MemberScalars" -> memberScalars,
    "MemberPatternIndices" -> memberPatternIndices,
    "UniqueSpinSymbolsByRef" -> uniqueSpinSymbolsByRef,
    "UniqueSpinSlotIndicesByRef" -> uniqueSpinSlotIndicesByRef,
    "RefModes" -> refModes,
    "PairFactorSlotIndicesByRef" -> pairFactorSlotIndicesByRef,
    "Members" -> memberRecords
  |>
];

selectorGroupRecords::usage =
  "selectorGroupRecords[groups, spinorSymbolIndex] builds the reusable group records used by the selector runtime.";
selectorGroupRecords[groups_List, spinorSymbolIndex_Association] := AssociationThread[
  Range[Length[groups]],
  selectorGroupSharedKernelRecord[#, spinorSymbolIndex] & /@ groups
];

selectionRuntimeWithParsedGroups::usage =
  "selectionRuntimeWithParsedGroups[groups, optsAssoc, targetRank] initializes exact selector runtime from parsed groups and attaches reusable group records.";
selectionRuntimeWithParsedGroups[groups_List, optsAssoc_Association, targetRank_Integer?NonNegative] := Module[
  {runtime},
  runtime = selectionRuntimeFromParsedCandidates[Flatten[groups, 1], optsAssoc, targetRank];
  AssociateTo[runtime, "GroupRecords" -> selectorGroupRecords[groups, runtime["SpinorSymbolIndex"]]];
  runtime
];

selectorAssignmentAt::usage =
  "selectorAssignmentAt[runtime, assignmentIndex] returns one deterministic selector probe from the runtime bank.";
selectorAssignmentAt[runtime_Association, assignmentIndex_Integer?Positive] := selectorProbeAssignment[
  runtime["SpinorSymbols"],
  runtime["VectorSymbols"],
  runtime["BaseSeed"],
  assignmentIndex,
  runtime["SparseProbeKValue"],
  runtime["SparseProbePrefixCount"],
  runtime["DenseFallbackProbeCount"]
];

extendAssignmentBank::usage =
  "extendAssignmentBank[runtime, count] appends count more exact dense probes to the runtime bank.";
extendAssignmentBank[runtime_Association, count_Integer?NonNegative] := Module[
  {nextRuntime = runtime, newCount, newAssignments, spinorSymbols, newSpinorBanks},
  newCount = runtime["AssignmentCount"] + count;
  If[newCount <= runtime["AssignmentCount"], Return[nextRuntime]];
  newAssignments = Table[selectorAssignmentAt[runtime, i], {i, runtime["AssignmentCount"] + 1, newCount}];
  spinorSymbols = runtime["SpinorSymbols"];
  newSpinorBanks = MapThread[
    Function[{bank, symbol},
      Join[
        bank,
        Map[Lookup[Lookup[#, "SpinorComponents", <||>], symbol, Missing["Unassigned"]] &, newAssignments]
      ]
    ],
    {runtime["SpinorBanksByIndex"], spinorSymbols}
  ];
  AssociateTo[
    nextRuntime,
    <|
      "Assignments" -> Join[runtime["Assignments"], newAssignments],
      "SpinorBanksByIndex" -> newSpinorBanks,
      "AssignmentCount" -> newCount
    |>
  ];
  nextRuntime
];

selectorGroupedCandidateInputQ::usage =
  "selectorGroupedCandidateInputQ[candidates] is True when candidates are already provided as explicit nested abstract groups.";
selectorGroupedCandidateInputQ[candidates_List] := candidates =!= {} && AllTrue[candidates, ListQ];
selectorGroupedCandidateInputQ[_] := False;

selectorAnnotateParsedCandidateGroups::usage =
  "selectorAnnotateParsedCandidateGroups[groups] adds stable flat-order and group/member positions to parsed selector candidate groups.";
selectorAnnotateParsedCandidateGroups[groups_List] := Module[{position = 0},
  MapIndexed[
    Function[{group, groupIndex},
      MapIndexed[
        Function[{candidate, memberIndex},
          position++;
          Join[
            candidate,
            <|
              "Position" -> position,
              "GroupIndex" -> First[groupIndex],
              "GroupMemberIndex" -> First[memberIndex]
            |>
          ]
        ],
        group
      ]
    ],
    groups
  ]
];

selectorParsedCandidateGroups::usage =
  "selectorParsedCandidateGroups[candidates] normalizes flat or grouped selector input to parsed candidate groups with stable flat-order positions.";
selectorParsedCandidateGroups[candidates_List, spinorHints_: <||>] := Module[{rawGroups, parsedGroups},
  If[candidates === {}, Return[{}]];
  rawGroups = If[selectorGroupedCandidateInputQ[candidates], Select[candidates, # =!= {} &], List /@ candidates];
  parsedGroups = selectorParseCandidates[#, spinorHints] & /@ rawGroups;
  If[MemberQ[parsedGroups, $Failed], Return[$Failed]];
  selectorAnnotateParsedCandidateGroups[parsedGroups]
];

selectorNormalizedParsedCandidateGroups0::usage =
  "selectorNormalizedParsedCandidateGroups0[candidates, spinorHints] reuses parsed selector groups when possible and only reparses raw input when needed.";
selectorNormalizedParsedCandidateGroups0[candidates_List, spinorHints_: <||>] := Module[{rawGroups, flattened, parsedGroups},
  If[candidates === {}, Return[{}]];
  rawGroups = If[selectorGroupedCandidateInputQ[candidates], Select[candidates, # =!= {} &], List /@ candidates];
  flattened = Flatten[rawGroups, 1];
  If[flattened === {}, Return[{}]];
  If[AllTrue[flattened, selectorParsedCandidateAnnotatedQ0], Return[rawGroups]];
  If[AllTrue[flattened, selectorParsedCandidateQ], Return[selectorAnnotateParsedCandidateGroups[rawGroups]]];
  parsedGroups = selectorParseCandidates[#, spinorHints] & /@ rawGroups;
  If[MemberQ[parsedGroups, $Failed], Return[$Failed]];
  selectorAnnotateParsedCandidateGroups[parsedGroups]
];

selectorCanonicalProbeAssignment::usage =
  "selectorCanonicalProbeAssignment[candidate, assignment] remaps one actual dense probe to the canonical representative family symbols of a parsed selector candidate.";
selectorCanonicalProbeAssignment[candidate_Association, assignment_Association] := Module[
  {parsed, canonicalSpinSymbols, canonicalVectorSymbols, actualSpinSymbols, actualVectorSymbols},
  parsed = candidate["FamilyData", "Parsed"];
  canonicalSpinSymbols = SortBy[Keys[parsed["SpinorChiralities"]], SymbolName];
  canonicalVectorSymbols = SortBy[Lookup[parsed, "ExternalVectors", {}], SymbolName];
  actualSpinSymbols = Lookup[candidate["FamilyData", "CanonicalToActualSpin"], canonicalSpinSymbols];
  actualVectorSymbols = Lookup[candidate["FamilyData", "CanonicalToActualVector"], canonicalVectorSymbols, Missing["Unassigned"]];
  <|
    "SpinorComponents" -> AssociationThread[
      canonicalSpinSymbols,
      Lookup[assignment["SpinorComponents"], actualSpinSymbols, Missing["Unassigned"]]
    ],
    "VectorComponents" -> AssociationThread[
      canonicalVectorSymbols,
      Lookup[assignment["VectorComponents"], actualVectorSymbols, Missing["Unassigned"]]
    ]
  |>
];

evaluateParsedCandidateAtProbe::usage =
  "evaluateParsedCandidateAtProbe[candidate, assignment] evaluates one parsed selector candidate on one deterministic exact dense probe through the shared gamma engine.";
evaluateParsedCandidateAtProbe[candidate_Association, assignment_Association] := Module[{canonicalProbe, value},
  If[candidate["ScalarFactor"] === 0, Return[0]];
  canonicalProbe = selectorCanonicalProbeAssignment[candidate, assignment];
  If[!FreeQ[canonicalProbe, Missing["Unassigned"], Infinity], Return[$Failed]];
  value = spinProjectionSelectorCompiledFamilyValue[
    spinProjectionSelectorCompiledFamilyData[candidate["FamilyData", "Parsed"]],
    canonicalProbe
  ];
  If[value === $Failed, Return[$Failed]];
  candidate["ScalarFactor"] value
];

selectorGroupProbeValuesReference0::usage =
  "selectorGroupProbeValuesReference0[groupRecord, assignment] is the scalar per-probe shared-kernel reference path used for parity tests and non-batched group evaluation.";
selectorGroupProbeValuesReference0[groupRecord_Association, assignment_Association] := Module[
  {compiled, refCache = <||>, refValue, memberValues},
  If[groupRecord["Mode"] =!= "SharedKernelGroup", Return[$Failed]];
  compiled = groupRecord["Compiled"];
  refValue[refIndex_Integer?Positive, spinSymbols_List] := Module[{cacheKey, spinVectors, value},
    cacheKey = {refIndex, spinSymbols};
    If[KeyExistsQ[refCache, cacheKey], Return[refCache[cacheKey]]];
    spinVectors = Lookup[assignment["SpinorComponents"], spinSymbols, Missing["Unassigned"]];
    If[!AllTrue[spinVectors, VectorQ[#, spinProjectionSelectorExactScalarQ] &], Return[$Failed]];
    value = spinProjectionGammaKernelProbeValue[
      compiled["GammaKernelRefs"][[refIndex, "Key"]],
      groupRecord["VectorTuples"][[refIndex]],
      spinVectors
    ];
    If[value === $Failed, Return[$Failed]];
    AssociateTo[refCache, cacheKey -> value];
    value
  ];
  memberValues = Association @ Map[
    Function[member,
      With[
        {
          memberValue = compiled["ScalarFactor"] member["ScalarFactor"] Times @@ Table[
            refValue[refIndex, member["SpinSymbolsByRef"][[refIndex]]],
            {refIndex, Length[compiled["GammaKernelRefs"]]}
          ]
        },
        member["Position"] -> memberValue
      ]
    ],
    groupRecord["Members"]
  ];
  If[MemberQ[Values[memberValues], $Failed], Return[$Failed]];
  memberValues
];

selectorGroupProbeValues::usage =
  "selectorGroupProbeValues[groupRecord, assignment] evaluates one reusable selector group record on one dense probe and returns all member values.";
selectorGroupProbeValues[groupRecord_Association, assignment_Association] := selectorGroupProbeValuesReference0[groupRecord, assignment];

selectorBoundaryRowsFromBanks0::usage =
  "selectorBoundaryRowsFromBanks0[spinorBanksByIndex, slotIndices, assignmentIndices] builds exact boundary rows directly from the runtime spinor banks for one local slot layout.";
selectorBoundaryRowsFromBanks0[spinorBanksByIndex_List, slotIndices_List, assignmentIndices_List] := Map[
  Function[assignmentIndex,
    spinProjectionGammaKernelBoundaryVector[spinorBanksByIndex[[#, assignmentIndex]] & /@ slotIndices]
  ],
  assignmentIndices
];

selectorSharedGroupRefPatternValues0::usage =
  "selectorSharedGroupRefPatternValues0[groupRecord, runtime, assignmentIndices, refIndex] returns batched exact probe values for every unique spin-pattern used by one shared-kernel ref across an assignment suffix.";
selectorSharedGroupRefPatternValues0[groupRecord_Association, runtime_Association, assignmentIndices_List, refIndex_Integer?Positive] := Module[
  {
    compiled,
    kernelKey,
    vectorTuple,
    kernel,
    mode,
    pairSlotIndices,
    assignments,
    valuesByPattern,
    spinVectorsBatch,
    spinSlotIndices,
    leftBoundaryRows,
    rightBoundaryRows,
    boundaryRows
  },
  compiled = groupRecord["Compiled"];
  kernelKey = compiled["GammaKernelRefs"][[refIndex, "Key"]];
  vectorTuple = groupRecord["VectorTuples"][[refIndex]];
  kernel = spinProjectionGammaKernelRegistry[kernelKey];
  mode = groupRecord["RefModes"][[refIndex]];
  pairSlotIndices = groupRecord["PairFactorSlotIndicesByRef"][[refIndex]];
  assignments = runtime["Assignments"][[assignmentIndices]];
  valuesByPattern = Table[
    Module[{spinSymbols},
      spinSymbols = groupRecord["UniqueSpinSymbolsByRef"][[refIndex, patternIndex]];
      spinSlotIndices = groupRecord["UniqueSpinSlotIndicesByRef"][[refIndex, patternIndex]];
      Switch[mode,
        "paired2x2",
        leftBoundaryRows = selectorBoundaryRowsFromBanks0[
          runtime["SpinorBanksByIndex"],
          spinSlotIndices[[pairSlotIndices[[1]]]],
          assignmentIndices
        ];
        rightBoundaryRows = selectorBoundaryRowsFromBanks0[
          runtime["SpinorBanksByIndex"],
          spinSlotIndices[[pairSlotIndices[[2]]]],
          assignmentIndices
        ];
        spinProjectionGammaKernelSelectorPairValues0[kernelKey, vectorTuple, leftBoundaryRows, rightBoundaryRows],
        "singleFactor2",
        boundaryRows = selectorBoundaryRowsFromBanks0[runtime["SpinorBanksByIndex"], spinSlotIndices, assignmentIndices];
        spinProjectionGammaKernelSelectorSingleFactorValues0[kernelKey, vectorTuple, boundaryRows],
        _,
        spinVectorsBatch = Lookup[Lookup[#, "SpinorComponents", <||>], spinSymbols, Missing["Unassigned"]] & /@ assignments;
        If[
          AnyTrue[
            spinVectorsBatch,
            !ListQ[#] || AnyTrue[#, MatchQ[Missing[__]]] || !AllTrue[#, VectorQ[#, spinProjectionSelectorExactScalarQ] &] &
          ],
          $Failed,
          If[
            spinProjectionGammaKernelPairMatrixQ[kernel],
            spinProjectionGammaKernelProbeValuesBatch0[kernelKey, vectorTuple, spinVectorsBatch],
            spinProjectionGammaKernelProbeValue[kernelKey, vectorTuple, #] & /@ spinVectorsBatch
          ]
        ]
      ]
    ],
    {patternIndex, Length[groupRecord["UniqueSpinSymbolsByRef"][[refIndex]]]}
  ];
  If[MemberQ[valuesByPattern, $Failed], Return[$Failed]];
  valuesByPattern
];

selectorGroupSignatureBlock0::usage =
  "selectorGroupSignatureBlock0[groupRecord, runtime, assignmentIndices] computes one full member-by-probe signature block for a batch-eligible shared selector group over a contiguous assignment suffix.";
selectorGroupSignatureBlock0[groupRecord_Association, runtime_Association, assignmentIndices_List] := Module[
  {compiled, assignmentCount, refPatternValues, memberValueVectors},
  If[!selectorGroupBatchEligibleQ0[groupRecord], Return[$Failed]];
  compiled = groupRecord["Compiled"];
  assignmentCount = Length[assignmentIndices];
  refPatternValues = Table[
    selectorSharedGroupRefPatternValues0[groupRecord, runtime, assignmentIndices, refIndex],
    {refIndex, Length[compiled["GammaKernelRefs"]]}
  ];
  If[MemberQ[refPatternValues, $Failed], Return[$Failed]];
  memberValueVectors = Table[
    Module[{valueVector},
      valueVector = ConstantArray[compiled["ScalarFactor"] groupRecord["MemberScalars"][[memberIndex]], assignmentCount];
      Do[
        valueVector = valueVector * refPatternValues[[refIndex, groupRecord["MemberPatternIndices"][[memberIndex, refIndex]]]],
        {refIndex, Length[compiled["GammaKernelRefs"]]}
      ];
      valueVector
    ],
    {memberIndex, Length[groupRecord["MemberPositions"]]}
  ];
  AssociationThread[groupRecord["MemberPositions"], memberValueVectors]
];

ensureGroupProbeValues::usage =
  "ensureGroupProbeValues[groupIndex, assignmentIndex, runtime] fills one selector group/probe cache entry lazily when a shared-kernel group is first touched.";
ensureGroupProbeValues[groupIndex_Integer?Positive, assignmentIndex_Integer?Positive, runtime_Association] := Module[
  {groupRecord, memberValues, nextRuntime = runtime},
  If[!KeyExistsQ[nextRuntime["GroupRecords"], groupIndex], Return[nextRuntime]];
  groupRecord = nextRuntime["GroupRecords"][groupIndex];
  If[groupRecord["Mode"] =!= "SharedKernelGroup" || selectorGroupBatchEligibleQ0[groupRecord], Return[nextRuntime]];
  If[KeyExistsQ[Lookup[nextRuntime["GroupProbeCache"], groupIndex, <||>], assignmentIndex], Return[nextRuntime]];
  memberValues = selectorGroupProbeValuesReference0[groupRecord, nextRuntime["Assignments"][[assignmentIndex]]];
  If[memberValues === $Failed, Return[$Failed]];
  If[!KeyExistsQ[nextRuntime["GroupProbeCache"], groupIndex], nextRuntime["GroupProbeCache", groupIndex] = <||>];
  nextRuntime["GroupProbeCache", groupIndex, assignmentIndex] = memberValues;
  nextRuntime
];

extendSharedGroupSignatureCache0::usage =
  "extendSharedGroupSignatureCache0[groupIndex, runtime, startAssignmentIndex, endAssignmentIndex] appends one shared-kernel signature block to every member cache entry in a batch-eligible selector group.";
extendSharedGroupSignatureCache0[
  groupIndex_Integer?Positive,
  runtime_Association,
  startAssignmentIndex_Integer?Positive,
  endAssignmentIndex_Integer?Positive
] := Module[
  {groupRecord, nextRuntime = runtime, existingLengths, startIndex, assignments, signatureBlock, memberKey, position, values, existing},
  If[!KeyExistsQ[nextRuntime["GroupRecords"], groupIndex], Return[$Failed]];
  groupRecord = nextRuntime["GroupRecords"][groupIndex];
  If[!selectorGroupBatchEligibleQ0[groupRecord], Return[$Failed]];
  existingLengths = DeleteDuplicates[Length /@ Lookup[nextRuntime["SignatureCache"], groupRecord["MemberKeys"], {}]];
  If[Length[existingLengths] =!= 1, Return[$Failed]];
  startIndex = Max[startAssignmentIndex, existingLengths[[1]] + 1];
  If[startIndex > endAssignmentIndex, Return[nextRuntime]];
  assignments = Range[startIndex, endAssignmentIndex];
  signatureBlock = selectorGroupSignatureBlock0[groupRecord, nextRuntime, assignments];
  If[signatureBlock === $Failed, Return[$Failed]];
  Do[
    memberKey = groupRecord["MemberKeys"][[memberIndex]];
    position = groupRecord["MemberPositions"][[memberIndex]];
    values = Lookup[signatureBlock, position, $Failed];
    If[values === $Failed, Return[$Failed]];
    existing = Lookup[nextRuntime["SignatureCache"], memberKey, {}];
    nextRuntime["SignatureCache", memberKey] = Join[existing, values],
    {memberIndex, Length[groupRecord["MemberKeys"]]}
  ];
  nextRuntime
];

ensureCandidateSignature::usage =
  "ensureCandidateSignature[candidate, runtime] extends one parsed candidate's exact signature to the current dense probe-bank size.";
ensureCandidateSignature[candidate_Association, runtime_Association] := Module[
  {existing, values, nextRuntime = runtime, groupIndex, probeValues, value},
  existing = Lookup[nextRuntime["SignatureCache"], candidate["Key"], {}];
  If[Length[existing] >= nextRuntime["AssignmentCount"], Return[nextRuntime]];
  groupIndex = Lookup[candidate, "GroupIndex", Missing["NoGroup"]];
  If[
    IntegerQ[groupIndex] &&
    KeyExistsQ[nextRuntime["GroupRecords"], groupIndex] &&
    selectorGroupBatchEligibleQ0[nextRuntime["GroupRecords"][groupIndex]],
    nextRuntime = extendSharedGroupSignatureCache0[groupIndex, nextRuntime, Length[existing] + 1, nextRuntime["AssignmentCount"]];
    If[nextRuntime === $Failed || Length[Lookup[nextRuntime["SignatureCache"], candidate["Key"], {}]] < nextRuntime["AssignmentCount"], Return[$Failed]];
    Return[nextRuntime];
  ];
  values = existing;
  Do[
    If[
      IntegerQ[groupIndex] &&
      KeyExistsQ[nextRuntime["GroupRecords"], groupIndex] &&
      nextRuntime["GroupRecords"][groupIndex, "Mode"] === "SharedKernelGroup",
      nextRuntime = ensureGroupProbeValues[groupIndex, i, nextRuntime];
      If[nextRuntime === $Failed, Return[$Failed]];
      probeValues = Lookup[Lookup[nextRuntime["GroupProbeCache"], groupIndex, <||>], i, <||>];
      value = Lookup[probeValues, candidate["Position"], $Failed],
      value = evaluateParsedCandidateAtProbe[candidate, nextRuntime["Assignments"][[i]]]
    ];
    values = Append[values, value],
    {i, Length[existing] + 1, nextRuntime["AssignmentCount"]}
  ];
  nextRuntime["SignatureCache", candidate["Key"]] = values;
  nextRuntime
];

candidateSignature::usage =
  "candidateSignature[candidate, runtime] returns the exact signature vector for one parsed candidate on the current dense probe bank.";
candidateSignature[candidate_Association, runtime_Association] := Lookup[runtime["SignatureCache"], candidate["Key"], {}];

selectorReduceSharedGroupAgainstState0::usage =
  "selectorReduceSharedGroupAgainstState0[groupRecord, runtime, state, acceptedCount, targetRank] reduces one batch-eligible shared selector group against the current exact pivot state and returns only the rank-increasing member positions.";
selectorReduceSharedGroupAgainstState0[
  groupRecord_Association,
  runtime_Association,
  state_Association,
  acceptedCount_Integer?NonNegative,
  targetRank_Integer?NonNegative
] := Module[
  {signatureBlock, nextState = state, acceptedPositions = {}, visitedPosition = 0, position, insertion},
  If[!selectorGroupBatchEligibleQ0[groupRecord], Return[$Failed]];
  signatureBlock = selectorGroupSignatureBlock0[groupRecord, runtime, Range[runtime["AssignmentCount"]]];
  If[signatureBlock === $Failed, Return[$Failed]];
  Do[
    If[acceptedCount + Length[acceptedPositions] >= targetRank, Break[]];
    position = groupRecord["MemberPositions"][[memberIndex]];
    visitedPosition = position;
    insertion = incrementalPivotInsert[nextState, Lookup[signatureBlock, position, {$Failed}]];
    If[TrueQ[insertion["RankIncreased"]],
      nextState = insertion["State"];
      AppendTo[acceptedPositions, position]
    ],
    {memberIndex, Length[groupRecord["MemberPositions"]]}
  ];
  <|
    "State" -> nextState,
    "AcceptedPositions" -> acceptedPositions,
    "VisitedPosition" -> visitedPosition
  |>
];

scanParsedCandidatesWithRuntime::usage =
  "scanParsedCandidatesWithRuntime[candidates, runtime, targetRank] scans parsed candidates in flat input order on the current exact dense probe bank.";
scanParsedCandidatesWithRuntime[candidates_List, runtime_Association, targetRank_Integer?NonNegative] := Module[
  {nextRuntime = runtime, state = initialPivotState[], accepted = {}, i, insertion, signature, visited = 0},
  For[i = 1, i <= Length[candidates] && Length[accepted] < targetRank, i++,
    visited = i;
    nextRuntime = ensureCandidateSignature[candidates[[i]], nextRuntime];
    signature = candidateSignature[candidates[[i]], nextRuntime];
    If[AnyTrue[signature, # === $Failed &], Return[$Failed]];
    insertion = incrementalPivotInsert[state, signature];
    If[TrueQ[insertion["RankIncreased"]],
      state = insertion["State"];
      AppendTo[accepted, candidates[[i, "Position"]]]
    ];
  ];
  <|"Runtime" -> nextRuntime, "AcceptedPositions" -> accepted, "VisitedCandidates" -> visited|>
];

scanParsedCandidateGroupsWithRuntime::usage =
  "scanParsedCandidateGroupsWithRuntime[groups, runtime, targetRank] scans parsed selector groups in flat input order, reducing batch-eligible shared groups from one exact signature block.";
scanParsedCandidateGroupsWithRuntime[groups_List, runtime_Association, targetRank_Integer?NonNegative] := Module[
  {
    nextRuntime = runtime,
    state = initialPivotState[],
    accepted = {},
    visited = 0,
    groupIndex,
    group,
    groupRecord,
    reduction,
    candidate,
    insertion,
    signature
  },
  For[groupIndex = 1, groupIndex <= Length[groups] && Length[accepted] < targetRank, groupIndex++,
    group = groups[[groupIndex]];
    If[group === {}, Continue[]];
    groupRecord = Lookup[nextRuntime["GroupRecords"], groupIndex, Missing["NotFound"]];
    If[AssociationQ[groupRecord] && selectorGroupBatchEligibleQ0[groupRecord],
      reduction = selectorReduceSharedGroupAgainstState0[groupRecord, nextRuntime, state, Length[accepted], targetRank];
      If[reduction === $Failed, Return[$Failed]];
      state = reduction["State"];
      accepted = Join[accepted, reduction["AcceptedPositions"]];
      visited = Max[visited, Lookup[reduction, "VisitedPosition", 0]];
      Continue[];
    ];
    Do[
      If[Length[accepted] >= targetRank, Break[]];
      visited = candidate["Position"];
      nextRuntime = ensureCandidateSignature[candidate, nextRuntime];
      signature = candidateSignature[candidate, nextRuntime];
      If[nextRuntime === $Failed || AnyTrue[signature, # === $Failed &], Return[$Failed]];
      insertion = incrementalPivotInsert[state, signature];
      If[TrueQ[insertion["RankIncreased"]],
        state = insertion["State"];
        AppendTo[accepted, candidate["Position"]]
      ],
      {candidate, group}
    ];
  ];
  <|"Runtime" -> nextRuntime, "AcceptedPositions" -> accepted, "VisitedCandidates" -> visited|>
];

scanCandidateList::usage =
  "scanCandidateList[candidates, targetRank, optsAssoc] scans a candidate list in order and returns the verified exact basis and visit count.";
scanCandidateList[candidates_List, targetRank_, optsAssoc_Association] := Module[
  {
    parsedGroups,
    parsedFlat,
    effectiveTarget,
    runtime,
    scanResult,
    verifyResult,
    visited = 0,
    positionToExpression,
    positionToCandidate,
    spinorHints
  },
  spinorHints = Lookup[optsAssoc, "SpinorChiralityHints", <||>];
  parsedGroups = selectorNormalizedParsedCandidateGroups0[candidates, spinorHints];
  If[parsedGroups === $Failed, Return[$Failed]];
  parsedFlat = Flatten[parsedGroups, 1];
  effectiveTarget = If[targetRank === Automatic, automaticParsedCandidateTargetRank[parsedFlat], targetRank];
  If[effectiveTarget <= 0, Return[<|"Basis" -> {}, "AcceptedCandidates" -> {}, "TargetRank" -> 0, "VisitedCandidates" -> 0|>]];
  runtime = selectionRuntimeWithParsedGroups[parsedGroups, optsAssoc, effectiveTarget];
  runtime = extendAssignmentBank[runtime, runtime["InitialBankSize"]];
  positionToExpression = Association[Map[# ["Position"] -> # ["Expression"] &, parsedFlat]];
  positionToCandidate = Association[Map[# ["Position"] -> # &, parsedFlat]];
  While[True,
    scanResult = scanParsedCandidateGroupsWithRuntime[parsedGroups, runtime, effectiveTarget];
    If[scanResult === $Failed, Return[$Failed]];
    runtime = scanResult["Runtime"];
    visited = Max[visited, scanResult["VisitedCandidates"]];
    If[Length[scanResult["AcceptedPositions"]] < effectiveTarget,
      runtime = extendAssignmentBank[runtime, runtime["ExtensionBankSize"]];
      Continue[];
    ];
    If[runtime["VerificationBankSize"] === 0, Break[]];
    runtime = extendAssignmentBank[runtime, runtime["VerificationBankSize"]];
    verifyResult = scanParsedCandidateGroupsWithRuntime[parsedGroups, runtime, effectiveTarget];
    If[verifyResult === $Failed, Return[$Failed]];
    runtime = verifyResult["Runtime"];
    visited = Max[visited, verifyResult["VisitedCandidates"]];
    If[verifyResult["AcceptedPositions"] === scanResult["AcceptedPositions"], Break[]];
  ];
  <|
    "Basis" -> Lookup[positionToExpression, scanResult["AcceptedPositions"]],
    "AcceptedCandidates" -> Lookup[positionToCandidate, scanResult["AcceptedPositions"]],
    "TargetRank" -> effectiveTarget,
    "VisitedCandidates" -> visited
  |>
];

scanRawCandidateList::usage =
  "scanRawCandidateList[candidates, targetRank, optsAssoc] is the exact selector scan over raw explicit candidate expressions.";
scanRawCandidateList[candidates_List, targetRank_, optsAssoc_Association] := scanCandidateList[candidates, targetRank, optsAssoc];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
