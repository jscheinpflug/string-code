(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`OPE`TypeII`FlatSpace`TensorStructures`IndependentTensorStructures`"];
Needs["StringCode`OPE`TypeII`FlatSpace`TensorStructures`CountSinglet`"];
Needs["StringCode`OPE`TypeII`FlatSpace`GammaMatrices`GammaProductGrammar`"];
Needs["StringCode`OPE`TypeII`FlatSpace`TensorStructures`IndependentTensorStructuresSelector`"];
Needs["StringCode`OPE`TypeII`FlatSpace`TensorStructures`"];


(* ::Section:: *)
(*Declare public variables and methods*)


findIndependentTensorStructures::usage =
  "findIndependentTensorStructures[incoming, outgoing, opts] returns a verified independent subset of TypeII flat-space tensor structures; with candidate-list input it scans the supplied concrete candidates in order.";

findIndependentTensorStructures::badarg =
  "Arguments are not in a supported form for independent tensor-structure selection.";
findIndependentTensorStructures::badtarget =
  "\"TargetRank\" must be Automatic or a nonnegative integer; received `1`.";
findIndependentTensorStructures::badopt =
  "Unsupported option `1` supplied to findIndependentTensorStructures.";
findIndependentTensorStructures::badoptvalue =
  "Option `1` has invalid value `2`.";
findIndependentTensorStructures::toomanyout =
  "Outgoing input may contain at most one spinor index for automatic target-rank computation.";
findIndependentTensorStructures::targetunmet =
  "Requested target rank `1` could not be reached; the maximal verified rank found was `2`.";
findIndependentTensorStructures::antisymtargetauto =
  "\"TargetRank\" -> Automatic is not supported when \"AntisymmetricVectorGroups\" is nonempty; supply an explicit target rank.";

Options[findIndependentTensorStructures] = {
  "TargetRank" -> Automatic,
  "ProbeCount" -> 5,
  "VerificationProbeCount" -> 0,
  "RandomSeed" -> Automatic,
  "ReturnStatistics" -> False,
  "AntisymmetricVectorGroups" -> {},
  "SparseProbeKValue" -> 4,
  "SparseProbePrefixCount" -> Automatic,
  "DenseFallbackProbeCount" -> 50,
  "ReturnSparseBasis" -> False
};


(* ::Section:: *)
(*Logic*)


Begin["Private`"];

validTargetRankOptionQ::usage = "validTargetRankOptionQ[target] checks whether the target-rank option is Automatic or a nonnegative integer.";
validTargetRankOptionQ[Automatic] := True;
validTargetRankOptionQ[target_Integer?NonNegative] := True;
validTargetRankOptionQ[_] := False;

validNonNegativeIntegerOrAutomaticOptionQ::usage =
  "validNonNegativeIntegerOrAutomaticOptionQ[value] checks whether an option value is Automatic or a nonnegative integer.";
validNonNegativeIntegerOrAutomaticOptionQ[Automatic] := True;
validNonNegativeIntegerOrAutomaticOptionQ[value_Integer?NonNegative] := True;
validNonNegativeIntegerOrAutomaticOptionQ[_] := False;

validPositiveIntegerOptionQ::usage = "validPositiveIntegerOptionQ[value] checks whether an option value is a positive integer.";
validPositiveIntegerOptionQ[value_Integer?Positive] := True;
validPositiveIntegerOptionQ[_] := False;

validBooleanOptionQ::usage = "validBooleanOptionQ[value] checks whether an option value is explicitly True or False.";
validBooleanOptionQ[True] := True;
validBooleanOptionQ[False] := True;
validBooleanOptionQ[_] := False;

parseSelectorOptions::usage = "parseSelectorOptions[opts] validates selector options and returns an option association or $Failed.";
parseSelectorOptions[opts_List] := Module[
  {
    assoc,
    targetRank,
    invalidOptions,
    sparseProbeKValue,
    sparseProbePrefixCount,
    denseFallbackProbeCount,
    returnStatistics,
    returnSparseBasis
  },
  invalidOptions = Complement[First /@ opts, First /@ Options[findIndependentTensorStructures]];
  If[invalidOptions =!= {}, Message[findIndependentTensorStructures::badopt, First[invalidOptions]]; Return[$Failed]];
  assoc = Association[Join[Options[findIndependentTensorStructures], opts]];
  targetRank = Lookup[assoc, "TargetRank", Automatic];
  If[!validTargetRankOptionQ[targetRank], Message[findIndependentTensorStructures::badtarget, targetRank]; Return[$Failed]];
  sparseProbeKValue = Lookup[assoc, "SparseProbeKValue", 4];
  If[!validPositiveIntegerOptionQ[sparseProbeKValue],
    Message[findIndependentTensorStructures::badoptvalue, "SparseProbeKValue", sparseProbeKValue];
    Return[$Failed];
  ];
  sparseProbePrefixCount = Lookup[assoc, "SparseProbePrefixCount", Automatic];
  If[!validNonNegativeIntegerOrAutomaticOptionQ[sparseProbePrefixCount],
    Message[findIndependentTensorStructures::badoptvalue, "SparseProbePrefixCount", sparseProbePrefixCount];
    Return[$Failed];
  ];
  denseFallbackProbeCount = Lookup[assoc, "DenseFallbackProbeCount", 50];
  If[!validNonNegativeIntegerOrAutomaticOptionQ[denseFallbackProbeCount],
    Message[findIndependentTensorStructures::badoptvalue, "DenseFallbackProbeCount", denseFallbackProbeCount];
    Return[$Failed];
  ];
  returnStatistics = Lookup[assoc, "ReturnStatistics", False];
  If[!validBooleanOptionQ[returnStatistics],
    Message[findIndependentTensorStructures::badoptvalue, "ReturnStatistics", returnStatistics];
    Return[$Failed];
  ];
  returnSparseBasis = Lookup[assoc, "ReturnSparseBasis", False];
  If[!validBooleanOptionQ[returnSparseBasis],
    Message[findIndependentTensorStructures::badoptvalue, "ReturnSparseBasis", returnSparseBasis];
    Return[$Failed];
  ];
  assoc
];

normalizeCandidateInput::usage =
  "normalizeCandidateInput[candidates] normalizes selector input to a list of candidate groups, preserving generator-provided abstract grouping.";
normalizeCandidateInput[candidates_List] := Which[
  candidates === {}, {},
  AllTrue[candidates, ListQ], Select[candidates, # =!= {} &],
  True, {candidates}
];

candidateInputCount::usage =
  "candidateInputCount[candidates] returns the flat candidate count represented by grouped or ungrouped selector input.";
candidateInputCount[candidates_List] := Total[Length /@ normalizeCandidateInput[candidates]];

findIndependentTensorStructuresCanonicalTemplateCache::usage =
  "findIndependentTensorStructuresCanonicalTemplateCache memoizes canonical grouped tensor-structure templates, parsed selector candidates, and caller-symbol relabel reuse for association-mode selection.";
findIndependentTensorStructuresCanonicalTemplateCache = <||>;

independentTensorStructuresCanonicalVectorSymbol::usage =
  "independentTensorStructuresCanonicalVectorSymbol[i] returns the deterministic canonical vector placeholder used in cached tensor-structure templates.";
independentTensorStructuresCanonicalVectorSymbol[i_Integer?Positive] :=
  Symbol["StringCode`OPE`TypeII`FlatSpace`TensorStructures`IndependentTensorStructures`cacheVector" <> ToString[i]];

independentTensorStructuresCanonicalSpinSymbol::usage =
  "independentTensorStructuresCanonicalSpinSymbol[i] returns the deterministic canonical spinor placeholder used in cached tensor-structure templates.";
independentTensorStructuresCanonicalSpinSymbol[i_Integer?Positive] :=
  Symbol["StringCode`OPE`TypeII`FlatSpace`TensorStructures`IndependentTensorStructures`cacheSpin" <> ToString[i]];

associationCanonicalTemplateData::usage =
  "associationCanonicalTemplateData[searchData, generatorOpts] returns canonicalized generator input, a stable cache key, and relabeling rules for association-mode candidate caching.";
associationCanonicalTemplateData[searchData_Association, generatorOpts_List] := Module[
  {
    incomingVectors,
    outgoingVectors,
    incomingSpins,
    outgoingSpins,
    actualVectors,
    actualSpins,
    canonicalVectors,
    canonicalSpins,
    canonicalIncoming,
    canonicalOutgoing,
    vectorRules,
    spinRules,
    generatorAssoc,
    canonicalGroups,
    canonicalKey
  },
  incomingVectors = searchData["Incoming", "vector"];
  outgoingVectors = searchData["Outgoing", "vector"];
  incomingSpins = searchData["Incoming", "spinor"];
  outgoingSpins = searchData["Outgoing", "spinor"];
  actualVectors = Join[incomingVectors, outgoingVectors];
  actualSpins = Join[incomingSpins[[All, 1]], outgoingSpins[[All, 1]]];
  canonicalVectors = independentTensorStructuresCanonicalVectorSymbol /@ Range[Length[actualVectors]];
  canonicalSpins = independentTensorStructuresCanonicalSpinSymbol /@ Range[Length[actualSpins]];
  vectorRules = Thread[actualVectors -> canonicalVectors];
  spinRules = Thread[actualSpins -> canonicalSpins];
  canonicalIncoming = <|
    "vector" -> (incomingVectors /. vectorRules),
    "spinor" -> MapThread[List, {Take[canonicalSpins, Length[incomingSpins]], incomingSpins[[All, 2]]}]
  |>;
  canonicalOutgoing = <|
    "vector" -> (outgoingVectors /. vectorRules),
    "spinor" -> MapThread[List, {Drop[canonicalSpins, Length[incomingSpins]], outgoingSpins[[All, 2]]}]
  |>;
  generatorAssoc = Association[Join[Options[generateTensorStructures], generatorOpts]];
  canonicalGroups = Lookup[generatorAssoc, "AntisymmetricVectorGroups", {}] /. vectorRules;
  canonicalGroups = SortBy[DeleteDuplicates[#], symbolSortKey] & /@ canonicalGroups;
  canonicalGroups = If[canonicalGroups === {}, {}, SortBy[canonicalGroups, symbolSortKey[First[#]] &]];
  canonicalKey = {
    Length[incomingVectors],
    incomingSpins[[All, 2]],
    Length[outgoingVectors],
    outgoingSpins[[All, 2]],
    canonicalGroups,
    Lookup[generatorAssoc, "MaxK", 5],
    TrueQ[Lookup[generatorAssoc, "RepresentativesOnly", False]]
  };
  <|
    "Incoming" -> canonicalIncoming,
    "Outgoing" -> canonicalOutgoing,
    "GeneratorOptions" -> DeleteCases[generatorOpts, Rule["AntisymmetricVectorGroups", _]],
    "CanonicalGroups" -> canonicalGroups,
    "CacheKey" -> canonicalKey,
    "RelabelRules" -> Join[Reverse /@ vectorRules, Reverse /@ spinRules]
  |>
];

associationCanonicalSpinorHints0::usage =
  "associationCanonicalSpinorHints0[templateData] returns the canonical spinor chirality hints used when caching parsed selector candidates.";
associationCanonicalSpinorHints0[templateData_Association] := AssociationThread[
  Join[templateData["Incoming", "spinor"][[All, 1]], templateData["Outgoing", "spinor"][[All, 1]]],
  Join[templateData["Incoming", "spinor"][[All, 2]], templateData["Outgoing", "spinor"][[All, 2]]]
];

associationCallerSymbolTuple0::usage =
  "associationCallerSymbolTuple0[searchData] returns the stable caller-symbol tuple used to memoize relabeled parsed selector groups for one association-mode selector shape.";
associationCallerSymbolTuple0[searchData_Association] := {
  searchData["Incoming", "vector"],
  searchData["Outgoing", "vector"],
  searchData["Incoming", "spinor"][[All, 1]],
  searchData["Outgoing", "spinor"][[All, 1]]
};

associationRelabelValue0::usage =
  "associationRelabelValue0[value, rules] applies relabeling rules through nested candidate-cache structures without mutating canonical selector cache keys.";
associationRelabelValue0[value_, rules_List] := Replace[value, rules, {0, Infinity}];

associationRelabelParsedCandidate0::usage =
  "associationRelabelParsedCandidate0[candidate, rules] relabels one cached parsed selector candidate back to caller symbols while keeping canonical family parse keys intact.";
associationRelabelParsedCandidate0[candidate_Association, rules_List] := Module[
  {relabeledExpr, relabeledParsed, relabeledFamilyData},
  relabeledExpr = associationRelabelValue0[candidate["Expression"], rules];
  relabeledParsed = Join[
    candidate["Parsed"],
    <|
      "Expression" -> relabeledExpr,
      "Key" -> candidateCacheKey[relabeledExpr],
      "Factors" -> associationRelabelValue0[candidate["Parsed", "Factors"], rules],
      "FactorParts" -> associationRelabelValue0[candidate["Parsed", "FactorParts"], rules],
      "SpinorChiralities" -> Association @ KeyValueMap[associationRelabelValue0[#1, rules] -> #2 &, candidate["Parsed", "SpinorChiralities"]],
      "ExternalVectors" -> associationRelabelValue0[candidate["Parsed", "ExternalVectors"], rules]
    |>
  ];
  relabeledFamilyData = Join[
    candidate["FamilyData"],
    <|
      "CanonicalToActualSpin" -> Association @ KeyValueMap[#1 -> associationRelabelValue0[#2, rules] &, candidate["FamilyData", "CanonicalToActualSpin"]],
      "CanonicalToActualVector" -> Association @ KeyValueMap[#1 -> associationRelabelValue0[#2, rules] &, candidate["FamilyData", "CanonicalToActualVector"]]
    |>
  ];
  Join[
    candidate,
    <|
      "Expression" -> relabeledExpr,
      "Key" -> candidateCacheKey[relabeledExpr],
      "Parsed" -> relabeledParsed,
      "SpinSymbols" -> associationRelabelValue0[candidate["SpinSymbols"], rules],
      "VectorSymbols" -> associationRelabelValue0[candidate["VectorSymbols"], rules],
      "FamilyData" -> relabeledFamilyData
    |>
  ]
];

associationRelabelParsedCandidateGroups0::usage =
  "associationRelabelParsedCandidateGroups0[groups, rules] relabels cached canonical parsed candidate groups back to caller symbols while preserving group and position metadata.";
associationRelabelParsedCandidateGroups0[groups_List, rules_List] := (associationRelabelParsedCandidate0[#, rules] & /@ #) & /@ groups;

associationCandidateTemplate::usage =
  "associationCandidateTemplate[searchData, generatorOpts] returns grouped parsed selector candidates via a canonical template cache and relabeling rules.";
associationCandidateTemplate[searchData_Association, generatorOpts_List] := Module[
  {
    templateData,
    generatorArgs,
    cachedTemplate,
    groupedCandidates,
    parsedCandidateGroups,
    spinorHints,
    callerSymbolTuple,
    relabeledCache
  },
  templateData = associationCanonicalTemplateData[searchData, generatorOpts];
  generatorArgs = Join[
    templateData["GeneratorOptions"],
    {
      "AntisymmetricVectorGroups" -> templateData["CanonicalGroups"],
      "ReturnSelectorCandidates" -> True
    }
  ];
  spinorHints = associationCanonicalSpinorHints0[templateData];
  callerSymbolTuple = associationCallerSymbolTuple0[searchData];
  cachedTemplate = If[
    KeyExistsQ[findIndependentTensorStructuresCanonicalTemplateCache, templateData["CacheKey"]],
    findIndependentTensorStructuresCanonicalTemplateCache[templateData["CacheKey"]],
    Missing["NotAvailable"]
  ];
  If[cachedTemplate === Missing["NotAvailable"],
    groupedCandidates = generateTensorStructures[
      templateData["Incoming"],
      templateData["Outgoing"],
      Sequence @@ generatorArgs
    ];
    parsedCandidateGroups = selectorNormalizedParsedCandidateGroups0[groupedCandidates, spinorHints];
    If[parsedCandidateGroups === $Failed, Return[$Failed]];
    cachedTemplate = <|
      "ParsedCandidateGroups" -> parsedCandidateGroups,
      "RelabeledParsedCandidateGroups" -> <||>
    |>;
    AssociateTo[findIndependentTensorStructuresCanonicalTemplateCache, templateData["CacheKey"] -> cachedTemplate],
    If[!AssociationQ[cachedTemplate] || !KeyExistsQ[cachedTemplate, "ParsedCandidateGroups"],
      groupedCandidates = If[AssociationQ[cachedTemplate], cachedTemplate["GroupedCandidates"], cachedTemplate];
      parsedCandidateGroups = selectorNormalizedParsedCandidateGroups0[groupedCandidates, spinorHints];
      If[parsedCandidateGroups === $Failed, Return[$Failed]];
      cachedTemplate = <|
        "ParsedCandidateGroups" -> parsedCandidateGroups,
        "RelabeledParsedCandidateGroups" -> <||>
      |>;
      AssociateTo[findIndependentTensorStructuresCanonicalTemplateCache, templateData["CacheKey"] -> cachedTemplate],
      If[
        !KeyExistsQ[cachedTemplate, "RelabeledParsedCandidateGroups"] ||
          !AssociationQ[cachedTemplate["RelabeledParsedCandidateGroups"]] ||
          !SubsetQ[Keys[cachedTemplate["RelabeledParsedCandidateGroups"]], {"CallerSymbolTuple", "Groups"}],
        cachedTemplate = Join[cachedTemplate, <|"RelabeledParsedCandidateGroups" -> <||>|>];
        AssociateTo[findIndependentTensorStructuresCanonicalTemplateCache, templateData["CacheKey"] -> cachedTemplate]
      ]
    ]
  ];
  relabeledCache = cachedTemplate["RelabeledParsedCandidateGroups"];
  If[
    Lookup[relabeledCache, "CallerSymbolTuple", Missing["NotAvailable"]] =!= callerSymbolTuple,
    relabeledCache = <|
      "CallerSymbolTuple" -> callerSymbolTuple,
      "Groups" -> associationRelabelParsedCandidateGroups0[cachedTemplate["ParsedCandidateGroups"], templateData["RelabelRules"]]
    |>;
    cachedTemplate["RelabeledParsedCandidateGroups"] = relabeledCache;
    AssociateTo[findIndependentTensorStructuresCanonicalTemplateCache, templateData["CacheKey"] -> cachedTemplate]
  ];
  relabeledCache["Groups"]
];

selectorSparseBasisRecord::usage =
  "selectorSparseBasisRecord[candidate] converts one accepted parsed selector candidate into the sparse-basis record consumed by the compiled RHS path.";
selectorSparseBasisRecord[candidate_Association] := <|
  "Expr" -> candidate["Expression"],
  "CanonicalToActualSpin" -> candidate["FamilyData", "CanonicalToActualSpin"],
  "CanonicalToActualVector" -> candidate["FamilyData", "CanonicalToActualVector"],
  "SelectorFamilyCache" -> spinProjectionSelectorFamilyCompileCache[candidate["FamilyData", "Parsed", "Key"]]
|>;

selectorResult::usage =
  "selectorResult[basis, acceptedCandidates, targetRank, visitedCandidates, optsAssoc] formats the selector return value according to ReturnStatistics and ReturnSparseBasis.";
selectorResult[
  basis_List,
  acceptedCandidates_List,
  targetRank_,
  visitedCandidates_Integer?NonNegative,
  optsAssoc_Association
] := Which[
  TrueQ[Lookup[optsAssoc, "ReturnSparseBasis", False]],
  selectorSparseBasisRecord /@ acceptedCandidates,
  TrueQ[Lookup[optsAssoc, "ReturnStatistics", False]],
  <|"Basis" -> basis, "TargetRank" -> targetRank, "VisitedCandidates" -> visitedCandidates|>,
  True,
  basis
];

associationSelectionData::usage = "associationSelectionData[incoming, outgoing] validates association input and returns normalized search metadata.";
associationSelectionData[incoming_Association, outgoing_Association] := Module[
  {inNorm, outNorm, inVec, outVec, inSpin, outSpin, allIndexSymbols, outSpinor},
  inNorm = normalizeIndexAssociation[incoming];
  outNorm = normalizeIndexAssociation[outgoing];
  inVec = inNorm["vector"];
  outVec = outNorm["vector"];
  inSpin = inNorm["spinor"];
  outSpin = outNorm["spinor"];
  If[!(validVectorIndexListQ[inVec] && validVectorIndexListQ[outVec] && validSpinorIndexListQ[inSpin] && validSpinorIndexListQ[outSpin]),
    Message[findIndependentTensorStructures::badarg];
    Return[$Failed];
  ];
  If[Length[outSpin] > 1, Message[findIndependentTensorStructures::toomanyout]; Return[$Failed]];
  allIndexSymbols = Join[inVec, outVec, inSpin[[All, 1]], outSpin[[All, 1]]];
  (* Repeated symbols or odd spinor count imply malformed index bookkeeping for tensor generation/selection. *)
  If[!DuplicateFreeQ[allIndexSymbols] || OddQ[Length[inSpin] + Length[outSpin]],
    Message[findIndependentTensorStructures::badarg];
    Return[$Failed];
  ];
  outSpinor = If[outSpin === {}, None, First[outSpin]];
  <|
    "Incoming" -> inNorm,
    "Outgoing" -> outNorm,
    "OutSpinor" -> outSpinor,
    "ExternalVectors" -> Join[inVec, outVec]
  |>
];

automaticAssociationTargetRank::usage = "automaticAssociationTargetRank[data] computes the exact automatic target rank from incoming and outgoing representation content.";
automaticAssociationTargetRank[data_Association] := Module[{nChiral, nAnti},
  nChiral = Count[data["Incoming"]["spinor"][[All, 2]], "chiral"];
  nAnti = Count[data["Incoming"]["spinor"][[All, 2]], "antichiral"];
  If[data["OutSpinor"] =!= None,
    If[data["OutSpinor"][[2]] === "chiral", nAnti++, nChiral++];
  ];
  countSinglets[nChiral, nAnti, Length[data["ExternalVectors"]]]
];

scanCandidatesOrFail::usage = "scanCandidatesOrFail[candidates, targetRank, optsAssoc] runs the exact selector and emits badarg on compile failure.";
scanCandidatesOrFail[candidates_List, targetRank_, optsAssoc_Association] := Module[{result = scanCandidateList[candidates, targetRank, optsAssoc]},
  If[result === $Failed, Message[findIndependentTensorStructures::badarg]; $Failed, result]
];

findIndependentTensorStructures[incoming_Association, outgoing_Association, opts___Rule] := Module[
  {optsAssoc, searchData, targetRank, candidates, candidateCount, scanResult, generatorOpts, antisymmetricVectorGroups},
  optsAssoc = parseSelectorOptions[{opts}];
  If[optsAssoc === $Failed, Return[$Failed]];
  withPersistentCacheBoundary @ Module[{},
    searchData = associationSelectionData[incoming, outgoing];
    If[searchData === $Failed, Return[$Failed]];
    AssociateTo[
      optsAssoc,
      "SpinorChiralityHints" -> AssociationThread[
        Join[searchData["Incoming"]["spinor"][[All, 1]], If[searchData["OutSpinor"] === None, {}, {searchData["OutSpinor"][[1]]}]],
        Join[searchData["Incoming"]["spinor"][[All, 2]], If[searchData["OutSpinor"] === None, {}, {searchData["OutSpinor"][[2]]}]]
      ]
    ];
    targetRank = Lookup[optsAssoc, "TargetRank", Automatic];
    antisymmetricVectorGroups = Lookup[optsAssoc, "AntisymmetricVectorGroups", {}];
    If[targetRank === Automatic && antisymmetricVectorGroups =!= {},
      Message[findIndependentTensorStructures::antisymtargetauto];
      Return[$Failed];
    ];
    targetRank = If[targetRank === Automatic, automaticAssociationTargetRank[searchData], targetRank];
    If[targetRank === 0, Return[selectorResult[{}, {}, 0, 0, optsAssoc]]];
    (* Association mode preserves generator grouping so the selector can compile and scan abstract families lazily. *)
    generatorOpts = FilterRules[{opts}, Options[generateTensorStructures]];
    candidates = associationCandidateTemplate[searchData, generatorOpts];
    If[candidates === $Failed, Return[$Failed]];
    candidates = normalizeCandidateInput[candidates];
    candidateCount = candidateInputCount[candidates];
    If[targetRank > candidateCount,
      Message[findIndependentTensorStructures::targetunmet, targetRank, candidateCount];
      Return[$Failed];
    ];
    scanResult = scanCandidatesOrFail[candidates, targetRank, optsAssoc];
    If[scanResult === $Failed, Return[$Failed]];
    If[Length[scanResult["Basis"]] < targetRank,
      Message[findIndependentTensorStructures::targetunmet, targetRank, Length[scanResult["Basis"]]];
      Return[$Failed];
    ];
    selectorResult[
      scanResult["Basis"],
      Lookup[scanResult, "AcceptedCandidates", {}],
      scanResult["TargetRank"],
      scanResult["VisitedCandidates"],
      optsAssoc
    ]
  ]
];

findIndependentTensorStructures[candidates_List, opts___Rule] := Module[
  {optsAssoc, normalizedCandidates, targetRank, candidateCount, scanResult},
  optsAssoc = parseSelectorOptions[{opts}];
  If[optsAssoc === $Failed, Return[$Failed]];
  withPersistentCacheBoundary @ Module[{},
    normalizedCandidates = normalizeCandidateInput[candidates];
    candidateCount = candidateInputCount[normalizedCandidates];
    targetRank = Lookup[optsAssoc, "TargetRank", Automatic];
    If[normalizedCandidates === {},
      targetRank = Replace[targetRank, Automatic -> 0];
      If[targetRank =!= 0, Message[findIndependentTensorStructures::targetunmet, targetRank, 0]; Return[$Failed]];
      Return[selectorResult[{}, {}, 0, 0, optsAssoc]];
    ];
    If[targetRank =!= Automatic && targetRank > candidateCount,
      Message[findIndependentTensorStructures::targetunmet, targetRank, candidateCount];
      Return[$Failed];
    ];
    (* List mode accepts flat or grouped candidates and scans them lazily in the supplied flat order. *)
    scanResult = scanCandidatesOrFail[normalizedCandidates, targetRank, optsAssoc];
    If[scanResult === $Failed, Return[$Failed]];
    If[targetRank =!= Automatic && Length[scanResult["Basis"]] < targetRank,
      Message[findIndependentTensorStructures::targetunmet, targetRank, Length[scanResult["Basis"]]];
      Return[$Failed];
    ];
    selectorResult[
      scanResult["Basis"],
      Lookup[scanResult, "AcceptedCandidates", {}],
      scanResult["TargetRank"],
      scanResult["VisitedCandidates"],
      optsAssoc
    ]
  ]
];

findIndependentTensorStructures[___] := Module[{},
  Message[findIndependentTensorStructures::badarg];
  $Failed
];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
