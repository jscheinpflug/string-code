(* ::Package:: *)

BeginPackage["StringCode`OPE`TypeII`FlatSpace`SpinProjection`Compile`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];
Needs["StringCode`Symbols`TypeII`FlatSpace`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`TypeII`"];
Needs["StringCode`Operators`"];
Needs["StringCode`OPE`"];
Needs["StringCode`BasisGeneration`"];
Needs["StringCode`BasisGeneration`TypeII`"];
Needs["StringCode`BasisGeneration`TypeII`FlatSpace`"];
Needs["StringCode`OPE`TypeII`FlatSpace`TensorStructures`CountSinglet`"];
Needs["StringCode`OPE`TypeII`FlatSpace`TensorStructures`"];
Needs["StringCode`OPE`TypeII`FlatSpace`TensorStructures`IndependentTensorStructures`"];

buildProjectedArtifacts::usage =
  "buildProjectedArtifacts[ops, wH, wA, seed] builds and caches the projected spin-sector artifacts for both chiral sectors.";

buildSectorArtifact::usage =
  "buildSectorArtifact[sector, ops, targetWeight, seed] builds one cached chiral sector artifact in ClosedForm or SpinProjection mode.";

familyOutputAssociation::usage =
  "familyOutputAssociation[family, tuple] lazily returns the operator association for one concrete family output tuple.";


Begin["Private`"];

spinProjectionArtifactCache0::usage =
  "spinProjectionArtifactCache0 memoizes complete projected sector artifacts keyed by sector, canonicalized ops, target weight, and seed.";
spinProjectionArtifactCache0 = <||>;

spinProjectionFamilyOutputTemplateCache0::usage =
  "spinProjectionFamilyOutputTemplateCache0 stores family output templates keyed for lazy tuple projection.";
spinProjectionFamilyOutputTemplateCache0 = <||>;

spinProjectionEnableSelectorSparseBasisPassthrough::usage =
  "spinProjectionEnableSelectorSparseBasisPassthrough gates selector sparse-basis passthrough into the RHS compile until scalar-output benchmarks justify enabling it.";
spinProjectionEnableSelectorSparseBasisPassthrough = False;

clearSpinProjectionCaches0::usage =
  "clearSpinProjectionCaches0[] clears in-kernel spin-projection caches after live code edits.";
clearSpinProjectionCaches0[] := Module[{},
  spinProjectionArtifactCache0 = <||>;
  spinProjectionFamilyOutputTemplateCache0 = <||>;
  If[NameQ["Private`spinProjectionConcreteGammaSpinSupportCache"], spinProjectionConcreteGammaSpinSupportCache = <||>];
  If[NameQ["Private`findIndependentTensorStructuresCanonicalTemplateCache"], findIndependentTensorStructuresCanonicalTemplateCache = <||>]
];

spinProjectionArtifactCacheLookup0::usage =
  "spinProjectionArtifactCacheLookup0[key] looks up one projected sector artifact cache entry.";
spinProjectionArtifactCacheLookup0[key_] := If[
  KeyExistsQ[spinProjectionArtifactCache0, key],
  spinProjectionArtifactCache0[key],
  Missing["NotAvailable"]
];

spinProjectionArtifactCacheStore0::usage =
  "spinProjectionArtifactCacheStore0[key, artifact] stores one projected sector artifact cache entry and returns the stored artifact.";
spinProjectionArtifactCacheStore0[key_, artifact_] := (spinProjectionArtifactCache0[key] = artifact);

spinProjectionCanonicalOps0::usage =
  "spinProjectionCanonicalOps0[ops] returns the canonicalized operator list used in sector artifact cache keys.";
spinProjectionCanonicalOps0[ops_List] := If[ops === {}, {}, spinProjectionCanonicalizeOps[ops]["Ops"]];

spinProjectionOverallSign0::usage =
  "spinProjectionOverallSign0[ops] returns the holomorphic/antiholomorphic factorization sign for a list of R-operators.";
spinProjectionOverallSign0[ops_List] := Module[{localLists},
  localLists = List @@ # & /@ ops;
  If[
    Flatten[localLists] === {},
    1,
    factorizationSign[Flatten[localLists], isHolomorphic, isAntiHolomorphic]
  ]
];

spinProjectionSectorOps0::usage =
  "spinProjectionSectorOps0[ops, spec] extracts one chiral sector's split operator list from full input operators.";
spinProjectionSectorOps0[ops_List, spec_Association] := Module[{localLists, splitLists},
  localLists = List @@ # & /@ ops;
  splitLists = splitOperators[#, isHolomorphic, isAntiHolomorphic] & /@ localLists;
  Select[R @@@ (splitLists[[All, spec["SplitIndex"]]]), RTest]
];

closedFormSectorQ0::usage =
  "closedFormSectorQ0[sectorOps] is True exactly for sectors that need no spin-projection solve.";
closedFormSectorQ0[sectorOps_List] := sectorOps === {};

pictureContributionHolo::usage =
  "Returns the picture number contribution of a holomorphic field (S or expϕf/expϕb).";
pictureContributionHolo[field_] := Switch[
  SymbolName[Head[field]],
  "S", field[[2]],
  "expϕf" | "expϕb", field[[1]],
  _, 0
];

pictureContributionAntiHolo::usage =
  "Returns the picture number contribution of an antiholomorphic field (St or expϕtf/expϕtb).";
pictureContributionAntiHolo[field_] := Switch[
  SymbolName[Head[field]],
  "St", field[[2]],
  "expϕtf" | "expϕtb", field[[1]],
  _, 0
];

totalInputPicture::usage =
  "totalInputPicture[ops, contributionFn] computes total picture number from a list of R-operators.";
totalInputPicture[ops_List, contributionFn_] :=
  Total[contributionFn /@ Flatten[List @@ # & /@ Select[ops, RTest]]];

mergeRepresentations::usage =
  "mergeRepresentations[reps] merges representation associations into one combined association.";
mergeRepresentations[reps_List] := <|
  "vector" -> Flatten[#["vector"] & /@ reps],
  "spinor" -> Flatten[#["spinor"] & /@ reps, 1]
|>;

representationsHaveRepeatedVectorsQ0::usage =
  "representationsHaveRepeatedVectorsQ0[incoming, outgoing] is True when the combined incoming/outgoing vector-label multiset contains repeated symbolic vectors, so abstract singlet counting can overestimate the true tensor rank.";
representationsHaveRepeatedVectorsQ0[incoming_Association, outgoing_Association] := Module[{vectors},
  vectors = Join[Lookup[incoming, "vector", {}], Lookup[outgoing, "vector", {}]];
  Length[DeleteDuplicates[vectors]] < Length[vectors]
];

gammaFactorHasRepeatedVectorIndicesQ0::usage =
  "gammaFactorHasRepeatedVectorIndicesQ0[factor] is True when a GammaAntisymmetricProductHold factor carries the same vector index more than once and therefore vanishes identically by antisymmetry.";
gammaFactorHasRepeatedVectorIndicesQ0[factor_GammaAntisymmetricProductHold] := Module[{indices},
  indices = Cases[factor[[1]], GammaUDHold[idx_] | GammaDUHold[idx_] :> idx];
  Length[DeleteDuplicates[indices]] < Length[indices]
];
gammaFactorHasRepeatedVectorIndicesQ0[_] := False;

tensorCandidateVanishesQ0::usage =
  "tensorCandidateVanishesQ0[expr] is True when a tensor-structure candidate contains an antisymmetrized gamma factor with repeated vector indices and is therefore identically zero.";
tensorCandidateVanishesQ0[expr_] := AnyTrue[
  Cases[expr, _GammaAntisymmetricProductHold, Infinity],
  gammaFactorHasRepeatedVectorIndicesQ0
];

normalizeTensorCandidateList0::usage =
  "normalizeTensorCandidateList0[candidates] drops identically vanishing tensor-structure candidates and deduplicates the survivors by stable InputForm key.";
normalizeTensorCandidateList0[candidates_List] := DeleteDuplicatesBy[
  DeleteCases[candidates, candidate_ /; tensorCandidateVanishesQ0[candidate]],
  ToString[InputForm[#]] &
];

spinProjectionPlaceholderSymbol::usage =
  "spinProjectionPlaceholderSymbol[kind, n] returns a deterministic shared-private placeholder symbol for abstract tensor bases.";
spinProjectionPlaceholderSymbol["Vector", n_Integer?Positive] := Symbol["Private`spinProjV" <> ToString[n]];
spinProjectionPlaceholderSymbol["Spinor", n_Integer?Positive] := Symbol["Private`spinProjS" <> ToString[n]];

normalizeMatterRepresentationLabel::usage =
  "normalizeMatterRepresentationLabel[label, kind, counter] returns {abstractSymbol, optionalEvaluationRule, nextCounter}.";
normalizeMatterRepresentationLabel[label_, kind_String, counter_Integer?NonNegative] := Module[{nextCounter, placeholder},
  If[SymbolQ[label], Return[{label, Nothing, counter}]];
  nextCounter = counter + 1;
  placeholder = spinProjectionPlaceholderSymbol[kind, nextCounter];
  {placeholder, placeholder -> label, nextCounter}
];

spinModeVectorIndices::usage =
  "spinModeVectorIndices[modes] extracts vector labels carried by spin-field oscillator modes.";
spinModeVectorIndices[modes_List] := Join[
  Cases[modes, {n_?NumericQ, idx_ /; !NumericQ[idx]} :> idx],
  Cases[modes, {idx_ /; !NumericQ[idx], n_?NumericQ} :> idx]
];

spinProjectionSymbolicSpinModeData::usage =
  "spinProjectionSymbolicSpinModeData[mode] returns {vectorIndex, excitationLevel} for one symbolic spin-field vector mode, or $Failed otherwise.";
spinProjectionSymbolicSpinModeData[{idx_Symbol, mode_Integer?NonPositive}] := {idx, -mode};
spinProjectionSymbolicSpinModeData[{mode_Integer?NonPositive, idx_Symbol}] := {idx, -mode};
spinProjectionSymbolicSpinModeData[_] := $Failed;

outgoingAntisymmetricVectorGroups::usage =
  "outgoingAntisymmetricVectorGroups[op, spinHead] extracts equal-level outgoing spin-mode vector blocks that must be antisymmetrized.";
outgoingAntisymmetricVectorGroups[op_ /; RTest[op], spinHead_] := Module[
  {spinField, symbolicModes},
  spinField = SelectFirst[List @@ op, Head[#] === spinHead &, Missing["NoSpinField"]];
  If[spinField === Missing["NoSpinField"], Return[{}]];
  symbolicModes = DeleteCases[spinProjectionSymbolicSpinModeData /@ spinField[[3]], $Failed];
  SortBy[
    SortBy[#, SymbolName] & /@ Select[Values @ GroupBy[symbolicModes, Last -> First], Length[#] > 1 &],
    SymbolName[First[#]] &
  ]
];
outgoingAntisymmetricVectorGroups[_, _] := {};

fermionicOutputVectorGroups0::usage =
  "fermionicOutputVectorGroups0[op] extracts vector-symbol groups carried by identical fermionic output fields and therefore antisymmetrized by operator ordering.";
fermionicOutputVectorGroups0[op_ /; RTest[op]] := Module[{fields},
  fields = Select[List @@ op, MemberQ[{ψ, ψt}, Head[#]] && Head[#[[1]]] === Symbol &];
  SortBy[
    SortBy[#, SymbolName] & /@ Select[
      Values @ GroupBy[fields, {Head[#], Sequence @@ Rest[List @@ #]} & -> First],
      Length[#] > 1 &
    ],
    SymbolName[First[#]] &
  ]
];
fermionicOutputVectorGroups0[_] := {};

spinProjectionOutputAntisymmetricVectorGroups0::usage =
  "spinProjectionOutputAntisymmetricVectorGroups0[op] collects output vector-symbol groups whose repeated equalization would annihilate the operator by antisymmetry.";
spinProjectionOutputAntisymmetricVectorGroups0[op_ /; RTest[op]] := SortBy[
  DeleteDuplicatesBy[
    Join[
      fermionicOutputVectorGroups0[op],
      outgoingAntisymmetricVectorGroups[op, S],
      outgoingAntisymmetricVectorGroups[op, St]
    ],
    ToString[InputForm[#]] &
  ],
  SymbolName[First[#]] &
];
spinProjectionOutputAntisymmetricVectorGroups0[_] := {};

spinProjectionVectorMatterHeads::usage =
  "spinProjectionVectorMatterHeads[psiHead] returns vector-carrying matter heads used in one spin-field projection sector.";
spinProjectionVectorMatterHeads[ψ] := {ψ, dX};
spinProjectionVectorMatterHeads[ψt] := {ψt, dXt};
spinProjectionVectorMatterHeads[head_] := {head};

extractMatterRepresentationData::usage =
  "extractMatterRepresentationData[Ra, psiHead, spinHead, counters] returns abstract representations, concrete evaluation rules, and updated placeholder counters.";
extractMatterRepresentationData[
  Ra_ /; RTest[Ra],
  psiHead_,
  spinHead_,
  counters_Association
] := Module[
  {
    fields = List @@ Ra,
    vectors = {},
    spinors = {},
    rules = {},
    vectorCounter = Lookup[counters, "Vector", 0],
    spinCounter = Lookup[counters, "Spinor", 0],
    vectorHeads = spinProjectionVectorMatterHeads[psiHead],
    normalized,
    modeIndices
  },
  Scan[
    Function[field,
      Which[
        MemberQ[vectorHeads, Head[field]],
          normalized = normalizeMatterRepresentationLabel[field[[1]], "Vector", vectorCounter];
          vectors = Append[vectors, normalized[[1]]];
          If[normalized[[2]] =!= Nothing, rules = Append[rules, normalized[[2]]]];
          vectorCounter = normalized[[3]],
        Head[field] === spinHead,
          normalized = normalizeMatterRepresentationLabel[field[[1, 1]], "Spinor", spinCounter];
          spinors = Append[spinors, {normalized[[1]], field[[1, 2]]}];
          If[normalized[[2]] =!= Nothing, rules = Append[rules, normalized[[2]]]];
          spinCounter = normalized[[3]];
          modeIndices = spinModeVectorIndices[field[[3]]];
          Scan[
            Function[idx,
              normalized = normalizeMatterRepresentationLabel[idx, "Vector", vectorCounter];
              vectors = Append[vectors, normalized[[1]]];
              If[normalized[[2]] =!= Nothing, rules = Append[rules, normalized[[2]]]];
              vectorCounter = normalized[[3]];
            ],
            modeIndices
          ],
        True, Null
      ]
    ],
    fields
  ];
  <|
    "Representations" -> <|"vector" -> vectors, "spinor" -> spinors|>,
    "EvaluationRules" -> DeleteCases[rules, Nothing],
    "Counters" -> <|"Vector" -> vectorCounter, "Spinor" -> spinCounter|>
  |>
];
extractMatterRepresentationData[1, _, _, counters_Association] := <|
  "Representations" -> <|"vector" -> {}, "spinor" -> {}|>,
  "EvaluationRules" -> {},
  "Counters" -> counters
|>;

extractMatterRepresentationDataList::usage =
  "extractMatterRepresentationDataList[ops, psiHead, spinHead] merges abstract representation data across one operator list.";
extractMatterRepresentationDataList[ops_List, psiHead_, spinHead_] := Module[
  {counters = <|"Vector" -> 0, "Spinor" -> 0|>, reps = {}, rules = {}, data},
  Scan[
    Function[op,
      data = extractMatterRepresentationData[op, psiHead, spinHead, counters];
      reps = Append[reps, data["Representations"]];
      rules = Join[rules, data["EvaluationRules"]];
      counters = data["Counters"];
    ],
    ops
  ];
  <|
    "Representations" -> mergeRepresentations[reps],
    "EvaluationRules" -> rules,
    "Counters" -> counters
  |>
];

inputGSOParityString::usage =
  "inputGSOParityString[ops] computes the product of GSO parities of input R-operators and returns \"Even\" or \"Odd\".";
inputGSOParityString[ops_List] := Module[{parity},
  parity = Times @@ (GSOParity /@ ops);
  If[parity === 1, "Even", "Odd"]
];

spinProjectionTargetRank::usage =
  "spinProjectionTargetRank[incoming, outgoing] returns the exact singlet-count target rank used by spin-field selection.";
spinProjectionTargetRank[incoming_Association, outgoing_Association] := Module[
  {nChiral, nAnti, outSpinor},
  nChiral = Count[incoming["spinor"][[All, 2]], "chiral"];
  nAnti = Count[incoming["spinor"][[All, 2]], "antichiral"];
  outSpinor = Lookup[outgoing, "spinor", {}];
  If[outSpinor =!= {},
    If[outSpinor[[1, 2]] === "chiral", nAnti++, nChiral++]
  ];
  countSinglets[nChiral, nAnti, Length[Lookup[incoming, "vector", {}]] + Length[Lookup[outgoing, "vector", {}]]]
];

spinProjectionSparseBasisRecordQ::usage =
  "spinProjectionSparseBasisRecordQ[tensor] is True exactly for sparse-basis selector records carrying Expr, relabel maps, and selector family cache data.";
spinProjectionSparseBasisRecordQ[tensor_] :=
  AssociationQ[tensor] &&
  KeyExistsQ[tensor, "Expr"] &&
  KeyExistsQ[tensor, "CanonicalToActualSpin"] &&
  KeyExistsQ[tensor, "CanonicalToActualVector"] &&
  KeyExistsQ[tensor, "SelectorFamilyCache"];

spinProjectionTensorExpr0::usage =
  "spinProjectionTensorExpr0[tensor] returns the raw tensor expression regardless of whether the input is a sparse-basis record or a plain expression.";
spinProjectionTensorExpr0[tensor_] := If[spinProjectionSparseBasisRecordQ[tensor], tensor["Expr"], tensor];

spinProjectionRelabelSparseBasisRecord0::usage =
  "spinProjectionRelabelSparseBasisRecord0[record, rules] relabels only Expr and actual-symbol maps of one sparse-basis record, leaving SelectorFamilyCache untouched.";
spinProjectionRelabelSparseBasisRecord0[record_Association, rules_List] := Module[{relabelValue},
  relabelValue[value_] := Replace[value, rules, {0, Infinity}];
  Join[
    record,
    <|
      "Expr" -> (record["Expr"] /. rules),
      "CanonicalToActualSpin" -> Association @ KeyValueMap[#1 -> relabelValue[#2] &, record["CanonicalToActualSpin"]],
      "CanonicalToActualVector" -> Association @ KeyValueMap[#1 -> relabelValue[#2] &, record["CanonicalToActualVector"]]
    |>
  ]
];

spinProjectionRelabelTensorStructure0::usage =
  "spinProjectionRelabelTensorStructure0[tensor, rules] relabels one tensor structure while preserving cached selector-family data inside sparse-basis records.";
spinProjectionRelabelTensorStructure0[tensor_, rules_List] := If[
  spinProjectionSparseBasisRecordQ[tensor],
  spinProjectionRelabelSparseBasisRecord0[tensor, rules],
  tensor /. rules
];

spinProjectionRelabelTensorStructureList0::usage =
  "spinProjectionRelabelTensorStructureList0[tensors, rules] relabels a tensor-structure list with sparse-basis record awareness.";
spinProjectionRelabelTensorStructureList0[tensors_List, rules_List] := spinProjectionRelabelTensorStructure0[#, rules] & /@ tensors;

spinProjectionFreshOutputSymbol0::usage =
  "spinProjectionFreshOutputSymbol0[kind, used] returns a deterministic fresh output-state symbol that avoids the given used-symbol set.";
spinProjectionFreshOutputSymbol0[kind : ("Spinor" | "Vector"), used_List] := Module[
  {prefix, n = 1, candidate},
  prefix = If[kind === "Spinor", "α", "μ"];
  While[True,
    candidate = Symbol["Global`" <> prefix <> ToString[n]];
    If[!MemberQ[used, SymbolName[candidate]], Return[candidate]];
    n++;
  ]
];

spinProjectionOutputCollisionRenameRules0::usage =
  "spinProjectionOutputCollisionRenameRules0[op, actualSymbols] renames output-state vector/spin symbols that would collide with actual external labels after inverse relabeling.";
spinProjectionOutputCollisionRenameRules0[op_ /; RTest[op], actualSymbols_List] := Module[
  {outputData, actualSymbolNames, used, renameRules = {}, candidate},
  outputData = spinProjectionOutputSymbolData[op];
  If[outputData === $Failed, Return[{}]];
  actualSymbolNames = DeleteDuplicates[SymbolName /@ Select[actualSymbols, Head[#] === Symbol &]];
  used = DeleteDuplicates@Join[
    actualSymbolNames,
    SymbolName /@ Lookup[outputData, "SpinSymbols", {}],
    SymbolName /@ Lookup[outputData, "VectorSymbols", {}]
  ];
  Scan[
    Function[symbol,
      If[MemberQ[actualSymbolNames, SymbolName[symbol]],
        candidate = spinProjectionFreshOutputSymbol0["Spinor", used];
        renameRules = Append[renameRules, symbol -> candidate];
        used = Append[used, SymbolName[candidate]];
      ]
    ],
    Lookup[outputData, "SpinSymbols", {}]
  ];
  Scan[
    Function[symbol,
      If[MemberQ[actualSymbolNames, SymbolName[symbol]],
        candidate = spinProjectionFreshOutputSymbol0["Vector", used];
        renameRules = Append[renameRules, symbol -> candidate];
        used = Append[used, SymbolName[candidate]];
      ]
    ],
    Lookup[outputData, "VectorSymbols", {}]
  ];
  renameRules
];
spinProjectionOutputCollisionRenameRules0[_, _List] := {};

spinProjectionRelabelSectorFamily0::usage =
  "spinProjectionRelabelSectorFamily0[{op, tensors}, rules] reinstates actual external labels for one cached canonical sector family without mutating selector caches.";
spinProjectionRelabelSectorFamily0[{op_, tensors_}, rules_List] := Module[
  {actualSymbols, outputRenameRules, renamedOp, renamedTensors},
  actualSymbols = DeleteDuplicates @ Select[Last /@ rules, Head[#] === Symbol &];
  outputRenameRules = spinProjectionOutputCollisionRenameRules0[op, actualSymbols];
  renamedOp = op /. outputRenameRules;
  renamedTensors = spinProjectionRelabelTensorStructureList0[tensors, outputRenameRules];
  {
    renamedOp /. rules,
    spinProjectionRelabelTensorStructureList0[renamedTensors, rules]
  }
];

generateSpinFieldOPEData::usage =
  "generateSpinFieldOPEData[ops, targetWeight, basisGeneratorFn, psiHead, spinHead, pictureContributionFn, seed] builds {operator, tensorStructures} pairs for one chiral sector.";
generateSpinFieldOPEData[
  ops_List,
  targetWeight_,
  basisGeneratorFn_,
  psiHead_, spinHead_,
  pictureContributionFn_,
  seed_ : Automatic
] := Module[
  {
    incomingData, incomingReps, totalPicture, gsoParity, basisOps, outgoingData,
    tensorStructures, targetRank, antisymmetricVectorGroups, tensorCandidates
  },

  incomingData = extractMatterRepresentationDataList[ops, psiHead, spinHead];
  incomingReps = incomingData["Representations"];

  totalPicture = totalInputPicture[ops, pictureContributionFn];
  gsoParity = inputGSOParityString[ops];

  basisOps = basisGeneratorFn[
    targetWeight,
    totalPicture,
    "GSOParity" -> gsoParity,
    "OutputRepresentation" -> "Operators",
    "FermionOnly" -> True,
    "SpinFieldDerivatives" -> False
  ];
  If[basisOps === {}, Return[{}]];

  DeleteCases[
    Function[op,
      outgoingData = extractMatterRepresentationData[op, psiHead, spinHead, incomingData["Counters"]];
      antisymmetricVectorGroups =
        outgoingAntisymmetricVectorGroups[op, spinHead] /. (Reverse /@ outgoingData["EvaluationRules"]);
      If[antisymmetricVectorGroups === {},
        If[representationsHaveRepeatedVectorsQ0[incomingReps, outgoingData["Representations"]],
          tensorCandidates = normalizeTensorCandidateList0 @ Flatten[
            generateTensorStructures[incomingReps, outgoingData["Representations"]],
            1
          ];
          tensorStructures = findIndependentTensorStructures[
            tensorCandidates,
            "RandomSeed" -> seed,
            "ReturnSparseBasis" -> spinProjectionEnableSelectorSparseBasisPassthrough
          ],
          targetRank = spinProjectionTargetRank[incomingReps, outgoingData["Representations"]];
          tensorStructures = findIndependentTensorStructures[
            incomingReps,
            outgoingData["Representations"],
            "TargetRank" -> targetRank,
            "RandomSeed" -> seed,
            "ReturnSparseBasis" -> spinProjectionEnableSelectorSparseBasisPassthrough
          ]
        ],
        tensorCandidates = generateTensorStructures[
          incomingReps,
          outgoingData["Representations"],
          "AntisymmetricVectorGroups" -> antisymmetricVectorGroups
        ];
        targetRank = Total[Length /@ tensorCandidates];
        tensorStructures = findIndependentTensorStructures[
          incomingReps,
          outgoingData["Representations"],
          "TargetRank" -> targetRank,
          "RandomSeed" -> seed,
          "AntisymmetricVectorGroups" -> antisymmetricVectorGroups,
          "ReturnSparseBasis" -> spinProjectionEnableSelectorSparseBasisPassthrough
        ]
      ];
      If[tensorStructures === $Failed || tensorStructures === {},
        Nothing,
        {
          op,
          spinProjectionRelabelTensorStructureList0[
            tensorStructures,
            Join[incomingData["EvaluationRules"], outgoingData["EvaluationRules"]]
          ]
        }
      ]
    ] /@ basisOps,
    Nothing
  ]
];

spinProjectionCanonicalizeOps::usage =
  "spinProjectionCanonicalizeOps[ops] replaces free symbolic vector/spin labels by deterministic placeholders and returns canonical ops plus inverse rules.";
spinProjectionCanonicalizeOps[ops_List] := Module[
  {typed, vectorSymbols, spinSymbols, canonicalRules, inverseRules},
  typed = spinTypedIndices[ops];
  vectorSymbols = SortBy[DeleteDuplicates[First /@ Select[typed, Last[#] === "v" &]], SymbolName];
  spinSymbols = Complement[
    SortBy[DeleteDuplicates[First /@ Select[typed, Last[#] === "s" &]], SymbolName],
    vectorSymbols
  ];
  canonicalRules = Join[
    Thread[vectorSymbols -> (spinProjectionPlaceholderSymbol["Vector", #] & /@ Range[Length[vectorSymbols]])],
    Thread[spinSymbols -> (spinProjectionPlaceholderSymbol["Spinor", #] & /@ Range[Length[spinSymbols]])]
  ];
  inverseRules = Reverse /@ canonicalRules;
  <|
    "Ops" -> (ops /. canonicalRules),
    "InverseRules" -> inverseRules
  |>
];

spinProjectionCanonicalSectorData::usage =
  "spinProjectionCanonicalSectorData[ops, targetWeight, basisGeneratorFn, psiHead, spinHead, pictureContributionFn, seed] memoizes canonicalized sector-family tensor data.";
spinProjectionCanonicalSectorData[
  ops_List,
  targetWeight_,
  basisGeneratorFn_,
  psiHead_,
  spinHead_,
  pictureContributionFn_,
  seed_
] := spinProjectionCanonicalSectorData[
  ops,
  targetWeight,
  basisGeneratorFn,
  psiHead,
  spinHead,
  pictureContributionFn,
  seed
] = generateSpinFieldOPEData[
  ops,
  targetWeight,
  basisGeneratorFn,
  psiHead,
  spinHead,
  pictureContributionFn,
  seed
];

spinProjectionSectorData::usage =
  "spinProjectionSectorData[ops, targetWeight, basisGeneratorFn, psiHead, spinHead, pictureContributionFn, seed] reuses canonicalized sector-family tensor data and reinstates the actual external labels.";
spinProjectionSectorData[
  ops_List,
  targetWeight_,
  basisGeneratorFn_,
  psiHead_,
  spinHead_,
  pictureContributionFn_,
  seed_
] := Module[{canonical},
  canonical = spinProjectionCanonicalizeOps[ops];
  spinProjectionRelabelSectorFamily0[#, canonical["InverseRules"]] & /@ spinProjectionCanonicalSectorData[
    canonical["Ops"],
    targetWeight,
    basisGeneratorFn,
    psiHead,
    spinHead,
    pictureContributionFn,
    seed
  ]
];

spinProjectionSectorSpec::usage =
  "spinProjectionSectorSpec[sector] returns the metadata used by one chiral spin-field projection sector.";
spinProjectionSectorSpec["Holo"] := <|
  "SplitIndex" -> 1,
  "OpsKey" -> "holoOps",
  "DataKey" -> "holoData",
  "ProbeInputsKey" -> "HoloInputs",
  "ProbeExprKey" -> "HoloExpr",
  "FailureLabel" -> "holomorphic",
  "BasisGenerator" -> generateBasisMatterHoloOPE,
  "PsiHead" -> ψ,
  "SpinHead" -> S,
  "PictureContribution" -> pictureContributionHolo,
  "Weight" -> totalWeightHolo,
  "Project" -> projectHolo,
  "ScaleSymbol" -> \[Epsilon]Holo
|>;
spinProjectionSectorSpec["Anti"] := <|
  "SplitIndex" -> 2,
  "OpsKey" -> "antiOps",
  "DataKey" -> "antiData",
  "ProbeInputsKey" -> "AntiInputs",
  "ProbeExprKey" -> "AntiExpr",
  "FailureLabel" -> "antiholomorphic",
  "BasisGenerator" -> generateBasisMatterAntiHoloOPE,
  "PsiHead" -> ψt,
  "SpinHead" -> St,
  "PictureContribution" -> pictureContributionAntiHolo,
  "Weight" -> totalWeightAntiHolo,
  "Project" -> projectAntiHolo,
  "ScaleSymbol" -> \[Epsilon]AntiHolo
|>;

spinProjectionConnectedSymbolGroups::usage =
  "spinProjectionConnectedSymbolGroups[symbols, edges] returns connected symbol groups, including singleton groups for isolated symbols.";
spinProjectionConnectedSymbolGroups[symbols_List, edges_List] := Module[
  {remaining = DeleteDuplicates[symbols], groups = {}, group, frontier, neighbors},
  neighbors[current_List] := DeleteDuplicates @ Flatten[
    Cases[edges, {a_, b_} /; MemberQ[current, a] :> b] ~Join~
    Cases[edges, {a_, b_} /; MemberQ[current, b] :> a]
  ];
  While[remaining =!= {},
    group = {First[remaining]};
    frontier = group;
    While[frontier =!= {},
      frontier = Complement[neighbors[frontier], group];
      group = Join[group, frontier];
    ];
    groups = Append[groups, group];
    remaining = Complement[remaining, group];
  ];
  groups
];

spinProjectionVectorConstraintPairs::usage =
  "spinProjectionVectorConstraintPairs[obj, freeVectors] extracts free-vector equality pairs implied by explicit delta tensors.";
spinProjectionVectorConstraintPairs[obj_, freeVectors_List] := DeleteDuplicates[
  Sort /@ Cases[
    HoldComplete[obj],
    factor_ /; Head[factor] === \[Delta] && Length[factor] == 2 &&
      MemberQ[freeVectors, factor[[1]]] && MemberQ[freeVectors, factor[[2]]] :>
        {factor[[1]], factor[[2]]},
    Infinity
  ]
];

spinProjectionExpandedTerms::usage =
  "spinProjectionExpandedTerms[obj] expands one expression or expression list into additive terms, dropping trivial zero terms.";
spinProjectionExpandedTerms[obj_] := DeleteCases[
  Flatten @ Replace[
    Expand /@ Flatten[{obj}],
    expr_ :> If[expr === 0, {}, If[Head[expr] === Plus, List @@ expr, {expr}]],
    {1}
  ],
  0
];

spinProjectionTermVectorConstraintData::usage =
  "spinProjectionTermVectorConstraintData[term, freeVectors] returns the free vectors present in one additive term together with the full equality closure implied by explicit deltas in that term.";
spinProjectionTermVectorConstraintData[term_, freeVectors_List] := Module[
  {present, groups},
  present = SortBy[
    Intersection[
      freeVectors,
      DeleteDuplicates @ Cases[
        HoldComplete[term],
        sym_Symbol /; MemberQ[freeVectors, sym] :> sym,
        Infinity
      ]
    ],
    SymbolName
  ];
  groups = spinProjectionConnectedSymbolGroups[
    present,
    spinProjectionVectorConstraintPairs[term, present]
  ];
  <|
    "Present" -> present,
    "Pairs" -> DeleteDuplicates[Sort /@ Flatten[Subsets[#, {2}] & /@ groups, 1]]
  |>
];

spinProjectionCommonVectorConstraintPairs::usage =
  "spinProjectionCommonVectorConstraintPairs[obj, freeVectors] returns the free-vector equality pairs that hold in every additive term where both symbols co-occur.";
spinProjectionCommonVectorConstraintPairs[obj_, freeVectors_List] := Module[
  {sortedVectors, termData},
  sortedVectors = SortBy[DeleteDuplicates[freeVectors], SymbolName];
  If[Length[sortedVectors] < 2, Return[{}]];
  termData = spinProjectionTermVectorConstraintData[#, sortedVectors] & /@ spinProjectionExpandedTerms[obj];
  DeleteDuplicates @ Select[
    Subsets[sortedVectors, {2}],
    Function[pair,
      Module[{cooccurringTerms},
        cooccurringTerms = Select[
          termData,
          Function[term, And @@ (MemberQ[term["Present"], #] & /@ pair)]
        ];
        cooccurringTerms =!= {} &&
          AllTrue[cooccurringTerms, MemberQ[#["Pairs"], pair] &]
      ]
    ]
  ]
];

spinProjectionSectorTemplate::usage =
  "spinProjectionSectorTemplate[ops, expr] collects free/dummy vector and spin symbols for one chiral spin-projection sector.";
spinProjectionSectorTemplate[ops_List, expr_] := Module[
  {
    typedInputs,
    typedRHS,
    typed,
    countsInput,
    countsRHS,
    vec,
    spi,
    allSymbols,
    free,
    dum,
    spinChiralities,
    freeVectorSymbols,
    freeVectorGroups
  },
  typedInputs = spinTypedIndices[ops];
  typedRHS = spinTypedIndices[expr];
  typed = Join[typedInputs, typedRHS];
  countsInput = Counts[First /@ typedInputs];
  countsRHS = Counts[First /@ typedRHS];
  spinChiralities = spinSymbolChiralities[{ops, expr}];
  vec = DeleteDuplicates[First /@ Select[typed, Last[#] === "v" &]];
  spi = Complement[DeleteDuplicates[First /@ Select[typed, Last[#] === "s" &]], vec];
  allSymbols = DeleteDuplicates@Join[vec, spi];
  free = Select[
    allSymbols,
    (Lookup[countsInput, #, 0] > 0 && Lookup[countsRHS, #, 0] > 0) ||
      (Lookup[countsInput, #, 0] + Lookup[countsRHS, #, 0] == 1) &
  ];
  dum = Select[
    allSymbols,
    (Lookup[countsInput, #, 0] + Lookup[countsRHS, #, 0] > 1) &&
      !MemberQ[free, #] &
  ];
  freeVectorSymbols = SortBy[Intersection[vec, free], SymbolName];
  (* Only equalities common to all co-occurring RHS terms should constrain probes globally; mixed equalities stay term-local. *)
  freeVectorGroups = spinProjectionConnectedSymbolGroups[
    freeVectorSymbols,
    spinProjectionCommonVectorConstraintPairs[expr, freeVectorSymbols]
  ];
  <|
    "Ops" -> ops,
    "Expr" -> expr,
    "VectorSymbols" -> vec,
    "SpinSymbols" -> spi,
    "FreeSymbols" -> free,
    "DummySymbols" -> dum,
    "FreeVectorGroups" -> freeVectorGroups,
    "SpinChiralities" -> spinChiralities
  |>
];

spinSymbolChiralities::usage = "spinSymbolChiralities[obj] collects the intended chirality for symbolic spinor indices appearing in spin fields and gamma products.";
spinSymbolChiralities[obj_] := Module[{fieldPairs, gammaTriples, gammaPairs},
  fieldPairs = Cases[
    obj,
    (S | St)[{idx_Symbol, chirality : ("chiral" | "antichiral")}, __] :> (idx -> chirality),
    Infinity
  ];
  gammaTriples = Cases[obj, GammaAntisymmetricProductHold[links_List, s1_, s2_] :> {links, s1, s2}, Infinity];
  gammaPairs = Flatten[
    Function[{triple},
      Module[{pair = gammaProductSpinorChiralities[triple[[1]]]},
        Join[
          Cases[{triple[[2]]}, idx_Symbol :> (idx -> pair[[1]])],
          Cases[{triple[[3]]}, idx_Symbol :> (idx -> pair[[2]])]
        ]
      ]
    ] /@ gammaTriples,
    1
  ];
  Association[DeleteDuplicatesBy[Join[fieldPairs, gammaPairs], First]]
];

symbolIndexQ::usage = "symbolIndexQ[x] checks whether x is a symbolic index placeholder rather than a numeric value.";
symbolIndexQ[x_] := Head[x] === Symbol;

spinTypedIndices::usage =
  "spinTypedIndices[obj] collects symbolic vector/spinor placeholders from spin-field OPE inputs or ansatz expressions.";
spinTypedIndices[obj_] := Join[
  Cases[obj, (ψ | ψt | dX | dXt)[μ_, __] /; symbolIndexQ[μ] :> {μ, "v"}, Infinity],
  Cases[obj, (S | St)[{α_, ("chiral" | "antichiral")}, __] /; symbolIndexQ[α] :> {α, "s"}, Infinity],
  Flatten[Cases[obj, (S | St)[_, _, m_List, __] :> Join[
    ({#, "v"} & /@ Cases[m, {_?NumericQ, ν_ /; symbolIndexQ[ν]} :> ν]),
    ({#, "v"} & /@ Cases[m, {ν_ /; symbolIndexQ[ν], _?NumericQ} :> ν])], Infinity], 1],
  Flatten[Cases[obj, GammaAntisymmetricProductHold[links_List, s1_, s2_] :>
    Join[
      ({#, "v"} & /@ Select[Flatten[gammaLinkVectorIndices /@ links], symbolIndexQ]),
      ({#, "s"} & /@ Select[{s1, s2}, symbolIndexQ])
    ], Infinity], 1]
];

buildProjectedArtifacts::usage =
  "buildProjectedArtifacts[ops, wH, wA, seed] builds and caches the projected spin-sector artifacts for both chiral sectors.";
buildProjectedArtifacts[ops_List, wH_, wA_, seed_] := <|
  "Sign" -> spinProjectionOverallSign0[ops],
  "Holo" -> buildSectorArtifact["Holo", ops, wH, seed],
  "Anti" -> buildSectorArtifact["Anti", ops, wA, seed]
|>;

buildSectorArtifact::usage =
  "buildSectorArtifact[sector, ops, targetWeight, seed] builds one cached chiral sector artifact in ClosedForm or SpinProjection mode.";
buildSectorArtifact[sector : ("Holo" | "Anti"), ops_List, targetWeight_, seed_] := withPersistentCacheBoundary @ Module[
  {spec, sectorOps, cacheKey, cached, data, artifact},
  If[targetWeight === None, Return[None]];
  spec = spinProjectionSectorSpec[sector];
  sectorOps = spinProjectionSectorOps0[ops, spec];
  cacheKey = {sector, spinProjectionCanonicalOps0[sectorOps], targetWeight, seed};
  cached = spinProjectionArtifactCacheLookup0[cacheKey];
  If[cached =!= Missing["NotAvailable"], Return[cached]];
  If[closedFormSectorQ0[sectorOps],
    artifact = buildClosedFormSectorArtifact0[sector, sectorOps, targetWeight, {}];
    Return[spinProjectionArtifactCacheStore0[cacheKey, artifact]]
  ];
  data = spinProjectionSectorData[
    sectorOps,
    targetWeight,
    spec["BasisGenerator"],
    spec["PsiHead"],
    spec["SpinHead"],
    spec["PictureContribution"],
    seed
  ];
  artifact = If[
    data === {},
    buildClosedFormSectorArtifact0[sector, sectorOps, targetWeight, {}],
    buildSpinSectorArtifact0[sector, sectorOps, targetWeight, data]
  ];
  spinProjectionArtifactCacheStore0[cacheKey, artifact]
];

buildClosedFormSectorArtifact0::usage =
  "buildClosedFormSectorArtifact0[sector, sectorOps, targetWeight, data] builds a direct-expression artifact for sectors that bypass compiled solving.";
buildClosedFormSectorArtifact0[sector_, sectorOps_List, targetWeight_, data_List] := Module[{expr},
  expr = Which[
    sectorOps === {}, If[targetWeight === 0, 1, 0],
    data === {}, 0,
    True, 0
  ];
  <|
    "Mode" -> "ClosedForm",
    "Sector" -> sector,
    "Ops" -> sectorOps,
    "Weight" -> targetWeight,
    "TargetWeight" -> targetWeight,
    "Expr" -> expr,
    "Vars" -> {},
    "VarCount" -> 0,
    "Columns" -> {},
    "Families" -> {},
    "FreeSpinSymbols" -> {},
    "FreeSpinChiralities" -> {},
    "FreeVectorGroups" -> {}
  |>
];

buildFailedSpinSectorArtifact0::usage =
  "buildFailedSpinSectorArtifact0[sector, sectorOps, targetWeight, reason] builds an explicit failed spin-projection artifact.";
buildFailedSpinSectorArtifact0[sector_, sectorOps_List, targetWeight_, reason_String] := <|
  "Mode" -> "SpinProjectionFailure",
  "Reason" -> reason,
  "Sector" -> sector,
  "Ops" -> sectorOps,
  "Weight" -> targetWeight,
  "TargetWeight" -> targetWeight,
  "Expr" -> 0,
  "Vars" -> {},
  "VarCount" -> 0,
  "Columns" -> {},
  "Families" -> {},
  "FreeSpinSymbols" -> {},
  "FreeSpinChiralities" -> {},
  "FreeVectorGroups" -> {}
|>;

spinProjectionRegisterFamilyOutputTemplate0::usage =
  "spinProjectionRegisterFamilyOutputTemplate0[template, spinSymbols, spinChiralities, vectorSymbols] stores one family template for lazy tuple projection and returns its key.";
spinProjectionRegisterFamilyOutputTemplate0[template_, spinSymbols_List, spinChiralities_List, vectorSymbols_List] := Module[{key},
  key = HoldComplete[template, spinSymbols, spinChiralities, vectorSymbols];
  If[!KeyExistsQ[spinProjectionFamilyOutputTemplateCache0, key],
    spinProjectionFamilyOutputTemplateCache0[key] = <|
      "Template" -> template,
      "SpinSymbols" -> spinSymbols,
      "SpinChiralities" -> spinChiralities,
      "VectorSymbols" -> vectorSymbols
    |>
  ];
  key
];

buildSpinSectorArtifact0::usage =
  "buildSpinSectorArtifact0[sector, sectorOps, targetWeight, data] compiles one spin-projection sector into the shared artifact contract with lazy family output lookup.";
buildSpinSectorArtifact0[sector_, sectorOps_List, targetWeight_, data_List] := Module[
  {model, columns, families, expr},
  model = compileSpinProjectionSectorModel[sector, sectorOps, targetWeight, data];
  If[model === $Failed, Return[None]];
  columns = model["Columns"];
  families = model["Families"];
  expr = model["Expr"];
  <|
    "Mode" -> "SpinProjection",
    "Sector" -> sector,
    "Ops" -> model["Ops"],
    "Weight" -> model["Weight"],
    "TargetWeight" -> model["TargetWeight"],
    "Expr" -> expr,
    "Vars" -> model["Vars"],
    "VarCount" -> model["VarCount"],
    "Columns" -> columns,
    "Families" -> families,
    "FreeSpinSymbols" -> model["FreeSpinSymbols"],
    "FreeSpinChiralities" -> model["FreeSpinChiralities"],
    "FreeVectorGroups" -> model["FreeVectorGroups"]
  |>
];

projectSingleFamilyOutputTuple0::usage =
  "projectSingleFamilyOutputTuple0[key, tuple] projects one family output template on one concrete output tuple.";
projectSingleFamilyOutputTuple0[key_, tuple_List] := Module[
  {templateData, spinCount, vectorCount, spinTuple, vectorTuple, spinRules, vectorRules},
  If[!KeyExistsQ[spinProjectionFamilyOutputTemplateCache0, key], Return[0]];
  templateData = spinProjectionFamilyOutputTemplateCache0[key];
  spinCount = Length[templateData["SpinSymbols"]];
  vectorCount = Length[templateData["VectorSymbols"]];
  If[Length[tuple] =!= spinCount + vectorCount, Return[0]];
  spinTuple = Take[tuple, spinCount];
  vectorTuple = Drop[tuple, spinCount];
  If[
    !AllTrue[
      MapThread[
        IntegerQ[#3] && 1 <= #3 <= Length[spinProjectionSpinBasisState[#2]] &,
        {templateData["SpinSymbols"], templateData["SpinChiralities"], spinTuple}
      ],
      TrueQ
    ],
    Return[0]
  ];
  spinRules = MapThread[
    #1 -> spinProjectionSpinBasisState[#2][[#3]] &,
    {templateData["SpinSymbols"], templateData["SpinChiralities"], spinTuple}
  ];
  vectorRules = Thread[templateData["VectorSymbols"] -> vectorTuple];
  Bosonize[templateData["Template"] /. Join[vectorRules, spinRules]]
];

familyOutputAssociation0::usage =
  "familyOutputAssociation0[key, tuple] memoizes one tuple-specific output operator association.";
familyOutputAssociation0[key_, tuple_List] := familyOutputAssociation0[key, tuple] = Module[{expr},
  expr = projectSingleFamilyOutputTuple0[key, tuple];
  spinProjectionOperatorAssociation[expr]
];

familyOutputAssociation::usage =
  "familyOutputAssociation[family, tuple] lazily returns the operator association for one concrete family output tuple.";
familyOutputAssociation[family_Association, tuple_List] := Module[{key},
  key = Lookup[family, "OutputAssociationKey", Missing["NotAvailable"]];
  If[key === Missing["NotAvailable"], Return[<||>]];
  familyOutputAssociation0[key, tuple]
];

spinProjectionArtifactData0::usage =
  "spinProjectionArtifactData0[artifact] reconstructs legacy {operator, tensors} sector data from one spin-projection artifact.";
spinProjectionArtifactData0[artifact_] := Which[
  artifact === None, {},
  Lookup[artifact, "Mode", None] =!= "SpinProjection", {},
  True,
    Module[{familyColumns},
      familyColumns = GroupBy[artifact["Columns"], #["FamilyIndex"] &];
      Table[
        {
          artifact["Families"][[i, "Template"]],
          Lookup[
            SortBy[Lookup[familyColumns, i, {}], #["CandidateIndex"] &],
            "TensorExpr",
            {}
          ]
        },
        {i, Length[artifact["Families"]]}
      ]
    ]
];


(* legacy compile core migrated from LegacyCore.m *)

spinProjectionSeededOrder::usage =
  "spinProjectionSeededOrder[list, seed, tag] deterministically orders a finite list using the probe seed and one local tag.";
spinProjectionSeededOrder[list_List, Automatic, tag_] := spinProjectionSeededOrder[list, 0, tag];
spinProjectionSeededOrder[list_List, seed_, tag_] := list[[Ordering[Hash[{seed, tag, #}] & /@ list]]];

spinProjectionOutputSymbolData::usage =
  "spinProjectionOutputSymbolData[op] returns the unresolved vector/spin slots for one compiled output operator template.";
spinProjectionOutputSymbolData[op_ /; RTest[op]] := Module[
  {typed, vectorSymbols, spinSymbols, spinChiralities},
  If[Cases[op, (dX | dXt)[__], Infinity] =!= {}, Return[$Failed]];
  typed = DeleteDuplicatesBy[spinTypedIndices[op], First];
  vectorSymbols = SortBy[First /@ Select[typed, Last[#] === "v" &], SymbolName];
  spinSymbols = SortBy[First /@ Select[typed, Last[#] === "s" &], SymbolName];
  spinChiralities = spinSymbolChiralities[op];
  If[AnyTrue[spinSymbols, !KeyExistsQ[spinChiralities, #] &], Return[$Failed]];
  <|
    "VectorSymbols" -> vectorSymbols,
    "SpinSymbols" -> spinSymbols,
    "SpinChiralities" -> Lookup[spinChiralities, spinSymbols]
  |>
];
spinProjectionOutputSymbolData[1] := <|
  "VectorSymbols" -> {},
  "SpinSymbols" -> {},
  "SpinChiralities" -> {}
|>;
spinProjectionOutputSymbolData[_] := $Failed;

spinProjectionBuildCompileContext0::usage =
  "spinProjectionBuildCompileContext0[ops, templateExpr] builds reusable compile context metadata for one sector model.";
spinProjectionBuildCompileContext0[ops_List, templateExpr_] := Module[
  {
    template,
    freeSpinSymbols,
    freeSpinChiralities,
    freeVectorGroups
  },
  template = spinProjectionSectorTemplate[ops, templateExpr];
  freeSpinSymbols = SortBy[Intersection[template["SpinSymbols"], template["FreeSymbols"]], SymbolName];
  freeSpinChiralities = Lookup[template["SpinChiralities"], freeSpinSymbols];
  freeVectorGroups = SortBy[template["FreeVectorGroups"], SymbolName @* First];
  <|
    "Template" -> template,
    "FreeSpinSymbols" -> freeSpinSymbols,
    "FreeSpinChiralities" -> freeSpinChiralities,
    "FreeSpinChirality" -> AssociationThread[freeSpinSymbols -> freeSpinChiralities],
    "FreeSpinSlot" -> AssociationThread[freeSpinSymbols -> Range[Length[freeSpinSymbols]]],
    "FreeVectorGroups" -> freeVectorGroups,
    "FreeVectorSlot" -> Association @ Flatten[MapIndexed[Thread[#1 -> First[#2]] &, freeVectorGroups], 1]
  |>
];

spinProjectionStateVectorAntisymmetricGroups0::usage =
  "spinProjectionStateVectorAntisymmetricGroups0[op, stateVectors] maps antisymmetric output vector-symbol groups onto compiled output state-vector sources.";
spinProjectionStateVectorAntisymmetricGroups0[op_ /; RTest[op], stateVectors_Association] := Select[
  Replace[
    spinProjectionOutputAntisymmetricVectorGroups0[op],
    group_List :> Cases[group, sym_ /; KeyExistsQ[stateVectors, sym] :> {2, stateVectors[sym]}],
    {1}
  ],
  Length[#] > 1 &
];
spinProjectionStateVectorAntisymmetricGroups0[_, _Association] := {};

spinProjectionVectorSource0::usage =
  "spinProjectionVectorSource0[sym, stateVectors, dummyVectors, context] maps one vector symbol to its compiled vector source descriptor.";
spinProjectionVectorSource0[sym_, stateVectors_Association, dummyVectors_Association, context_Association] := Which[
  IntegerQ[sym], {4, sym},
  KeyExistsQ[context["FreeVectorSlot"], sym], {1, context["FreeVectorSlot"][sym]},
  KeyExistsQ[stateVectors, sym], {2, stateVectors[sym]},
  KeyExistsQ[dummyVectors, sym], {3, dummyVectors[sym]},
  True, $Failed
];

spinProjectionSpinSource0::usage =
  "spinProjectionSpinSource0[sym, stateSpins, context] maps one spin symbol to its compiled spin source descriptor.";
spinProjectionSpinSource0[sym_, stateSpins_Association, context_Association] := Which[
  KeyExistsQ[context["FreeSpinSlot"], sym], {1, context["FreeSpinSlot"][sym]},
  KeyExistsQ[stateSpins, sym], {2, stateSpins[sym]},
  True, $Failed
];

spinProjectionMatrixDesc0::usage =
  "spinProjectionMatrixDesc0[part, stateVectors, dummyVectors, context] builds one compiled gamma-matrix descriptor for one parsed factor part.";
spinProjectionMatrixDesc0[
  part_Association,
  stateVectors_Association,
  dummyVectors_Association,
  context_Association
] := Module[{sources, links},
  sources = spinProjectionVectorSource0[#, stateVectors, dummyVectors, context] & /@ part["VectorSymbols"];
  If[MemberQ[sources, $Failed], Return[$Failed]];
  If[AllTrue[sources, First[#] === 4 &],
    links = Join[
      If[part["CTag"] === None, {}, {part["CTag"]}],
      MapThread[If[#1 === GammaUDHold, GammaUDHold[#2[[2]]], GammaDUHold[#2[[2]]]] &, {Head /@ part["VectorLinks"], sources}],
      part["TailLinks"]
    ];
    {
      part["CTag"],
      Replace[Head /@ part["VectorLinks"], {GammaUDHold -> 1, GammaDUHold -> 2}, 1],
      sources,
      part["TailLinks"],
      spinProjectionGammaFactorMatrix[links]
    },
    {
      part["CTag"],
      Replace[Head /@ part["VectorLinks"], {GammaUDHold -> 1, GammaDUHold -> 2}, 1],
      sources,
      part["TailLinks"],
      None
    }
  ]
];

spinProjectionScalarDesc0::usage =
  "spinProjectionScalarDesc0[part, stateSpins, stateSpinChiralities, stateVectors, dummyVectors, context] builds one compiled scalar descriptor for one parsed factor part.";
spinProjectionScalarDesc0[
  part_Association,
  stateSpins_Association,
  stateSpinChiralities_Association,
  stateVectors_Association,
  dummyVectors_Association,
  context_Association
] := Module[{left, right, matrix, pairChiralities, spinChirality},
  spinChirality[sym_] := Lookup[stateSpinChiralities, sym, Lookup[context["FreeSpinChirality"], sym, Missing["Unknown"]]];
  Switch[part["Kind"],
    "Delta",
    {
      0,
      spinProjectionVectorSource0[part["VectorSymbols"][[1]], stateVectors, dummyVectors, context],
      spinProjectionVectorSource0[part["VectorSymbols"][[2]], stateVectors, dummyVectors, context]
    },
    "Gamma",
    left = spinProjectionSpinSource0[part["Spinors"][[1]], stateSpins, context];
    right = spinProjectionSpinSource0[part["Spinors"][[2]], stateSpins, context];
    If[MemberQ[{left, right}, $Failed], Return[$Failed]];
    pairChiralities = spinChirality /@ part["Spinors"];
    If[
      part["VectorLinks"] === {} &&
        part["CTag"] === None &&
        part["TailLinks"] === {} &&
        AllTrue[pairChiralities, StringQ] &&
        SameQ @@ pairChiralities,
      {1, left, right},
      matrix = spinProjectionMatrixDesc0[part, stateVectors, dummyVectors, context];
      If[matrix === $Failed, $Failed, {2, left, right, matrix}]
    ],
    _,
    $Failed
  ]
];

spinProjectionSelectorSparseBasisFastPathQ0::usage =
  "spinProjectionSelectorSparseBasisFastPathQ0[tensor, stateSpins, stateVectors] is True exactly when a sparse-basis tensor can reuse selector gamma-kernel refs in scalar-output RHS compile.";
spinProjectionSelectorSparseBasisFastPathQ0[tensor_, stateSpins_Association, stateVectors_Association] :=
  spinProjectionSparseBasisRecordQ[tensor] &&
  Keys[stateSpins] === {} &&
  Keys[stateVectors] === {} &&
  Lookup[tensor["SelectorFamilyCache"], "Mode", None] === "sharedKernel";

spinProjectionSelectorCachedSpinSource0::usage =
  "spinProjectionSelectorCachedSpinSource0[slot, selectorCache, record, context] remaps one selector cached free-spin slot into the compiled RHS free-spin slot namespace.";
spinProjectionSelectorCachedSpinSource0[slot_, selectorCache_Association, record_Association, context_Association] := Switch[slot[[1]],
  1,
  spinProjectionSpinSource0[
    Lookup[record["CanonicalToActualSpin"], selectorCache["SpinSymbols"][[slot[[2]]]], Missing["Unassigned"]],
    <||>,
    context
  ],
  _,
  $Failed
];

spinProjectionSelectorCachedVectorSource0::usage =
  "spinProjectionSelectorCachedVectorSource0[slot, selectorCache, record, context] remaps one selector cached free-vector slot into the compiled RHS free-vector slot namespace.";
spinProjectionSelectorCachedVectorSource0[slot_, selectorCache_Association, record_Association, context_Association] := Switch[slot[[1]],
  1,
  spinProjectionVectorSource0[
    Lookup[record["CanonicalToActualVector"], selectorCache["VectorSymbols"][[slot[[2]]]], Missing["Unassigned"]],
    <||>,
    <||>,
    context
  ],
  4,
  slot,
  _,
  $Failed
];

spinProjectionSelectorCachedGammaKernelRefs0::usage =
  "spinProjectionSelectorCachedGammaKernelRefs0[record, context] remaps selector cached gamma-kernel refs onto compiled RHS free-slot descriptors.";
spinProjectionSelectorCachedGammaKernelRefs0[record_Association, context_Association] := Module[{selectorCache, refs},
  selectorCache = record["SelectorFamilyCache"];
  refs = Map[
    Function[ref,
      <|
        "Key" -> ref["Key"],
        "SpinSlots" -> (spinProjectionSelectorCachedSpinSource0[#, selectorCache, record, context] & /@ ref["SpinSlots"]),
        "VectorSlots" -> (spinProjectionSelectorCachedVectorSource0[#, selectorCache, record, context] & /@ ref["VectorSlots"])
      |>
    ],
    selectorCache["GammaKernelRefs"]
  ];
  If[MemberQ[refs, _?(MemberQ[#, $Failed, Infinity] &)], $Failed, refs]
];

spinProjectionOutputSpinSupportPartRecipe0::usage =
  "spinProjectionOutputSpinSupportPartRecipe0[part, outputSpinSlot] compiles one scalar part into a solve-time output-spin support recipe or Nothing when the part is irrelevant.";
spinProjectionOutputSpinSupportPartRecipe0[part_, outputSpinSlot_Integer?Positive] := Module[
  {kind = part[[1]], left = part[[2]], right = part[[3]]},
  Switch[kind,
    0,
    Nothing,
    1,
    Which[
      left[[1]] === 2 && left[[2]] === outputSpinSlot && right[[1]] === 1,
        <|"Mode" -> "FreeSpinEquality", "FreeSpinSlot" -> right[[2]]|>,
      right[[1]] === 2 && right[[2]] === outputSpinSlot && left[[1]] === 1,
        <|"Mode" -> "FreeSpinEquality", "FreeSpinSlot" -> left[[2]]|>,
      left[[1]] === 2 && left[[2]] === outputSpinSlot,
        <|"Mode" -> "Fallback"|>,
      right[[1]] === 2 && right[[2]] === outputSpinSlot,
        <|"Mode" -> "Fallback"|>,
      True,
        Nothing
    ],
    2,
    Which[
      left[[1]] === 2 && left[[2]] === outputSpinSlot && right[[1]] === 1,
        <|"Mode" -> "GammaColumnSupport", "FreeSpinSlot" -> right[[2]], "Desc" -> part[[4]]|>,
      right[[1]] === 2 && right[[2]] === outputSpinSlot && left[[1]] === 1,
        <|"Mode" -> "GammaRowSupport", "FreeSpinSlot" -> left[[2]], "Desc" -> part[[4]]|>,
      left[[1]] === 2 && left[[2]] === outputSpinSlot,
        <|"Mode" -> "Fallback"|>,
      right[[1]] === 2 && right[[2]] === outputSpinSlot,
        <|"Mode" -> "Fallback"|>,
      True,
        Nothing
    ],
    _,
    <|"Mode" -> "Fallback"|>
  ]
];

spinProjectionOutputSpinSupportRecipe0::usage =
  "spinProjectionOutputSpinSupportRecipe0[parts, outputSpinSlot] compiles the solve-time support recipe for one term in a one-output-spin family.";
spinProjectionOutputSpinSupportRecipe0[parts_List, outputSpinSlot_Integer?Positive] := Module[{recipes},
  recipes = DeleteCases[
    spinProjectionOutputSpinSupportPartRecipe0[#, outputSpinSlot] & /@ parts,
    Nothing
  ];
  If[
    MemberQ[recipes, _Association?(Lookup[#, "Mode", None] === "Fallback" &)],
    <|"Mode" -> "Fallback"|>,
    Which[
      recipes === {}, <|"Mode" -> "All"|>,
      Length[recipes] == 1, First[recipes],
      True, <|"Mode" -> "Intersection", "Parts" -> recipes|>
    ]
  ]
];

spinProjectionEqualityClasses0::usage =
  "spinProjectionEqualityClasses0[equalities] returns the exposed-vector equality classes implied by normalized compiled term equalities.";
spinProjectionEqualityClasses0[equalities_List] := Module[
  {parents = <||>, sources, find, join, roots},
  If[equalities === {}, Return[{}]];
  sources = DeleteDuplicates @ Flatten[equalities, 1];
  Scan[Function[src, parents[src] = src], sources];
  find[src_] := parents[src] = If[parents[src] === src, src, find[parents[src]]];
  join[left_, right_] := Module[{leftRoot = find[left], rightRoot = find[right]},
    If[leftRoot =!= rightRoot, parents[rightRoot] = leftRoot]
  ];
  Scan[join @@ # &, equalities];
  roots = DeleteDuplicates[find /@ sources];
  DeleteDuplicates @ Map[
    Function[root, DeleteDuplicates @ Select[sources, find[#] === root &]],
    roots
  ]
];

spinProjectionOutputAntisymmetricEqualityVanishesQ0::usage =
  "spinProjectionOutputAntisymmetricEqualityVanishesQ0[vectorEqualities, antisymmetricGroups] is True when compiled equalities force two antisymmetrized output vector slots to coincide.";
spinProjectionOutputAntisymmetricEqualityVanishesQ0[vectorEqualities_List, antisymmetricGroups_List] := Module[{classes},
  If[vectorEqualities === {} || antisymmetricGroups === {}, Return[False]];
  classes = spinProjectionEqualityClasses0[vectorEqualities];
  AnyTrue[
    antisymmetricGroups,
    Function[group,
      AnyTrue[classes, Length[Intersection[group, #]] > 1 &]
    ]
  ]
];

spinProjectionStructuralSortKey0::usage =
  "spinProjectionStructuralSortKey0[expr] returns one deterministic lexical sort key for nested compiled spin-projection metadata.";
spinProjectionStructuralSortKey0[expr_] := ToString[InputForm[expr]];

spinProjectionApplyOutputSlotPermutation0::usage =
  "spinProjectionApplyOutputSlotPermutation0[expr, rules] relabels compiled output-state vector-slot descriptors by one exact antisymmetric-slot permutation.";
spinProjectionApplyOutputSlotPermutation0[expr_, rules_List] := If[rules === {}, expr, expr /. Dispatch[rules]];

spinProjectionAntisymmetricGroupActions0::usage =
  "spinProjectionAntisymmetricGroupActions0[groups] enumerates exact combined output-slot permutation actions and signs for one antisymmetric output-slot decomposition.";
spinProjectionAntisymmetricGroupActions0[groups_List] := spinProjectionAntisymmetricGroupActions0[groups] = Module[
  {groupActions},
  groupActions = Map[
    Function[group,
      Module[{position = AssociationThread[group -> Range[Length[group]]]},
        Map[
          Function[perm,
            <|
              "Rules" -> Thread[group -> perm],
              "Sign" -> Signature[Lookup[position, perm]]
            |>
          ],
          Permutations[group]
        ]
      ]
    ],
    Select[groups, Length[#] > 1 &]
  ];
  If[groupActions === {}, Return[{<|"Rules" -> {}, "Sign" -> 1|>}]];
  Map[
    Function[actionTuple,
      <|
        "Rules" -> Flatten[Lookup[actionTuple, "Rules", {}], 1],
        "Sign" -> Times @@ Lookup[actionTuple, "Sign", 1]
      |>
    ],
    Tuples[groupActions]
  ]
];

spinProjectionCompiledTermDedupKey0::usage =
  "spinProjectionCompiledTermDedupKey0[term, antisymmetricGroups] returns one canonical duplicate-elimination key modulo antisymmetric output-slot relabelings, or Missing[\"ZeroOrbit\"] when an odd slot symmetry annihilates the term.";
spinProjectionCompiledTermDedupKey0[term_Association, antisymmetricGroups_List] := Module[
  {baseKey, transformed, grouped, canonicalKeyString},
  baseKey = With[
    {
      spinEqualities = SortBy[Lookup[term, "SpinEqualities", {}], spinProjectionStructuralSortKey0],
      vectorEqualities = SortBy[Lookup[term, "VectorEqualities", {}], spinProjectionStructuralSortKey0],
      gammaKernelRefs = SortBy[Lookup[term, "GammaKernelRefs", {}], spinProjectionStructuralSortKey0],
      outputSpinSupportRecipe = Lookup[term, "OutputSpinSupportRecipe", <||>]
    },
    HoldComplete[spinEqualities, vectorEqualities, gammaKernelRefs, outputSpinSupportRecipe]
  ];
  If[Select[antisymmetricGroups, Length[#] > 1 &] === {}, Return[baseKey]];
  transformed = Map[
    Function[action,
      <|
        "Key" -> spinProjectionApplyOutputSlotPermutation0[baseKey, action["Rules"]],
        "Sign" -> action["Sign"]
      |>
    ],
    spinProjectionAntisymmetricGroupActions0[antisymmetricGroups]
  ];
  grouped = GatherBy[transformed, spinProjectionStructuralSortKey0[Lookup[#, "Key", HoldComplete[]]] &];
  If[
    AnyTrue[
      grouped,
      MemberQ[DeleteDuplicates[Lookup[#, "Sign", 1]], 1] && MemberQ[DeleteDuplicates[Lookup[#, "Sign", 1]], -1] &
    ],
    Return[Missing["ZeroOrbit"]]
  ];
  canonicalKeyString = First @ Sort[spinProjectionStructuralSortKey0[Lookup[#, "Key", HoldComplete[]]] & /@ transformed];
  Lookup[
    SelectFirst[transformed, spinProjectionStructuralSortKey0[Lookup[#, "Key", HoldComplete[]]] === canonicalKeyString &],
    "Key",
    baseKey
  ]
];

spinProjectionCompileTensorTerm0::usage =
  "spinProjectionCompileTensorTerm0[tensor, stateSpins, stateSpinChiralities, stateVectors, context, columnIndex, antisymmetricOutputVectorGroups] compiles one tensor candidate into one term record and returns the next column index.";
spinProjectionCompileTensorTerm0[
  tensor_,
  stateSpins_Association,
  stateSpinChiralities_Association,
  stateVectors_Association,
  context_Association,
  columnIndex_Integer?NonNegative,
  antisymmetricOutputVectorGroups_List
] := Module[
  {
    nextColumn = columnIndex,
    tensorExpr,
    factors,
    tensorFactors,
    scalarFactor,
    parsedTensor,
    indexSymbols,
    dummySymbols,
    dummyVectors,
    parts,
    normalized,
    kernelData,
    outputSpinSupportRecipe,
    overallScalarFactor
  },
  tensorExpr = spinProjectionTensorExpr0[tensor];
  factors = If[Head[tensorExpr] === Times, List @@ tensorExpr, {tensorExpr}];
  tensorFactors = Select[factors, candidateFactorQ];
  scalarFactor = Times @@ Select[factors, !candidateFactorQ[#] &];
  indexSymbols = DeleteDuplicates[First /@ spinTypedIndices[tensorExpr]];
  If[indexSymbols =!= {} && !FreeQ[scalarFactor, Alternatives @@ indexSymbols], Return[$Failed]];
  parsedTensor = If[tensorFactors === {}, parseCandidate[1], parseCandidate[Times @@ tensorFactors]];
  If[parsedTensor === $Failed, Return[$Failed]];
  dummySymbols = SortBy[
    Complement[
      DeleteDuplicates @ Select[
        Flatten[Lookup[parsedTensor["FactorParts"], "VectorSymbols", {}]],
        Head[#] === Symbol &
      ],
      Keys[stateVectors],
      Keys[context["FreeVectorSlot"]]
    ],
    SymbolName
  ];
  dummyVectors = AssociationThread[dummySymbols -> Range[Length[dummySymbols]]];
  parts = spinProjectionScalarDesc0[
    #,
    stateSpins,
    stateSpinChiralities,
    stateVectors,
    dummyVectors,
    context
  ] & /@ parsedTensor["FactorParts"];
  If[MemberQ[parts, $Failed], Return[$Failed]];
  normalized = spinProjectionNormalizeCompiledTermParts[parts];
  If[normalized === $Failed, Return[$Failed]];
  If[
    spinProjectionOutputAntisymmetricEqualityVanishesQ0[
      normalized["VectorEqualities"],
      antisymmetricOutputVectorGroups
    ],
    Return[<|"NextColumn" -> columnIndex, "Term" -> None|>]
  ];
  outputSpinSupportRecipe = If[
    Length[stateSpins] == 1,
    spinProjectionOutputSpinSupportRecipe0[parts, First[Values[stateSpins]]],
    <|"Mode" -> "Fallback"|>
  ];
  kernelData = If[
    spinProjectionSelectorSparseBasisFastPathQ0[tensor, stateSpins, stateVectors],
    Module[{refs},
      refs = spinProjectionSelectorCachedGammaKernelRefs0[tensor, context];
      If[refs === $Failed,
        $Failed,
        <|
          "ScalarFactor" -> tensor["SelectorFamilyCache", "ScalarFactor"],
          "KernelRefs" -> refs
        |>
      ]
    ],
    spinProjectionGammaKernelData[If[normalized["ScalarFactor"] === 0, {}, normalized["GammaParts"]]]
  ];
  If[kernelData === $Failed, Return[$Failed]];
  overallScalarFactor = scalarFactor normalized["ScalarFactor"] kernelData["ScalarFactor"];
  If[overallScalarFactor === 0, Return[<|"NextColumn" -> columnIndex, "Term" -> None|>]];
  nextColumn = columnIndex + 1;
  <|
    "NextColumn" -> nextColumn,
    "Term" -> <|
      "Column" -> nextColumn,
      "ScalarFactor" -> overallScalarFactor,
      "Parts" -> parts,
      "DummyCount" -> Length[dummySymbols],
      "SpinEqualities" -> normalized["SpinEqualities"],
      "VectorEqualities" -> normalized["VectorEqualities"],
      "GammaKernelRefs" -> kernelData["KernelRefs"],
      "OutputSpinSupportRecipe" -> outputSpinSupportRecipe
    |>
  |>
];

spinProjectionCompileFamily0::usage =
  "spinProjectionCompileFamily0[{op, tensors}, familyIndex, context, columnIndex] compiles one output family and returns family data, family columns, and the next column index.";
spinProjectionCompileFamily0[
  {op_, tensors_},
  familyIndex_Integer?Positive,
  context_Association,
  columnIndex_Integer?NonNegative
] := Module[
  {
    outputData,
    stateSpins,
    stateSpinChiralities,
    stateVectors,
    antisymmetricOutputVectorGroups,
    nextColumn = columnIndex,
    outputAssociationKey,
    reaped,
    terms,
    columns,
    compileResult,
    term,
    tensor,
    tensorExpr,
    repExpr,
    candidateNextColumn,
    dedupKey,
    seenDedupKeys = <||>
  },
  outputData = spinProjectionOutputSymbolData[op];
  If[outputData === $Failed, Return[$Failed]];
  stateSpins = AssociationThread[outputData["SpinSymbols"] -> Range[Length[outputData["SpinSymbols"]]]];
  stateSpinChiralities = AssociationThread[outputData["SpinSymbols"] -> outputData["SpinChiralities"]];
  stateVectors = AssociationThread[outputData["VectorSymbols"] -> Range[Length[outputData["VectorSymbols"]]]];
  antisymmetricOutputVectorGroups = spinProjectionStateVectorAntisymmetricGroups0[op, stateVectors];
  reaped = Reap[
    Do[
      tensor = tensors[[candidateIndex]];
      tensorExpr = spinProjectionTensorExpr0[tensor];
      If[tensorCandidateVanishesQ0[tensorExpr], Continue[]];
      compileResult = spinProjectionCompileTensorTerm0[
        tensor,
        stateSpins,
        stateSpinChiralities,
        stateVectors,
        context,
        nextColumn,
        antisymmetricOutputVectorGroups
      ];
      If[compileResult === $Failed, Return[$Failed]];
      If[compileResult["Term"] === None, Continue[]];
      candidateNextColumn = compileResult["NextColumn"];
      term = compileResult["Term"];
      dedupKey = spinProjectionCompiledTermDedupKey0[term, antisymmetricOutputVectorGroups];
      If[MissingQ[dedupKey] || KeyExistsQ[seenDedupKeys, dedupKey], Continue[]];
      seenDedupKeys[dedupKey] = True;
      nextColumn = candidateNextColumn;
      repExpr = tensorExpr op;
      Sow[
        <|
          "Index" -> term["Column"],
          "RepresentativeExpr" -> repExpr,
          "TensorExpr" -> tensorExpr,
          "FamilyIndex" -> familyIndex,
          "CandidateIndex" -> candidateIndex
        |> ,
        "Columns"
      ];
      Sow[
        Join[term, <|"RepresentativeExpr" -> repExpr, "TensorExpr" -> tensorExpr|>],
        "Terms"
      ],
      {candidateIndex, Length[tensors]}
    ],
    _,
    Rule
  ];
  If[reaped === $Failed, Return[$Failed]];
  terms = Lookup[Association[reaped[[2]]], "Terms", {}];
  columns = Lookup[Association[reaped[[2]]], "Columns", {}];
  outputAssociationKey = spinProjectionRegisterFamilyOutputTemplate0[
    op,
    outputData["SpinSymbols"],
    outputData["SpinChiralities"],
    outputData["VectorSymbols"]
  ];
  <|
    "Family" -> <|
      "Template" -> op,
      "SpinSymbols" -> outputData["SpinSymbols"],
      "SpinChiralities" -> outputData["SpinChiralities"],
      "VectorSymbols" -> outputData["VectorSymbols"],
      "OutputAssociationKey" -> outputAssociationKey,
      "OutputSpinSupportFastPathQ" ->
        Length[outputData["SpinSymbols"]] == 1 &&
        AllTrue[terms, Lookup[Lookup[#, "OutputSpinSupportRecipe", <||>], "Mode", None] =!= "Fallback" &],
      "Terms" -> terms
    |>,
    "Columns" -> columns,
    "NextColumn" -> nextColumn
  |>
];

compileSpinProjectionSectorModel::usage =
  "compileSpinProjectionSectorModel[sector, ops, weight, data] builds the direct numeric RHS model for one supported chiral sector straight from outgoing tensor data.";
compileSpinProjectionSectorModel[sector : ("Holo" | "Anti"), ops_List, weight_, data_List] := Module[
  {
    templateExpr,
    context,
    columns = {},
    vars,
    expr,
    families,
    pieceColumn = 0,
    familyResult
  },
  If[
    ops === {},
    Return[
      <|
        "Sector" -> sector,
        "Ops" -> ops,
        "Weight" -> weight,
        "TargetWeight" -> weight,
        "Expr" -> If[weight === 0, 1, 0],
        "Vars" -> {},
        "VarCount" -> 0,
        "Columns" -> {},
        "Families" -> {},
        "FreeSpinSymbols" -> {},
        "FreeSpinChiralities" -> {},
        "FreeVectorGroups" -> {}
      |>
    ]
  ];
  If[
    data === {},
    Return[
      <|
        "Sector" -> sector,
        "Ops" -> ops,
        "Weight" -> weight,
        "TargetWeight" -> weight,
        "Expr" -> 0,
        "Vars" -> {},
        "VarCount" -> 0,
        "Columns" -> {},
        "Families" -> {},
        "FreeSpinSymbols" -> {},
        "FreeSpinChiralities" -> {},
        "FreeVectorGroups" -> {}
      |>
    ]
  ];
  templateExpr = Total @ Flatten[Function[pair, (# pair[[1]]) & /@ pair[[2]]] /@ data];
  context = spinProjectionBuildCompileContext0[ops, templateExpr];
  families = Table[
    familyResult = spinProjectionCompileFamily0[data[[familyIndex]], familyIndex, context, pieceColumn];
    If[familyResult === $Failed, Return[$Failed]];
    pieceColumn = familyResult["NextColumn"];
    columns = Join[columns, familyResult["Columns"]];
    familyResult["Family"],
    {familyIndex, Length[data]}
  ];
  columns = SortBy[columns, #["Index"] &];
  vars = spinProjectedCoefficient /@ Range[Length[columns]];
  columns = Map[Append[#, "Var" -> spinProjectedCoefficient[#["Index"]]] &, columns];
  expr = If[
    columns === {},
    0,
    Total[(#["Var"] #["RepresentativeExpr"]) & /@ columns]
  ];
  <|
    "Sector" -> sector,
    "Ops" -> ops,
    "Weight" -> weight,
    "TargetWeight" -> None,
    "Expr" -> expr,
    "Vars" -> vars,
    "VarCount" -> Length[vars],
    "Columns" -> columns,
    "Families" -> families,
    "FreeSpinSymbols" -> context["FreeSpinSymbols"],
    "FreeSpinChiralities" -> context["FreeSpinChiralities"],
    "FreeVectorGroups" -> context["FreeVectorGroups"]
  |>
];

End[];


EndPackage[];
