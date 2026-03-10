(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`OPE`TypeII`FlatSpace`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];
Needs["StringCode`Symbols`TypeII`FlatSpace`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`TypeII`"];
Needs["StringCode`Operators`"];
Needs["StringCode`OPE`"];
Needs["StringCode`Taylor`"];
Needs["StringCode`BasisGeneration`TypeII`"];
Needs["StringCode`BasisGeneration`TypeII`FlatSpace`"];
Needs["StringCode`OPE`TypeII`FlatSpace`CountSinglet`"];
Needs["StringCode`OPE`TypeII`FlatSpace`GammaMatrices`"];
Needs["StringCode`OPE`TypeII`FlatSpace`GammaProductGrammar`"];
Needs["StringCode`OPE`TypeII`FlatSpace`IndependentTensorStructures`"];
Needs["StringCode`OPE`TypeII`FlatSpace`TensorStructures`"];
Needs["StringCode`OPE`TypeII`FlatSpace`TensorStructuresVisualize`"];


(* ::Section:: *)
(*Declare public variables and methods*)

(* ::Section:: *)
(*Logic*)


Begin["Private`"];

projectionExponentReplacement = {\[Alpha]p -> 0};
If[FreeQ[Options[OPEProjected], "RandomSeed" -> _], Options[OPEProjected] = Append[Options[OPEProjected], "RandomSeed" -> Automatic]];
OPEProjected::spinsolve =
  "Could not determine a unique spin-field projection in the `1` sector after `2` probe attempts.";

hasSpinFieldQ::usage = "Checks whether a normal-ordered operator contains TypeII spin fields S or St.";
hasSpinFieldQ[Ra_ /; RTest[Ra]] := AnyTrue[List @@ Ra, MemberQ[{S, St}, Head[#]] &];


OPEWickList::usage = "OPEWickList[rList] folds OPEWick over a list of normal-ordered products.";
OPEWickList[rList_List] := Which[
  rList === {}, 1,
  Length[rList] === 1, First[rList],
  True, OPEWick[First[rList], OPEWickList[Rest[rList]]]
];

psiExpPhiHeads = {\[Psi], \[Psi]t, d\[Phi], d\[Phi]t, exp\[Phi]b, exp\[Phi]f, exp\[Phi]tb, exp\[Phi]tf};
purePsiExpPhiQ::usage = "purePsiExpPhiQ[Ra] is True when Ra contains only ψ/∂ϕ/expϕ TypeII fields handled by the bosonized free-field OPE path.";
purePsiExpPhiQ[Ra_ /; RTest[Ra]] := AllTrue[List @@ Ra, MemberQ[psiExpPhiHeads, Head[#]] &];

pictureContributionHolo::usage = "Returns the picture number contribution of a holomorphic field (S or expϕf/expϕb).";
pictureContributionHolo[field_] := Switch[
  SymbolName[Head[field]],
  "S", field[[2]],
  "expϕf" | "expϕb", field[[1]],
  _, 0
];

pictureContributionAntiHolo::usage = "Returns the picture number contribution of an antiholomorphic field (St or expϕtf/expϕtb).";
pictureContributionAntiHolo[field_] := Switch[
  SymbolName[Head[field]],
  "St", field[[2]],
  "expϕtf" | "expϕtb", field[[1]],
  _, 0
];

totalInputPicture::usage = "Computes total picture number from a list of R-operators using the given contribution function.";
totalInputPicture[ops_List, contributionFn_] :=
  Total[contributionFn /@ Flatten[List @@ # & /@ Select[ops, RTest]]];

mergeRepresentations::usage = "Merges a list of representation associations into a single combined association.";
mergeRepresentations[reps_List] := <|
  "vector" -> Flatten[#["vector"] & /@ reps],
  "spinor" -> Flatten[#["spinor"] & /@ reps, 1]
|>;

spinProjectionPlaceholderSymbol::usage =
  "spinProjectionPlaceholderSymbol[kind, n] returns a fresh shared-private placeholder symbol used to build abstract tensor bases.";
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

spinProjectionVectorMatterHeads::usage =
  "spinProjectionVectorMatterHeads[psiHead] returns the vector-carrying matter heads relevant to one spin-field projection sector.";
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

extractMatterRepresentationDataList::usage =
  "extractMatterRepresentationDataList[ops, psiHead, spinHead] merges abstract representation data across a list of normal-ordered operators.";
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

inputGSOParityString::usage = "Computes the product of GSO parities of input R-operators and returns \"Even\" or \"Odd\".";
inputGSOParityString[ops_List] := Module[{parity},
  parity = Times @@ (GSOParity /@ ops);
  If[parity === 1, "Even", "Odd"]
];

generateSpinFieldOPEData::usage = "Generates {operator, tensorStructures} pairs for a spin field OPE in one chiral sector.";
generateSpinFieldOPEData[
  ops_List,
  targetWeight_,
  basisGeneratorFn_,
  psiHead_, spinHead_,
  pictureContributionFn_,
  seed_: Automatic
] := Module[
  {incomingData, incomingReps, totalPicture, gsoParity, basisOps, outgoingData, tensorStructures},

  incomingData = extractMatterRepresentationDataList[ops, psiHead, spinHead];
  incomingReps = incomingData["Representations"];

  totalPicture = totalInputPicture[ops, pictureContributionFn];
  gsoParity = inputGSOParityString[ops];

  basisOps = basisGeneratorFn[targetWeight, totalPicture,
    "GSOParity" -> gsoParity, "OutputRepresentation" -> "Operators"];
  If[basisOps === {}, Return[{}]];

  DeleteCases[
    Function[op,
      outgoingData = extractMatterRepresentationData[op, psiHead, spinHead, incomingData["Counters"]];
      tensorStructures = findIndependentTensorStructures[
        incomingReps,
        outgoingData["Representations"],
        "RandomSeed" -> seed
      ];
      If[tensorStructures === $Failed || tensorStructures === {},
        Nothing,
        {op, tensorStructures /. Join[incomingData["EvaluationRules"], outgoingData["EvaluationRules"]]}
      ]
    ] /@ basisOps,
    Nothing
  ]
];

OPE[Ra_, Rb_] := OPEWick[Ra, Rb] /; (
  RTest[Ra] && RTest[Rb] &&
  purePsiExpPhiQ[Ra] && purePsiExpPhiQ[Rb]
);

combineChiral::usage = "combineChiral[a, b] rejoins holomorphic and antiholomorphic projected factors into one normal-ordered expression.";
combineChiral[a_, b_] := Which[
  a === 0 || b === 0, 0,
  a === 1, b,
  b === 1, a,
  True, R[a, b]
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

getOutgoingOperatorsTensors::usage = "Returns sign and outgoing spin-field tensor data split into holomorphic/antiholomorphic sectors.";
getOutgoingOperatorsTensors[ops_List, wH_, wA_, seed_: Automatic] := Module[
  {localLists, splitLists, sign, sectorData, targetWeights = <|"Holo" -> wH, "Anti" -> wA|>, spec, sectorOps},
  localLists = List @@ # & /@ ops;
  splitLists = splitOperators[#, isHolomorphic, isAntiHolomorphic] & /@ localLists;
  sign = If[Flatten[localLists] === {}, 1, factorizationSign[Flatten[localLists], isHolomorphic, isAntiHolomorphic]];
  sectorData = AssociationMap[
    Function[sector,
      spec = spinProjectionSectorSpec[sector];
      sectorOps = Select[R @@@ (splitLists[[All, spec["SplitIndex"]]]), RTest];
      <|
        "Ops" -> sectorOps,
        "Data" -> If[
          sectorOps === {},
          {},
          generateSpinFieldOPEData[
            sectorOps,
            targetWeights[sector],
            spec["BasisGenerator"],
            spec["PsiHead"],
            spec["SpinHead"],
            spec["PictureContribution"],
            seed
          ]
        ]
      |>
    ],
    {"Holo", "Anti"}
  ];
  <|
    "sign" -> sign,
    "holoOps" -> sectorData["Holo"]["Ops"],
    "antiOps" -> sectorData["Anti"]["Ops"],
    "holoData" -> sectorData["Holo"]["Data"],
    "antiData" -> sectorData["Anti"]["Data"]
  |>
];

spinProjectedCoefficient::usage = "spinProjectedCoefficient[i] is an internal placeholder for one unresolved spin-field OPE coefficient.";

attachSpinProjectionCoefficients::usage =
  "attachSpinProjectionCoefficients[data, offset] builds a symbolic tensor ansatz and returns {expr, vars, lastUsedIndex}.";
attachSpinProjectionCoefficients[data_List, offset_Integer : 0] := Module[
  {i = offset, terms = {}, vars = {}, var},
  Scan[
    Function[pair,
      With[{op = pair[[1]], tensors = pair[[2]]},
        Scan[
          Function[tensor,
            i++;
            var = spinProjectedCoefficient[i];
            vars = Append[vars, var];
            terms = Append[terms, var tensor op];
          ],
          tensors
        ]
      ]
    ],
    data
  ];
  {If[terms === {}, 0, Total[terms]], vars, i}
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


spinIterationValues::usage = "spinIterationValues[chirality] returns the explicit spin-vector basis used to randomize or sum over that chirality.";
spinIterationValues["antichiral"] := antichiralspins;
spinIterationValues[_] := chiralspins;

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

spinProjectionGammaLinkMatrix::usage =
  "spinProjectionGammaLinkMatrix[link] returns the exact 16x16 matrix associated with one concrete gamma-chain link.";
spinProjectionGammaLinkMatrix[CUDHold] := CUD;
spinProjectionGammaLinkMatrix[CDUHold] := CDU;
spinProjectionGammaLinkMatrix[GammaUDHold[mu_Integer]] /; 1 <= mu <= 10 := GammaUD[mu];
spinProjectionGammaLinkMatrix[GammaDUHold[mu_Integer]] /; 1 <= mu <= 10 := GammaDU[mu];
spinProjectionGammaLinkMatrix[Gamma11UUHold[]] := Gamma11UU;
spinProjectionGammaLinkMatrix[Gamma11DDHold[]] := Gamma11DD;
spinProjectionGammaLinkMatrix[_] := $Failed;

spinProjectionAntisymmetrizedMatrix::usage =
  "spinProjectionAntisymmetrizedMatrix[vectorLinks] returns the exact antisymmetrized gamma matrix for one concrete vector-link list.";
spinProjectionAntisymmetrizedMatrix[{}] := IdentityMatrix[Length[CUD]];
spinProjectionAntisymmetrizedMatrix[vectorLinks_List] := spinProjectionAntisymmetrizedMatrix[vectorLinks] = Module[
  {rank = Length[vectorLinks]},
  1/rank Sum[
    (-1)^(pos - 1) spinProjectionGammaLinkMatrix[vectorLinks[[pos]]] . spinProjectionAntisymmetrizedMatrix[Delete[vectorLinks, pos]],
    {pos, 1, rank}
  ]
];

spinProjectionGammaFactorMatrix::usage =
  "spinProjectionGammaFactorMatrix[links] returns the exact matrix represented by one concrete GammaAntisymmetricProductHold link list.";
spinProjectionGammaFactorMatrix[{CUDHold, GammaDUHold[mu_Integer]}] /; 1 <= mu <= 10 := CGamma[mu];
spinProjectionGammaFactorMatrix[{CDUHold, GammaUDHold[mu_Integer]}] /; 1 <= mu <= 10 := CIGamma[mu];
spinProjectionGammaFactorMatrix[links_List] := Module[
  {cTag, coreLinks, vectorLinks, tailLinks, pairingMatrix},
  If[links === {},
    pairingMatrix = Switch[
      gammaProductSpinorChiralities[links],
      {"chiral", "antichiral"}, CUD,
      {"antichiral", "chiral"}, CDU,
      _, IdentityMatrix[Length[CUD]]
    ];
    Return[pairingMatrix];
  ];
  cTag = If[MatchQ[First[links], CUDHold | CDUHold], First[links], None];
  coreLinks = If[cTag === None, links, Rest[links]];
  vectorLinks = Select[coreLinks, gammaVectorLinkQ];
  tailLinks = Select[coreLinks, !gammaVectorLinkQ[#] &];
  Fold[
    Dot,
    If[cTag === None, IdentityMatrix[Length[CUD]], spinProjectionGammaLinkMatrix[cTag]],
    Join[
      {spinProjectionAntisymmetrizedMatrix[vectorLinks]},
      spinProjectionGammaLinkMatrix /@ tailLinks
    ]
  ]
];

spinProjectionGammaFactorValue::usage =
  "spinProjectionGammaFactorValue[factor] evaluates one concrete GammaAntisymmetricProductHold factor to its exact scalar matrix element when possible.";
spinProjectionGammaFactorValue[factor_GammaAntisymmetricProductHold] := Module[
  {links = factor[[1]], spinors = {factor[[2]], factor[[3]]}, chiralities, indices, matrix},
  chiralities = gammaProductSpinorChiralities[links];
  indices = MapThread[spinProjectionSpinorBasisIndex, {spinors, chiralities}];
  If[!AllTrue[indices, IntegerQ], Return[factor]];
  matrix = spinProjectionGammaFactorMatrix[links];
  If[!MatrixQ[matrix], Return[factor]];
  matrix[[indices[[1]], indices[[2]]]]
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

spinProjectionMaxAttempts::usage = "Maximum number of randomized probes used to solve one spin-field projected OPE.";
spinProjectionMaxAttempts = 40;

spinRandomizationTemplate::usage =
  "spinRandomizationTemplate[holoOps, antiOps, hExpr, aExpr] precomputes shared index-randomization metadata for one spin-field projected OPE solve.";
spinRandomizationTemplate[holoOps_List, antiOps_List, hExpr_, aExpr_] := Module[
  {
    obj = {holoOps, antiOps, hExpr, aExpr},
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
  typedInputs = spinTypedIndices[{holoOps, antiOps}];
  typedRHS = spinTypedIndices[{hExpr, aExpr}];
  typed = Join[typedInputs, typedRHS];
  countsInput = Counts[First /@ typedInputs];
  countsRHS = Counts[First /@ typedRHS];
  spinChiralities = spinSymbolChiralities[obj];
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
  freeVectorSymbols = Intersection[vec, free];
  freeVectorGroups = spinProjectionConnectedSymbolGroups[
    freeVectorSymbols,
    spinProjectionVectorConstraintPairs[{hExpr, aExpr}, freeVectorSymbols]
  ];
  <|
    "HoloOps" -> holoOps,
    "AntiOps" -> antiOps,
    "HoloExpr" -> hExpr,
    "AntiExpr" -> aExpr,
    "VectorSymbols" -> vec,
    "SpinSymbols" -> spi,
    "AllSymbols" -> allSymbols,
    "FreeSymbols" -> free,
    "FreeVectorGroups" -> freeVectorGroups,
    "DummySymbols" -> dum,
    "SpinChiralities" -> spinChiralities
  |>
];

spinProjectionAttemptSeed::usage =
  "spinProjectionAttemptSeed[baseSeed, attempt] derives a deterministic per-attempt seed for repeated randomized probes.";
spinProjectionAttemptSeed[Automatic, _Integer?Positive] := Automatic;
spinProjectionAttemptSeed[seed_, attempt_Integer?Positive] := Hash[{seed, attempt}];

spinProjectionProbeWrapExpression::usage =
  "spinProjectionProbeWrapExpression[expr, template, rules, iterators] applies one randomized probe to a symbolic sector expression.";
spinProjectionProbeWrapExpression[expr_, template_Association, rules_List, iterators_List] := Module[
  {expressionSymbols, applySums, localSymbols, localIterators},
  expressionSymbols[e_] := DeleteDuplicates @ Cases[
    HoldComplete[e],
    sym_Symbol /; MemberQ[template["AllSymbols"], sym] :> sym,
    Infinity
  ];
  applySums[e_] := Module[{},
    localSymbols = expressionSymbols[e];
    localIterators = Select[iterators, MemberQ[localSymbols, First[#]] &];
    If[localIterators === {}, e, Apply[Sum, Prepend[localIterators, e]]]
  ];
  spinProjectionEvaluateTensorScalars @ Expand[
    (applySums[expr /. rules]) /. ra_ /; RTest[ra] :> Bosonize[ra]
  ]
];

spinRandomizationProbe::usage =
  "spinRandomizationProbe[template, seed] applies one random index assignment, bosonizes the sector inputs, and stores a lazy wrapper for sector ansatz expressions.";
spinRandomizationProbe[template_Association, seed_: Automatic] := Module[{run},
  run[] := Module[{rules, it, expressionSymbols, applySums, wrap},
    rules = Join[
      Flatten[
        Function[group,
          With[{value = RandomInteger[{1, 10}]},
            (# -> value) & /@ group
          ]
        ] /@ template["FreeVectorGroups"],
        1
      ],
      (# -> RandomChoice[spinIterationValues[Lookup[template["SpinChiralities"], #, "chiral"]]] & /@ Intersection[template["SpinSymbols"], template["FreeSymbols"]])
    ];
    it = Join[
      ({#, 1, 10} & /@ Intersection[template["VectorSymbols"], template["DummySymbols"]]),
      ({#, spinIterationValues[Lookup[template["SpinChiralities"], #, "chiral"]]} & /@ Intersection[template["SpinSymbols"], template["DummySymbols"]])
    ];
    wrap[e_] := spinProjectionProbeWrapExpression[e, template, rules, it];
    <|
      "HoloInputs" -> (wrap /@ template["HoloOps"]),
      "AntiInputs" -> (wrap /@ template["AntiOps"]),
      "Wrap" -> wrap
    |>
  ];
  If[seed === Automatic, run[], BlockRandom[SeedRandom[seed]; run[]]]
];

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

spinProjectionEquations::usage =
  "spinProjectionEquations[lhs, rhs] returns coefficient-matching equations on the bosonized operator basis.";
spinProjectionEquations[lhs_, rhs_] := Module[{lhsAssoc, rhsAssoc, keys},
  lhsAssoc = spinProjectionOperatorAssociation[lhs];
  rhsAssoc = spinProjectionOperatorAssociation[rhs];
  keys = DeleteDuplicates@Join[Keys[lhsAssoc], Keys[rhsAssoc]];
  Lookup[lhsAssoc, #, 0] == Lookup[rhsAssoc, #, 0] & /@ keys
];

completeSpinProjectionSolutionQ::usage =
  "completeSpinProjectionSolutionQ[solution, vars] checks whether Solve returned a full parameter-free solution for all unknown coefficients.";
completeSpinProjectionSolutionQ[solution_List, vars_List] := Module[{assoc = Association[solution]},
  FreeQ[solution, C[_]] && AllTrue[vars, KeyExistsQ[assoc, #] &]
];

solveSpinProjectionVariables::usage =
  "solveSpinProjectionVariables[eqns, vars] solves the accumulated linear coefficient system or returns $Failed.";
solveSpinProjectionVariables[eqns_List, vars_List] := Module[{normalizedEqns, solutions},
  If[vars === {}, Return[{}]];
  normalizedEqns = DeleteDuplicates[DeleteCases[Simplify /@ eqns, True]];
  If[MemberQ[normalizedEqns, False] || normalizedEqns === {}, Return[$Failed]];
  solutions = Quiet[Solve[normalizedEqns, vars]];
  If[!ListQ[solutions] || solutions === {}, Return[$Failed]];
  solutions = Select[solutions, completeSpinProjectionSolutionQ[#, vars] &];
  If[solutions === {}, $Failed, First[solutions]]
];

spinProjectionSectorEvaluation::usage =
  "spinProjectionSectorEvaluation[sector, weight, inputs] evaluates one randomized projected OPE sector on bosonized inputs.";
spinProjectionSectorEvaluation[sector : ("Holo" | "Anti"), weight_, inputs_List] := Module[
  {spec, insertionWeight, targetWeight},
  spec = spinProjectionSectorSpec[sector];
  If[inputs === {}, Return[If[weight === 0, 1, 0]]];
  insertionWeight = Total[spinProjectionExpressionWeight[#, sector] & /@ inputs];
  targetWeight = weight - insertionWeight;
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

spinProjectionGroundSpinRQ::usage =
  "spinProjectionGroundSpinRQ[Ra] returns True for a normal-ordered product consisting of one undescended spin field.";
spinProjectionGroundSpinRQ[Ra_ /; RTest[Ra]] := MatchQ[
  List @@ Ra,
  {(S | St)[{_, ("chiral" | "antichiral")}, _?NumericQ, {}, 0, _]}
];
spinProjectionGroundSpinRQ[_] := False;

spinProjectionSkipZeroLHSSectorQ::usage =
  "spinProjectionSkipZeroLHSSectorQ[ops, expr] detects sector ansaetze where a vanishing bosonized OPE probe can be skipped safely before RHS tensor evaluation.";
spinProjectionSkipZeroLHSSectorQ[ops_List, expr_] := Module[{sectorOperators},
  sectorOperators = Cases[expr, ra_ /; RTest[ra] :> ra, Infinity];
  ops =!= {} &&
    AllTrue[ops, spinProjectionGroundSpinRQ] &&
    sectorOperators =!= {} &&
    AllTrue[sectorOperators, spinProjectionGroundSpinRQ]
];

solveSpinProjectionSectors::usage =
  "solveSpinProjectionSectors[template, wH, wA, hExpr, hVars, aExpr, aVars, seed] accumulates randomized coefficient equations until both sectors solve or retries are exhausted.";
solveSpinProjectionSectors[template_Association, wH_, wA_, hExpr_, hVars_List, aExpr_, aVars_List, seed_] := Module[
  {
    attempt = 1,
    probe,
    sectors = {"Holo", "Anti"},
    sectorStates,
    groundSpinProbeCharge,
    groundSpinOutputCharges,
    groundSpinChargeMismatchQ,
    updateSector,
    sectorResult
  },
  groundSpinProbeCharge[sector_, expr_] := Module[{bosonHead, charges},
    bosonHead = If[sector === "Holo", expH, expHt];
    charges = Cases[expr, R[bosonHead[c_List, _]] :> c, Infinity];
    If[Length[charges] === 1, First[charges], Missing["NotGroundSpinInput"]]
  ];
  groundSpinOutputCharges[expr_] := DeleteDuplicates @ Flatten[
    Cases[
      expr,
      (S | St)[{_, chirality : ("chiral" | "antichiral")}, q_?NumericQ, {}, 0, _] :>
        (Prepend[#, q] & /@ spinIterationValues[chirality]),
      Infinity
    ],
    1
  ];
  groundSpinChargeMismatchQ[sector_, inputs_List, outputCharges_List] := Module[{inputCharges},
    If[outputCharges === {}, Return[False]];
    inputCharges = groundSpinProbeCharge[sector, #] & /@ inputs;
    AllTrue[inputCharges, ListQ] && !MemberQ[outputCharges, Total[inputCharges]]
  ];
  sectorStates = <|
    "Holo" -> <|
      "Expr" -> hExpr,
      "Vars" -> hVars,
      "Weight" -> wH,
      "Eqns" -> {},
      "Solution" -> If[hExpr =!= 0 && hExpr =!= 1 && hVars =!= {}, $Failed, {}],
      "Needs" -> hExpr =!= 0 && hExpr =!= 1 && hVars =!= {},
      "SkipZeroLHS" -> spinProjectionSkipZeroLHSSectorQ[template["HoloOps"], hExpr],
      "OutputCharges" -> If[spinProjectionSkipZeroLHSSectorQ[template["HoloOps"], hExpr], groundSpinOutputCharges[hExpr], {}]
    |>,
    "Anti" -> <|
      "Expr" -> aExpr,
      "Vars" -> aVars,
      "Weight" -> wA,
      "Eqns" -> {},
      "Solution" -> If[aExpr =!= 0 && aExpr =!= 1 && aVars =!= {}, $Failed, {}],
      "Needs" -> aExpr =!= 0 && aExpr =!= 1 && aVars =!= {},
      "SkipZeroLHS" -> spinProjectionSkipZeroLHSSectorQ[template["AntiOps"], aExpr],
      "OutputCharges" -> If[spinProjectionSkipZeroLHSSectorQ[template["AntiOps"], aExpr], groundSpinOutputCharges[aExpr], {}]
    |>
  |>;
  updateSector[sector_] := Module[{spec, state, lhs, rhs},
    state = sectorStates[sector];
    If[!TrueQ[state["Needs"]], Return[Null]];
    spec = spinProjectionSectorSpec[sector];
    If[
      TrueQ[state["SkipZeroLHS"]] &&
      groundSpinChargeMismatchQ[sector, probe[spec["ProbeInputsKey"]], state["OutputCharges"]],
      Return[Null]
    ];
    lhs = spinProjectionSectorEvaluation[sector, state["Weight"], probe[spec["ProbeInputsKey"]]];
    If[TrueQ[state["SkipZeroLHS"]] && lhs === 0, Return[Null]];
    rhs = probe["Wrap"][state["Expr"]];
    state["Eqns"] = DeleteDuplicates@Join[
      state["Eqns"],
      spinProjectionEquations[
        lhs,
        rhs
      ]
    ];
    state["Solution"] = solveSpinProjectionVariables[state["Eqns"], state["Vars"]];
    state["Needs"] = state["Solution"] === $Failed;
    sectorStates[sector] = state;
  ];
  sectorResult[sector_] := Module[{state = sectorStates[sector]},
    Which[
      state["Expr"] === 0, 0,
      state["Expr"] === 1, 1,
      state["Vars"] === {}, state["Expr"],
      state["Solution"] === $Failed, $Failed,
      True, state["Expr"] /. state["Solution"]
    ]
  ];
  While[
    attempt <= spinProjectionMaxAttempts &&
      AnyTrue[sectors, sectorStates[#]["Needs"] &],
    probe = spinRandomizationProbe[template, spinProjectionAttemptSeed[seed, attempt]];
    Scan[updateSector, sectors];
    attempt++;
  ];
  <|
    "Attempts" -> Min[attempt - 1, spinProjectionMaxAttempts],
    "Holo" -> sectorResult["Holo"],
    "Anti" -> sectorResult["Anti"]
  |>
];

OPEProjected[wH_, wA_][Ra__ /; (And @@ (RTest /@ {Ra}) && AnyTrue[{Ra}, hasSpinFieldQ]), opts___Rule] := Module[
  {o, hExpr, aExpr, hVars, aVars, n, seed, template, solved, buildSectorProjection},
  seed = Lookup[Association[Join[Options[OPEProjected], {opts}]], "RandomSeed", Automatic];
  o = getOutgoingOperatorsTensors[{Ra}, wH, wA, seed];
  buildSectorProjection[opsKey_, dataKey_, weight_, offset_] := Which[
    o[opsKey] === {}, {If[weight === 0, 1, 0], {}, offset},
    o[dataKey] === {}, {0, {}, offset},
    True, attachSpinProjectionCoefficients[o[dataKey], offset]
  ];
  {hExpr, hVars, n} = buildSectorProjection["holoOps", "holoData", wH, 0];
  {aExpr, aVars, n} = buildSectorProjection["antiOps", "antiData", wA, n];
  If[hExpr === 0 || aExpr === 0, Return[0]];
  template = spinRandomizationTemplate[o["holoOps"], o["antiOps"], hExpr, aExpr];
  solved = solveSpinProjectionSectors[template, wH, wA, hExpr, hVars, aExpr, aVars, seed];
  Do[
    If[solved[sector] === $Failed,
      Message[OPEProjected::spinsolve, spinProjectionSectorSpec[sector]["FailureLabel"], solved["Attempts"]];
      Return[Unevaluated[OPEProjected[wH, wA][Ra]]];
    ],
    {sector, {"Holo", "Anti"}}
  ];
  o["sign"] combineChiral[solved["Holo"], solved["Anti"]]
];

OPEProjected[wH_, wA_][Ra__ /; (And @@ (RTest /@ {Ra}) && !AnyTrue[{Ra}, hasCollapsable] && !AnyTrue[{Ra}, hasSpinFieldQ])] := Module[
  {
    \[Epsilon]Holo, \[Epsilon]AntiHolo, localLists, splitLists, sign, holoOps, antiOps,
    insertionWeightHolo, insertionWeightAntiHolo, targetWeightHolo, targetWeightAntiHolo,
    projectedHolo, projectedAntiHolo
  },
  localLists = List @@ # & /@ {Ra};
  splitLists = splitOperators[#, isHolomorphic, isAntiHolomorphic] & /@ localLists;
  insertionWeightHolo = Total[totalWeightHolo /@ {Ra}];
  insertionWeightAntiHolo = Total[totalWeightAntiHolo /@ {Ra}];
  targetWeightHolo = wH - insertionWeightHolo;
  targetWeightAntiHolo = wA - insertionWeightAntiHolo;

  sign = If[Flatten[localLists] === {}, 1, factorizationSign[Flatten[localLists], isHolomorphic, isAntiHolomorphic]];

  holoOps = Select[R @@@ (splitLists[[All, 1]]), RTest];
  antiOps = Select[R @@@ (splitLists[[All, 2]]), RTest];

  projectedHolo = projectHolo[
    OPEWickList[rescaleR[\[Epsilon]Holo] /@ holoOps],
    targetWeightHolo, \[Epsilon]Holo
  ];
  projectedAntiHolo = projectAntiHolo[
    OPEWickList[rescaleR[\[Epsilon]AntiHolo] /@ antiOps],
    targetWeightAntiHolo, \[Epsilon]AntiHolo
  ];

  sign combineChiral[projectedHolo, projectedAntiHolo]
];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
