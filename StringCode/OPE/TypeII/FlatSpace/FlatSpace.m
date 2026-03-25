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
  spinProjectionCanonicalSectorData[
    canonical["Ops"],
    targetWeight,
    basisGeneratorFn,
    psiHead,
    spinHead,
    pictureContributionFn,
    seed
  ] /. canonical["InverseRules"]
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
getOutgoingOperatorsTensors[ops_List, wH_, wA_, seed_: Automatic] := getOutgoingOperatorsTensors[ops, wH, wA, seed] = Module[
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
          spinProjectionSectorData[
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

spinProjectionSpinBasisState::usage =
  "spinProjectionSpinBasisState[chirality] returns the ordered explicit spin basis used by the compiled numeric probe solver.";
spinProjectionSpinBasisState[chirality_String] := spinProjectionSpinBasisState[chirality] = spinIterationValues[chirality];

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
spinProjectionGammaFactorMatrix[links_List] := spinProjectionGammaFactorMatrix[links] = Module[
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
  "spinRandomizationProbe[template, seed, forcedSpinRules] applies one randomized index assignment, optionally overriding selected free-spin values, bosonizes the sector inputs, and stores a lazy wrapper for sector ansatz expressions.";
spinRandomizationProbe[template_Association, seed_: Automatic, forcedSpinRules_: Automatic] := Module[{run},
  run[] := Module[{rules, it, wrap},
    rules = Join[
      Flatten[
        Function[group,
          With[{value = RandomInteger[{1, 10}]},
            (# -> value) & /@ group
          ]
        ] /@ template["FreeVectorGroups"],
        1
      ],
      Module[{forcedAssoc, freeSpinSymbols},
        forcedAssoc = Association[Replace[forcedSpinRules, Automatic -> {}]];
        freeSpinSymbols = Intersection[template["SpinSymbols"], template["FreeSymbols"]];
        Table[
          sym -> Lookup[
            forcedAssoc,
            sym,
            RandomChoice[spinIterationValues[Lookup[template["SpinChiralities"], sym, "chiral"]]]
          ],
          {sym, freeSpinSymbols}
        ]
      ]
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

spinProjectionGroundSpinRQ::usage =
  "spinProjectionGroundSpinRQ[Ra] returns True for a normal-ordered product consisting of one undescended spin field.";
spinProjectionGroundSpinRQ[Ra_ /; RTest[Ra]] := MatchQ[
  List @@ Ra,
  {(S | St)[{_, ("chiral" | "antichiral")}, _?NumericQ, {}, 0, _]}
];
spinProjectionGroundSpinRQ[_] := False;

spinProjectionGroundSpinProbeCharge::usage =
  "spinProjectionGroundSpinProbeCharge[sector, expr] returns the bosonized charge vector carried by one concrete ground-spin probe input, or Missing if expr is not one ground spin.";
spinProjectionGroundSpinProbeCharge[sector_, expr_] := Module[{bosonHead, charges},
  bosonHead = If[sector === "Holo", expH, expHt];
  charges = Cases[expr, R[bosonHead[c_List, _]] :> c, Infinity];
  If[Length[charges] === 1, First[charges], Missing["NotGroundSpinInput"]]
];

spinProjectionGroundSpinOutputCharges::usage =
  "spinProjectionGroundSpinOutputCharges[expr] returns the allowed bosonized charge vectors for ground-spin output operators appearing in expr.";
spinProjectionGroundSpinOutputCharges[expr_] := DeleteDuplicates @ Flatten[
  Cases[
    expr,
    (S | St)[{_, chirality : ("chiral" | "antichiral")}, q_?NumericQ, {}, 0, _] :>
      (Prepend[#, q] & /@ spinIterationValues[chirality]),
    Infinity
  ],
  1
];

spinProjectionGroundSpinChargeMismatchQ::usage =
  "spinProjectionGroundSpinChargeMismatchQ[sector, inputs, outputCharges] returns True when concrete ground-spin probe inputs cannot match any allowed output charge.";
spinProjectionGroundSpinChargeMismatchQ[sector_, inputs_List, outputCharges_List] := Module[{inputCharges},
  If[outputCharges === {}, Return[False]];
  inputCharges = spinProjectionGroundSpinProbeCharge[sector, #] & /@ inputs;
  AllTrue[inputCharges, ListQ] && !MemberQ[outputCharges, Total[inputCharges]]
];

spinProjectionSkipZeroLHSSectorQ::usage =
  "spinProjectionSkipZeroLHSSectorQ[ops, expr] detects sector ansaetze where a vanishing bosonized OPE probe can be skipped safely before RHS tensor evaluation.";
spinProjectionSkipZeroLHSSectorQ[ops_List, expr_] := Module[{sectorOperators},
  sectorOperators = Cases[expr, ra_ /; RTest[ra] :> ra, Infinity];
  ops =!= {} &&
    AllTrue[ops, spinProjectionGroundSpinRQ] &&
    sectorOperators =!= {} &&
    AllTrue[sectorOperators, spinProjectionGroundSpinRQ]
];

spinProjectionCompiledCandidateLimit::usage =
  "Maximum number of deterministic compiled probe assignments enumerated before falling back to the legacy symbolic solver.";
spinProjectionCompiledCandidateLimit = 20 spinProjectionMaxAttempts;

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
  freeVectorSymbols = Intersection[vec, free];
  freeVectorGroups = spinProjectionConnectedSymbolGroups[
    freeVectorSymbols,
    spinProjectionVectorConstraintPairs[expr, freeVectorSymbols]
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

spinProjectionSeededOrder::usage =
  "spinProjectionSeededOrder[list, seed, tag] deterministically orders a finite list using the probe seed and one local tag.";
spinProjectionSeededOrder[list_List, Automatic, _] := list;
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
spinProjectionOutputSymbolData[_] := $Failed;

compileSpinProjectionSectorModel::usage =
  "compileSpinProjectionSectorModel[sector, ops, weight, data] builds the direct numeric RHS model for one supported chiral sector straight from outgoing tensor data, or returns $Failed.";
compileSpinProjectionSectorModel[sector : ("Holo" | "Anti"), ops_List, weight_, data_List] := Module[
  {
    expr,
    vars,
    template,
    freeSpinSymbols,
    freeSpinChiralities,
    freeSpinSlot,
    freeVectorGroups,
    freeVectorSlot,
    chargeGuidedQ,
    freeSpinPictures,
    vsrc,
    ssrc,
    matrixDesc,
    scalarDesc,
    compileTerm,
    compileFamily,
    families,
    pieceColumn = 0
  },
  If[ops === {}, Return[<|"Sector" -> sector, "Ops" -> ops, "Weight" -> weight, "TargetWeight" -> weight, "Expr" -> If[weight === 0, 1, 0], "Vars" -> {}, "VarCount" -> 0, "Terms" -> {}|>]];
  If[data === {}, Return[<|"Sector" -> sector, "Ops" -> ops, "Weight" -> weight, "TargetWeight" -> weight, "Expr" -> 0, "Vars" -> {}, "VarCount" -> 0, "Terms" -> {}|>]];
  {expr, vars} = Take[attachSpinProjectionCoefficients[data], 2];
  template = spinProjectionSectorTemplate[ops, expr];
  freeSpinSymbols = SortBy[Intersection[template["SpinSymbols"], template["FreeSymbols"]], SymbolName];
  freeSpinChiralities = Lookup[template["SpinChiralities"], freeSpinSymbols];
  freeSpinSlot = AssociationThread[freeSpinSymbols -> Range[Length[freeSpinSymbols]]];
  freeVectorGroups = SortBy[template["FreeVectorGroups"], SymbolName @* First];
  freeVectorSlot = Association @ Flatten[MapIndexed[Thread[#1 -> First[#2]] &, freeVectorGroups], 1];
  chargeGuidedQ =
    freeVectorGroups === {} &&
    freeSpinSymbols =!= {} &&
    ops =!= {} &&
    AllTrue[ops, spinProjectionGroundSpinRQ] &&
    AllTrue[Cases[expr, ra_ /; RTest[ra] :> ra, Infinity], spinProjectionGroundSpinRQ];
  freeSpinPictures = Association @ Cases[
    ops,
    R[(S | St)[{sym_, _}, q_?NumericQ, {}, 0, _]] /; MemberQ[freeSpinSymbols, sym] :> (sym -> q),
    Infinity
  ];
  If[chargeGuidedQ && Length[freeSpinPictures] =!= Length[freeSpinSymbols], chargeGuidedQ = False];
  vsrc[sym_, stateVectors_, dummyVectors_] := Which[
    IntegerQ[sym], {4, sym},
    KeyExistsQ[freeVectorSlot, sym], {1, freeVectorSlot[sym]},
    KeyExistsQ[stateVectors, sym], {2, stateVectors[sym]},
    KeyExistsQ[dummyVectors, sym], {3, dummyVectors[sym]},
    True, $Failed
  ];
  ssrc[sym_, stateSpins_] := Which[
    KeyExistsQ[freeSpinSlot, sym], {1, freeSpinSlot[sym]},
    KeyExistsQ[stateSpins, sym], {2, stateSpins[sym]},
    True, $Failed
  ];
  matrixDesc[part_, stateVectors_, dummyVectors_] := Module[{sources, links},
    sources = vsrc[#, stateVectors, dummyVectors] & /@ part["VectorSymbols"];
    If[MemberQ[sources, $Failed], Return[$Failed]];
    If[AllTrue[sources, First[#] === 4 &],
      links = Join[
        If[part["CTag"] === None, {}, {part["CTag"]}],
        MapThread[If[#1 === GammaUDHold, GammaUDHold[#2[[2]]], GammaDUHold[#2[[2]]]] &, {Head /@ part["VectorLinks"], sources}],
        part["TailLinks"]
      ];
      {part["CTag"], Replace[Head /@ part["VectorLinks"], {GammaUDHold -> 1, GammaDUHold -> 2}, 1], sources, part["TailLinks"], SparseArray[spinProjectionGammaFactorMatrix[links]]},
      {part["CTag"], Replace[Head /@ part["VectorLinks"], {GammaUDHold -> 1, GammaDUHold -> 2}, 1], sources, part["TailLinks"], None}
    ]
  ];
  scalarDesc[part_, stateSpins_, stateVectors_, dummyVectors_] := Module[{left, right, matrix},
    Switch[part["Kind"],
      "Delta",
      {0, vsrc[part["VectorSymbols"][[1]], stateVectors, dummyVectors], vsrc[part["VectorSymbols"][[2]], stateVectors, dummyVectors]},
      "Gamma",
      left = ssrc[part["Spinors"][[1]], stateSpins];
      right = ssrc[part["Spinors"][[2]], stateSpins];
      If[MemberQ[{left, right}, $Failed], Return[$Failed]];
      If[part["VectorLinks"] === {} && part["CTag"] === None && part["TailLinks"] === {} && SameQ @@ part["SpinorChiralities"],
        {1, left, right},
        matrix = matrixDesc[part, stateVectors, dummyVectors];
        If[matrix === $Failed, $Failed, {2, left, right, matrix}]
      ],
      _,
      $Failed
    ]
  ];
  compileTerm[tensor_, stateSpins_, stateVectors_] := Module[
    {factors, tensorFactors, scalarFactor, parsedTensor, indexSymbols, dummySymbols, dummyVectors, parts},
    pieceColumn++;
    factors = If[Head[tensor] === Times, List @@ tensor, {tensor}];
    tensorFactors = Select[factors, candidateFactorQ];
    scalarFactor = Times @@ Select[factors, !candidateFactorQ[#] &];
    indexSymbols = DeleteDuplicates[First /@ spinTypedIndices[tensor]];
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
        Keys[freeVectorSlot]
      ],
      SymbolName
    ];
    dummyVectors = AssociationThread[dummySymbols -> Range[Length[dummySymbols]]];
    parts = scalarDesc[#, stateSpins, stateVectors, dummyVectors] & /@ parsedTensor["FactorParts"];
    If[MemberQ[parts, $Failed], Return[$Failed]];
    {pieceColumn, scalarFactor, parts, Length[dummySymbols]}
  ];
  compileFamily[{op_, tensors_}] := Module[{outputData, stateSpins, stateVectors, terms},
    outputData = spinProjectionOutputSymbolData[op];
    If[outputData === $Failed, Return[$Failed]];
    stateSpins = AssociationThread[outputData["SpinSymbols"] -> Range[Length[outputData["SpinSymbols"]]]];
    stateVectors = AssociationThread[outputData["VectorSymbols"] -> Range[Length[outputData["VectorSymbols"]]]];
    terms = compileTerm[#, stateSpins, stateVectors] & /@ tensors;
    If[MemberQ[terms, $Failed], Return[$Failed]];
    <|
      "Template" -> op,
      "SpinSymbols" -> outputData["SpinSymbols"],
      "SpinChiralities" -> outputData["SpinChiralities"],
      "VectorSymbols" -> outputData["VectorSymbols"],
      "Terms" -> terms
    |>
  ];
  families = compileFamily /@ data;
  If[MemberQ[families, $Failed], Return[$Failed]];
  <|
    "Sector" -> sector,
    "Ops" -> ops,
    "Weight" -> weight,
    "TargetWeight" -> None,
    "Expr" -> expr,
    "Vars" -> vars,
    "VarCount" -> Length[vars],
    "Families" -> families,
    "FreeSpinSymbols" -> freeSpinSymbols,
    "FreeSpinChiralities" -> freeSpinChiralities,
    "FreeVectorGroups" -> freeVectorGroups,
    "ChargeGuidedQ" -> chargeGuidedQ,
    "FreeSpinPictures" -> Lookup[freeSpinPictures, freeSpinSymbols, Missing["NotChargeGuided"]],
    "OutputCharges" -> If[chargeGuidedQ, spinProjectionGroundSpinOutputCharges[expr], {}]
  |>
];

spinProjectionChargeBasisIndex::usage =
  "spinProjectionChargeBasisIndex[table, charge] returns the 1-based basis index for a charge vector in a small ordered charge table, or 0 if absent.";
spinProjectionChargeBasisIndex[table_List, charge_] := Module[{pos},
  pos = FirstPosition[table, charge, 0, {1}, Heads -> False];
  If[ListQ[pos], First[pos], 0]
];

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

spinProjectionLoopDummyVectors::usage =
  "spinProjectionLoopDummyVectors[k, body] iterates over k dummy vector slots in 1..10 without materializing tuples.";
spinProjectionLoopDummyVectors[k_Integer?NonNegative, body_] := Switch[k,
  0, body[{}],
  1, Do[body[{i1}], {i1, 10}],
  2, Do[body[{i1, i2}], {i1, 10}, {i2, 10}],
  3, Do[body[{i1, i2, i3}], {i1, 10}, {i2, 10}, {i3, 10}],
  4, Do[body[{i1, i2, i3, i4}], {i1, 10}, {i2, 10}, {i3, 10}, {i4, 10}],
  _, Module[{dummy = ConstantArray[1, k], done = False, pos},
    While[!done,
      body[dummy];
      pos = k;
      While[pos >= 1 && dummy[[pos]] == 10, dummy[[pos]] = 1; pos--];
      If[pos == 0, done = True, dummy[[pos]]++]
    ]
  ]
];

spinProjectionVectorSourceValue::usage =
  "spinProjectionVectorSourceValue[src, freeVectors, stateVectors, dummy] resolves one compiled vector source to a concrete vector index.";
spinProjectionVectorSourceValue[src_, freeVectors_List, stateVectors_List, dummy_List] := Switch[src[[1]],
  1, freeVectors[[src[[2]]]],
  2, stateVectors[[src[[2]]]],
  3, dummy[[src[[2]]]],
  4, src[[2]],
  _, $Failed
];

spinProjectionSpinSourceValue::usage =
  "spinProjectionSpinSourceValue[src, freeSpins, stateSpins] resolves one compiled spin source to a concrete 1-based spin basis index.";
spinProjectionSpinSourceValue[src_, freeSpins_List, stateSpins_List] := Switch[src[[1]],
  1, freeSpins[[src[[2]]]],
  2, stateSpins[[src[[2]]]],
  _, $Failed
];

spinProjectionConcreteGammaMatrix::usage =
  "spinProjectionConcreteGammaMatrix[desc, freeVectors, stateVectors, dummy] resolves one compiled exact gamma descriptor to a concrete 16x16 matrix.";
spinProjectionConcreteGammaMatrix[desc_, freeVectors_List, stateVectors_List, dummy_List] := Module[{values},
  If[desc[[5]] =!= None, Return[Normal[desc[[5]]]]];
  values = spinProjectionVectorSourceValue[#, freeVectors, stateVectors, dummy] & /@ desc[[3]];
  If[!AllTrue[values, IntegerQ], Return[$Failed]];
  spinProjectionGammaFactorMatrix @ Join[
    If[desc[[1]] === None, {}, {desc[[1]]}],
    MapThread[If[#1 === 1, GammaUDHold[#2], GammaDUHold[#2]] &, {desc[[2]], values}],
    desc[[4]]
  ]
];

spinProjectionConcreteGammaSparseMatrix::usage =
  "spinProjectionConcreteGammaSparseMatrix[desc, freeVectors, stateVectors, dummy] resolves one compiled exact gamma descriptor to a concrete sparse 16x16 matrix.";
spinProjectionConcreteGammaSparseMatrix[desc_, freeVectors_List, stateVectors_List, dummy_List] := Module[{matrix},
  matrix = If[desc[[5]] =!= None, desc[[5]], spinProjectionConcreteGammaMatrix[desc, freeVectors, stateVectors, dummy]];
  If[matrix === $Failed, $Failed, If[Head[matrix] === SparseArray, matrix, SparseArray[matrix]]]
];

spinProjectionFactorOutputSpinSupport::usage =
  "spinProjectionFactorOutputSpinSupport[factor, outputSpinSlot, freeSpins, freeVectors] returns All or the allowed output-spin basis indices for one compiled factor under one candidate assignment.";
spinProjectionFactorOutputSpinSupport[factor_, outputSpinSlot_Integer?Positive, freeSpins_List, freeVectors_List] := Module[
  {left = factor[[2]], right = factor[[3]], desc, matrix},
  Switch[factor[[1]],
    0, All,
    1, Which[left[[1]] === 2 && left[[2]] === outputSpinSlot && right[[1]] === 1, {freeSpins[[right[[2]]]]}, right[[1]] === 2 && right[[2]] === outputSpinSlot && left[[1]] === 1, {freeSpins[[left[[2]]]]}, True, All],
    2,
    desc = factor[[4]];
    If[!AllTrue[desc[[3]], MemberQ[{1, 4}, First[#]] &], Return[All]];
    matrix = spinProjectionConcreteGammaSparseMatrix[desc, freeVectors, {}, {}];
    If[matrix === $Failed, Return[All]];
    Which[
      left[[1]] === 2 && left[[2]] === outputSpinSlot && right[[1]] === 1, Flatten[Position[Normal[Unitize[matrix[[All, freeSpins[[right[[2]]]]]]]], 1]],
      right[[1]] === 2 && right[[2]] === outputSpinSlot && left[[1]] === 1, Flatten[Position[Normal[Unitize[matrix[[freeSpins[[left[[2]]]], All]]]], 1]],
      True, All
    ],
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
        {supports = Select[spinProjectionFactorOutputSpinSupport[#, 1, freeSpins, freeVectors] & /@ term[[3]], ListQ]},
        If[supports === {}, fullDomain, Intersection @@ supports]
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

spinProjectionScalarFactorValue::usage =
  "spinProjectionScalarFactorValue[factor, freeSpins, freeVectors, stateSpins, stateVectors, dummy] evaluates one compiled exact tensor factor.";
spinProjectionScalarFactorValue[factor_, freeSpins_List, freeVectors_List, stateSpins_List, stateVectors_List, dummy_List] := Module[
  {left, right, matrix},
  Switch[factor[[1]],
    0,
    If[
      spinProjectionVectorSourceValue[factor[[2]], freeVectors, stateVectors, dummy] ===
        spinProjectionVectorSourceValue[factor[[3]], freeVectors, stateVectors, dummy],
      1,
      0
    ],
    1,
    If[
      spinProjectionSpinSourceValue[factor[[2]], freeSpins, stateSpins] ===
        spinProjectionSpinSourceValue[factor[[3]], freeSpins, stateSpins],
      1,
      0
    ],
    2,
    matrix = spinProjectionConcreteGammaSparseMatrix[factor[[4]], freeVectors, stateVectors, dummy];
    left = spinProjectionSpinSourceValue[factor[[2]], freeSpins, stateSpins];
    right = spinProjectionSpinSourceValue[factor[[3]], freeSpins, stateSpins];
    If[matrix =!= $Failed && IntegerQ[left] && IntegerQ[right], matrix[[left, right]], $Failed],
    _,
    $Failed
  ]
];

spinProjectionTermValue::usage =
  "spinProjectionTermValue[term, freeSpins, freeVectors, stateSpins, stateVectors] evaluates one compiled tensor term at a concrete probe and output state.";
spinProjectionTermValue[term_List, freeSpins_List, freeVectors_List, stateSpins_List, stateVectors_List] := Module[
  {total = 0, failed = False, prod},
  spinProjectionLoopDummyVectors[
    term[[4]],
    Function[dummy,
      prod = term[[2]];
      Do[
        prod *= spinProjectionScalarFactorValue[factor, freeSpins, freeVectors, stateSpins, stateVectors, dummy];
        If[prod === $Failed, failed = True; Return[]];
        If[prod === 0, Return[]],
        {factor, term[[3]]}
      ];
      total += prod
    ]
  ];
  If[failed, $Failed, total]
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

spinProjectionConcreteOutputAssociation::usage =
  "spinProjectionConcreteOutputAssociation[family, state] bosonizes one concrete output state and returns its operator association.";
spinProjectionConcreteOutputAssociation[family_Association, {stateSpins_List, stateVectors_List}] := Module[{rules},
  rules = Join[
    Thread[family["VectorSymbols"] -> stateVectors],
    MapThread[#1 -> spinProjectionSpinBasisState[#2][[#3]] &, {family["SpinSymbols"], family["SpinChiralities"], stateSpins}]
  ];
  spinProjectionOperatorAssociation[Bosonize[family["Template"] /. rules]]
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

spinProjectionCandidateRows::usage =
  "spinProjectionCandidateRows[model, candidate, lhsAssoc, basis, seed] lazily scans concrete output states and returns only exact coefficient rows that increase rank.";
spinProjectionCandidateRows[model_Association, candidate : {freeSpins_List, freeVectors_List}, lhsAssoc_Association, basis_Association, seed_] := Module[
  {state = basis, rows = {}, rhs = {}, row, assoc, familyRows, insert, nextState, tuple, stateSpins, stateVectors, spinDomain, termBuckets},
  Do[
    familyRows = <||>;
    {spinDomain, termBuckets} = If[Length[family["SpinSymbols"]] == 1, spinProjectionFamilyOutputSpinDomain[family, candidate, seed, True], {spinProjectionFamilyOutputSpinDomain[family, candidate, seed], <||>}];
    nextState = spinProjectionFamilyStateIterator[family, seed, spinDomain];
    While[True,
      tuple = nextState[];
      If[tuple === EndOfFile, Break[]];
      tuple = Reverse[tuple];
      stateSpins = Developer`ToPackedArray[Take[tuple, Length[family["SpinSymbols"]]]];
      stateVectors = Developer`ToPackedArray[Drop[tuple, Length[family["SpinSymbols"]]]];
      row = ConstantArray[0, model["VarCount"]];
      Scan[
        Function[term,
          With[{value = spinProjectionTermValue[term, freeSpins, freeVectors, stateSpins, stateVectors]},
            If[value === $Failed, row = $Failed, If[value =!= 0, row[[term[[1]]]] += value]]
          ]
        ],
        If[Length[family["SpinSymbols"]] == 1, Join[Lookup[termBuckets, 0, {}], Lookup[termBuckets, stateSpins[[1]], {}]], family["Terms"]]
      ];
      If[row === $Failed || !AnyTrue[row, # =!= 0 &], Continue[]];
      assoc = spinProjectionConcreteOutputAssociation[family, {stateSpins, stateVectors}];
      Scan[
        Function[pair,
          familyRows[pair[[1]]] = Lookup[familyRows, pair[[1]], ConstantArray[0, model["VarCount"]]] + pair[[2]] row
        ],
        Normal[assoc]
      ];
    ];
    Scan[
      Function[pair,
        insert = spinProjectionExactBasisInsertRow[state, pair[[2]]];
        If[insert[[2]],
          state = insert[[1]];
          AppendTo[rows, pair[[2]]];
          AppendTo[rhs, Lookup[lhsAssoc, pair[[1]], 0]]
        ]
      ],
      SortBy[Normal[familyRows], If[Lookup[lhsAssoc, First[#], 0] === 0, 1, 0] &]
    ];
    If[Length[state["Pivots"]] >= model["VarCount"], Break[]],
    {family, model["Families"]}
  ];
  <|"Basis" -> state, "Rows" -> rows, "RHS" -> rhs|>
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

spinProjectionAssignmentIterator::usage =
  "spinProjectionAssignmentIterator[model, seed] returns a zero-argument function that lazily enumerates compiled probe assignments without replacement, or $Failed when the search space is too large.";
spinProjectionAssignmentIterator[model_Association, seed_] := Module[
  {
    maxCount = spinProjectionCompiledCandidateLimit,
    spinDomains,
    vectorDomains,
    nextTuple,
    yielded = 0,
    outputCharges,
    solvedTable,
    fixedTables,
    tuple,
    outputIndex = 1,
    tupleIterator,
    tupleSeed,
    next
  },
  tupleSeed = If[Length[model["Vars"]] <= 2, None, seed];
  spinDomains = MapThread[
    spinProjectionSeededOrder[Range[Length[spinProjectionSpinBasisState[#1]]], seed, #2] &,
    {model["FreeSpinChiralities"], model["FreeSpinSymbols"]}
  ];
  vectorDomains = spinProjectionSeededOrder[Range[10], seed, #] & /@ model["FreeVectorGroups"];
  If[TrueQ[model["ChargeGuidedQ"]],
    If[spinDomains === {}, Return[Function[{}, EndOfFile]]];
    fixedTables = MapThread[spinProjectionSpinBasisChargeTable, {Most[model["FreeSpinChiralities"]], Most[model["FreeSpinPictures"]]}];
    solvedTable = spinProjectionSpinBasisChargeTable[Last[model["FreeSpinChiralities"]], Last[model["FreeSpinPictures"]]];
    outputCharges = spinProjectionSeededOrder[model["OutputCharges"], seed, "outputCharges"];
    tupleIterator = spinProjectionTupleIterator[Reverse[Most[spinDomains]], tupleSeed, {"chargeTuples", model["FreeSpinSymbols"]}];
    tuple = tupleIterator[];
    next[] := Module[{outputCharge, currentTuple, required, solvedValue},
      While[yielded < maxCount && tuple =!= EndOfFile,
        currentTuple = Reverse[tuple];
        While[outputIndex <= Length[outputCharges],
          outputCharge = outputCharges[[outputIndex]];
          outputIndex++;
          required = outputCharge - Total[MapThread[#1[[#2]] &, {fixedTables, currentTuple}]];
          solvedValue = spinProjectionChargeBasisIndex[solvedTable, required];
          If[solvedValue == 0, Continue[]];
          yielded++;
          Return[{Developer`ToPackedArray[Join[currentTuple, {solvedValue}]], Developer`ToPackedArray[{}]}];
        ];
        tuple = tupleIterator[];
        outputIndex = 1;
      ];
      EndOfFile
    ];
    Return[next]
  ];
  nextTuple = spinProjectionTupleIterator[Reverse@Join[spinDomains, vectorDomains], tupleSeed, {"genericTuples", model["FreeSpinSymbols"], model["FreeVectorGroups"]}];
  next[] := Module[{tuple, spinCount = Length[spinDomains]},
    If[yielded >= maxCount, Return[EndOfFile]];
    tuple = nextTuple[];
    If[tuple === EndOfFile, Return[EndOfFile]];
    tuple = Reverse[tuple];
    yielded++;
    {
      Developer`ToPackedArray[Take[tuple, spinCount]],
      Developer`ToPackedArray[Drop[tuple, spinCount]]
    }
  ];
  next
];

solveCompiledSpinProjectionSector::usage =
  "solveCompiledSpinProjectionSector[model, seed] solves one supported sector using deterministic concrete probes and direct exact RHS contraction, or returns $Failed.";
solveCompiledSpinProjectionSector[model_Association, seed_] := Module[
  {
    expr = model["Expr"],
    vars = model["Vars"],
    varCount = model["VarCount"],
    sector = model["Sector"],
    weight = model["Weight"],
    targetWeight = Lookup[model, "TargetWeight", model["Weight"]],
    nextCandidate,
    targetInputs,
    exactBasis = <|"Rows" -> {}, "Pivots" -> {}|>,
    rows = {},
    rhs = {},
    attempts = 0,
    lhs,
    lhsAssoc,
    inputs,
    accepted,
    solution,
    candidate
  },
  If[expr === 0, Return[<|"Expr" -> 0, "Attempts" -> 0|>]];
  If[expr === 1, Return[<|"Expr" -> 1, "Attempts" -> 0|>]];
  If[varCount == 0, Return[<|"Expr" -> expr, "Attempts" -> 0|>]];
  If[targetWeight === None,
    targetInputs = spinProjectionConcreteInputs[
      model,
      {
        Developer`ToPackedArray[ConstantArray[1, Length[model["FreeSpinSymbols"]]]],
        Developer`ToPackedArray[ConstantArray[1, Length[model["FreeVectorGroups"]]]]
      }
    ];
    targetWeight = weight - Total[spinProjectionExpressionWeight[#, sector] & /@ targetInputs];
  ];
  nextCandidate = spinProjectionAssignmentIterator[model, seed];
  If[nextCandidate === $Failed, Return[$Failed]];
  While[Length[rows] < varCount,
    candidate = nextCandidate[];
    If[candidate === EndOfFile, Break[]];
    inputs = spinProjectionConcreteInputs[model, candidate];
    lhs = spinProjectionProjectInputs[sector, weight, targetWeight, inputs];
    lhsAssoc = spinProjectionOperatorAssociation[lhs];
    accepted = spinProjectionCandidateRows[model, candidate, lhsAssoc, exactBasis, seed];
    If[accepted["Rows"] === {}, Continue[]];
    exactBasis = accepted["Basis"];
    rows = Join[rows, accepted["Rows"]];
    rhs = Join[rhs, accepted["RHS"]];
    attempts++;
  ];
  If[Length[rows] < varCount, Return[$Failed]];
  solution = Thread[vars -> LinearSolve[rows, rhs]];
  <|"Expr" -> (expr /. solution), "Attempts" -> attempts|>
];

solveCompiledSpinProjectionSectors::usage =
  "solveCompiledSpinProjectionSectors[holoOps, antiOps, wH, wA, holoData, antiData, seed] solves all supported spin-field sectors with the compiled direct-contraction path or returns $Failed.";
solveCompiledSpinProjectionSectors[holoOps_List, antiOps_List, wH_, wA_, holoData_List, antiData_List, seed_] := Module[
  {hModel, aModel, hSolved, aSolved},
  hModel = compileSpinProjectionSectorModel["Holo", holoOps, wH, holoData];
  aModel = compileSpinProjectionSectorModel["Anti", antiOps, wA, antiData];
  If[MemberQ[{hModel, aModel}, $Failed], Return[$Failed]];
  hSolved = solveCompiledSpinProjectionSector[hModel, seed];
  aSolved = solveCompiledSpinProjectionSector[aModel, seed];
  If[MemberQ[{hSolved, aSolved}, $Failed], Return[$Failed]];
  <|
    "Attempts" -> Max[hSolved["Attempts"], aSolved["Attempts"]],
    "Holo" -> hSolved["Expr"],
    "Anti" -> aSolved["Expr"]
  |>
];

solveSpinProjectionSectors::usage =
  "solveSpinProjectionSectors[template, wH, wA, hExpr, hVars, aExpr, aVars, seed] accumulates randomized coefficient equations until both sectors solve or retries are exhausted.";
solveSpinProjectionSectors[template_Association, wH_, wA_, hExpr_, hVars_List, aExpr_, aVars_List, seed_] := Module[
  {
    sampleAttempt = 1,
    meaningfulAttempts = 0,
    maxSampleAttempts = 50 spinProjectionMaxAttempts,
    probe,
    sectors = {"Holo", "Anti"},
    sectorStates,
    guidedProbeRules,
    updateSector,
    sectorResult,
    probeDidWork
  },
  sectorStates = <|
    "Holo" -> <|
      "Expr" -> hExpr,
      "Vars" -> hVars,
      "Weight" -> wH,
      "Eqns" -> {},
      "Solution" -> If[hExpr =!= 0 && hExpr =!= 1 && hVars =!= {}, $Failed, {}],
      "Needs" -> hExpr =!= 0 && hExpr =!= 1 && hVars =!= {},
      "SkipZeroLHS" -> spinProjectionSkipZeroLHSSectorQ[template["HoloOps"], hExpr],
      "OutputCharges" -> If[spinProjectionSkipZeroLHSSectorQ[template["HoloOps"], hExpr], spinProjectionGroundSpinOutputCharges[hExpr], {}]
    |>,
    "Anti" -> <|
      "Expr" -> aExpr,
      "Vars" -> aVars,
      "Weight" -> wA,
      "Eqns" -> {},
      "Solution" -> If[aExpr =!= 0 && aExpr =!= 1 && aVars =!= {}, $Failed, {}],
      "Needs" -> aExpr =!= 0 && aExpr =!= 1 && aVars =!= {},
      "SkipZeroLHS" -> spinProjectionSkipZeroLHSSectorQ[template["AntiOps"], aExpr],
      "OutputCharges" -> If[spinProjectionSkipZeroLHSSectorQ[template["AntiOps"], aExpr], spinProjectionGroundSpinOutputCharges[aExpr], {}]
    |>
  |>;
  guidedProbeRules = Module[
    {
      freeSpinSymbols = SortBy[Intersection[template["SpinSymbols"], template["FreeSymbols"]], SymbolName],
      freeVectorSymbols = Intersection[template["VectorSymbols"], template["FreeSymbols"]],
      guidedSector,
      spinChargeDomains,
      fixedSymbols,
      solvedSymbol,
      fixedDomains,
      fixedTuples,
      solvedDomain,
      count = 0,
      result
    },
    If[freeVectorSymbols =!= {} || freeSpinSymbols === {}, Return[{}]];
    guidedSector = SelectFirst[
      sectors,
      TrueQ[sectorStates[#]["SkipZeroLHS"]] && sectorStates[#]["OutputCharges"] =!= {} &,
      Missing["NotFound"]
    ];
    If[guidedSector === Missing["NotFound"], Return[{}]];
    spinChargeDomains = Association @ Cases[
      {template["HoloOps"], template["AntiOps"]},
      R[(S | St)[{sym_, chirality : ("chiral" | "antichiral")}, q_?NumericQ, {}, 0, _]] /; MemberQ[freeSpinSymbols, sym] :>
        (sym -> ((Prepend[#, q] &) /@ spinIterationValues[chirality])),
      Infinity
    ];
    If[Length[spinChargeDomains] =!= Length[freeSpinSymbols], Return[{}]];
    fixedSymbols = Most[freeSpinSymbols];
    solvedSymbol = Last[freeSpinSymbols];
    fixedDomains = Lookup[spinChargeDomains, fixedSymbols];
    fixedTuples = If[fixedDomains === {}, {{}}, Tuples[fixedDomains]];
    solvedDomain = Lookup[spinChargeDomains, solvedSymbol];
    result = Reap[
      Catch[
        Do[
          Do[
            Module[{required, assignment},
              required = outputCharge - Total[tuple];
              If[MemberQ[solvedDomain, required],
                assignment = Thread[freeSpinSymbols -> (Rest /@ Join[tuple, {required}])];
                Sow[assignment];
                count++;
                If[count >= maxSampleAttempts, Throw[Null]];
              ];
            ],
            {tuple, fixedTuples}
          ],
          {outputCharge, sectorStates[guidedSector]["OutputCharges"]}
        ]
      ]
    ];
    result = If[Length[result] < 2, {}, DeleteDuplicates[result[[2, 1]]]];
    If[seed === Automatic || result === {}, result, result[[Ordering[Hash[{seed, #}] & /@ result]]]]
  ];
  updateSector[sector_] := Module[{spec, state, lhs, rhs},
    state = sectorStates[sector];
    If[!TrueQ[state["Needs"]], Return[False]];
    spec = spinProjectionSectorSpec[sector];
    If[
      TrueQ[state["SkipZeroLHS"]] &&
      spinProjectionGroundSpinChargeMismatchQ[sector, probe[spec["ProbeInputsKey"]], state["OutputCharges"]],
      Return[False]
    ];
    lhs = spinProjectionSectorEvaluation[sector, state["Weight"], probe[spec["ProbeInputsKey"]]];
    If[TrueQ[state["SkipZeroLHS"]] && lhs === 0, Return[False]];
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
    True
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
    meaningfulAttempts < spinProjectionMaxAttempts &&
      sampleAttempt <= maxSampleAttempts &&
      AnyTrue[sectors, sectorStates[#]["Needs"] &],
    probe = spinRandomizationProbe[
      template,
      spinProjectionAttemptSeed[seed, sampleAttempt],
      If[sampleAttempt <= Length[guidedProbeRules], guidedProbeRules[[sampleAttempt]], Automatic]
    ];
    probeDidWork = AnyTrue[updateSector /@ sectors, TrueQ];
    If[probeDidWork, meaningfulAttempts++];
    sampleAttempt++;
  ];
  <|
    "Attempts" -> meaningfulAttempts,
    "Holo" -> sectorResult["Holo"],
    "Anti" -> sectorResult["Anti"]
  |>
];

OPEProjected[wH_, wA_][Ra__ /; (And @@ (RTest /@ {Ra}) && AnyTrue[{Ra}, hasSpinFieldQ]), opts___Rule] := Module[
  {o, hExpr, aExpr, hVars, aVars, n, seed, template, solved, buildSectorProjection},
  seed = Lookup[Association[Join[Options[OPEProjected], {opts}]], "RandomSeed", Automatic];
  o = getOutgoingOperatorsTensors[{Ra}, wH, wA, seed];
  solved = solveCompiledSpinProjectionSectors[o["holoOps"], o["antiOps"], wH, wA, o["holoData"], o["antiData"], seed];
  If[solved === $Failed,
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
  ];
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
