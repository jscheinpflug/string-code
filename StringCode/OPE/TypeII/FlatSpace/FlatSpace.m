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

spinProjectionSectorEvaluation::usage =
  "spinProjectionSectorEvaluation[sector, weight, inputs] evaluates one randomized projected OPE sector on bosonized inputs.";
spinProjectionSectorEvaluation[sector : ("Holo" | "Anti"), weight_, inputs_List] := spinProjectionSectorEvaluation[sector, weight, inputs] = Module[
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

spinProjectionCompiledSelectorTolerance::usage =
  "Tolerance used by the numeric selector basis when screening dense compiled probe rows.";
spinProjectionCompiledSelectorTolerance = 10.^-9;

spinProjectionSelectorProjection::usage =
  "spinProjectionSelectorProjection[n, k, tag] returns a deterministic packed machine-complex selector sketch matrix.";
spinProjectionSelectorProjection[n_Integer?NonNegative, k_Integer?NonNegative, tag_] := Developer`ToPackedArray @ N @ If[
  n == 0 || k == 0,
  ConstantArray[0., {k, n}],
  Table[(I^Mod[Hash[{tag, i, j}], 4])/Sqrt[n], {i, k}, {j, n}]
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
  "spinProjectionOutputSymbolData[op] returns the finite vector/spin domains needed to instantiate one compiled output operator template.";
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
    "Domains" -> Join[
      AssociationThread[vectorSymbols -> ConstantArray[Range[10], Length[vectorSymbols]]],
      AssociationThread[spinSymbols -> (spinIterationValues /@ Lookup[spinChiralities, spinSymbols])]
    ]
  |>
];
spinProjectionOutputSymbolData[_] := $Failed;

spinProjectionOutputBasis::usage =
  "spinProjectionOutputBasis[op] returns the finite concrete output-basis states for one compiled output operator template.";
spinProjectionOutputBasis[op_ /; RTest[op]] := Module[{data, symbols, domains, tuples},
  data = spinProjectionOutputSymbolData[op];
  If[data === $Failed, Return[$Failed]];
  symbols = Join[data["VectorSymbols"], data["SpinSymbols"]];
  domains = Lookup[data["Domains"], symbols, {}];
  tuples = If[symbols === {}, {{}}, Tuples[domains]];
  Table[
    With[
      {
        rules = Thread[symbols -> tuple],
        vectorSymbols = data["VectorSymbols"],
        spinSymbols = data["SpinSymbols"]
      },
      <|
        "Rules" -> rules,
        "Vectors" -> Association @ Cases[rules, Rule[sym_, value_Integer] :> (sym -> value)],
        "Spins" -> Association @ Cases[rules, Rule[sym_, value_List] :> (sym -> value)],
        "Assoc" -> spinProjectionOperatorAssociation[Bosonize[op /. rules]]
      |>
    ],
    {tuple, tuples}
  ]
];
spinProjectionOutputBasis[_] := $Failed;

splitSpinProjectionTerm::usage =
  "splitSpinProjectionTerm[term, vars] parses one ansatz term into {column, scalar tensor candidate, output data, output basis}.";
splitSpinProjectionTerm[term_, vars_List] := Module[
  {factors, varMatches, opMatches, var, op, remainder, tensorFactors, scalarFactor, parsedTensor, basis, column, indexSymbols, outputData},
  factors = If[Head[term] === Times, List @@ term, {term}];
  varMatches = Cases[factors, _spinProjectedCoefficient];
  opMatches = Select[factors, RTest];
  If[Length[varMatches] =!= 1 || Length[opMatches] =!= 1, Return[$Failed]];
  var = First[varMatches];
  op = First[opMatches];
  column = FirstPosition[vars, var, Missing["UnknownVariable"]];
  If[MissingQ[column], Return[$Failed]];
  remainder = DeleteCases[factors, x_ /; x === var || x === op];
  tensorFactors = Select[remainder, candidateFactorQ];
  scalarFactor = Times @@ Select[remainder, !candidateFactorQ[#] &];
  indexSymbols = DeleteDuplicates[First /@ spinTypedIndices[term]];
  If[indexSymbols =!= {} && !FreeQ[scalarFactor, Alternatives @@ indexSymbols], Return[$Failed]];
  parsedTensor = If[tensorFactors === {}, parseCandidate[1], parseCandidate[Times @@ tensorFactors]];
  If[parsedTensor === $Failed, Return[$Failed]];
  parsedTensor = Join[
    parsedTensor,
    <|
      "DummyVectorSymbols" -> SortBy[
        DeleteDuplicates @ Select[
          Flatten[Lookup[parsedTensor["FactorParts"], "VectorSymbols", {}]],
          Head[#] === Symbol &
        ],
        SymbolName
      ]
    |>
  ];
  outputData = spinProjectionOutputSymbolData[op];
  If[outputData === $Failed, Return[$Failed]];
  basis = spinProjectionOutputBasis[op];
  If[basis === $Failed, Return[$Failed]];
  <|
    "Var" -> var,
    "VarColumn" -> First[column],
    "ScalarFactor" -> scalarFactor,
    "Tensor" -> parsedTensor,
    "OutputTemplate" -> op,
    "OutputData" -> outputData,
    "OutputBasis" -> basis
  |>
];

compileSpinProjectionSectorModel::usage =
  "compileSpinProjectionSectorModel[sector, ops, weight, expr, vars] builds the direct numeric RHS model for one supported chiral sector, or returns $Failed.";
compileSpinProjectionSectorModel[sector : ("Holo" | "Anti"), ops_List, weight_, expr_, vars_List] := compileSpinProjectionSectorModel[sector, ops, weight, expr, vars] = Module[
  {
    template,
    terms,
    pieces,
    freeSpinSymbols,
    freeSpinChiralities,
    freeSpinSlot,
    freeVectorGroups,
    freeVectorSlot,
    chargeGuidedQ,
    freeSpinPictures,
    outputSpinSymbols,
    outputKeys,
    outputRowIndex,
    selectorMatrix,
    selectorCols,
    selectorRows,
    rowsFromAssoc,
    selectorWeights,
    vsrc,
    ssrc,
    matrixDesc,
    scalarDesc,
    outputDesc,
    fastTerm,
    spinChirs
  },
  If[expr === 0 || expr === 1 || vars === {}, Return[<|"Sector" -> sector, "Ops" -> ops, "Weight" -> weight, "Expr" -> expr, "Vars" -> vars, "VarCount" -> Length[vars], "Terms" -> {}|>]];
  template = spinProjectionSectorTemplate[ops, expr];
  terms = Replace[Expand[expr], {0 -> {}, sum_Plus :> List @@ sum, other_ :> {other}}];
  pieces = splitSpinProjectionTerm[#, vars] & /@ terms;
  If[MemberQ[pieces, $Failed], Return[$Failed]];
  freeSpinSymbols = SortBy[Intersection[template["SpinSymbols"], template["FreeSymbols"]], SymbolName];
  freeSpinChiralities = Lookup[template["SpinChiralities"], freeSpinSymbols];
  freeSpinSlot = AssociationThread[freeSpinSymbols -> Range[Length[freeSpinSymbols]]];
  freeVectorGroups = SortBy[template["FreeVectorGroups"], SymbolName @* First];
  freeVectorSlot = Association @ Flatten[MapIndexed[Thread[#1 -> First[#2]] &, freeVectorGroups], 1];
  outputSpinSymbols = DeleteDuplicates @ Flatten[Lookup[Lookup[pieces, "OutputData", <||>], "SpinSymbols", {}], 1];
  If[Complement[Intersection[template["SpinSymbols"], template["DummySymbols"]], outputSpinSymbols] =!= {}, Return[$Failed]];
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
  outputKeys = SortBy[
    DeleteDuplicates @ Flatten[
      Cases[pieces, state_Association /; KeyExistsQ[state, "Assoc"] :> Keys[state["Assoc"]], Infinity],
      1
    ],
    ToString[InputForm[#]] &
  ];
  outputRowIndex = AssociationThread[outputKeys -> Range[Length[outputKeys]]];
  selectorMatrix = If[
    outputKeys === {},
    ConstantArray[0., {0, 0}],
    Join[
      spinProjectionSelectorProjection[Length[outputKeys], Min[8, Length[outputKeys]], {sector, "A", outputKeys}],
      spinProjectionSelectorProjection[Length[outputKeys], Min[8, Length[outputKeys]], {sector, "B", outputKeys}]
    ]
  ];
  selectorCols = If[selectorMatrix === {}, {}, Transpose[selectorMatrix]];
  selectorRows = Length[selectorMatrix];
  rowsFromAssoc[assoc_Association] := KeyValueMap[Function[{key, coeff}, {outputRowIndex[key], coeff}], assoc];
  selectorWeights[rows_List] := Which[
    selectorRows == 0, {},
    rows === {}, ConstantArray[0. + 0. I, {selectorRows}],
    True, Developer`ToPackedArray @ Total[(#[[2]] selectorCols[[#[[1]]]] &) /@ rows]
  ];
  vsrc[sym_, stateVectors_, dummyVectors_] := Which[
    IntegerQ[sym], {4, sym},
    KeyExistsQ[freeVectorSlot, sym], {1, freeVectorSlot[sym]},
    KeyExistsQ[stateVectors, sym], {2, stateVectors[sym]},
    KeyExistsQ[dummyVectors, sym], {3, dummyVectors[sym]},
    True, $Failed
  ];
  ssrc[sym_, stateSpins_, outputSym_] := Which[
    KeyExistsQ[freeSpinSlot, sym], {1, freeSpinSlot[sym]},
    KeyExistsQ[stateSpins, sym], {2, stateSpins[sym]},
    sym === outputSym, {3, 1},
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
      {part["CTag"], Replace[Head /@ part["VectorLinks"], {GammaUDHold -> 1, GammaDUHold -> 2}, 1], sources, part["TailLinks"], spinProjectionGammaFactorMatrix[links], spinProjectionNumericGammaFactorMatrix[links]},
      {part["CTag"], Replace[Head /@ part["VectorLinks"], {GammaUDHold -> 1, GammaDUHold -> 2}, 1], sources, part["TailLinks"], None, None}
    ]
  ];
  scalarDesc[part_, stateSpins_, stateVectors_, dummyVectors_, outputSym_] := Module[{left, right, matrix},
    Switch[part["Kind"],
      "Delta",
      {0, vsrc[part["VectorSymbols"][[1]], stateVectors, dummyVectors], vsrc[part["VectorSymbols"][[2]], stateVectors, dummyVectors]},
      "Gamma",
      If[MemberQ[part["Spinors"], outputSym], Return[$Failed]];
      left = ssrc[part["Spinors"][[1]], stateSpins, outputSym];
      right = ssrc[part["Spinors"][[2]], stateSpins, outputSym];
      If[MemberQ[{left, right}, $Failed], Return[$Failed]];
      If[part["VectorLinks"] === {} && part["CTag"] === None && part["TailLinks"] === {} && SameQ @@ part["SpinorChiralities"],
        {1, left, right},
        matrix = matrixDesc[part, stateVectors, dummyVectors];
        If[matrix === $Failed, $Failed, {2, matrix, left, right}]
      ],
      _,
      $Failed
    ]
  ];
  outputDesc[part_, stateSpins_, stateVectors_, dummyVectors_, outputSym_] := Module[{pos, other, matrix},
    If[Count[part["Spinors"], outputSym] =!= 1, Return[$Failed]];
    pos = First @ FirstPosition[part["Spinors"], outputSym];
    other = ssrc[part["Spinors"][[3 - pos]], stateSpins, outputSym];
    If[other === $Failed, Return[$Failed]];
    If[part["VectorLinks"] === {} && part["CTag"] === None && part["TailLinks"] === {},
      {0, other},
      matrix = matrixDesc[part, stateVectors, dummyVectors];
      If[matrix === $Failed, $Failed, {1, pos, matrix, other}]
    ]
  ];
  fastTerm[piece_] := Module[
    {
      outputSym,
      stateSpinSymbols,
      stateVectorSymbols,
      stateSpins,
      stateVectors,
      dummySymbols,
      dummyVectors,
      parts,
      outputPos,
      scalarFactors,
      outputFactor,
      states,
      basisDim,
      rows,
      basisStates,
      spinIndex,
      sharedStates
    },
    outputSym = If[piece["OutputData"]["VectorSymbols"] === {} && Length[piece["OutputData"]["SpinSymbols"]] === 1, First[piece["OutputData"]["SpinSymbols"]], None];
    spinChirs = spinSymbolChiralities[piece["OutputTemplate"]];
    stateSpinSymbols = DeleteCases[piece["OutputData"]["SpinSymbols"], outputSym];
    stateVectorSymbols = piece["OutputData"]["VectorSymbols"];
    stateSpins = AssociationThread[stateSpinSymbols -> Range[Length[stateSpinSymbols]]];
    stateVectors = AssociationThread[stateVectorSymbols -> Range[Length[stateVectorSymbols]]];
    dummySymbols = Complement[piece["Tensor"]["DummyVectorSymbols"], stateVectorSymbols, Keys[freeVectorSlot]];
    dummyVectors = AssociationThread[dummySymbols -> Range[Length[dummySymbols]]];
    parts = piece["Tensor"]["FactorParts"];
    If[outputSym === None,
      scalarFactors = scalarDesc[#, stateSpins, stateVectors, dummyVectors, None] & /@ parts;
      If[MemberQ[scalarFactors, $Failed], Return[$Failed]];
      states = Function[state,
          rows = rowsFromAssoc[state["Assoc"]];
          {
            Developer`ToPackedArray[
              spinProjectionSpinorBasisIndex[Lookup[state["Spins"], #], Lookup[spinChirs, #]] & /@ stateSpinSymbols
            ],
            Developer`ToPackedArray[Lookup[state["Vectors"], stateVectorSymbols, {}]],
            rows,
            selectorWeights[rows]
          }
        ] /@ piece["OutputBasis"];
      If[!AllTrue[states[[All, 1]], VectorQ[#, IntegerQ] &] || !AllTrue[states[[All, 2]], VectorQ[#, IntegerQ] &], Return[$Failed]];
      Return[{1, piece["VarColumn"], piece["ScalarFactor"], N[piece["ScalarFactor"]], scalarFactors, states, Length[dummySymbols]}]
    ];
    outputPos = Select[Range[Length[parts]], MemberQ[parts[[#, "Spinors"]], outputSym] &];
    If[Length[outputPos] =!= 1, Return[$Failed]];
    scalarFactors = scalarDesc[#, stateSpins, stateVectors, dummyVectors, outputSym] & /@ Delete[parts, First[outputPos]];
    If[MemberQ[scalarFactors, $Failed], Return[$Failed]];
    outputFactor = outputDesc[parts[[First[outputPos]]], stateSpins, stateVectors, dummyVectors, outputSym];
    If[outputFactor === $Failed, Return[$Failed]];
    basisDim = Length[spinIterationValues[Lookup[spinChirs, outputSym]]];
    basisStates = Table[
      {Developer`ToPackedArray[{}], Developer`ToPackedArray[{}], {}, ConstantArray[0. + 0. I, {selectorRows}]},
      {basisDim}
    ];
    Scan[
      Function[state,
        rows = rowsFromAssoc[state["Assoc"]];
        spinIndex = spinProjectionSpinorBasisIndex[state["Spins"][outputSym], Lookup[spinChirs, outputSym]];
        If[IntegerQ[spinIndex],
          basisStates[[spinIndex]] = {
            Developer`ToPackedArray[
              spinProjectionSpinorBasisIndex[Lookup[state["Spins"], #], Lookup[spinChirs, #]] & /@ stateSpinSymbols
            ],
            Developer`ToPackedArray[Lookup[state["Vectors"], stateVectorSymbols, {}]],
            rows,
            selectorWeights[rows]
          }
        ];
      ],
      piece["OutputBasis"]
    ];
    sharedStates = DeleteDuplicates[basisStates[[All, {1, 2}]]];
    If[
      Length[sharedStates] == 1,
      {0, piece["VarColumn"], piece["ScalarFactor"], N[piece["ScalarFactor"]], scalarFactors, outputFactor, sharedStates[[1, 1]], sharedStates[[1, 2]], basisStates[[All, 3]], basisStates[[All, 4]], Length[dummySymbols]},
      {2, piece["VarColumn"], piece["ScalarFactor"], N[piece["ScalarFactor"]], scalarFactors, outputFactor, basisStates, Length[dummySymbols]}
    ]
  ];
  pieces = fastTerm /@ pieces;
  If[MemberQ[pieces, $Failed], Return[$Failed]];
  <|
    "Sector" -> sector,
    "Ops" -> ops,
    "Weight" -> weight,
    "Expr" -> expr,
    "Vars" -> vars,
    "VarCount" -> Length[vars],
    "OutputKeys" -> outputKeys,
    "OutputCount" -> Length[outputKeys],
    "SelectorRowCount" -> selectorRows,
    "FreeSpinSymbols" -> freeSpinSymbols,
    "FreeSpinChiralities" -> freeSpinChiralities,
    "FreeVectorGroups" -> freeVectorGroups,
    "ChargeGuidedQ" -> chargeGuidedQ,
    "FreeSpinPictures" -> Lookup[freeSpinPictures, freeSpinSymbols, Missing["NotChargeGuided"]],
    "OutputCharges" -> If[chargeGuidedQ, spinProjectionGroundSpinOutputCharges[expr], {}],
    "Terms" -> pieces
  |>
];

spinProjectionNumericGammaLinkMatrix::usage =
  "spinProjectionNumericGammaLinkMatrix[link] returns the machine-precision 16x16 matrix for one concrete gamma-chain link.";
spinProjectionNumericGammaLinkMatrix[link_] := spinProjectionNumericGammaLinkMatrix[link] = N[spinProjectionGammaLinkMatrix[link]];

spinProjectionNumericAntisymmetrizedMatrix::usage =
  "spinProjectionNumericAntisymmetrizedMatrix[vectorLinks] returns the machine-precision antisymmetrized gamma matrix for one concrete vector-link list.";
spinProjectionNumericAntisymmetrizedMatrix[{}] := IdentityMatrix[Length[CUD]] // N;
spinProjectionNumericAntisymmetrizedMatrix[vectorLinks_List] := spinProjectionNumericAntisymmetrizedMatrix[vectorLinks] = Module[
  {rank = Length[vectorLinks]},
  1./rank Sum[
    (-1.)^(pos - 1) spinProjectionNumericGammaLinkMatrix[vectorLinks[[pos]]] . spinProjectionNumericAntisymmetrizedMatrix[Delete[vectorLinks, pos]],
    {pos, 1, rank}
  ]
];

spinProjectionNumericGammaFactorMatrix::usage =
  "spinProjectionNumericGammaFactorMatrix[links] returns the machine-precision matrix represented by one concrete gamma-chain link list.";
spinProjectionNumericGammaFactorMatrix[{CUDHold, GammaDUHold[mu_Integer]}] /; 1 <= mu <= 10 := N[CGamma[mu]];
spinProjectionNumericGammaFactorMatrix[{CDUHold, GammaUDHold[mu_Integer]}] /; 1 <= mu <= 10 := N[CIGamma[mu]];
spinProjectionNumericGammaFactorMatrix[links_List] := spinProjectionNumericGammaFactorMatrix[links] = Module[
  {cTag, coreLinks, vectorLinks, tailLinks, pairingMatrix},
  If[links === {},
    pairingMatrix = Switch[
      gammaProductSpinorChiralities[links],
      {"chiral", "antichiral"}, N[CUD],
      {"antichiral", "chiral"}, N[CDU],
      _, IdentityMatrix[Length[CUD]] // N
    ];
    Return[pairingMatrix];
  ];
  cTag = If[MatchQ[First[links], CUDHold | CDUHold], First[links], None];
  coreLinks = If[cTag === None, links, Rest[links]];
  vectorLinks = Select[coreLinks, gammaVectorLinkQ];
  tailLinks = Select[coreLinks, !gammaVectorLinkQ[#] &];
  Fold[
    Dot,
    If[cTag === None, IdentityMatrix[Length[CUD]] // N, spinProjectionNumericGammaLinkMatrix[cTag]],
    Join[
      {spinProjectionNumericAntisymmetrizedMatrix[vectorLinks]},
      spinProjectionNumericGammaLinkMatrix /@ tailLinks
    ]
  ]
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

spinProjectionRowBlock::usage =
  "spinProjectionRowBlock[model, assignment, numericQ] returns one RHS coefficient row block in machine or exact arithmetic for a concrete compiled probe assignment.";
spinProjectionRowBlock[model_Association, assignment : {freeSpins_List, freeVectors_List}, numericQ_: False] := Module[
  {
    rows = If[numericQ, model["SelectorRowCount"], model["OutputCount"]],
    cols = model["VarCount"],
    zero = If[numericQ, 0. + 0. I, 0],
    one = If[numericQ, 1. + 0. I, 1],
    block,
    vectorValue,
    spinValue,
    gammaMatrix,
    scalarValue,
    outputVector,
    outputScalar,
    addTerm,
    loopDummy
  },
  block = ConstantArray[zero, {rows, cols}];
  vectorValue[src_, stateVectors_, dummy_] := Switch[src[[1]],
    1, freeVectors[[src[[2]]]],
    2, stateVectors[[src[[2]]]],
    3, dummy[[src[[2]]]],
    4, src[[2]],
    _, $Failed
  ];
  spinValue[src_, stateSpins_, out_] := Switch[src[[1]],
    1, freeSpins[[src[[2]]]],
    2, stateSpins[[src[[2]]]],
    3, out,
    _, $Failed
  ];
  gammaMatrix[desc_, stateVectors_, dummy_] := Module[{cached, values},
    cached = If[numericQ, desc[[6]], desc[[5]]];
    If[cached =!= None, Return[cached]];
    values = vectorValue[#, stateVectors, dummy] & /@ desc[[3]];
    If[!AllTrue[values, IntegerQ], Return[$Failed]];
    If[
      numericQ,
      spinProjectionNumericGammaFactorMatrix @ Join[
        If[desc[[1]] === None, {}, {desc[[1]]}],
        MapThread[If[#1 === 1, GammaUDHold[#2], GammaDUHold[#2]] &, {desc[[2]], values}],
        desc[[4]]
      ],
      spinProjectionGammaFactorMatrix @ Join[
        If[desc[[1]] === None, {}, {desc[[1]]}],
        MapThread[If[#1 === 1, GammaUDHold[#2], GammaDUHold[#2]] &, {desc[[2]], values}],
        desc[[4]]
      ]
    ]
  ];
  scalarValue[factor_, stateSpins_, stateVectors_, dummy_, out_] := Switch[factor[[1]],
    0,
    If[vectorValue[factor[[2]], stateVectors, dummy] === vectorValue[factor[[3]], stateVectors, dummy], one, zero],
    1,
    If[spinValue[factor[[2]], stateSpins, out] === spinValue[factor[[3]], stateSpins, out], one, zero],
    2,
    With[
      {
        matrix = gammaMatrix[factor[[2]], stateVectors, dummy],
        i = spinValue[factor[[3]], stateSpins, out],
        j = spinValue[factor[[4]], stateSpins, out]
      },
      If[MatrixQ[matrix] && IntegerQ[i] && IntegerQ[j], matrix[[i, j]], $Failed]
    ],
    _,
    $Failed
  ];
  outputVector[factor_, basisDim_, stateSpins_, stateVectors_, dummy_] := Switch[factor[[1]],
    0,
    With[{i = spinValue[factor[[2]], stateSpins, 1]},
      If[IntegerQ[i], If[numericQ, N[UnitVector[basisDim, i]], UnitVector[basisDim, i]], $Failed]
    ],
    1,
    With[
      {
        matrix = gammaMatrix[factor[[3]], stateVectors, dummy],
        i = spinValue[factor[[4]], stateSpins, 1]
      },
      If[!MatrixQ[matrix] || !IntegerQ[i], $Failed, If[factor[[2]] === 1, matrix[[All, i]], matrix[[i, All]]]]
    ],
    _,
    $Failed
  ];
  outputScalar[factor_, out_, stateSpins_, stateVectors_, dummy_] := Switch[factor[[1]],
    0,
    With[{i = spinValue[factor[[2]], stateSpins, out]},
      If[IntegerQ[i], If[i == out, one, zero], $Failed]
    ],
    1,
    With[
      {
        matrix = gammaMatrix[factor[[3]], stateVectors, dummy],
        i = spinValue[factor[[4]], stateSpins, out]
      },
      If[!MatrixQ[matrix] || !IntegerQ[i], $Failed, If[factor[[2]] === 1, matrix[[out, i]], matrix[[i, out]]]]
    ],
    _,
    $Failed
  ];
  loopDummy[k_Integer, body_] := Switch[k,
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
  addTerm[term_] := Module[{kind, col, pref, scalars, dummyCount, prod, vec},
    kind = term[[1]];
    col = term[[2]];
    pref = If[numericQ, term[[4]], term[[3]]];
    scalars = term[[5]];
    dummyCount = term[[If[kind == 0, 11, If[kind == 2, 8, 7]]]];
    loopDummy[
      dummyCount,
      Function[dummy,
        Which[
          kind == 1,
          Scan[
            Function[state,
              prod = pref;
              Do[
                prod *= scalarValue[scalar, state[[1]], state[[2]], dummy, 0];
                If[prod === $Failed || If[numericQ, Chop[prod] == 0., prod === 0], Return[]],
                {scalar, scalars}
              ];
              If[numericQ,
                block[[All, col]] += prod state[[4]],
                Scan[(block[[#[[1]], col]] += #[[2]] prod) &, state[[3]]]
              ]
            ],
            term[[6]]
          ],
          kind == 0,
          (
            prod = pref;
            Do[
              prod *= scalarValue[scalar, term[[7]], term[[8]], dummy, 0];
              If[prod === $Failed || If[numericQ, Chop[prod] == 0., prod === 0], Return[]],
              {scalar, scalars}
            ];
            vec = outputVector[term[[6]], Length[term[[9]]], term[[7]], term[[8]], dummy];
            If[vec === $Failed || If[numericQ, Norm[vec] == 0., !AnyTrue[vec, # =!= 0 &]], Return[]];
            If[numericQ,
              block[[All, col]] += prod Total[MapThread[#1 #2 &, {vec, term[[10]]}]],
              Do[
                If[vec[[i]] =!= 0, Scan[(block[[#[[1]], col]] += #[[2]] vec[[i]] prod) &, term[[9, i]]]],
                {i, Length[vec]}
              ]
            ]
          ),
          kind == 2,
          Do[
            prod = pref;
            Do[
              prod *= scalarValue[scalar, term[[7, i, 1]], term[[7, i, 2]], dummy, i];
              If[prod === $Failed || If[numericQ, Chop[prod] == 0., prod === 0], Return[]],
              {scalar, scalars}
            ];
            prod *= outputScalar[term[[6]], i, term[[7, i, 1]], term[[7, i, 2]], dummy];
            If[prod === $Failed || If[numericQ, Chop[prod] == 0., prod === 0], Continue[]];
            If[numericQ,
              block[[All, col]] += prod term[[7, i, 4]],
              Scan[(block[[#[[1]], col]] += #[[2]] prod) &, term[[7, i, 3]]]
            ],
            {i, Length[term[[7]]]}
          ]
        ]
      ]
    ]
  ];
  Scan[addTerm, model["Terms"]];
  If[numericQ, Chop[block], block]
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
    solvedLookup,
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
    solvedLookup = AssociationThread[
      spinProjectionSpinBasisChargeTable[Last[model["FreeSpinChiralities"]], Last[model["FreeSpinPictures"]]] ->
        Range[Length[spinProjectionSpinBasisState[Last[model["FreeSpinChiralities"]]]]]
    ];
    outputCharges = spinProjectionSeededOrder[model["OutputCharges"], seed, "outputCharges"];
    tupleIterator = spinProjectionTupleIterator[Most[spinDomains], tupleSeed, {"chargeTuples", model["FreeSpinSymbols"]}];
    tuple = tupleIterator[];
    next[] := Module[{outputCharge, currentTuple, required, solvedValue, rules},
      While[yielded < maxCount && tuple =!= EndOfFile,
        currentTuple = tuple;
        While[outputIndex <= Length[outputCharges],
          outputCharge = outputCharges[[outputIndex]];
          outputIndex++;
          required = outputCharge - Total[MapThread[#1[[#2]] &, {fixedTables, currentTuple}]];
          solvedValue = If[KeyExistsQ[solvedLookup, required], solvedLookup[required], Missing["NotFound"]];
          If[MissingQ[solvedValue], Continue[]];
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
  nextTuple = spinProjectionTupleIterator[Join[spinDomains, vectorDomains], tupleSeed, {"genericTuples", model["FreeSpinSymbols"], model["FreeVectorGroups"]}];
  next[] := Module[{tuple, spinCount = Length[spinDomains]},
    If[yielded >= maxCount, Return[EndOfFile]];
    tuple = nextTuple[];
    If[tuple === EndOfFile, Return[EndOfFile]];
    yielded++;
    {
      Developer`ToPackedArray[Take[tuple, spinCount]],
      Developer`ToPackedArray[Drop[tuple, spinCount]]
    }
  ];
  next
];

spinProjectionNumericBasisInsert::usage =
  "spinProjectionNumericBasisInsert[basis, rows, tolerance] inserts independent machine-precision rows into an orthonormal selector basis.";
spinProjectionNumericBasisInsert[basis_List, rows_?MatrixQ, tolerance_: spinProjectionCompiledSelectorTolerance] := Module[
  {localBasis = basis, accepted = {}, residual, norm},
  Do[
    residual = N[rows[[i]]];
    If[Norm[residual] <= tolerance, Continue[]];
    Do[residual -= (Conjugate[b].residual) b, {b, localBasis}];
    norm = Norm[residual];
    If[norm > tolerance,
      localBasis = Append[localBasis, residual/norm];
      accepted = Append[accepted, i];
    ],
    {i, Length[rows]}
  ];
  <|"Basis" -> localBasis, "Accepted" -> accepted|>
];

spinProjectionExactBasisInsert::usage =
  "spinProjectionExactBasisInsert[state, rows] inserts independent exact rows into one reduced exact row basis.";
spinProjectionExactBasisInsert[state_Association, rows_?MatrixQ] := Module[
  {basisRows = state["Rows"], pivots = state["Pivots"], accepted = {}, acceptedRows = {}, row, pivotPos, pivot, coeff, insertPos},
  Do[
    row = rows[[i]];
    If[!AnyTrue[row, # =!= 0 &], Continue[]];
    Do[
      coeff = row[[pivots[[j]]]];
      If[coeff =!= 0, row = row - coeff basisRows[[j]]],
      {j, Length[basisRows]}
    ];
    pivotPos = FirstPosition[row, x_ /; x =!= 0, Missing["NoPivot"], {1}, Heads -> False];
    If[MissingQ[pivotPos], Continue[]];
    pivot = First[pivotPos];
    row = row/row[[pivot]];
    Do[
      coeff = basisRows[[j, pivot]];
      If[coeff =!= 0, basisRows[[j]] = basisRows[[j]] - coeff row],
      {j, Length[basisRows]}
    ];
    insertPos = 1 + Count[pivots, _?(# < pivot &)];
    basisRows = Insert[basisRows, row, insertPos];
    pivots = Insert[pivots, pivot, insertPos];
    accepted = Append[accepted, i];
    acceptedRows = Append[acceptedRows, rows[[i]]],
    {i, Length[rows]}
  ];
  <|
    "Basis" -> <|"Rows" -> basisRows, "Pivots" -> pivots|>,
    "Accepted" -> accepted,
    "AcceptedRows" -> acceptedRows
  |>
];

solveCompiledSpinProjectionSector::usage =
  "solveCompiledSpinProjectionSector[model, seed] solves one supported sector using deterministic concrete probes and direct exact RHS contraction, or returns $Failed.";
solveCompiledSpinProjectionSector[model_Association, seed_] := solveCompiledSpinProjectionSector[model, seed] = Module[
  {
    nextCandidate,
    useSelector,
    selectorBasis = {},
    exactBasis = <|"Rows" -> {}, "Pivots" -> {}|>,
    rows = {},
    rhs = {},
    attempts = 0,
    selectorBlock,
    selectorInsert,
    rowBlock,
    exactInsert,
    independentRows,
    independentIndices,
    lhs,
    lhsAssoc,
    inputs,
    solution,
    candidate
  },
  If[model["Expr"] === 0, Return[<|"Expr" -> 0, "Attempts" -> 0|>]];
  If[model["Expr"] === 1, Return[<|"Expr" -> 1, "Attempts" -> 0|>]];
  If[model["VarCount"] == 0, Return[<|"Expr" -> model["Expr"], "Attempts" -> 0|>]];
  useSelector = model["SelectorRowCount"] > 0 && model["VarCount"] > 2;
  nextCandidate = spinProjectionAssignmentIterator[model, seed];
  If[nextCandidate === $Failed, Return[$Failed]];
  While[Length[rows] < model["VarCount"],
    candidate = nextCandidate[];
    If[candidate === EndOfFile, Break[]];
    If[useSelector,
      selectorBlock = spinProjectionRowBlock[model, candidate, True];
      If[selectorBlock === $Failed, Continue[]];
      selectorInsert = spinProjectionNumericBasisInsert[selectorBasis, selectorBlock];
      If[selectorInsert["Accepted"] === {}, Continue[]]
    ];
    rowBlock = spinProjectionRowBlock[model, candidate, False];
    If[rowBlock === $Failed, Continue[]];
    exactInsert = spinProjectionExactBasisInsert[exactBasis, rowBlock];
    independentIndices = exactInsert["Accepted"];
    independentRows = exactInsert["AcceptedRows"];
    If[independentIndices === {}, Continue[]];
    exactBasis = exactInsert["Basis"];
    If[useSelector, selectorBasis = selectorInsert["Basis"]];
    inputs = spinProjectionConcreteInputs[model, candidate];
    lhs = spinProjectionSectorEvaluation[model["Sector"], model["Weight"], inputs];
    lhsAssoc = spinProjectionOperatorAssociation[lhs];
    rows = Join[rows, independentRows];
    rhs = Join[rhs, Lookup[lhsAssoc, model["OutputKeys"][[#]], 0] & /@ independentIndices];
    attempts++;
  ];
  If[Length[rows] < model["VarCount"], Return[$Failed]];
  solution = Thread[model["Vars"] -> LinearSolve[rows, rhs]];
  <|"Expr" -> (model["Expr"] /. solution), "Attempts" -> attempts|>
];

solveCompiledSpinProjectionSectors::usage =
  "solveCompiledSpinProjectionSectors[holoOps, antiOps, wH, wA, hExpr, hVars, aExpr, aVars, seed] solves all supported spin-field sectors with the compiled direct-contraction path or returns $Failed.";
solveCompiledSpinProjectionSectors[holoOps_List, antiOps_List, wH_, wA_, hExpr_, hVars_List, aExpr_, aVars_List, seed_] := Module[
  {hModel, aModel, hSolved, aSolved},
  hModel = compileSpinProjectionSectorModel["Holo", holoOps, wH, hExpr, hVars];
  aModel = compileSpinProjectionSectorModel["Anti", antiOps, wA, aExpr, aVars];
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
  buildSectorProjection[opsKey_, dataKey_, weight_, offset_] := Which[
    o[opsKey] === {}, {If[weight === 0, 1, 0], {}, offset},
    o[dataKey] === {}, {0, {}, offset},
    True, attachSpinProjectionCoefficients[o[dataKey], offset]
  ];
  {hExpr, hVars, n} = buildSectorProjection["holoOps", "holoData", wH, 0];
  {aExpr, aVars, n} = buildSectorProjection["antiOps", "antiData", wA, n];
  If[hExpr === 0 || aExpr === 0, Return[0]];
  solved = solveCompiledSpinProjectionSectors[o["holoOps"], o["antiOps"], wH, wA, hExpr, hVars, aExpr, aVars, seed];
  If[solved === $Failed,
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
