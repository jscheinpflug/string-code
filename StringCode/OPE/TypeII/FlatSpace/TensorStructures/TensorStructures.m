(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`OPE`TypeII`FlatSpace`TensorStructures`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];
Needs["StringCode`Symbols`TypeII`FlatSpace`"];
Needs["StringCode`OPE`TypeII`FlatSpace`GammaMatrices`GammaProductGrammar`"];
Needs["StringCode`OPE`TypeII`FlatSpace`TensorStructures`IndependentTensorStructuresSelector`"];


(* ::Section:: *)
(*Declare public variables and methods*)


generateTensorStructures::usage =
  "generateTensorStructures[incoming, outgoing, opts] enumerates allowed gamma and vector-contraction tensor structures grouped by abstract shape.";

generateTensorStructures::dupidx =
  "Duplicate or colliding index symbols were found across incoming/outgoing vector/spinor inputs.";
generateTensorStructures::badchir =
  "Spinor entries must be pairs {symbol, \"chiral\"|\"antichiral\"}.";
generateTensorStructures::toomanyout =
  "Outgoing input may contain at most one spinor index.";
generateTensorStructures::oddspinor =
  "Total number of spinor indices must be even.";
generateTensorStructures::toomanyspinors =
  "Total spinor pairs k=`1` exceeds MaxK=`2`.";
generateTensorStructures::badarg =
  "Both incoming and outgoing arguments must be Association objects.";
generateTensorStructures::badvec =
  "\"vector\" entries must be lists of symbols.";
generateTensorStructures::badantisym =
  "\"AntisymmetricVectorGroups\" must be a list of pairwise-disjoint symbolic vector groups drawn from the incoming/outgoing vector labels.";

Options[generateTensorStructures] = {
  "MaxK" -> 5,
  "RepresentativesOnly" -> False,
  "AntisymmetricVectorGroups" -> {},
  "ReturnSelectorCandidates" -> False
};


(* ::Section:: *)
(*Logic*)


Begin["Private`"];

formOrder::usage = "formOrder[form] gives a stable total ordering key for supported gamma heads.";
formOrder[GammaFormUU] := 1;
formOrder[GammaFormDD] := 2;
formOrder[GammaFormUD] := 3;
formOrder[GammaForm11UU] := 4;
formOrder[GammaForm11DD] := 5;
formOrder[GammaForm11UD] := 6;

parseMaxKOption::usage = "parseMaxKOption[opts] extracts a nonnegative integer MaxK option, defaulting to 5.";
parseMaxKOption[opts_List] := Module[{maxK},
  maxK = Lookup[Association[Join[Options[generateTensorStructures], opts]], "MaxK", 5];
  If[IntegerQ[maxK] && maxK >= 0, maxK, 5]
];

parseRepresentativesOnlyOption::usage = "parseRepresentativesOnlyOption[opts] extracts optional boolean RepresentativesOnly flag.";
parseRepresentativesOnlyOption[opts_List] := Module[{flag},
  flag = Lookup[Association[Join[Options[generateTensorStructures], opts]], "RepresentativesOnly", False];
  TrueQ[flag]
];

parseReturnSelectorCandidatesOption::usage = "parseReturnSelectorCandidatesOption[opts] extracts optional boolean ReturnSelectorCandidates flag for internal selector-ready generation.";
parseReturnSelectorCandidatesOption[opts_List] := Module[{flag},
  flag = Lookup[Association[Join[Options[generateTensorStructures], opts]], "ReturnSelectorCandidates", False];
  TrueQ[flag]
];

parseAntisymmetricVectorGroupsOption::usage =
  "parseAntisymmetricVectorGroupsOption[opts, vectorIndices] validates and canonicalizes antisymmetric external-vector groups.";
parseAntisymmetricVectorGroupsOption[opts_List, vectorIndices_List] := Module[
  {groups, normalized, validVectors},
  groups = Lookup[Association[Join[Options[generateTensorStructures], opts]], "AntisymmetricVectorGroups", {}];
  validVectors = DeleteDuplicates[vectorIndices];
  If[!ListQ[groups],
    Message[generateTensorStructures::badantisym];
    Return[$Failed];
  ];
  normalized = SortBy[DeleteDuplicates[#], symbolSortKey] & /@ groups;
  If[
    !AllTrue[normalized, ListQ[#] && Length[#] > 1 && AllTrue[#, SymbolQ] &] ||
      !AllTrue[normalized, SubsetQ[validVectors, #] &] ||
      !DuplicateFreeQ[Flatten[normalized]],
    Message[generateTensorStructures::badantisym];
    Return[$Failed];
  ];
  SortBy[normalized, symbolSortKey[First[#]] &]
];

normalizeIndexAssociation::usage = "normalizeIndexAssociation[data] ensures keys \"vector\" and \"spinor\" exist with list defaults.";
normalizeIndexAssociation[data_Association] := <|
  "vector" -> Lookup[data, "vector", {}],
  "spinor" -> Lookup[data, "spinor", {}]
|>;

validVectorIndexListQ::usage = "validVectorIndexListQ[vecs] checks vecs is a list of symbols.";
validVectorIndexListQ[vecs_] := ListQ[vecs] && AllTrue[vecs, SymbolQ];

validSpinorIndexListQ::usage = "validSpinorIndexListQ[spinors] checks spinors is a list of {symbol, chirality} pairs.";
validSpinorIndexListQ[spinors_] := ListQ[spinors] &&
  AllTrue[
    spinors,
    MatchQ[#, {_, ("chiral" | "antichiral")}] && SymbolQ[#[[1]]] &
  ];

upperTriangleValues::usage = "upperTriangleValues[m] flattens strict upper-triangular matrix entries in lexicographic index order.";
upperTriangleValues[m_List] := Module[{k = Length[m]},
  Flatten@Table[m[[i, j]], {i, 1, k - 1}, {j, i + 1, k}]
];

gammaTypeConfigs::usage = "gammaTypeConfigs[nChiral, nAnti] enumerates admissible {a,b,c} gamma-count configurations.";
gammaTypeConfigs[nChiral_Integer, nAnti_Integer] := Module[
  {k, a, c, b, reaped},
  If[nChiral < 0 || nAnti < 0 || OddQ[nChiral + nAnti], Return[{}]];
  k = (nChiral + nAnti)/2;
  reaped = Last @ Reap[
    For[a = 0, a <= Floor[nChiral/2], a++,
      c = nChiral - 2 a;
      b = (nAnti - c)/2;
      If[IntegerQ[b] && b >= 0 && a + b + c == k,
        Sow[<|"a" -> a, "b" -> b, "c" -> c|>]
      ];
    ]
  ];
  If[reaped === {}, {}, First[reaped]]
];

outgoingSlotOptions::usage = "outgoingSlotOptions[typeConfig, outChirality] returns allowed outgoing-slot forms.";
outgoingSlotOptions[typeConfig_Association, outChirality_String] := Module[
  {a = typeConfig["a"], b = typeConfig["b"], c = typeConfig["c"], reaped},
  reaped = Last @ Reap[
  Switch[outChirality,
    "chiral",
      If[a > 0, Sow[GammaFormUU]];
      If[c > 0, Sow[GammaFormUD]],
    "antichiral",
      If[b > 0, Sow[GammaFormDD]];
      If[c > 0, Sow[GammaFormUD]]
  ];
  ];
  If[reaped === {}, {}, First[reaped]]
];

outgoingEmittedForm::usage =
  "outgoingEmittedForm[pairForm, outChirality] maps outgoing-pair chirality class to emitted gamma head.";
outgoingEmittedForm[GammaFormUU, "chiral"] := GammaFormUD;
outgoingEmittedForm[GammaFormDD, "antichiral"] := GammaFormUD;
outgoingEmittedForm[GammaFormUD, "chiral"] := GammaFormUU;
outgoingEmittedForm[GammaFormUD, "antichiral"] := GammaFormDD;
outgoingEmittedForm[_, _] := $Failed;

buildSlotBlueprint::usage =
  "buildSlotBlueprint[typeConfig, outPairForm, outChirality] constructs slot descriptors with pair/emitted forms.";
buildSlotBlueprint[typeConfig_Association, outPairForm_, outChirality_] := Module[
  {counts, rest},
  counts = <|GammaFormUU -> typeConfig["a"], GammaFormDD -> typeConfig["b"], GammaFormUD -> typeConfig["c"]|>;
  If[outPairForm =!= None,
    counts[outPairForm] = counts[outPairForm] - 1;
    rest = Join[
      Table[<|"pairForm" -> GammaFormUU, "emitBaseForm" -> GammaFormUU, "hasOutgoing" -> False|>, {counts[GammaFormUU]}],
      Table[<|"pairForm" -> GammaFormDD, "emitBaseForm" -> GammaFormDD, "hasOutgoing" -> False|>, {counts[GammaFormDD]}],
      Table[<|"pairForm" -> GammaFormUD, "emitBaseForm" -> GammaFormUD, "hasOutgoing" -> False|>, {counts[GammaFormUD]}]
    ];
    Prepend[
      rest,
      <|
        "pairForm" -> outPairForm,
        "emitBaseForm" -> outgoingEmittedForm[outPairForm, outChirality],
        "hasOutgoing" -> True
      |>
    ],
    Join[
      Table[<|"pairForm" -> GammaFormUU, "emitBaseForm" -> GammaFormUU, "hasOutgoing" -> False|>, {counts[GammaFormUU]}],
      Table[<|"pairForm" -> GammaFormDD, "emitBaseForm" -> GammaFormDD, "hasOutgoing" -> False|>, {counts[GammaFormDD]}],
      Table[<|"pairForm" -> GammaFormUD, "emitBaseForm" -> GammaFormUD, "hasOutgoing" -> False|>, {counts[GammaFormUD]}]
    ]
  ]
];

baseParitySet::usage = "baseParitySet[emitBaseForm] returns allowed ranks before outgoing truncation.";
baseParitySet[emitBaseForm_] := If[
  MemberQ[{GammaFormUU, GammaFormDD}, emitBaseForm],
  {1, 3, 5, 7, 9},
  {0, 2, 4, 6, 8, 10}
];

allowedPForSlot::usage = "allowedPForSlot[slot] returns the allowed rank list for one slot descriptor.";
allowedPForSlot[slot_Association] := Module[{base},
  base = baseParitySet[slot["emitBaseForm"]];
  If[TrueQ[slot["hasOutgoing"]], Select[base, # <= 5 &], base]
];

pTupleSymmetryCompatibleQ::usage = "pTupleSymmetryCompatibleQ[slotBlueprint, pTuple] keeps sorted p-tuples on equivalent non-outgoing same-form slots.";
pTupleSymmetryCompatibleQ[slotBlueprint_List, pTuple_List] := Module[
  {indicesByForm},
  indicesByForm = GroupBy[
    Select[Range[Length[slotBlueprint]], slotBlueprint[[#, "hasOutgoing"]] === False &],
    {slotBlueprint[[#, "emitBaseForm"]], slotBlueprint[[#, "pairForm"]]} &
  ];
  And @@ (OrderedQ[pTuple[[#]]] & /@ Values[indicesByForm])
];

validPTuples::usage = "validPTuples[pSets, nExtVec, slotBlueprint] returns admissible p-tuples after parity/symmetry filtering.";
validPTuples[pSets_List, nExtVec_Integer, slotBlueprint_List] := Select[
  Tuples[pSets],
  OddQ[Total[#]] === OddQ[nExtVec] &&
    pTupleSymmetryCompatibleQ[slotBlueprint, #] &
];

externalVectorAssignmentTotals::usage =
  "externalVectorAssignmentTotals[pTuple, nExtVec] returns admissible numbers of external vectors assigned directly to gamma slots.";
externalVectorAssignmentTotals[pTuple_List, nExtVec_Integer] := Select[
  Range[0, Min[nExtVec, Total[pTuple]]],
  EvenQ[nExtVec - #] && EvenQ[Total[pTuple] - #] &
];

externalCountDistributions::usage = "externalCountDistributions[pTuple, nExtVec] distributes external vectors among slots with bounds 0<=e_i<=p_i.";
externalCountDistributions[pTuple_List, nExtVec_Integer] := Module[
  {k = Length[pTuple], recurse},
  If[nExtVec == 0, Return[{ConstantArray[0, k]}]];
  recurse[idx_, rem_, acc_] := Module[{maxAssign, val, out = {}},
    If[idx > k, Return[If[rem == 0, {acc}, {}]]];
    maxAssign = Min[pTuple[[idx]], rem];
    For[val = 0, val <= maxAssign, val++,
      out = Join[out, recurse[idx + 1, rem - val, Append[acc, val]]];
    ];
    out
  ];
  recurse[1, nExtVec, {}]
];

matrixFromPairValues::usage = "matrixFromPairValues[k, pairs, values] builds a symmetric contraction matrix from pair assignments.";
matrixFromPairValues[k_Integer, pairs_List, values_List] := Module[{m, t, i, j},
  m = ConstantArray[0, {k, k}];
  Do[
    {i, j} = pairs[[t]];
    m[[i, j]] = values[[t]];
    m[[j, i]] = values[[t]],
    {t, Length[pairs]}
  ];
  m
];

feasibleRemainingContractionsQ::usage =
  "feasibleRemainingContractionsQ[nextPairIndex, rem, pairs] checks whether remaining row sums can still be satisfied.";
feasibleRemainingContractionsQ[nextPairIndex_Integer, rem_List, pairs_List] := Module[
  {k = Length[rem], remPairs, neighbors, cap, i},
  If[Or @@ Thread[rem < 0], Return[False]];
  If[OddQ[Total[rem]], Return[False]];
  remPairs = If[nextPairIndex <= Length[pairs], pairs[[nextPairIndex ;;]], {}];
  For[i = 1, i <= k, i++,
    neighbors = Join[
      Cases[remPairs, {i, j_} :> j],
      Cases[remPairs, {j_, i} :> j]
    ];
    If[neighbors === {} && rem[[i]] != 0, Return[False]];
    cap = Total[rem[[#]] & /@ neighbors];
    If[rem[[i]] > cap, Return[False]];
  ];
  True
];

contractionMatrices::usage = "contractionMatrices[dummyCounts] enumerates all no-self-contraction symmetric matrices with given row sums.";
contractionMatrices[dummyCounts_List] := Module[
  {k = Length[dummyCounts], d = dummyCounts, c12, c13, c14, c23, c24, c34, s, pairs, recurse, m, harvest},
  If[Or @@ Thread[d < 0], Return[{}]];
  If[OddQ[Total[d]], Return[{}]];
  Switch[k,
    0, {{}},
    _ /; Total[d] == 0, {ConstantArray[0, {k, k}]},
    1, If[d[[1]] == 0, {{{0}}}, {}],
    2,
      If[d[[1]] == d[[2]],
        {{{0, d[[1]]}, {d[[1]], 0}}},
        {}
      ],
    3,
      c12 = (d[[1]] + d[[2]] - d[[3]])/2;
      c13 = (d[[1]] + d[[3]] - d[[2]])/2;
      c23 = (d[[2]] + d[[3]] - d[[1]])/2;
      If[And @@ (IntegerQ /@ {c12, c13, c23}) && Min[c12, c13, c23] >= 0,
        {{{0, c12, c13}, {c12, 0, c23}, {c13, c23, 0}}},
        {}
      ],
    4,
      s = (d[[1]] + d[[2]] + d[[3]] - d[[4]])/2;
      If[!IntegerQ[s] || s < 0, Return[{}]];
      harvest = Reap[
        For[c12 = 0, c12 <= Min[d[[1]], d[[2]], s], c12++,
          For[c13 = 0, c13 <= Min[d[[1]] - c12, d[[3]], s - c12], c13++,
            c23 = s - c12 - c13;
            If[c23 < 0 || c23 > d[[2]] - c12 || c23 > d[[3]] - c13, Continue[]];
            c14 = d[[1]] - c12 - c13;
            c24 = d[[2]] - c12 - c23;
            c34 = d[[3]] - c13 - c23;
            If[Min[c14, c24, c34] < 0, Continue[]];
            If[c14 + c24 + c34 =!= d[[4]], Continue[]];
            m = {
              {0, c12, c13, c14},
              {c12, 0, c23, c24},
              {c13, c23, 0, c34},
              {c14, c24, c34, 0}
            };
            Sow[m];
          ];
        ];
      ][[2]];
      If[harvest === {}, {}, First[harvest]],
    _,
      pairs = Subsets[Range[k], {2}];
      recurse[idx_, rem_, vals_] := Module[
        {i, j, maxVal, v, out = {}, nextRem},
        If[idx > Length[pairs],
          Return[If[Total[Abs[rem]] == 0, {vals}, {}]]
        ];
        {i, j} = pairs[[idx]];
        maxVal = Min[rem[[i]], rem[[j]]];
        For[v = 0, v <= maxVal, v++,
          nextRem = rem;
          nextRem[[i]] -= v;
          nextRem[[j]] -= v;
          If[feasibleRemainingContractionsQ[idx + 1, nextRem, pairs],
            out = Join[out, recurse[idx + 1, nextRem, Append[vals, v]]]
          ];
        ];
        out
      ];
      matrixFromPairValues[k, pairs, #] & /@ recurse[1, d, {}]
  ]
];

initialChainIndex::usage = "initialChainIndex[form] returns the left boundary index type (\"U\" or \"D\") used to build a gamma chain.";
initialChainIndex[GammaFormUU] := "U";
initialChainIndex[GammaFormDD] := "D";
initialChainIndex[GammaFormUD] := "U";
initialChainIndex[_] := "U";

emittedChainStartIndex::usage =
  "emittedChainStartIndex[emitBaseForm, pairForm, hasOutgoing] returns the base chain start index for one emitted slot.";
emittedChainStartIndex[GammaFormUD, GammaFormDD, True] := "D";
emittedChainStartIndex[emitBaseForm_, _, _] := initialChainIndex[emitBaseForm];

flipChainIndex::usage = "flipChainIndex[idx] toggles chain index type between \"U\" and \"D\".";
flipChainIndex["U"] := "D";
flipChainIndex["D"] := "U";
flipChainIndex[other_] := other;

gammaLinkHeadForIndex::usage = "gammaLinkHeadForIndex[idx] returns GammaUDHold for \"U\" and GammaDUHold for \"D\".";
gammaLinkHeadForIndex["U"] := GammaUDHold;
gammaLinkHeadForIndex["D"] := GammaDUHold;
gammaLinkHeadForIndex[_] := GammaUDHold;

gamma11TailHeadForIndex::usage = "gamma11TailHeadForIndex[idx] returns Gamma11UUHold for \"U\" and Gamma11DDHold for \"D\".";
gamma11TailHeadForIndex["U"] := Gamma11UUHold;
gamma11TailHeadForIndex["D"] := Gamma11DDHold;
gamma11TailHeadForIndex[_] := Gamma11UUHold;

buildGammaLinks::usage =
  "buildGammaLinks[startIndex, vectorIndices] returns {links, lastIndexType} for alternating GammaUDHold/GammaDUHold links.";
buildGammaLinks[startIndex_String, vectorIndices_List] := Module[
  {state = startIndex, links, i},
  links = Table[Null, {Length[vectorIndices]}];
  For[i = 1, i <= Length[vectorIndices], i++,
    links[[i]] = gammaLinkHeadForIndex[state][vectorIndices[[i]]];
    state = flipChainIndex[state];
  ];
  {links, state}
];

slotWithRank::usage =
  "slotWithRank[slotBlueprint, p] creates slot data {baseHead, rank, hasOutgoing, pairForm} for one rank choice.";
slotWithRank[slot_Association, p_Integer] := {slot["emitBaseForm"], p, slot["hasOutgoing"], slot["pairForm"]};

canonicalizeAbstractStructure::usage =
  "canonicalizeAbstractStructure[slots, extCounts, cMatrix] canonicalizes under permutations within equal non-outgoing form classes.";
canonicalizeAbstractStructure[slots_List, extCounts_List, cMatrix_List] := Module[
  {
    k = Length[slots], outgoingPos, permutable, groups, permBlocks, blockChoices,
    basePerm, perm, candidates = {}, g, choice, slotRep, key, slotPerm, extPerm, cPerm
  },
  outgoingPos = FirstPosition[slots, {_, _, True, _}, Missing["NotFound"]];
  permutable = Complement[
    Range[k],
    If[outgoingPos === Missing["NotFound"], {}, {outgoingPos[[1]]}]
  ];
  groups = Values @ GroupBy[permutable, {slots[[#, 1]], slots[[#, 4]]} &];
  permBlocks = Permutations /@ groups;
  blockChoices = If[permBlocks === {}, {{}}, Tuples[permBlocks]];
  Do[
    basePerm = Range[k];
    choice = blockChoices[[g]];
    Do[
      basePerm[[groups[[j]]]] = choice[[j]],
      {j, Length[groups]}
    ];
    perm = basePerm;
    slotPerm = slots[[perm]];
    extPerm = extCounts[[perm]];
    cPerm = cMatrix[[perm, perm]];
    slotRep = ({formOrder[#[[1]]], #[[2]], Boole[#[[3]]], formOrder[#[[4]]]} &) /@ slotPerm;
    key = {slotRep, extPerm, upperTriangleValues[cPerm]};
    AppendTo[candidates, <|"slots" -> slotPerm, "externalCounts" -> extPerm, "contractionMatrix" -> cPerm, "key" -> key|>],
    {g, Length[blockChoices]}
  ];
  First @ SortBy[candidates, #["key"] &]
];

typeConfigFromSlots::usage =
  "typeConfigFromSlots[slots] returns count vector for {GammaFormUU,GammaFormDD,GammaFormUD}.";
typeConfigFromSlots[slots_List] := Module[{forms = slots[[All, 1]]},
  {
    Count[forms, GammaFormUU],
    Count[forms, GammaFormDD],
    Count[forms, GammaFormUD]
  }
];

abstractSortKey::usage = "abstractSortKey[abstract] returns deterministic ordering key for abstract structures.";
abstractSortKey[abstract_Association] := Module[
  {slots = abstract["slots"], ext = abstract["externalCounts"], c = abstract["contractionMatrix"]},
  {
    Sequence @@ typeConfigFromSlots[slots],
    formOrder /@ slots[[All, 1]],
    slots[[All, 2]],
    Boole /@ slots[[All, 3]],
    formOrder /@ slots[[All, 4]],
    ext,
    upperTriangleValues[c]
  }
];

generateAbstractStructures::usage =
  "generateAbstractStructures[inSpinors, outSpinor, nExtVec] enumerates/deduplicates canonical abstract structures.";
generateAbstractStructures[inSpinors_List, outSpinor_, nExtVec_Integer] := Module[
  {
    allSpinors, nChiral, nAnti, typeConfigs, canonicalByKey = <||>,
    cfg, outPairForms, outPairForm, slotBlueprint, pSets, pTuples, pTuple,
    slotsWithRankData, pOrigTuple, extTotals, nAssignedExt, extDistributions, extCounts, dummyCounts, cMats, cMat,
    canonical, contractionCache = <||>, extDistCache = <||>, extKey, dummyKey
  },
  allSpinors = Join[inSpinors, If[outSpinor === None, {}, {outSpinor}]];
  nChiral = Count[allSpinors[[All, 2]], "chiral"];
  nAnti = Count[allSpinors[[All, 2]], "antichiral"];
  typeConfigs = gammaTypeConfigs[nChiral, nAnti];
  Do[
    outPairForms = If[outSpinor === None, {None}, outgoingSlotOptions[cfg, outSpinor[[2]]]];
    Do[
      slotBlueprint = buildSlotBlueprint[cfg, outPairForm, If[outSpinor === None, None, outSpinor[[2]]]];
      If[AnyTrue[slotBlueprint, #["emitBaseForm"] === $Failed &], Continue[]];
      pSets = allowedPForSlot /@ slotBlueprint;
      pTuples = validPTuples[pSets, nExtVec, slotBlueprint];
      Do[
        slotsWithRankData = MapThread[slotWithRank, {slotBlueprint, pTuple}];
        pOrigTuple = slotsWithRankData[[All, 2]];
        extTotals = externalVectorAssignmentTotals[pOrigTuple, nExtVec];
        Do[
          extKey = {pOrigTuple, nAssignedExt};
          If[!KeyExistsQ[extDistCache, extKey],
            extDistCache[extKey] = externalCountDistributions[pOrigTuple, nAssignedExt]
          ];
          extDistributions = extDistCache[extKey];
          Do[
            dummyCounts = pOrigTuple - extCounts;
            dummyKey = dummyCounts;
            If[!KeyExistsQ[contractionCache, dummyKey],
              contractionCache[dummyKey] = contractionMatrices[dummyCounts]
            ];
            cMats = contractionCache[dummyKey];
            Do[
              canonical = canonicalizeAbstractStructure[slotsWithRankData, extCounts, cMat];
              If[!KeyExistsQ[canonicalByKey, canonical["key"]],
                canonicalByKey[canonical["key"]] = canonical
              ],
              {cMat, cMats}
            ],
            {extCounts, extDistributions}
          ],
          {nAssignedExt, extTotals}
        ],
        {pTuple, pTuples}
      ],
      {outPairForm, outPairForms}
    ],
    {cfg, typeConfigs}
  ];
  SortBy[Values[canonicalByKey], abstractSortKey]
];

slotSpinorChiralities::usage = "slotSpinorChiralities[form] gives the ordered spinor chirality pair for one gamma form.";
slotSpinorChiralities[GammaFormUU] := {"chiral", "chiral"};
slotSpinorChiralities[GammaFormDD] := {"antichiral", "antichiral"};
slotSpinorChiralities[GammaFormUD] := {"chiral", "antichiral"};

slotEndpointChiralities::usage =
  "slotEndpointChiralities[slot] returns the actual ordered endpoint chiralities carried by one emitted slot.";
slotEndpointChiralities[{emitBaseForm_, _, hasOutgoing_, pairForm_}] := Module[{},
  Which[
    TrueQ[hasOutgoing] && pairForm === GammaFormUD && emitBaseForm === GammaFormUU,
      {"chiral", "antichiral"},
    TrueQ[hasOutgoing] && pairForm === GammaFormUD && emitBaseForm === GammaFormDD,
      {"antichiral", "chiral"},
    True,
      slotSpinorChiralities[pairForm]
  ]
];
slotEndpointChiralities[_] := $Failed;

sameChiralitySlotQ::usage =
  "sameChiralitySlotQ[slot] is True exactly when the emitted slot carries two endpoints of the same chirality.";
sameChiralitySlotQ[slot_List] := Module[{chirPair = slotEndpointChiralities[slot]},
  ListQ[chirPair] && Length[chirPair] == 2 && SameQ @@ chirPair
];
sameChiralitySlotQ[_] := False;

preserveOutgoingSpinOrderQ::usage =
  "preserveOutgoingSpinOrderQ[slot] is True when one outgoing same-chirality slot must keep its emitted leg order.";
preserveOutgoingSpinOrderQ[{_, _, True, GammaFormUU}] := True;
preserveOutgoingSpinOrderQ[{_, _, True, GammaFormDD}] := True;
preserveOutgoingSpinOrderQ[_] := False;

chiralityAssignmentUnits::usage =
  "chiralityAssignmentUnits[openPositions] groups chirality-specific open legs into ordered single/pair assignment units.";
chiralityAssignmentUnits[openPositions_List] := Module[
  {grouped, units},
  grouped = GatherBy[SortBy[openPositions, #["id"] &], #["slot"] &];
  units = Map[
    If[
      Length[#] == 2,
      <|"kind" -> "pair", "ids" -> Sort[#[[All, "id"]]]|>,
      <|"kind" -> "single", "ids" -> {First[#]["id"]}|>
    ] &,
    grouped
  ];
  SortBy[units, First[#["ids"]] &]
];

removeSymbolAt::usage = "removeSymbolAt[symbols, index] removes one symbol from a list by 1-based position.";
removeSymbolAt[symbols_List, index_Integer] := Delete[symbols, index];

removeSymbolPairAt::usage =
  "removeSymbolPairAt[symbols, i, j] removes two symbols at positions i<j from a list in one deterministic step.";
removeSymbolPairAt[symbols_List, i_Integer, j_Integer] := Delete[symbols, {{j}, {i}}];

assignmentsForUnits::usage =
  "assignmentsForUnits[units, symbols, incomingPos] enumerates deterministic chirality assignments with pair-leg symmetry reduced.";
assignmentsForUnits[units_List, symbols_List, incomingPos_Association] := Module[
  {orderedSymbols, recurse},
  orderedSymbols = SortBy[symbols, Lookup[incomingPos, #, Infinity] &];
  recurse[idx_, rem_, acc_] := Module[
    {unit, ids, out = {}, i, j, s1, s2},
    If[idx > Length[units], Return[{acc}]];
    unit = units[[idx]];
    ids = unit["ids"];
    If[unit["kind"] === "single",
      For[i = 1, i <= Length[rem], i++,
        out = Join[
          out,
          recurse[
            idx + 1,
            removeSymbolAt[rem, i],
            Join[acc, {ids[[1]] -> rem[[i]]}]
          ]
        ];
      ],
      For[i = 1, i <= Length[rem] - 1, i++,
        For[j = i + 1, j <= Length[rem], j++,
          s1 = rem[[i]];
          s2 = rem[[j]];
          out = Join[
            out,
            recurse[
              idx + 1,
              removeSymbolPairAt[rem, i, j],
              Join[
                acc,
                If[
                  Lookup[incomingPos, s1, Infinity] <= Lookup[incomingPos, s2, Infinity],
                  {ids[[1]] -> s1, ids[[2]] -> s2},
                  {ids[[1]] -> s2, ids[[2]] -> s1}
                ]
              ]
            ]
          ];
        ];
      ];
    ];
    out
  ];
  If[Length[units] == 0,
    {{}},
    recurse[1, orderedSymbols, {}]
  ]
];

assignmentsForChirality::usage =
  "assignmentsForChirality[openPositions, symbols, incomingPos] enumerates deterministic assignments from symbols to open legs.";
assignmentsForChirality[openPositions_List, symbols_List, incomingPos_Association] := Module[{units},
  units = chiralityAssignmentUnits[openPositions];
  assignmentsForUnits[units, symbols, incomingPos]
];

spinorPlacementSortKey::usage = "spinorPlacementSortKey[placement, incomingPos] returns ordering key by incoming spinor list positions.";
spinorPlacementSortKey[placement_List, incomingPos_Association] := Replace[
  Flatten[placement],
  s_Symbol :> Lookup[incomingPos, s, 0],
  {1}
];

canonicalizeSpinPlacementForSlots::usage =
  "canonicalizeSpinPlacementForSlots[slots, placement] sorts same-chirality slot spinor pairs deterministically.";
canonicalizeSpinPlacementForSlots[slots_List, placement_List] := Module[{out = placement, i, pair},
  For[i = 1, i <= Length[slots], i++,
    If[sameChiralitySlotQ[slots[[i]]] && !preserveOutgoingSpinOrderQ[slots[[i]]],
      pair = SortBy[out[[i]], symbolSortKey];
      out[[i]] = pair;
    ];
  ];
  out
];

spinorPlacements::usage =
  "spinorPlacements[slots, inSpinors, outSpinor] enumerates concrete spinor assignments per slot.";
spinorPlacements[slots_List, inSpinors_List, outSpinor_] := Module[
  {
    k = Length[slots], basePlacement, openPos = {}, slot, form, chirPair, leg,
    outgoingPos, outgoingLeg, incomingChiral, incomingAnti, openChiralPos, openAntiPos,
    assignChiral, assignAnti, combinedAssign, placement, incomingPos, out = {}
  },
  basePlacement = ConstantArray[{None, None}, k];
  Do[
    chirPair = slotEndpointChiralities[slots[[slot]]];
    Do[
      AppendTo[openPos, <|"id" -> 2 (slot - 1) + leg, "slot" -> slot, "leg" -> leg, "chirality" -> chirPair[[leg]]|>],
      {leg, 2}
    ],
    {slot, k}
  ];

  If[outSpinor =!= None,
    outgoingPos = FirstPosition[slots, {_, _, True, _}, Missing["NotFound"]];
    If[outgoingPos === Missing["NotFound"], Return[{}]];
    chirPair = slotEndpointChiralities[slots[[outgoingPos[[1]]]]];
    outgoingLeg = FirstPosition[chirPair, outSpinor[[2]], Missing["NotFound"]];
    If[outgoingLeg === Missing["NotFound"], Return[{}]];
    basePlacement[[outgoingPos[[1]], outgoingLeg[[1]]]] = outSpinor[[1]];
    openPos = Select[openPos, !(
      #["slot"] == outgoingPos[[1]] &&
      #["leg"] == outgoingLeg[[1]]
    ) &];
  ];

  incomingChiral = Cases[inSpinors, {s_, "chiral"} :> s];
  incomingAnti = Cases[inSpinors, {s_, "antichiral"} :> s];
  incomingPos = AssociationThread[inSpinors[[All, 1]] -> Range[Length[inSpinors]]];
  openChiralPos = Cases[openPos, p_ /; p["chirality"] == "chiral"];
  openAntiPos = Cases[openPos, p_ /; p["chirality"] == "antichiral"];
  If[Length[incomingChiral] =!= Length[openChiralPos] || Length[incomingAnti] =!= Length[openAntiPos], Return[{}]];

  assignChiral = assignmentsForChirality[openChiralPos, incomingChiral, incomingPos];
  assignAnti = assignmentsForChirality[openAntiPos, incomingAnti, incomingPos];

  Do[
    placement = basePlacement;
    Scan[
      (
        placement[[Quotient[First[#] - 1, 2] + 1, Mod[First[#] - 1, 2] + 1]] = Last[#]
      ) &,
      Join[combinedAssign[[1]], combinedAssign[[2]]]
    ];
    placement = canonicalizeSpinPlacementForSlots[slots, placement];
    AppendTo[out, placement],
    {combinedAssign, Tuples[{assignChiral, assignAnti}]}
  ];

  SortBy[out, spinorPlacementSortKey[#, incomingPos] &]
];

firstSpinorPlacement::usage =
  "firstSpinorPlacement[slots, inSpinors, outSpinor] builds one deterministic valid spinor assignment.";
firstSpinorPlacement[slots_List, inSpinors_List, outSpinor_] := Module[
  {
    k = Length[slots], placement, openPos = {}, slot, chirPair, leg,
    outgoingPos, outgoingLeg, incomingChiral, incomingAnti, openChiral, openAnti, i
  },
  placement = ConstantArray[{None, None}, k];
  Do[
    chirPair = slotEndpointChiralities[slots[[slot]]];
    Do[
      AppendTo[openPos, <|"id" -> 2 (slot - 1) + leg, "slot" -> slot, "leg" -> leg, "chirality" -> chirPair[[leg]]|>],
      {leg, 2}
    ],
    {slot, k}
  ];

  If[outSpinor =!= None,
    outgoingPos = FirstPosition[slots, {_, _, True, _}, Missing["NotFound"]];
    If[outgoingPos === Missing["NotFound"], Return[$Failed]];
    chirPair = slotEndpointChiralities[slots[[outgoingPos[[1]]]]];
    outgoingLeg = FirstPosition[chirPair, outSpinor[[2]], Missing["NotFound"]];
    If[outgoingLeg === Missing["NotFound"], Return[$Failed]];
    placement[[outgoingPos[[1]], outgoingLeg[[1]]]] = outSpinor[[1]];
    openPos = Select[openPos, !(
      #["slot"] == outgoingPos[[1]] &&
      #["leg"] == outgoingLeg[[1]]
    ) &];
  ];

  incomingChiral = Cases[inSpinors, {s_, "chiral"} :> s];
  incomingAnti = Cases[inSpinors, {s_, "antichiral"} :> s];
  openChiral = SortBy[Cases[openPos, p_ /; p["chirality"] == "chiral" :> p["id"]], Identity];
  openAnti = SortBy[Cases[openPos, p_ /; p["chirality"] == "antichiral" :> p["id"]], Identity];
  If[Length[incomingChiral] =!= Length[openChiral] || Length[incomingAnti] =!= Length[openAnti], Return[$Failed]];

  For[i = 1, i <= Length[openChiral], i++,
    placement[[Quotient[openChiral[[i]] - 1, 2] + 1, Mod[openChiral[[i]] - 1, 2] + 1]] = incomingChiral[[i]];
  ];
  For[i = 1, i <= Length[openAnti], i++,
    placement[[Quotient[openAnti[[i]] - 1, 2] + 1, Mod[openAnti[[i]] - 1, 2] + 1]] = incomingAnti[[i]];
  ];
  canonicalizeSpinPlacementForSlots[slots, placement]
];

canonicalizeVectorPair::usage =
  "canonicalizeVectorPair[pair] sorts one vector-index pair deterministically for \\[Delta]-factor emission.";
canonicalizeVectorPair[pair_List] := SortBy[pair, symbolSortKey];

vectorPairings::usage = "vectorPairings[vectorIndices] enumerates deterministic perfect matchings of vectorIndices.";
vectorPairings[{}] := {{}};
vectorPairings[vectorIndices_List] := Module[{first, rest},
  If[OddQ[Length[vectorIndices]], Return[{}]];
  first = First[vectorIndices];
  rest = Rest[vectorIndices];
  Flatten[
    Table[
      Prepend[
        #,
        canonicalizeVectorPair[{first, rest[[i]]}]
      ] & /@ vectorPairings[Delete[rest, i]],
      {i, 1, Length[rest]}
    ],
    1
  ]
];

antisymmetricVectorGroupLookup::usage =
  "antisymmetricVectorGroupLookup[groups] maps each antisymmetrized vector label to its group number.";
antisymmetricVectorGroupLookup[groups_List] := Association @ Flatten[
  MapIndexed[Thread[#1 -> First[#2]] &, groups],
  1
];

validAntisymmetricDeltaPairingQ::usage =
  "validAntisymmetricDeltaPairingQ[pairs, groupLookup] is False when a delta pairing contracts two labels from the same antisymmetric block.";
validAntisymmetricDeltaPairingQ[pairs_List, groupLookup_Association] := AllTrue[
  pairs,
  Module[{left = Lookup[groupLookup, #[[1]], None], right = Lookup[groupLookup, #[[2]], None]},
    left === None || right === None || left =!= right
  ] &
];

vectorPlacements::usage =
  "vectorPlacements[externalCounts, vectorIndices] distributes named external vectors among slots and leftover \\[Delta] pairings.";
vectorPlacements[externalCounts_List, vectorIndices_List, antisymmetricVectorGroups_List : {}] := Module[
  {k = Length[externalCounts], n = Length[vectorIndices], leftoverCount, recurse, groupLookup, pairings},
  leftoverCount = n - Total[externalCounts];
  If[leftoverCount < 0 || OddQ[leftoverCount], Return[{}]];
  groupLookup = antisymmetricVectorGroupLookup[antisymmetricVectorGroups];
  recurse[pos_, rem_, remLeftover_, slotAcc_, leftoverAcc_] := Module[{slot, out = {}},
    If[pos > n,
      pairings = Select[vectorPairings[leftoverAcc], validAntisymmetricDeltaPairingQ[#, groupLookup] &];
      Return[
        If[
          remLeftover == 0 && And @@ Thread[rem == 0],
          (<|"SlotVectors" -> slotAcc, "DeltaPairs" -> #|> &) /@ pairings,
          {}
        ]
      ]
    ];
    If[remLeftover > 0,
      out = Join[out, recurse[pos + 1, rem, remLeftover - 1, slotAcc, Append[leftoverAcc, vectorIndices[[pos]]]]]
    ];
    For[slot = 1, slot <= k, slot++,
      If[rem[[slot]] > 0,
        out = Join[
          out,
          recurse[
            pos + 1,
            ReplacePart[rem, slot -> rem[[slot]] - 1],
            remLeftover,
            ReplacePart[slotAcc, slot -> Append[slotAcc[[slot]], vectorIndices[[pos]]]],
            leftoverAcc
          ]
        ];
      ];
    ];
    out
  ];
  recurse[1, externalCounts, leftoverCount, ConstantArray[{}, k], {}]
];

firstVectorPlacement::usage =
  "firstVectorPlacement[externalCounts, vectorIndices] builds one deterministic slot-plus-\\[Delta] vector assignment.";
firstVectorPlacement[externalCounts_List, vectorIndices_List, antisymmetricVectorGroups_List : {}] := Module[
  {
    k = Length[externalCounts], n = Length[vectorIndices], leftoverCount, slotVectors, cursor = 1, i,
    takeCount, leftovers, pairings, groupLookup
  },
  leftoverCount = n - Total[externalCounts];
  If[leftoverCount < 0 || OddQ[leftoverCount], Return[$Failed]];
  groupLookup = antisymmetricVectorGroupLookup[antisymmetricVectorGroups];
  slotVectors = ConstantArray[{}, k];
  For[i = 1, i <= k, i++,
    takeCount = externalCounts[[i]];
    If[takeCount > 0,
      slotVectors[[i]] = Take[vectorIndices, {cursor, cursor + takeCount - 1}];
      cursor += takeCount;
    ];
  ];
  leftovers = If[cursor > n, {}, Take[vectorIndices, {cursor, n}]];
  pairings = Select[vectorPairings[leftovers], validAntisymmetricDeltaPairingQ[#, groupLookup] &];
  If[pairings === {}, Return[$Failed]];
  <|"SlotVectors" -> slotVectors, "DeltaPairs" -> First[pairings]|>
];

dummyIndexBaseSymbol::usage =
  "dummyIndexBaseSymbol is the base \\[Nu] symbol, held in package context, from which buildDummyIndexSymbols generates fresh contraction dummies.";
dummyIndexBaseSymbol = Symbol["StringCode`OPE`TypeII`FlatSpace`TensorStructures`" <> "\[Nu]"];

buildDummyIndexSymbols::usage =
  "buildDummyIndexSymbols[count] returns count freshly generated dummy symbols \\[Nu]$nnn in package context. Deliberately NOT memoized: each call must yield symbols distinct from every previous call, otherwise two independently built tensor structures both receive \\[Nu]1 and their contractions collide when the structures are multiplied, producing an index repeated four times that canonicalizeOneTermDummies (which only relabels symbols occurring exactly twice) silently leaves alone.";
buildDummyIndexSymbols[count_Integer] := Table[Unique[dummyIndexBaseSymbol], {count}];

deltaFactorFromPair::usage = "deltaFactorFromPair[pair] emits one canonical inert \\[Delta] factor.";
deltaFactorFromPair[pair_List] := Module[{ordered},
  ordered = canonicalizeVectorPair[pair];
  \[Delta][ordered[[1]], ordered[[2]]]
];

gammaProductCTag::usage =
  "gammaProductCTag[hasOutgoing, pairForm] returns CUDHold/CDUHold for incoming same-chirality slots and None otherwise.";
gammaProductCTag[hasOutgoing_, pairForm_] := Which[
  TrueQ[hasOutgoing], None,
  pairForm === GammaFormUU, CUDHold,
  pairForm === GammaFormDD, CDUHold,
  True, None
];

gammaProductCTagForRank::usage =
  "gammaProductCTagForRank[hasOutgoing, pairForm, rank] returns the C tag for one emitted slot, refining gammaProductCTag with the chain rank. Incoming mixed-chirality (GammaFormUD) slots carry only even ranks, and an untagged even-rank chain has label {X, X} -- two endpoints of the SAME chirality -- which contradicts slotSpinorChiralities[GammaFormUD] = {chiral, antichiral}. Inserting CUDHold supplies the missing flip, so rank 2 emits {CUDHold, GammaDUHold, GammaUDHold} (gammaChainStartIndex already flips the chain start when a C tag is present). Rank 0 is deliberately left untagged: the empty link list is already special-cased to CUD by both gammaProductSpinorChiralities and spinProjectionGammaFactorMatrixRaw, so {} and {CUDHold} denote the same matrix and keeping {} preserves the emitted form of every existing rank-0 structure.";
gammaProductCTagForRank[hasOutgoing_, pairForm_, rank_Integer] := Which[
  TrueQ[hasOutgoing], None,
  pairForm === GammaFormUD && rank > 0, CUDHold,
  True, gammaProductCTag[hasOutgoing, pairForm]
];

gammaChainStartIndex::usage =
  "gammaChainStartIndex[emitBaseForm, cTag] returns the chain start index after optional C insertion.";
gammaChainStartIndex[emitBaseForm_, pairForm_, hasOutgoing_, None] := emittedChainStartIndex[emitBaseForm, pairForm, hasOutgoing];
gammaChainStartIndex[emitBaseForm_, pairForm_, hasOutgoing_, cTag_] /; MemberQ[{CUDHold, CDUHold}, cTag] :=
  flipChainIndex[emittedChainStartIndex[emitBaseForm, pairForm, hasOutgoing]];
gammaChainStartIndex[emitBaseForm_, pairForm_, hasOutgoing_, _] := emittedChainStartIndex[emitBaseForm, pairForm, hasOutgoing];

gammaAntisymmetricProductFromParts::usage =
  "gammaAntisymmetricProductFromParts[cTag, links, spinor1, spinor2] emits GammaAntisymmetricProductHold[linksWithOptionalCTag, spinor1, spinor2].";
gammaAntisymmetricProductFromParts[None, links_List, spinor1_, spinor2_] := GammaAntisymmetricProductHold[links, spinor1, spinor2];
gammaAntisymmetricProductFromParts[cTag_, links_List, spinor1_, spinor2_] /; MemberQ[{CUDHold, CDUHold}, cTag] :=
  GammaAntisymmetricProductHold[Prepend[links, cTag], spinor1, spinor2];
gammaAntisymmetricProductFromParts[_, links_List, spinor1_, spinor2_] := GammaAntisymmetricProductHold[links, spinor1, spinor2];

buildGammaAntisymmetricProduct::usage =
  "buildGammaAntisymmetricProduct[emitBaseForm, pairForm, hasOutgoing, vectorIndices, spinor1, spinor2, includeGamma11] builds one GammaAntisymmetricProductHold chain factor.";
buildGammaAntisymmetricProduct[
  emitBaseForm_, pairForm_, hasOutgoing_, vectorIndices_List, spinor1_, spinor2_, includeGamma11_ : False
] := Module[
  {cTag, startIndex, links, lastIndexType, tailHead},
  cTag = gammaProductCTagForRank[hasOutgoing, pairForm, Length[vectorIndices]];
  startIndex = gammaChainStartIndex[emitBaseForm, pairForm, hasOutgoing, cTag];
  {links, lastIndexType} = buildGammaLinks[startIndex, vectorIndices];
  If[TrueQ[includeGamma11],
    tailHead = gamma11TailHeadForIndex[lastIndexType];
    links = Append[links, tailHead[]];
  ];
  gammaAntisymmetricProductFromParts[cTag, links, spinor1, spinor2]
];

symbolSortKey::usage = "symbolSortKey[sym] gives a deterministic ordering key for symbolic indices.";
symbolSortKey[sym_Symbol] := SymbolName[Unevaluated[sym]];

canonicalizeSameChiralityFactor::usage =
  "canonicalizeSameChiralityFactor[factor] canonicalizes same-chirality factor orientation when applicable.";
canonicalizeSameChiralityFactor[factor_] := factor;

canonicalizeStructureExpression::usage =
  "canonicalizeStructureExpression[expr] canonicalizes factor-level spinor ordering for same-chirality heads.";
canonicalizeStructureExpression[expr_] := canonicalizeSameChiralityFactor[expr];

deduplicateGroupStructures::usage =
  "deduplicateGroupStructures[group] canonicalizes and removes duplicates while preserving deterministic order.";
deduplicateGroupStructures[group_List] := DeleteDuplicatesBy[
  group,
  canonicalizeStructureExpression @ If[AssociationQ[#] && KeyExistsQ[#, "Expression"], #["Expression"], #] &
];

buildConcreteStructure::usage =
  "buildConcreteStructure[slots, cMatrix, spinPlacement, extPlacement] builds one Times-product structure with gamma and optional \\[Delta] factors.";
buildConcreteStructure[slots_List, cMatrix_List, spinPlacement_List, extPlacement_Association] := Module[
  {
    k = Length[slots], slotVectorsOrig, deltaPairs, dummyTotal, dummies, cursor = 1,
    i, j, count, pairDummies,
    gammaFactors, deltaFactors, baseHead, pRank, hasOutgoing, pairForm, gammaVecs
  },
  slotVectorsOrig = Lookup[extPlacement, "SlotVectors", {}];
  deltaPairs = Lookup[extPlacement, "DeltaPairs", {}];
  dummyTotal = Total[upperTriangleValues[cMatrix]];
  dummies = buildDummyIndexSymbols[dummyTotal];
  For[i = 1, i <= k - 1, i++,
    For[j = i + 1, j <= k, j++,
      count = cMatrix[[i, j]];
      If[count > 0,
        pairDummies = Take[dummies, {cursor, cursor + count - 1}];
        cursor += count;
        slotVectorsOrig[[i]] = Join[slotVectorsOrig[[i]], pairDummies];
        slotVectorsOrig[[j]] = Join[slotVectorsOrig[[j]], pairDummies];
      ];
    ];
  ];
  gammaFactors = Table[
    {baseHead, pRank, hasOutgoing, pairForm} = slots[[i]];
    gammaVecs = slotVectorsOrig[[i]];
    buildGammaAntisymmetricProduct[
      baseHead,
      pairForm,
      hasOutgoing,
      gammaVecs,
      spinPlacement[[i, 1]],
      spinPlacement[[i, 2]]
    ],
    {i, 1, k}
  ];
  deltaFactors = deltaFactorFromPair /@ deltaPairs;
  If[Join[gammaFactors, deltaFactors] === {}, 1, Times @@ Join[gammaFactors, deltaFactors]]
];

buildGammaFactorData0::usage =
  "buildGammaFactorData0[emitBaseForm, pairForm, hasOutgoing, vectorIndices, spinor1, spinor2, includeGamma11] builds one generated gamma factor together with parsed selector parts.";
buildGammaFactorData0[
  emitBaseForm_, pairForm_, hasOutgoing_, vectorIndices_List, spinor1_, spinor2_, includeGamma11_ : False
] := Module[{cTag, startIndex, links, lastIndexType, tailHead, allLinks, vectorLinks},
  cTag = gammaProductCTagForRank[hasOutgoing, pairForm, Length[vectorIndices]];
  startIndex = gammaChainStartIndex[emitBaseForm, pairForm, hasOutgoing, cTag];
  {links, lastIndexType} = buildGammaLinks[startIndex, vectorIndices];
  If[TrueQ[includeGamma11],
    tailHead = gamma11TailHeadForIndex[lastIndexType];
    links = Append[links, tailHead[]];
  ];
  allLinks = Join[If[cTag === None, {}, {cTag}], links];
  vectorLinks = Select[links, gammaVectorLinkQ];
  <|
    "Expression" -> gammaAntisymmetricProductFromParts[cTag, links, spinor1, spinor2],
    "Parts" -> <|
      "Kind" -> "Gamma",
      "CTag" -> cTag,
      "VectorLinks" -> vectorLinks,
      "VectorSymbols" -> (gammaLinkIndexSelector /@ vectorLinks),
      "TailLinks" -> Select[links, !gammaVectorLinkQ[#] &],
      "Spinors" -> {spinor1, spinor2},
      "SpinorChiralities" -> gammaProductSpinorChiralities[allLinks]
    |>
  |>
];

buildDeltaFactorData0::usage =
  "buildDeltaFactorData0[pair] builds one generated delta factor together with parsed selector parts.";
buildDeltaFactorData0[pair_List] := Module[{ordered},
  ordered = canonicalizeVectorPair[pair];
  <|
    "Expression" -> \[Delta][ordered[[1]], ordered[[2]]],
    "Parts" -> <|
      "Kind" -> "Delta",
      "VectorSymbols" -> ordered,
      "Spinors" -> {},
      "SpinorChiralities" -> {}
    |>
  |>
];

buildConcreteStructureData0::usage =
  "buildConcreteStructureData0[slots, cMatrix, spinPlacement, extPlacement] builds one concrete generated structure together with parsed selector factor data.";
buildConcreteStructureData0[slots_List, cMatrix_List, spinPlacement_List, extPlacement_Association] := Module[
  {
    k = Length[slots], slotVectorsOrig, deltaPairs, dummyTotal, dummies, cursor = 1,
    i, j, count, pairDummies, gammaFactorData, deltaFactorData, factors, factorParts
  },
  slotVectorsOrig = Lookup[extPlacement, "SlotVectors", {}];
  deltaPairs = Lookup[extPlacement, "DeltaPairs", {}];
  dummyTotal = Total[upperTriangleValues[cMatrix]];
  dummies = buildDummyIndexSymbols[dummyTotal];
  For[i = 1, i <= k - 1, i++,
    For[j = i + 1, j <= k, j++,
      count = cMatrix[[i, j]];
      If[count > 0,
        pairDummies = Take[dummies, {cursor, cursor + count - 1}];
        cursor += count;
        slotVectorsOrig[[i]] = Join[slotVectorsOrig[[i]], pairDummies];
        slotVectorsOrig[[j]] = Join[slotVectorsOrig[[j]], pairDummies];
      ];
    ];
  ];
  gammaFactorData = Table[
    buildGammaFactorData0[
      slots[[i, 1]],
      slots[[i, 4]],
      slots[[i, 3]],
      slotVectorsOrig[[i]],
      spinPlacement[[i, 1]],
      spinPlacement[[i, 2]]
    ],
    {i, 1, k}
  ];
  deltaFactorData = buildDeltaFactorData0 /@ deltaPairs;
  factors = Join[gammaFactorData[[All, "Expression"]], deltaFactorData[[All, "Expression"]]];
  factorParts = Join[gammaFactorData[[All, "Parts"]], deltaFactorData[[All, "Parts"]]];
  <|
    "Expression" -> If[factors === {}, 1, Times @@ factors],
    "Factors" -> factors,
    "FactorParts" -> factorParts
  |>
];

buildGeneratedSelectorCandidate0::usage =
  "buildGeneratedSelectorCandidate0[data] builds one selector-ready parsed candidate record directly from generation-time factor data.";
buildGeneratedSelectorCandidate0[data_Association] := Module[{parsed, familyData, spinSymbols},
  parsed = <|
    "Expression" -> data["Expression"],
    "Key" -> candidateCacheKey[data["Expression"]],
    "Factors" -> data["Factors"],
    "FactorParts" -> data["FactorParts"],
    "SpinorChiralities" -> candidateSpinorChiralities[data["FactorParts"]],
    "ExternalVectors" -> candidateExternalVectors[data["FactorParts"]]
  |>;
  familyData = selectorCanonicalFamilyData[parsed];
  If[familyData === $Failed, Return[$Failed]];
  spinSymbols = SortBy[Keys[parsed["SpinorChiralities"]], SymbolName];
  <|
    "Expression" -> data["Expression"],
    "Key" -> parsed["Key"],
    "ScalarFactor" -> 1,
    "Parsed" -> parsed,
    "SpinSymbols" -> spinSymbols,
    "SpinChiralities" -> Lookup[parsed["SpinorChiralities"], spinSymbols],
    "VectorSymbols" -> SortBy[parsed["ExternalVectors"], SymbolName],
    "FamilyData" -> familyData
  |>
];

buildGeneratedCandidate0::usage =
  "buildGeneratedCandidate0[slots, cMatrix, spinPlacement, extPlacement, returnSelectorCandidates] emits either a plain tensor-structure expression or a selector-ready parsed candidate record.";
buildGeneratedCandidate0[
  slots_List, cMatrix_List, spinPlacement_List, extPlacement_Association, returnSelectorCandidates_
] := Module[{data},
  If[!TrueQ[returnSelectorCandidates], Return[buildConcreteStructure[slots, cMatrix, spinPlacement, extPlacement]]];
  data = buildConcreteStructureData0[slots, cMatrix, spinPlacement, extPlacement];
  buildGeneratedSelectorCandidate0[data]
];

spinorPlacementCacheKey::usage =
  "spinorPlacementCacheKey[slots, outSpinor] builds a cache key for spinor placement enumeration from slot chirality layout.";
spinorPlacementCacheKey[slots_List, outSpinor_] := Module[{forms, outgoing},
  forms = slots[[All, 4]];
  outgoing = slots[[All, 3]];
  {forms, outgoing, If[outSpinor === None, None, outSpinor[[2]]]}
];

vectorPlacementCacheKey::usage =
  "vectorPlacementCacheKey[externalCounts] builds a cache key for vector placement enumeration.";
vectorPlacementCacheKey[externalCounts_List, antisymmetricVectorGroups_List : {}] := {
  externalCounts,
  antisymmetricVectorGroups
};

abstractAutomorphisms::usage =
  "abstractAutomorphisms[slots, extCounts, cMatrix] lists slot permutations that preserve the abstract structure exactly.";
abstractAutomorphisms[slots_List, extCounts_List, cMatrix_List] := Module[
  {k = Length[slots], blocks, permBlocks, choices, choice, perm, candidates = {}, b},
  blocks = Values @ GroupBy[Range[k], {slots[[#]], extCounts[[#]]} &];
  permBlocks = Permutations /@ blocks;
  choices = If[permBlocks === {}, {{}}, Tuples[permBlocks]];
  Do[
    perm = Range[k];
    choice = choices[[b]];
    Do[
      perm[[blocks[[j]]]] = choice[[j]],
      {j, Length[blocks]}
    ];
    If[
      slots[[perm]] === slots &&
      extCounts[[perm]] === extCounts &&
      cMatrix[[perm, perm]] === cMatrix,
      AppendTo[candidates, perm]
    ],
    {b, Length[choices]}
  ];
  SortBy[DeleteDuplicates[candidates], Identity]
];

slotSpinPairForKey::usage =
  "slotSpinPairForKey[slot, spinPair] returns canonical pair order in same-chirality slots and original order otherwise.";
slotSpinPairForKey[slot_List, spinPair_List, spinRank_Association] := Module[{r1, r2},
  r1 = Lookup[spinRank, spinPair[[1]], Infinity];
  r2 = Lookup[spinRank, spinPair[[2]], Infinity];
  If[
    MemberQ[{GammaFormUU, GammaFormDD}, slot[[4]]] && !preserveOutgoingSpinOrderQ[slot],
    If[r1 <= r2, {r1, r2}, {r2, r1}],
    {r1, r2}
  ]
];

slotPlacementKey::usage =
  "slotPlacementKey[slot, spinPair, vecs] builds a deterministic comparable key for one slot placement.";
slotPlacementKey[slot_List, spinPair_List, vecs_List, spinRank_Association, vecRank_Association] := {
  slotSpinPairForKey[slot, spinPair, spinRank],
  Lookup[vecRank, #, Infinity] & /@ vecs
};

listPermutationSignature::usage =
  "listPermutationSignature[source, target] returns the permutation signature carrying source to target.";
listPermutationSignature[source_List, target_List] := Signature[Flatten[Position[source, #] & /@ target]];

antisymmetricRelabelings::usage =
  "antisymmetricRelabelings[groups] enumerates all antisymmetric-block relabelings together with their fermionic signs.";
antisymmetricRelabelings[groups_List] := antisymmetricRelabelings[groups] = Module[{groupChoices, choices},
  If[groups === {}, Return[{<|"Rules" -> {}, "Sign" -> 1|>}]];
  groupChoices = Map[
    Function[group,
      Map[
        <|"Rules" -> Thread[group -> #], "Sign" -> listPermutationSignature[group, #]|> &,
        Permutations[group]
      ]
    ],
    groups
  ];
  choices = Tuples[groupChoices];
  Map[
    <|
      "Rules" -> Flatten[#[[All, "Rules"]], 1],
      "Sign" -> Times @@ #[[All, "Sign"]]
    |>&,
    choices
  ]
];

placementOrbitKey::usage =
  "placementOrbitKey[slots, spinPlacement, vecPlacement, automorphisms] canonicalizes a placement under slot automorphisms.";
placementOrbitKey[
  slots_List, spinPlacement_List, vecPlacement_Association, automorphisms_List,
  spinRank_Association, vecRank_Association, antisymmetricVectorGroups_List : {}
] := Module[
  {signsByKey = <||>, relabelings, relabeling, slotKeys, deltaKey, keyData, key},
  relabelings = antisymmetricRelabelings[antisymmetricVectorGroups];
  Do[
    relabeling = relabelings[[i]];
    slotKeys = Table[
      slotPlacementKey[
        slots[[j]],
        spinPlacement[[j]],
        Replace[vecPlacement["SlotVectors"][[j]], relabeling["Rules"], {1}],
        spinRank,
        vecRank
      ],
      {j, Length[slots]}
    ];
    deltaKey = deltaPairingKey[Replace[vecPlacement["DeltaPairs"], relabeling["Rules"], {2}]];
    Do[
      keyData = {slotKeys[[automorphisms[[j]]]], deltaKey};
      key = ToString[InputForm[keyData]];
      AssociateTo[
        signsByKey,
        key -> Union[Append[Lookup[signsByKey, key, {}], relabeling["Sign"]]]
      ],
      {j, Length[automorphisms]}
    ],
    {i, Length[relabelings]}
  ];
  key = First @ Sort[Keys[signsByKey]];
  If[Length[Lookup[signsByKey, key, {}]] > 1, 0, key]
];

deltaPairingKey::usage = "deltaPairingKey[pairs] returns a deterministic key for one list of \\[Delta] pairings.";
deltaPairingKey[pairs_List] := SortBy[
  ({symbolSortKey[#[[1]]], symbolSortKey[#[[2]]]} &) /@ (canonicalizeVectorPair /@ pairs),
  Identity
];

uniquePlacementPairs::usage =
  "uniquePlacementPairs[slots, spins, vecs, automorphisms] keeps one representative spin/vector-placement pair per automorphism orbit.";
uniquePlacementPairs[
  slots_List, spins_List, vecs_List, automorphisms_List,
  spinRank_Association, vecRank_Association, antisymmetricVectorGroups_List : {}
] := Module[
  {seen = <||>, harvested, i, j, key},
  harvested = Reap[
    For[i = 1, i <= Length[spins], i++,
      For[j = 1, j <= Length[vecs], j++,
        key = placementOrbitKey[
          slots,
          spins[[i]],
          vecs[[j]],
          automorphisms,
          spinRank,
          vecRank,
          antisymmetricVectorGroups
        ];
        If[key === 0, Continue[]];
        If[!KeyExistsQ[seen, key],
          AssociateTo[seen, key -> True];
          Sow[{spins[[i]], vecs[[j]], key}]
        ];
      ];
    ];
  ][[2]];
  If[harvested === {}, Return[{}]];
  harvested = First[harvested];
  harvested = SortBy[harvested, #[[3]] &];
  harvested[[All, {1, 2}]]
];

generateTensorStructures::usage = "generateTensorStructures[incoming, outgoing, opts] enumerates grouped gamma and vector-contraction tensor structures.";
generateTensorStructures[incoming_, outgoing_, opts___Rule] := Module[
  {
    maxK, inNorm, outNorm, inVec, outVec, inSpin, outSpin, allIndexSymbols,
    totalSpinors, k, outSpinor, extVectors, abstractStructures, groups = {},
    abstract, slots, extCounts, cMatrix, spins, vecs, representativesOnly, returnSelectorCandidates,
    oneSpin, oneVec, builtGroup, spinPlacementCache = <||>, vectorPlacementCache = <||>,
    spinKey, vecKey, firstSpinCache = <||>, firstVecCache = <||>,
    autoCache = <||>, autoKey, automorphisms, pairs, spinRank, vecRank,
    antisymmetricVectorGroups
  },
  If[!(AssociationQ[incoming] && AssociationQ[outgoing]),
    Message[generateTensorStructures::badarg];
    Return[{}];
  ];

  maxK = parseMaxKOption[{opts}];
  representativesOnly = parseRepresentativesOnlyOption[{opts}];
  returnSelectorCandidates = parseReturnSelectorCandidatesOption[{opts}];
  inNorm = normalizeIndexAssociation[incoming];
  outNorm = normalizeIndexAssociation[outgoing];

  inVec = inNorm["vector"];
  outVec = outNorm["vector"];
  inSpin = inNorm["spinor"];
  outSpin = outNorm["spinor"];

  If[!(validVectorIndexListQ[inVec] && validVectorIndexListQ[outVec]),
    Message[generateTensorStructures::badvec];
    Return[{}];
  ];
  If[!(validSpinorIndexListQ[inSpin] && validSpinorIndexListQ[outSpin]),
    Message[generateTensorStructures::badchir];
    Return[{}];
  ];

  If[Length[outSpin] > 1,
    Message[generateTensorStructures::toomanyout];
    Return[{}];
  ];

  allIndexSymbols = Join[inVec, outVec, inSpin[[All, 1]], outSpin[[All, 1]]];
  If[!DuplicateFreeQ[allIndexSymbols],
    Message[generateTensorStructures::dupidx];
    Return[{}];
  ];

  totalSpinors = Length[inSpin] + Length[outSpin];
  If[OddQ[totalSpinors],
    Message[generateTensorStructures::oddspinor];
    Return[{}];
  ];

  k = totalSpinors/2;
  If[k > maxK,
    Message[generateTensorStructures::toomanyspinors, k, maxK];
    Return[{}];
  ];

  outSpinor = If[outSpin === {}, None, First[outSpin]];
  extVectors = Join[inVec, outVec];
  antisymmetricVectorGroups = parseAntisymmetricVectorGroupsOption[{opts}, extVectors];
  If[antisymmetricVectorGroups === $Failed, Return[{}]];
  spinRank = AssociationThread[inSpin[[All, 1]] -> Range[Length[inSpin]]];
  If[outSpinor =!= None, spinRank[outSpinor[[1]]] = 0];
  vecRank = AssociationThread[extVectors -> Range[Length[extVectors]]];

  abstractStructures = generateAbstractStructures[inSpin, outSpinor, Length[extVectors]];
  Do[
    slots = abstract["slots"];
    extCounts = abstract["externalCounts"];
    cMatrix = abstract["contractionMatrix"];
    If[representativesOnly,
      spinKey = spinorPlacementCacheKey[slots, outSpinor];
      If[!KeyExistsQ[firstSpinCache, spinKey],
        firstSpinCache[spinKey] = firstSpinorPlacement[slots, inSpin, outSpinor]
      ];
      oneSpin = firstSpinCache[spinKey];
      vecKey = vectorPlacementCacheKey[extCounts, antisymmetricVectorGroups];
      If[!KeyExistsQ[firstVecCache, vecKey],
        firstVecCache[vecKey] = firstVectorPlacement[extCounts, extVectors, antisymmetricVectorGroups]
      ];
      oneVec = firstVecCache[vecKey];
      builtGroup = If[
        oneSpin === $Failed || oneVec === $Failed,
        {},
        DeleteCases[{buildGeneratedCandidate0[slots, cMatrix, oneSpin, oneVec, returnSelectorCandidates]}, $Failed]
      ];
      AppendTo[groups, builtGroup],
      spinKey = spinorPlacementCacheKey[slots, outSpinor];
      If[!KeyExistsQ[spinPlacementCache, spinKey],
        spinPlacementCache[spinKey] = spinorPlacements[slots, inSpin, outSpinor]
      ];
      spins = spinPlacementCache[spinKey];
      vecKey = vectorPlacementCacheKey[extCounts, antisymmetricVectorGroups];
      If[!KeyExistsQ[vectorPlacementCache, vecKey],
        vectorPlacementCache[vecKey] = vectorPlacements[extCounts, extVectors, antisymmetricVectorGroups]
      ];
      vecs = vectorPlacementCache[vecKey];
      autoKey = {slots, extCounts, cMatrix};
      If[!KeyExistsQ[autoCache, autoKey],
        autoCache[autoKey] = abstractAutomorphisms[slots, extCounts, cMatrix]
      ];
      automorphisms = autoCache[autoKey];
      pairs = uniquePlacementPairs[
        slots,
        spins,
        vecs,
        automorphisms,
        spinRank,
        vecRank,
        antisymmetricVectorGroups
      ];
      AppendTo[
        groups,
        DeleteCases[
          Table[
            buildGeneratedCandidate0[slots, cMatrix, pairs[[i, 1]], pairs[[i, 2]], returnSelectorCandidates],
            {i, 1, Length[pairs]}
          ],
          $Failed
        ]
      ]
    ],
    {abstract, abstractStructures}
  ];

  deduplicateGroupStructures /@ groups
];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
