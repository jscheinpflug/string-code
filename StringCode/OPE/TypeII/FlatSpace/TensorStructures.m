(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`OPE`TypeII`FlatSpace`TensorStructures`"];
Needs["StringCode`Symbols`TypeII`FlatSpace`"];


(* ::Section:: *)
(*Declare public variables and methods*)


generateTensorStructures::usage =
  "generateTensorStructures[incoming, outgoing, opts] enumerates allowed Clifford tensor structures grouped by abstract shape.";

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

Options[generateTensorStructures] = {"MaxK" -> 5, "RepresentativesOnly" -> False};


(* ::Section:: *)
(*Logic*)


Begin["Private`"];

formOrder::usage = "formOrder[form] gives a stable total ordering key for supported gamma heads.";
formOrder[CGamma] := 1;
formOrder[CIGamma] := 2;
formOrder[GammaM] := 3;
formOrder[Gamma11CGamma] := 4;
formOrder[Gamma11CIGamma] := 5;
formOrder[Gamma11GammaM] := 6;
formOrder[Eps10] := 7;

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
  {k, configs = {}, a, c, b},
  If[nChiral < 0 || nAnti < 0 || OddQ[nChiral + nAnti], Return[{}]];
  k = (nChiral + nAnti)/2;
  For[a = 0, a <= Floor[nChiral/2], a++,
    c = nChiral - 2 a;
    b = (nAnti - c)/2;
    If[IntegerQ[b] && b >= 0 && a + b + c == k,
      AppendTo[configs, <|"a" -> a, "b" -> b, "c" -> c|>]
    ];
  ];
  configs
];

outgoingSlotOptions::usage = "outgoingSlotOptions[typeConfig, outChirality] returns allowed outgoing-slot forms.";
outgoingSlotOptions[typeConfig_Association, outChirality_String] := Module[
  {a = typeConfig["a"], b = typeConfig["b"], c = typeConfig["c"], forms = {}},
  Switch[outChirality,
    "chiral",
      If[a > 0, AppendTo[forms, CGamma]];
      If[c > 0, AppendTo[forms, GammaM]],
    "antichiral",
      If[b > 0, AppendTo[forms, CIGamma]];
      If[c > 0, AppendTo[forms, GammaM]]
  ];
  forms
];

outgoingEmittedForm::usage =
  "outgoingEmittedForm[pairForm, outChirality] maps outgoing-pair chirality class to emitted gamma head.";
outgoingEmittedForm[CGamma, "chiral"] := GammaM;
outgoingEmittedForm[CIGamma, "antichiral"] := GammaM;
outgoingEmittedForm[GammaM, "chiral"] := CIGamma;
outgoingEmittedForm[GammaM, "antichiral"] := CGamma;
outgoingEmittedForm[_, _] := $Failed;

buildSlotBlueprint::usage =
  "buildSlotBlueprint[typeConfig, outPairForm, outChirality] constructs slot descriptors with pair/emitted forms.";
buildSlotBlueprint[typeConfig_Association, outPairForm_, outChirality_] := Module[
  {counts, rest},
  counts = <|CGamma -> typeConfig["a"], CIGamma -> typeConfig["b"], GammaM -> typeConfig["c"]|>;
  If[outPairForm =!= None,
    counts[outPairForm] = counts[outPairForm] - 1;
    rest = Join[
      Table[<|"pairForm" -> CGamma, "emitBaseForm" -> CGamma, "hasOutgoing" -> False|>, {counts[CGamma]}],
      Table[<|"pairForm" -> CIGamma, "emitBaseForm" -> CIGamma, "hasOutgoing" -> False|>, {counts[CIGamma]}],
      Table[<|"pairForm" -> GammaM, "emitBaseForm" -> GammaM, "hasOutgoing" -> False|>, {counts[GammaM]}]
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
      Table[<|"pairForm" -> CGamma, "emitBaseForm" -> CGamma, "hasOutgoing" -> False|>, {counts[CGamma]}],
      Table[<|"pairForm" -> CIGamma, "emitBaseForm" -> CIGamma, "hasOutgoing" -> False|>, {counts[CIGamma]}],
      Table[<|"pairForm" -> GammaM, "emitBaseForm" -> GammaM, "hasOutgoing" -> False|>, {counts[GammaM]}]
    ]
  ]
];

baseParitySet::usage = "baseParitySet[emitBaseForm] returns allowed ranks before outgoing truncation.";
baseParitySet[emitBaseForm_] := If[
  MemberQ[{CGamma, CIGamma}, emitBaseForm],
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

validPTuples::usage = "validPTuples[pSets, nExtVec, slotBlueprint] returns admissible p-tuples after parity/size/symmetry filtering.";
validPTuples[pSets_List, nExtVec_Integer, slotBlueprint_List] := Select[
  Tuples[pSets],
  Total[#] >= nExtVec &&
    EvenQ[Total[#] - nExtVec] &&
    pTupleSymmetryCompatibleQ[slotBlueprint, #] &
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

gamma11LiftHead::usage = "gamma11LiftHead[form] returns the explicit Gamma11-lifted head for a base gamma form.";
gamma11LiftHead[CGamma] := Gamma11CGamma;
gamma11LiftHead[CIGamma] := Gamma11CIGamma;
gamma11LiftHead[GammaM] := Gamma11GammaM;
gamma11LiftHead[other_] := other;

slotWithRank::usage =
  "slotWithRank[slotBlueprint, p] creates slot data {baseHead,pOrig,pEff,hasOutgoing,pairForm,canDualize} for one rank choice.";
slotWithRank[slot_Association, p_Integer] := Module[{canDualize},
  canDualize = (!TrueQ[slot["hasOutgoing"]] && p > 5);
  {slot["emitBaseForm"], p, If[canDualize, 10 - p, p], slot["hasOutgoing"], slot["pairForm"], canDualize}
];

finalizeSlotDescriptors::usage =
  "finalizeSlotDescriptors[slotData, cMatrix] resolves which slots are dualized and returns concrete slot descriptors.";
finalizeSlotDescriptors[slotData_List, cMatrix_List] := Module[
  {k = Length[slotData]},
  Table[
    Module[{baseHead, pOrig, pDual, hasOutgoing, pairForm, canDualize, useDualize},
      {baseHead, pOrig, pDual, hasOutgoing, pairForm, canDualize} = slotData[[i]];
      useDualize = TrueQ[canDualize];
      {
        baseHead,
        pOrig,
        If[useDualize, pDual, pOrig],
        hasOutgoing,
        pairForm,
        useDualize
      }
    ],
    {i, 1, k}
  ]
];

canonicalizeAbstractStructure::usage =
  "canonicalizeAbstractStructure[slots, extCounts, cMatrix] canonicalizes under permutations within equal non-outgoing form classes.";
canonicalizeAbstractStructure[slots_List, extCounts_List, cMatrix_List] := Module[
  {
    k = Length[slots], outgoingPos, permutable, groups, permBlocks, blockChoices,
    basePerm, perm, candidates = {}, g, choice, slotRep, key, slotPerm, extPerm, cPerm
  },
  outgoingPos = FirstPosition[slots, {_, _, _, True, _, _}, Missing["NotFound"]];
  permutable = Complement[
    Range[k],
    If[outgoingPos === Missing["NotFound"], {}, {outgoingPos[[1]]}]
  ];
  groups = Values @ GroupBy[permutable, {slots[[#, 1]], slots[[#, 5]], Boole[slots[[#, 6]]]} &];
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
    slotRep = ({formOrder[#[[1]]], #[[2]], #[[3]], Boole[#[[4]]], formOrder[#[[5]]], Boole[#[[6]]]} &) /@ slotPerm;
    key = {slotRep, extPerm, upperTriangleValues[cPerm]};
    AppendTo[candidates, <|"slots" -> slotPerm, "externalCounts" -> extPerm, "contractionMatrix" -> cPerm, "key" -> key|>],
    {g, Length[blockChoices]}
  ];
  First @ SortBy[candidates, #["key"] &]
];

typeConfigFromSlots::usage =
  "typeConfigFromSlots[slots] returns count vector for {CGamma,CIGamma,GammaM}.";
typeConfigFromSlots[slots_List] := Module[{forms = slots[[All, 1]]},
  {
    Count[forms, CGamma],
    Count[forms, CIGamma],
    Count[forms, GammaM]
  }
];

abstractSortKey::usage = "abstractSortKey[abstract] returns deterministic ordering key for abstract structures.";
abstractSortKey[abstract_Association] := Module[
  {slots = abstract["slots"], ext = abstract["externalCounts"], c = abstract["contractionMatrix"]},
  {
    Sequence @@ typeConfigFromSlots[slots],
    formOrder /@ slots[[All, 1]],
    slots[[All, 2]],
    slots[[All, 3]],
    formOrder /@ slots[[All, 5]],
    Boole /@ slots[[All, 6]],
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
    slotsWithRankData, slotsWithP, pOrigTuple, extDistributions, extCounts, dummyCounts, cMats, cMat,
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
        extKey = pOrigTuple;
        If[!KeyExistsQ[extDistCache, extKey],
          extDistCache[extKey] = externalCountDistributions[pOrigTuple, nExtVec]
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
            slotsWithP = finalizeSlotDescriptors[slotsWithRankData, cMat];
            canonical = canonicalizeAbstractStructure[slotsWithP, extCounts, cMat];
            If[!KeyExistsQ[canonicalByKey, canonical["key"]],
              canonicalByKey[canonical["key"]] = canonical
            ],
            {cMat, cMats}
          ],
          {extCounts, extDistributions}
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
slotSpinorChiralities[CGamma] := {"chiral", "chiral"};
slotSpinorChiralities[CIGamma] := {"antichiral", "antichiral"};
slotSpinorChiralities[GammaM] := {"chiral", "antichiral"};

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
    If[MemberQ[{CGamma, CIGamma}, slots[[i, 1]]],
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
    form = slots[[slot, 5]];
    chirPair = slotSpinorChiralities[form];
    Do[
      AppendTo[openPos, <|"id" -> 2 (slot - 1) + leg, "slot" -> slot, "leg" -> leg, "chirality" -> chirPair[[leg]]|>],
      {leg, 2}
    ],
    {slot, k}
  ];

  If[outSpinor =!= None,
    outgoingPos = FirstPosition[slots, {_, _, _, True, _, _}, Missing["NotFound"]];
    If[outgoingPos === Missing["NotFound"], Return[{}]];
    chirPair = slotSpinorChiralities[slots[[outgoingPos[[1]], 5]]];
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
    k = Length[slots], placement, openPos = {}, slot, form, chirPair, leg,
    outgoingPos, outgoingLeg, incomingChiral, incomingAnti, openChiral, openAnti, i
  },
  placement = ConstantArray[{None, None}, k];
  Do[
    form = slots[[slot, 5]];
    chirPair = slotSpinorChiralities[form];
    Do[
      AppendTo[openPos, <|"id" -> 2 (slot - 1) + leg, "slot" -> slot, "leg" -> leg, "chirality" -> chirPair[[leg]]|>],
      {leg, 2}
    ],
    {slot, k}
  ];

  If[outSpinor =!= None,
    outgoingPos = FirstPosition[slots, {_, _, _, True, _, _}, Missing["NotFound"]];
    If[outgoingPos === Missing["NotFound"], Return[$Failed]];
    chirPair = slotSpinorChiralities[slots[[outgoingPos[[1]], 5]]];
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

vectorPlacements::usage =
  "vectorPlacements[externalCounts, vectorIndices] distributes named external vectors among slots in deterministic lexicographic order.";
vectorPlacements[externalCounts_List, vectorIndices_List] := Module[
  {k = Length[externalCounts], n = Length[vectorIndices], recurse, labelAssignments},
  If[n == 0, Return[{ConstantArray[{}, k]}]];
  If[Total[externalCounts] =!= n, Return[{}]];

  recurse[pos_, rem_, acc_] := Module[{slot, out = {}},
    If[pos > n, Return[{acc}]];
    For[slot = 1, slot <= k, slot++,
      If[rem[[slot]] > 0,
        out = Join[
          out,
          recurse[
            pos + 1,
            ReplacePart[rem, slot -> rem[[slot]] - 1],
            Append[acc, slot]
          ]
        ];
      ];
    ];
    out
  ];

  labelAssignments = recurse[1, externalCounts, {}];
  Table[
    Table[Pick[vectorIndices, labels, slot], {slot, 1, k}],
    {labels, labelAssignments}
  ]
];

firstVectorPlacement::usage =
  "firstVectorPlacement[externalCounts, vectorIndices] builds one deterministic external-vector assignment.";
firstVectorPlacement[externalCounts_List, vectorIndices_List] := Module[
  {k = Length[externalCounts], n = Length[vectorIndices], out, cursor = 1, i, takeCount},
  If[n == 0, Return[ConstantArray[{}, k]]];
  If[Total[externalCounts] =!= n, Return[$Failed]];
  out = ConstantArray[{}, k];
  For[i = 1, i <= k, i++,
    takeCount = externalCounts[[i]];
    If[takeCount > 0,
      out[[i]] = Take[vectorIndices, {cursor, cursor + takeCount - 1}];
      cursor += takeCount;
    ];
  ];
  out
];

buildDummyIndexSymbols::usage =
  "buildDummyIndexSymbols[count] returns deterministic dummy symbols \\[Nu]1, \\[Nu]2, ... in package context.";
buildDummyIndexSymbols[count_Integer] := buildDummyIndexSymbols[count] = Table[
  Symbol["StringCode`OPE`TypeII`FlatSpace`TensorStructures`" <> "\[Nu]" <> ToString[i]],
  {i, 1, count}
];

buildDualIndexSymbols::usage =
  "buildDualIndexSymbols[count] returns deterministic dualization symbols \\[Rho]1, \\[Rho]2, ... in package context.";
buildDualIndexSymbols[count_Integer] := buildDualIndexSymbols[count] = Table[
  Symbol["StringCode`OPE`TypeII`FlatSpace`TensorStructures`" <> "\[Rho]" <> ToString[i]],
  {i, 1, count}
];

buildGammaFactor::usage = "buildGammaFactor[form, vectorIndices, spinor1, spinor2] constructs one gamma-factor expression.";
buildGammaFactor[form_, vectorIndices_List, spinor1_, spinor2_] := Switch[form,
  CGamma, CGamma[vectorIndices, spinor1, spinor2],
  CIGamma, CIGamma[vectorIndices, spinor1, spinor2],
  GammaM, GammaM[vectorIndices, spinor1, spinor2],
  Gamma11CGamma, Gamma11CGamma[vectorIndices, spinor1, spinor2],
  Gamma11CIGamma, Gamma11CIGamma[vectorIndices, spinor1, spinor2],
  Gamma11GammaM, Gamma11GammaM[vectorIndices, spinor1, spinor2]
];

buildEpsilonFactor::usage = "buildEpsilonFactor[upIndices, downIndices] builds explicit Levi-Civita tensor factor.";
buildEpsilonFactor[upIndices_List, downIndices_List] := Eps10[upIndices, downIndices];

symbolSortKey::usage = "symbolSortKey[sym] gives a deterministic ordering key for symbolic indices.";
symbolSortKey[sym_Symbol] := SymbolName[Unevaluated[sym]];

canonicalizeSameChiralityFactor::usage =
  "canonicalizeSameChiralityFactor[factor] sorts spinor arguments for CGamma/CIGamma factors.";
canonicalizeSameChiralityFactor[factor_CGamma] := Module[{vec = factor[[1]], s1 = factor[[2]], s2 = factor[[3]], pair},
  pair = SortBy[{s1, s2}, symbolSortKey];
  CGamma[vec, pair[[1]], pair[[2]]]
];
canonicalizeSameChiralityFactor[factor_CIGamma] := Module[{vec = factor[[1]], s1 = factor[[2]], s2 = factor[[3]], pair},
  pair = SortBy[{s1, s2}, symbolSortKey];
  CIGamma[vec, pair[[1]], pair[[2]]]
];
canonicalizeSameChiralityFactor[factor_Gamma11CGamma] := Module[{vec = factor[[1]], s1 = factor[[2]], s2 = factor[[3]], pair},
  pair = SortBy[{s1, s2}, symbolSortKey];
  Gamma11CGamma[vec, pair[[1]], pair[[2]]]
];
canonicalizeSameChiralityFactor[factor_Gamma11CIGamma] := Module[{vec = factor[[1]], s1 = factor[[2]], s2 = factor[[3]], pair},
  pair = SortBy[{s1, s2}, symbolSortKey];
  Gamma11CIGamma[vec, pair[[1]], pair[[2]]]
];
canonicalizeSameChiralityFactor[factor_] := factor;

canonicalizeStructureExpression::usage =
  "canonicalizeStructureExpression[expr] canonicalizes factor-level spinor ordering for same-chirality heads.";
canonicalizeStructureExpression[expr_] := expr /. {
  factor_CGamma :> canonicalizeSameChiralityFactor[factor],
  factor_CIGamma :> canonicalizeSameChiralityFactor[factor],
  factor_Gamma11CGamma :> canonicalizeSameChiralityFactor[factor],
  factor_Gamma11CIGamma :> canonicalizeSameChiralityFactor[factor]
};

deduplicateGroupStructures::usage =
  "deduplicateGroupStructures[group] canonicalizes and removes duplicates while preserving deterministic order.";
deduplicateGroupStructures[group_List] := DeleteDuplicates[canonicalizeStructureExpression /@ group];

buildConcreteStructure::usage =
  "buildConcreteStructure[slots, cMatrix, spinPlacement, extPlacement] builds one Times-product structure.";
buildConcreteStructure[slots_List, cMatrix_List, spinPlacement_List, extPlacement_List] := Module[
  {
    k = Length[slots], slotVectorsOrig, dummyTotal, dummies, cursor = 1,
    i, j, count, pairDummies, dualTotal, dualSymbols, dualCursor = 1,
    factors, factorCursor = 1, baseHead, pOrig, pGamma, hasOutgoing, pairForm, dualizeQ, gammaVecs, dualVecs, gammaHead, nDualFactors
  },
  slotVectorsOrig = extPlacement;
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
  dualTotal = Total[If[TrueQ[#[[6]]], #[[3]], 0] & /@ slots];
  dualSymbols = buildDualIndexSymbols[dualTotal];
  nDualFactors = Count[slots[[All, 6]], True];
  factors = ConstantArray[Null, k + nDualFactors];
  For[i = 1, i <= k, i++,
    {baseHead, pOrig, pGamma, hasOutgoing, pairForm, dualizeQ} = slots[[i]];
    gammaVecs = slotVectorsOrig[[i]];
    gammaHead = baseHead;
    If[TrueQ[dualizeQ],
      dualVecs = Take[dualSymbols, {dualCursor, dualCursor + pGamma - 1}];
      dualCursor += pGamma;
      factors[[factorCursor]] = buildEpsilonFactor[gammaVecs, dualVecs];
      factorCursor += 1;
      gammaVecs = dualVecs;
      gammaHead = gamma11LiftHead[baseHead];
    ];
    factors[[factorCursor]] = buildGammaFactor[gammaHead, gammaVecs, spinPlacement[[i, 1]], spinPlacement[[i, 2]]];
    factorCursor += 1;
  ];
  If[factorCursor == 1, 1, Times @@ Take[factors, factorCursor - 1]]
];

spinorPlacementCacheKey::usage =
  "spinorPlacementCacheKey[slots, outSpinor] builds a cache key for spinor placement enumeration from slot chirality layout.";
spinorPlacementCacheKey[slots_List, outSpinor_] := Module[{forms, outgoing},
  forms = slots[[All, 5]];
  outgoing = slots[[All, 4]];
  {forms, outgoing, If[outSpinor === None, None, outSpinor[[2]]]}
];

vectorPlacementCacheKey::usage =
  "vectorPlacementCacheKey[externalCounts] builds a cache key for vector placement enumeration.";
vectorPlacementCacheKey[externalCounts_List] := externalCounts;

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
  MemberQ[{CGamma, CIGamma}, slot[[5]]],
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

placementOrbitKey::usage =
  "placementOrbitKey[slots, spinPlacement, vecPlacement, automorphisms] canonicalizes a placement under slot automorphisms.";
placementOrbitKey[
  slots_List, spinPlacement_List, vecPlacement_List, automorphisms_List,
  spinRank_Association, vecRank_Association
] := Module[
  {slotKeys, orbitKeys},
  slotKeys = Table[
    slotPlacementKey[slots[[i]], spinPlacement[[i]], vecPlacement[[i]], spinRank, vecRank],
    {i, Length[slots]}
  ];
  orbitKeys = slotKeys[[#]] & /@ automorphisms;
  First @ SortBy[orbitKeys, Identity]
];

uniquePlacementPairs::usage =
  "uniquePlacementPairs[slots, spins, vecs, automorphisms] keeps one representative pair per automorphism orbit.";
uniquePlacementPairs[
  slots_List, spins_List, vecs_List, automorphisms_List,
  spinRank_Association, vecRank_Association
] := Module[
  {seen = <||>, harvested, i, j, key},
  harvested = Reap[
    For[i = 1, i <= Length[spins], i++,
      For[j = 1, j <= Length[vecs], j++,
        key = placementOrbitKey[slots, spins[[i]], vecs[[j]], automorphisms, spinRank, vecRank];
        If[!KeyExistsQ[seen, key],
          seen[key] = True;
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

generateTensorStructures::usage = "generateTensorStructures[incoming, outgoing, opts] enumerates grouped Clifford tensor structures.";
generateTensorStructures[incoming_, outgoing_, opts___Rule] := Module[
  {
    maxK, inNorm, outNorm, inVec, outVec, inSpin, outSpin, allIndexSymbols,
    totalSpinors, k, outSpinor, extVectors, abstractStructures, groups = {},
    abstract, slots, extCounts, cMatrix, spins, vecs, representativesOnly,
    oneSpin, oneVec, builtGroup, spinPlacementCache = <||>, vectorPlacementCache = <||>,
    spinKey, vecKey, firstSpinCache = <||>, firstVecCache = <||>,
    autoCache = <||>, autoKey, automorphisms, pairs, spinRank, vecRank
  },
  If[!(AssociationQ[incoming] && AssociationQ[outgoing]),
    Message[generateTensorStructures::badarg];
    Return[{}];
  ];

  maxK = parseMaxKOption[{opts}];
  representativesOnly = parseRepresentativesOnlyOption[{opts}];
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

  If[k == 0,
    Return[If[Length[inVec] + Length[outVec] == 0, {{1}}, {}]];
  ];

  outSpinor = If[outSpin === {}, None, First[outSpin]];
  extVectors = Join[inVec, outVec];
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
      vecKey = vectorPlacementCacheKey[extCounts];
      If[!KeyExistsQ[firstVecCache, vecKey],
        firstVecCache[vecKey] = firstVectorPlacement[extCounts, extVectors]
      ];
      oneVec = firstVecCache[vecKey];
      builtGroup = If[oneSpin === $Failed || oneVec === $Failed, {}, {buildConcreteStructure[slots, cMatrix, oneSpin, oneVec]}];
      AppendTo[groups, builtGroup],
      spinKey = spinorPlacementCacheKey[slots, outSpinor];
      If[!KeyExistsQ[spinPlacementCache, spinKey],
        spinPlacementCache[spinKey] = spinorPlacements[slots, inSpin, outSpinor]
      ];
      spins = spinPlacementCache[spinKey];
      vecKey = vectorPlacementCacheKey[extCounts];
      If[!KeyExistsQ[vectorPlacementCache, vecKey],
        vectorPlacementCache[vecKey] = vectorPlacements[extCounts, extVectors]
      ];
      vecs = vectorPlacementCache[vecKey];
      autoKey = {slots, extCounts, cMatrix};
      If[!KeyExistsQ[autoCache, autoKey],
        autoCache[autoKey] = abstractAutomorphisms[slots, extCounts, cMatrix]
      ];
      automorphisms = autoCache[autoKey];
      pairs = uniquePlacementPairs[slots, spins, vecs, automorphisms, spinRank, vecRank];
      AppendTo[
        groups,
        Table[
          buildConcreteStructure[slots, cMatrix, pairs[[i, 1]], pairs[[i, 2]]],
          {i, 1, Length[pairs]}
        ]
      ]
    ],
    {abstract, abstractStructures}
  ];

  groups
];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
