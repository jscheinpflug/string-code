(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`BasisGeneration`TypeII`FlatSpace`"];


Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];
Needs["StringCode`Symbols`TypeII`FlatSpace`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`TypeII`"];
Needs["StringCode`BasisGeneration`"];
Needs["StringCode`BasisGeneration`TypeII`"];

(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


(* ::Input::Initialization:: *)
Begin["Private`"];

(* ============================================================ *)
(* SECTION 1: VALIDATION PREDICATES                             *)
(* ============================================================ *)

halfIntegerQ[x_] := IntegerQ[2 x] && OddQ[2 x];

validChiralityQ[chirality_] := MemberQ[{"chiral", "antichiral"}, chirality];

validPictureInputQ[picture_] := IntegerQ[picture] || halfIntegerQ[picture];

validPictureSpecQ[picture_] :=
  IntegerQ[picture] ||
    MatchQ[picture, {q_ /; halfIntegerQ[q], chirality_ /; validChiralityQ[chirality]}];

expandPictureSpecs[picture_Integer] := {picture};
expandPictureSpecs[picture_ /; halfIntegerQ[picture]] :=
  {{picture, "chiral"}, {picture, "antichiral"}};

pictureValue[picture_Integer] := picture;
pictureValue[{picture_ /; halfIntegerQ[picture], chirality_ /; validChiralityQ[chirality]}] :=
  picture;

pictureChirality[picture_Integer] := None;
pictureChirality[{picture_ /; halfIntegerQ[picture], chirality_ /; validChiralityQ[chirality]}] :=
  chirality;

validWeightQ[weight_] := NumericQ[weight] && weight >= 0 && IntegerQ[2 weight];

groundStateWeight[picture_?validPictureSpecQ] := Module[{q},
  q = pictureValue[picture];
  If[IntegerQ[q],
    -1/2 q (q + 2),
    5/8 - 1/2 q (q + 2)
  ]
];

gsoParityOfGroundState[picture_?validPictureSpecQ] := Module[
  {q, baseParity, chiralitySign},
  q = pictureValue[picture];
  baseParity = If[IntegerQ[q], (-1)^q, (-1)^(q + 1/2)];
  chiralitySign = Switch[pictureChirality[picture],
    "antichiral", -1,
    _, 1
  ];
  chiralitySign baseParity
];

(* ============================================================ *)
(* SECTION 2: WEIGHT BOUND CALCULATIONS                         *)
(* ============================================================ *)

(* At picture q, allowed superghost creation modes are
   beta[r] with r <= -3/2 - q and gamma[r] with r <= 1/2 + q. *)
minSuperghostWeightForGhostNumber[ghostNumber_Integer, picture_?validPictureSpecQ] := Module[{q},
  q = pictureValue[picture];
  If[
    ghostNumber >= 0,
    -(1/2 + q) ghostNumber,
    -(3/2 + q) ghostNumber
  ]
];
minSuperghostWeightForGhostNumber[ghostNumber_Integer] :=
  minSuperghostWeightForGhostNumber[ghostNumber, 0];

typeIIGhostWeightAtSplit[
  totalGhostNumber_Integer,
  bcGhostNumber_Integer,
  picture_?validPictureSpecQ
] :=
  minGhostWeightForGhostNumberBosonic[bcGhostNumber] +
    minSuperghostWeightForGhostNumber[totalGhostNumber - bcGhostNumber, picture];

(* Min over bc/superghost split at fixed total ghost number and picture. *)
minTypeIIGhostWeightForGhostNumber[ghostNumber_Integer, picture_?validPictureSpecQ] := Module[
  {q, case1Vertex, case2Vertex, case1Candidates, case2Candidates, values},
  q = pictureValue[picture];
  case1Vertex = 1 - q;
  case2Vertex = -q;
  case1Candidates = Select[
    DeleteDuplicates[{Floor[case1Vertex], Ceiling[case1Vertex], ghostNumber}],
    # <= ghostNumber &
  ];
  case2Candidates = Select[
    DeleteDuplicates[{Floor[case2Vertex], Ceiling[case2Vertex], ghostNumber + 1}],
    # >= ghostNumber + 1 &
  ];
  values = Join[
    typeIIGhostWeightAtSplit[ghostNumber, #, picture] & /@ case1Candidates,
    typeIIGhostWeightAtSplit[ghostNumber, #, picture] & /@ case2Candidates
  ];
  Min[values]
];
minTypeIIGhostWeightForGhostNumber[ghostNumber_Integer] :=
  minTypeIIGhostWeightForGhostNumber[ghostNumber, 0];

minSectorWeightForGhostAndPicture[ghostNumber_Integer, picture_?validPictureSpecQ] :=
  groundStateWeight[picture] + minTypeIIGhostWeightForGhostNumber[ghostNumber, picture];

findFeasibleSplitRange[splitFeasibleQ_, center_Integer, maxRadius_Integer?Positive] := Module[
  {seed = Missing["NotFound"], radius = 0, candidates, minSplit, maxSplit},
  While[radius <= maxRadius && MissingQ[seed],
    candidates = DeleteDuplicates[{center - radius, center + radius}];
    seed = SelectFirst[candidates, splitFeasibleQ, Missing["NotFound"]];
    radius++;
  ];
  If[MissingQ[seed],
    Return[{}]
  ];
  minSplit = seed;
  maxSplit = seed;
  While[splitFeasibleQ[minSplit - 1], minSplit--];
  While[splitFeasibleQ[maxSplit + 1], maxSplit++];
  Range[minSplit, maxSplit]
];

ghostSplitRangeTypeII[ghostNumber_Integer, maxWeight_?NumericQ, picture_?validPictureSpecQ] := Module[
  {center, maxRadius, splitFeasibleQ},
  If[maxWeight < minTypeIIGhostWeightForGhostNumber[ghostNumber, picture],
    Return[{}]
  ];
  splitFeasibleQ[bcGhostNumber_Integer] :=
    minGhostWeightForGhostNumberBosonic[bcGhostNumber] +
      minSuperghostWeightForGhostNumber[ghostNumber - bcGhostNumber, picture] <= maxWeight;
  center = Floor[ghostNumber/2];
  maxRadius = Max[64, 2 Abs[ghostNumber] + Ceiling[2 Max[0, maxWeight]] + 16];
  findFeasibleSplitRange[splitFeasibleQ, center, maxRadius]
];
ghostSplitRangeTypeII[ghostNumber_Integer, maxWeight_?NumericQ] :=
  ghostSplitRangeTypeII[ghostNumber, maxWeight, 0];

ghostSplitRangeClosedString[
  totalGhostNumber_Integer,
  totalWeight_?NumericQ,
  pictureLeft_?validPictureSpecQ,
  pictureRight_?validPictureSpecQ
] := Module[{center, maxRadius, splitFeasibleQ},
  splitFeasibleQ[holoGhostNumber_Integer] :=
    minSectorWeightForGhostAndPicture[holoGhostNumber, pictureLeft] +
      minSectorWeightForGhostAndPicture[totalGhostNumber - holoGhostNumber, pictureRight] <=
        totalWeight;
  center = Floor[totalGhostNumber/2];
  maxRadius = Max[
    64,
    2 Abs[totalGhostNumber] + Ceiling[2 Max[0, totalWeight]] +
      Ceiling[2 Abs[groundStateWeight[pictureLeft]]] +
      Ceiling[2 Abs[groundStateWeight[pictureRight]]] + 16
  ];
  findFeasibleSplitRange[splitFeasibleQ, center, maxRadius]
];

(* ============================================================ *)
(* SECTION 3: MODE CONFIG GENERATORS                            *)
(* ============================================================ *)

generateSuperghostModes[betaOffsets_List, gammaOffsets_List, picture_?validPictureSpecQ] := Module[
  {q},
  q = pictureValue[picture];
  Join[
    mode[\[Beta], -3/2 - q - #] & /@ betaOffsets,
    mode[\[Gamma], 1/2 + q - #] & /@ gammaOffsets
  ]
];

superghostOffsetBudget[
  betaCount_Integer,
  superghostNumber_Integer,
  maxWeight_?NumericQ,
  picture_?validPictureSpecQ
] := Module[
  {q, gammaCount, minWeight},
  q = pictureValue[picture];
  gammaCount = betaCount + superghostNumber;
  If[gammaCount < 0,
    Return[-1]
  ];
  minWeight = betaCount - (1/2 + q) superghostNumber;
  If[minWeight > maxWeight, -1, Floor[maxWeight - minWeight]]
];

enumerateSuperghostAtCounts[
  betaCount_Integer,
  gammaCount_Integer,
  maxOffsetBudget_Integer,
  picture_?validPictureSpecQ
] := Module[
  {
    q,
    superghostNumber,
    minWeight,
    collectedConfigs,
    betaOffsetSum,
    gammaOffsetSum,
    betaOffsetConfigs,
    gammaOffsetConfigs,
    totalWeight,
    betaOffsets,
    gammaOffsets
  },
  If[maxOffsetBudget < 0 || betaCount < 0 || gammaCount < 0,
    Return[{}]
  ];
  q = pictureValue[picture];
  superghostNumber = gammaCount - betaCount;
  minWeight = betaCount - (1/2 + q) superghostNumber;
  collectedConfigs = Reap[
    Do[
      betaOffsetConfigs = bosonicModesByExactSum[betaCount, betaOffsetSum, 0];
      If[betaOffsetConfigs === {},
        Continue[]
      ];
      Do[
        totalWeight = minWeight + betaOffsetSum + gammaOffsetSum;
        gammaOffsetConfigs = bosonicModesByExactSum[gammaCount, gammaOffsetSum, 0];
        If[gammaOffsetConfigs === {},
          Continue[]
        ];
        Do[
          Do[
            Sow[{generateSuperghostModes[betaOffsets, gammaOffsets, picture], totalWeight}],
            {gammaOffsets, gammaOffsetConfigs}
          ],
          {betaOffsets, betaOffsetConfigs}
        ],
        {gammaOffsetSum, 0, maxOffsetBudget - betaOffsetSum}
      ],
      {betaOffsetSum, 0, maxOffsetBudget}
    ]
  ][[2]];
  If[collectedConfigs === {}, {}, collectedConfigs[[1]]]
];

generateSuperghostConfigs[maxWeight_?NumericQ, superghostNumber_Integer, picture_?validPictureSpecQ] /;
    maxWeight < minSuperghostWeightForGhostNumber[superghostNumber, picture] := {};
generateSuperghostConfigs[maxWeight_?NumericQ, superghostNumber_Integer, picture_?validPictureSpecQ] :=
  generateSuperghostConfigs[maxWeight, superghostNumber, picture] = Module[
    {
      q,
      minBetaCount,
      maxBetaCount,
      collectedConfigs,
      betaCount,
      gammaCount,
      maxOffsetBudget,
      superghostConfigsAtCount,
      superghostConfig
    },
    If[!IntegerQ[2 maxWeight],
      Return[{}]
    ];
    q = pictureValue[picture];
    minBetaCount = Max[0, -superghostNumber];
    maxBetaCount = Floor[maxWeight + (1/2 + q) superghostNumber];
    If[maxBetaCount < minBetaCount,
      Return[{}]
    ];
    collectedConfigs = Reap[
      Do[
        gammaCount = betaCount + superghostNumber;
        maxOffsetBudget =
          superghostOffsetBudget[betaCount, superghostNumber, maxWeight, picture];
        superghostConfigsAtCount =
          enumerateSuperghostAtCounts[betaCount, gammaCount, maxOffsetBudget, picture];
        Do[Sow[superghostConfig], {superghostConfig, superghostConfigsAtCount}],
        {betaCount, minBetaCount, maxBetaCount}
      ]
    ][[2]];
    If[collectedConfigs === {}, {}, collectedConfigs[[1]]]
  ];
generateSuperghostConfigs[maxWeight_?NumericQ, superghostNumber_Integer] :=
  generateSuperghostConfigs[maxWeight, superghostNumber, 0];

generateSuperghostConfigs[_, _, _] := {};
generateSuperghostConfigs[_, _] := {};

generateDXModes[matterPartition_List] := Module[{makeMatterMode},
  makeMatterMode[partWeight_Integer] := Module[{mu},
    mode[dX[mu], -partWeight]
  ];
  makeMatterMode /@ matterPartition
];

generateDXModeConfigs[targetWeight_Integer?NonNegative] :=
  generateDXModeConfigs[targetWeight] = Module[{partitions},
    partitions = If[targetWeight == 0, {{}}, IntegerPartitions[targetWeight]];
    generateDXModes /@ partitions
  ];

psiBaseWeight[picture_?validPictureSpecQ] := If[IntegerQ[pictureValue[picture]], 1/2, 0];
psiMinOffset[picture_?validPictureSpecQ] := If[IntegerQ[pictureValue[picture]], 0, 1];

generatePsiModes[offsets_List, picture_?validPictureSpecQ] := Module[
  {baseWeight, makePsiMode},
  baseWeight = psiBaseWeight[picture];
  makePsiMode[offset_Integer?NonNegative] := Module[{mu},
    mode[\[Psi][mu], -baseWeight - offset]
  ];
  makePsiMode /@ offsets
];

generatePsiModeConfigs[targetWeight_?NumericQ, picture_?validPictureSpecQ] :=
  generatePsiModeConfigs[targetWeight, picture] = Module[
    {
      baseWeight,
      minOffset,
      psiCount = 0,
      minPsiWeight,
      maxOffsetSum,
      minOffsetSum,
      offsetSum,
      offsetConfigs,
      collectedConfigs
    },
    If[targetWeight < 0 || !IntegerQ[2 targetWeight],
      Return[{}]
    ];
    baseWeight = psiBaseWeight[picture];
    minOffset = psiMinOffset[picture];
    collectedConfigs = Reap[
      While[True,
        minPsiWeight = baseWeight psiCount + minDistinctModeSum[psiCount, minOffset];
        If[minPsiWeight > targetWeight,
          Break[]
        ];
        minOffsetSum = minDistinctModeSum[psiCount, minOffset];
        maxOffsetSum = Floor[targetWeight - baseWeight psiCount];
        Do[
          offsetConfigs = distinctModesByExactSum[psiCount, offsetSum, minOffset];
          Do[
            Sow[{generatePsiModes[offsets, picture], baseWeight psiCount + offsetSum}],
            {offsets, offsetConfigs}
          ],
          {offsetSum, minOffsetSum, maxOffsetSum}
        ];
        psiCount++;
      ]
    ][[2]];
    If[collectedConfigs === {}, {}, collectedConfigs[[1]]]
  ];

generatePsiModeConfigs[_, _] := {};

generateMatterModeConfigs[targetWeight_?NumericQ, picture_?validPictureSpecQ] :=
  generateMatterModeConfigs[targetWeight, picture] = Module[
    {psiModeConfigs, collectedConfigs},
    If[targetWeight < 0 || !IntegerQ[2 targetWeight],
      Return[{}]
    ];
    psiModeConfigs = generatePsiModeConfigs[targetWeight, picture];
    If[psiModeConfigs === {},
      Return[{}]
    ];
    collectedConfigs = Reap[
      Do[
        Module[{psiModes, psiWeight, remainingDXWeight, dxModeConfigs, dxModes},
          {psiModes, psiWeight} = psiConfig;
          remainingDXWeight = targetWeight - psiWeight;
          If[remainingDXWeight >= 0 && IntegerQ[remainingDXWeight],
            dxModeConfigs = generateDXModeConfigs[remainingDXWeight];
            Do[Sow[Join[dxModes, psiModes]], {dxModes, dxModeConfigs}]
          ]
        ],
        {psiConfig, psiModeConfigs}
      ]
    ][[2]];
    If[collectedConfigs === {}, {}, collectedConfigs[[1]]]
  ];

generateMatterModeConfigs[_, _] := {};

(* ============================================================ *)
(* SECTION 4: MODE UTILITIES                                    *)
(* ============================================================ *)

canonicalizeLorentzIndicesModes[modes_List] := Module[
  {indexSymbols, canonicalSymbols, renamingRules},
  indexSymbols = DeleteDuplicates @ Cases[
    modes,
    mode[(dX | dXt | \[Psi] | \[Psi]t)[mu_Symbol], __] :> mu,
    Infinity
  ];
  canonicalSymbols = Symbol["mu" <> ToString[#]] & /@ Range[Length[indexSymbols]];
  renamingRules = Thread[indexSymbols -> canonicalSymbols];
  modes /. renamingRules
];

modeSpecies[mode[head_, _]] := If[AtomQ[head], head, Head[head]];

modeWeightContribution[mode[_, modeNumber_]] := -modeNumber;

modeGhostContribution[modeObj : mode[_, _]] := Switch[
  modeSpecies[modeObj],
  b | bt | \[Beta] | \[Beta]t, -1,
  c | ct | \[Gamma] | \[Gamma]t, 1,
  _, 0
];

modeGSOParityContribution[modeObj : mode[_, _]] :=
  If[
    MemberQ[{\[Psi], \[Psi]t, \[Beta], \[Beta]t, \[Gamma], \[Gamma]t}, modeSpecies[modeObj]],
    -1,
    1
  ];

modeListGhostNumber[modeList_List] :=
  Total[modeGhostContribution /@ Cases[modeList, mode[_, _], Infinity]];

modeListWeight[modeList_List] :=
  Total[modeWeightContribution /@ Cases[modeList, mode[_, _], Infinity]];

gsoParityOfConfig[modeList_List, picture_?validPictureSpecQ] :=
  gsoParityOfGroundState[picture] *
    Times @@ (modeGSOParityContribution /@ Cases[modeList, mode[_, _], Infinity]);

buildHoloState[picture_?validPictureSpecQ, bcModes_List, superghostModes_List, matterModes_List] :=
  Module[{modeList},
    modeList = canonicalizeLorentzIndicesModes[
      Join[bcModes, superghostModes, matterModes]
    ];
    {picture, modeList}
  ];

antiModeFromHolo[mode[b, modeNumber_]] := mode[bt, modeNumber];
antiModeFromHolo[mode[c, modeNumber_]] := mode[ct, modeNumber];
antiModeFromHolo[mode[\[Beta], modeNumber_]] := mode[\[Beta]t, modeNumber];
antiModeFromHolo[mode[\[Gamma], modeNumber_]] := mode[\[Gamma]t, modeNumber];
antiModeFromHolo[mode[dX[mu_], modeNumber_]] := mode[dXt[mu], modeNumber];
antiModeFromHolo[mode[\[Psi][mu_], modeNumber_]] := mode[\[Psi]t[mu], modeNumber];
antiModeFromHolo[modeObj_] := modeObj;

(* ============================================================ *)
(* SECTION 5: CLOSED STRING COMBINATORICS                       *)
(* ============================================================ *)

parseGSOOption[opts___] := Module[{optionList, gsoProjected},
  optionList = Flatten[{opts}];
  If[!OptionQ[optionList],
    Return[$Failed]
  ];
  gsoProjected = readBooleanOption[optionList, "GSOProjected", True];
  If[gsoProjected === $Failed, $Failed, gsoProjected]
];

parseFullBasisOptions[opts___] := Module[
  {optionList, levelMatched, gsoProjected},
  optionList = Flatten[{opts}];
  If[!OptionQ[optionList],
    Return[$Failed]
  ];
  levelMatched = readBooleanOption[optionList, "LevelMatched", True];
  gsoProjected = readBooleanOption[optionList, "GSOProjected", True];
  If[levelMatched === $Failed || gsoProjected === $Failed,
    $Failed,
    {levelMatched, gsoProjected}
  ]
];

combineHoloAntiStates[holoBasis_List, antiBasis_List] :=
  Flatten[
    Table[
      Join[holoTuple[[2]], antiTuple[[2]]],
      {holoTuple, holoBasis},
      {antiTuple, antiBasis}
    ],
    1
  ];

generateJoinedSectorStates[
  holoWeight_,
  holoGhostNumber_Integer,
  pictureLeft_?validPictureSpecQ,
  antiWeight_,
  antiGhostNumber_Integer,
  pictureRight_?validPictureSpecQ,
  gsoProjected_
] := Module[{holoBasis, antiBasis},
  holoBasis = generateBasisHoloForPictureSpec[
    holoWeight,
    holoGhostNumber,
    pictureLeft,
    "GSOProjected" -> gsoProjected
  ];
  If[holoBasis === {},
    Return[{}]
  ];
  antiBasis = generateBasisAntiHoloForPictureSpec[
    antiWeight,
    antiGhostNumber,
    pictureRight,
    "GSOProjected" -> gsoProjected
  ];
  If[antiBasis === {},
    Return[{}]
  ];
  combineHoloAntiStates[holoBasis, antiBasis]
];

collectLevelMatchedStates[
  weight_?validWeightQ,
  ghostNumber_Integer,
  pictureLeft_?validPictureSpecQ,
  pictureRight_?validPictureSpecQ,
  gsoProjected_,
  holoGhostSplits_List
] := Module[
  {sectorWeight, collectedStates, antiGhostNumber, joinedStates},
  sectorWeight = weight/2;
  collectedStates = Reap[
    Do[
      antiGhostNumber = ghostNumber - holoGhostNumber;
      If[
        minSectorWeightForGhostAndPicture[holoGhostNumber, pictureLeft] > sectorWeight ||
        minSectorWeightForGhostAndPicture[antiGhostNumber, pictureRight] > sectorWeight,
        Continue[]
      ];
      joinedStates = generateJoinedSectorStates[
        sectorWeight,
        holoGhostNumber,
        pictureLeft,
        sectorWeight,
        antiGhostNumber,
        pictureRight,
        gsoProjected
      ];
      Do[Sow[joinedState], {joinedState, joinedStates}],
      {holoGhostNumber, holoGhostSplits}
    ]
  ][[2]];
  If[collectedStates === {}, {}, collectedStates[[1]]]
];

collectAllSplitStates[
  weight_?validWeightQ,
  ghostNumber_Integer,
  pictureLeft_?validPictureSpecQ,
  pictureRight_?validPictureSpecQ,
  gsoProjected_,
  holoGhostSplits_List
] := Module[
  {
    collectedStates,
    antiGhostNumber,
    minHoloWeight,
    maxHoloWeight,
    minHoloWeight2,
    maxHoloWeight2,
    holoWeight,
    antiWeight,
    joinedStates
  },
  collectedStates = Reap[
    Do[
      antiGhostNumber = ghostNumber - holoGhostNumber;
      minHoloWeight = minSectorWeightForGhostAndPicture[holoGhostNumber, pictureLeft];
      maxHoloWeight =
        weight - minSectorWeightForGhostAndPicture[antiGhostNumber, pictureRight];
      If[maxHoloWeight < minHoloWeight,
        Continue[]
      ];
      minHoloWeight2 = Ceiling[2 minHoloWeight];
      maxHoloWeight2 = Floor[2 maxHoloWeight];
      Do[
        holoWeight = holoWeight2/2;
        antiWeight = weight - holoWeight;
        joinedStates = generateJoinedSectorStates[
          holoWeight,
          holoGhostNumber,
          pictureLeft,
          antiWeight,
          antiGhostNumber,
          pictureRight,
          gsoProjected
        ];
        Do[Sow[joinedState], {joinedState, joinedStates}],
        {holoWeight2, minHoloWeight2, maxHoloWeight2}
      ],
      {holoGhostNumber, holoGhostSplits}
    ]
  ][[2]];
  If[collectedStates === {}, {}, collectedStates[[1]]]
];

formatBasisResult[pictures_List, states_List] := Module[{basisStates},
  basisStates = DeleteDuplicates[states];
  If[basisStates === {},
    {},
    {pictures, basisStates}
  ]
];

(* ============================================================ *)
(* SECTION 6: HOLOMORPHIC BASIS CORE                            *)
(* ============================================================ *)

enumerateMatterAtRemainingWeight[
  bcModes_List,
  bcWeight_,
  superghostModes_List,
  superghostWeight_,
  remainingWeight_,
  picture_?validPictureSpecQ,
  ghostNumber_Integer,
  gsoProjected_
] := Module[
  {
    remainingMatterWeight,
    matterModeConfigs,
    collectedTuples,
    groundWeight,
    matterModes,
    candidateState,
    candidateModes,
    candidateParity
  },
  remainingMatterWeight = remainingWeight - bcWeight - superghostWeight;
  If[remainingMatterWeight < 0,
    Return[{}]
  ];
  matterModeConfigs = generateMatterModeConfigs[remainingMatterWeight, picture];
  If[matterModeConfigs === {},
    Return[{}]
  ];
  groundWeight = groundStateWeight[picture];
  collectedTuples = Reap[
    Do[
      candidateState = buildHoloState[picture, bcModes, superghostModes, matterModes];
      candidateModes = candidateState[[2]];
      If[modeListGhostNumber[candidateModes] =!= ghostNumber,
        Continue[]
      ];
      If[groundWeight + modeListWeight[candidateModes] =!= remainingWeight + groundWeight,
        Continue[]
      ];
      candidateParity = gsoParityOfConfig[candidateModes, picture];
      If[(!TrueQ[gsoProjected]) || candidateParity === 1,
        Sow[candidateState]
      ],
      {matterModes, matterModeConfigs}
    ]
  ][[2]];
  If[collectedTuples === {}, {}, collectedTuples[[1]]]
];

enumerateAtBcGhostSplit[
  bcGhostNumber_Integer,
  ghostNumber_Integer,
  remainingWeight_,
  picture_?validPictureSpecQ,
  gsoProjected_
] := Module[
  {
    superghostNumber,
    bcMaxWeight,
    bcConfigs,
    collectedTuples,
    bcConfig,
    bcModes,
    bcWeight,
    superghostMaxWeight,
    superghostConfigs,
    superghostConfig,
    superghostModes,
    superghostWeight,
    matterTuples,
    matterTuple
  },
  superghostNumber = ghostNumber - bcGhostNumber;
  bcMaxWeight =
    Floor[remainingWeight - minSuperghostWeightForGhostNumber[superghostNumber, picture]];
  bcConfigs = generateGhostConfigsHolo[bcMaxWeight, bcGhostNumber];
  If[bcConfigs === {},
    Return[{}]
  ];
  collectedTuples = Reap[
    Do[
      {bcModes, bcWeight} = bcConfig;
      superghostMaxWeight = remainingWeight - bcWeight;
      superghostConfigs = generateSuperghostConfigs[superghostMaxWeight, superghostNumber, picture];
      If[superghostConfigs === {},
        Continue[]
      ];
      Do[
        {superghostModes, superghostWeight} = superghostConfig;
        matterTuples = enumerateMatterAtRemainingWeight[
          bcModes,
          bcWeight,
          superghostModes,
          superghostWeight,
          remainingWeight,
          picture,
          ghostNumber,
          gsoProjected
        ];
        Do[Sow[matterTuple], {matterTuple, matterTuples}],
        {superghostConfig, superghostConfigs}
      ],
      {bcConfig, bcConfigs}
    ]
  ][[2]];
  If[collectedTuples === {}, {}, collectedTuples[[1]]]
];

generateBasisHoloForPictureSpec[
  weight_?validWeightQ,
  ghostNumber_Integer,
  picture_?validPictureSpecQ,
  opts___
] := Module[
  {
    gsoProjected,
    groundWeight,
    remainingWeight,
    bcGhostSplits,
    collectedTuples,
    basisTuples,
    bcGhostNumber,
    splitTuples,
    splitTuple
  },
  gsoProjected = parseGSOOption[opts];
  If[gsoProjected === $Failed,
    Return[{}]
  ];
  groundWeight = groundStateWeight[picture];
  remainingWeight = weight - groundWeight;
  If[!IntegerQ[2 remainingWeight],
    Return[{}]
  ];
  bcGhostSplits = ghostSplitRangeTypeII[ghostNumber, remainingWeight, picture];
  If[bcGhostSplits === {},
    Return[{}]
  ];
  collectedTuples = Reap[
    Do[
      splitTuples = enumerateAtBcGhostSplit[
        bcGhostNumber,
        ghostNumber,
        remainingWeight,
        picture,
        gsoProjected
      ];
      Do[Sow[splitTuple], {splitTuple, splitTuples}],
      {bcGhostNumber, bcGhostSplits}
    ]
  ][[2]];
  basisTuples = If[collectedTuples === {}, {}, collectedTuples[[1]]];
  DeleteDuplicates[basisTuples]
];

generateBasisHoloForPictureSpec[___] := {};

(* ============================================================ *)
(* SECTION 7: ANTI-HOLOMORPHIC BASIS CORE                       *)
(* ============================================================ *)

generateBasisAntiHoloForPictureSpec[
  weight_?validWeightQ,
  ghostNumber_Integer,
  picture_?validPictureSpecQ,
  opts___
] := Module[{gsoProjected, holoBasis},
  gsoProjected = parseGSOOption[opts];
  If[gsoProjected === $Failed,
    Return[{}]
  ];
  holoBasis = generateBasisHoloForPictureSpec[
    weight,
    ghostNumber,
    picture,
    "GSOProjected" -> gsoProjected
  ];
  ({#[[1]], antiModeFromHolo /@ #[[2]]} &) /@ holoBasis
];

generateBasisAntiHoloForPictureSpec[___] := {};

(* ============================================================ *)
(* SECTION 8: CLOSED STRING BASIS ASSEMBLY                      *)
(* ============================================================ *)

generateBasisForPictureSpecs[
  weight_?validWeightQ,
  ghostNumber_Integer,
  pictures : {pictureLeft_?validPictureSpecQ, pictureRight_?validPictureSpecQ},
  opts___
] := Module[
  {
    parsedOptions,
    levelMatched,
    gsoProjected,
    holoGhostSplits,
    basisStates
  },
  parsedOptions = parseFullBasisOptions[opts];
  If[parsedOptions === $Failed,
    Return[{}]
  ];
  {levelMatched, gsoProjected} = parsedOptions;
  If[TrueQ[levelMatched] && OddQ[2 weight],
    Return[{}]
  ];
  holoGhostSplits = ghostSplitRangeClosedString[
    ghostNumber,
    weight,
    pictureLeft,
    pictureRight
  ];
  If[holoGhostSplits === {},
    Return[{}]
  ];
  basisStates = If[TrueQ[levelMatched],
    collectLevelMatchedStates[
      weight,
      ghostNumber,
      pictureLeft,
      pictureRight,
      gsoProjected,
      holoGhostSplits
    ],
    collectAllSplitStates[
      weight,
      ghostNumber,
      pictureLeft,
      pictureRight,
      gsoProjected,
      holoGhostSplits
    ]
  ];
  formatBasisResult[pictures, basisStates]
];

generateBasisForPictureSpecs[___] := {};

(* ============================================================ *)
(* SECTION 9: PUBLIC API                                        *)
(* ============================================================ *)

generateBasisHolo[
  weight_?validWeightQ,
  ghostNumber_Integer,
  picture_?validPictureInputQ,
  opts___
] := Module[{basisBySpec},
  basisBySpec = Flatten[
    generateBasisHoloForPictureSpec[weight, ghostNumber, #, opts] & /@ expandPictureSpecs[picture],
    1
  ];
  DeleteDuplicates[basisBySpec]
];

generateBasisHolo[___] := {};

generateBasisAntiHolo[
  weight_?validWeightQ,
  ghostNumber_Integer,
  picture_?validPictureInputQ,
  opts___
] := Module[{basisBySpec},
  basisBySpec = Flatten[
    generateBasisAntiHoloForPictureSpec[weight, ghostNumber, #, opts] & /@ expandPictureSpecs[picture],
    1
  ];
  DeleteDuplicates[basisBySpec]
];

generateBasisAntiHolo[___] := {};

generateBasis[
  weight_?validWeightQ,
  ghostNumber_Integer,
  pictures : {pictureLeft_?validPictureInputQ, pictureRight_?validPictureInputQ},
  opts___
] := Module[
  {leftSpecs, rightSpecs, groupedResults},
  leftSpecs = expandPictureSpecs[pictureLeft];
  rightSpecs = expandPictureSpecs[pictureRight];
  groupedResults = DeleteCases[
    Flatten[
      Table[
        generateBasisForPictureSpecs[weight, ghostNumber, {leftSpec, rightSpec}, opts],
        {leftSpec, leftSpecs},
        {rightSpec, rightSpecs}
      ],
      1
    ],
    {}
  ];
  If[groupedResults === {},
    {},
    If[Length[leftSpecs] == 1 && Length[rightSpecs] == 1,
      First[groupedResults],
      groupedResults
    ]
  ]
];

generateBasis[___] := {};


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
