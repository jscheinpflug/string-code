(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`BasisGeneration`Bosonic`FlatSpace`"];


Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`Bosonic`"];
Needs["StringCode`Symbols`Bosonic`FlatSpace`"];
Needs["StringCode`BasisGeneration`"];
Needs["StringCode`BasisGeneration`Bosonic`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`Bosonic`"];

(* ::Section:: *)
(*Declare public variables and methods*)

(* ::Section:: *)
(*Logic*)


(* ::Input::Initialization:: *)
Begin["Private`"];

(* Convert a matter partition to intermediate mode[...] data.
   For dX, each partition part p contributes one mode with modeNumber = -p. *)
matterModesFromPartition[matterPartition_List] := Module[{makeMatterMode},
  makeMatterMode[partWeight_Integer] := Module[{mu},
    mode[dX[mu], -partWeight]
  ];
  makeMatterMode /@ matterPartition
];

(* Matter sector at fixed holomorphic weight, represented in mode language. *)
generateMatterModeConfigs[targetWeight_Integer?NonNegative] :=
  generateMatterModeConfigs[targetWeight] = Module[{partitions},
    partitions = If[targetWeight == 0, {{}}, IntegerPartitions[targetWeight]];
    matterModesFromPartition /@ partitions
  ];

(* Translate one FlatSpace matter mode to local-operator form. *)
flatSpaceMatterModeToOperatorField[mode[dX[mu_], modeNumber_Integer], z_] :=
  dX[mu, -1 - modeNumber, z];

(* Convert FlatSpace matter mode lists into local operator factors. *)
flatSpaceMatterModesToOperatorFields[matterModes_List, z_] :=
  flatSpaceMatterModeToOperatorField[#, z] & /@ matterModes;

(* Canonicalize Lorentz-index placeholders to deterministic symbols mu1, mu2, ...
   following first appearance order in the expression. *)
canonicalizeLorentzIndices[expr_] := Module[{indexSymbols, canonicalSymbols, renamingRules},
  indexSymbols = DeleteDuplicates @ Cases[expr, (dX | dXt)[mu_Symbol, __] :> mu, Infinity];
  canonicalSymbols = Symbol["mu" <> ToString[#]] & /@ Range[Length[indexSymbols]];
  renamingRules = Thread[indexSymbols -> canonicalSymbols];
  expr /. renamingRules
];

(* Final assembly stage: translate mode[...] data, then build/canonicalize the operator. *)
buildHoloOperatorFromModes[ghostModes_List, matterModes_List, z_] := Module[
  {ghostFields, matterFields, rawOperator},
  ghostFields = ghostModesToOperatorFields[ghostModes, z];
  matterFields = flatSpaceMatterModesToOperatorFields[matterModes, z];
  rawOperator = R @@ Join[ghostFields, matterFields];
  canonicalizeLorentzIndices[rawOperator]
];

(* Fast fail: no states can exist below the ghost lower bound at fixed ghost number. *)
generateBasisHolo[weight_Integer, ghostNumber_Integer, z_: 0] /;
    weight < minGhostWeightForGhostNumberBosonic[ghostNumber] := {};

(* Holomorphic basis generation strategy:
   1) Enumerate admissible ghost configs {ghostModes,ghostWeight}.
   2) Fill remaining weight with FlatSpace matter mode configs.
   3) Translate mode[...] data to local operators only at the final stage. *)
generateBasisHolo[weight_Integer, ghostNumber_Integer, z_: 0] := Module[
  {ghostSectorConfigs, collectedOperators, basisOperators},
  ghostSectorConfigs =
    generateGhostConfigsHolo[weight, ghostNumber];
  If[ghostSectorConfigs === {},
    Return[{}]
  ];
  collectedOperators = Reap[
    Scan[
      Function[ghostConfig,
        Module[{ghostModes, ghostSectorWeight, remainingMatterWeight, matterModeConfigs},
          {ghostModes, ghostSectorWeight} = ghostConfig;
          remainingMatterWeight = weight - ghostSectorWeight;
          If[remainingMatterWeight >= 0,
            matterModeConfigs = generateMatterModeConfigs[remainingMatterWeight];
            Scan[
              Function[matterModes,
                Module[{candidateOperator},
                  candidateOperator = buildHoloOperatorFromModes[ghostModes, matterModes, z];
                  (* Keep only non-trivial normal-ordered products. *)
                  If[candidateOperator =!= 1,
                    Sow[candidateOperator]
                  ]
                ]
              ],
              matterModeConfigs
            ]
          ];
        ]
      ],
      ghostSectorConfigs
    ]
  ][[2]];
  basisOperators = If[collectedOperators === {}, {}, collectedOperators[[1]]];
  basisOperators
];

generateBasisHolo[_, _, ___] := {};

(* Anti-holomorphic basis is the same combinatorics, with symbol relabeling. *)
generateBasisAntiHolo[weight_Integer, ghostNumber_Integer, zbar_: 0] := (
  generateBasisHolo[weight, ghostNumber, zbar] /. {b -> bt, c -> ct, dX -> dXt}
);
generateBasisAntiHolo[_, _, ___] := {};

(* For fixed total (ghostNumber, weight), find all feasible holomorphic ghost-number splits.
   We use the ghost lower bound in each sector to avoid scanning impossible splits. *)
ghostSplitRange[ghostNumber_Integer, weight_Integer] := Module[
  {centerLowerGuess, centerUpperGuess, splitFeasibleQ, seedSplit, minSplit, maxSplit},
  splitFeasibleQ[holoGhostNumber_Integer] :=
    minGhostWeightForGhostNumberBosonic[holoGhostNumber] +
      minGhostWeightForGhostNumberBosonic[
        ghostNumber - holoGhostNumber
      ] <= weight;
  centerLowerGuess = Floor[ghostNumber/2];
  centerUpperGuess = Ceiling[ghostNumber/2];
  If[splitFeasibleQ[centerLowerGuess],
    seedSplit = centerLowerGuess,
    If[splitFeasibleQ[centerUpperGuess],
      seedSplit = centerUpperGuess,
      Return[{}]
    ]
  ];
  minSplit = seedSplit;
  maxSplit = seedSplit;
  While[splitFeasibleQ[minSplit - 1], minSplit--];
  While[splitFeasibleQ[maxSplit + 1], maxSplit++];
  Range[minSplit, maxSplit]
];

(* We treat the vacuum as available when a sector has (weight, ghostNumber)=(0,0),
   but final full basis still removes overall identity later. *)
sectorBasisWithVacuum[generator_, sectorWeight_Integer, sectorGhostNumber_Integer, position_] :=
  If[sectorGhostNumber == 0 && sectorWeight == 0, {1}, generator[sectorWeight, sectorGhostNumber, position]];

(* Build the Cartesian product of sector bases and combine as R[holo, anti].
   Ordering matches nested loops: anti basis varies fastest for each holo element. *)
combineSectorBases[holoBasis_List, antiBasis_List] := Module[
  {combinedProducts},
  combinedProducts = canonicalizeLorentzIndices /@ Flatten[Outer[R, holoBasis, antiBasis], 1];
  DeleteCases[combinedProducts, 1 | R[1, 1]]
];

(* Full basis generation without level-matching:
   1) Split total ghost number into holomorphic + anti-holomorphic sectors.
   2) Split total weight between sectors within minimal-weight bounds.
   3) Take Cartesian product of sector bases and combine with R[hol, anti].
   4) Remove duplicates from different split paths. *)
generateBasisAllSplits[weight_Integer, ghostNumber_Integer, z_: 0, zbar_: 0] := Module[
  {holoGhostNumberSplits, collectedOperators, basisOperators},
  holoGhostNumberSplits = ghostSplitRange[ghostNumber, weight];
  If[holoGhostNumberSplits === {},
    Return[{}]
  ];
  collectedOperators = Reap[
    Scan[
      Function[holoGhostNumber,
        Module[{antiGhostNumber, minHoloWeight, maxHoloWeight},
          antiGhostNumber = ghostNumber - holoGhostNumber;
          (* Holomorphic weight bounds induced by sector minimal ghost weights. *)
          minHoloWeight =
            minGhostWeightForGhostNumberBosonic[holoGhostNumber];
          maxHoloWeight =
            weight - minGhostWeightForGhostNumberBosonic[
              antiGhostNumber
            ];
          Do[
            Module[{antiWeight, holoBasis, antiBasis},
              antiWeight = weight - holoWeight;
              holoBasis = sectorBasisWithVacuum[generateBasisHolo, holoWeight, holoGhostNumber, z];
              If[holoBasis === {}, Continue[]];
              antiBasis = sectorBasisWithVacuum[generateBasisAntiHolo, antiWeight, antiGhostNumber, zbar];
              If[antiBasis === {}, Continue[]];
              Scan[Sow, combineSectorBases[holoBasis, antiBasis]]
            ],
            {holoWeight, minHoloWeight, maxHoloWeight}
          ]
        ]
      ],
      holoGhostNumberSplits
    ]
  ][[2]];
  basisOperators = If[collectedOperators === {}, {}, collectedOperators[[1]]];
  DeleteDuplicates[basisOperators]
];

(* Public full basis API:
   - "LevelMatched" -> True (default): equivalent to generateBasisLevelMatched
   - "LevelMatched" -> False: include all holomorphic/antiholomorphic weight splits *)
generateBasis[weight_Integer, ghostNumber_Integer, opts___] :=
  generateBasis[weight, ghostNumber, 0, 0, opts];
generateBasis[weight_Integer, ghostNumber_Integer, z_, zbar_, opts___] := Module[
  {optionList, levelMatchedQ},
  optionList = Flatten[{opts}];
  If[!OptionQ[optionList],
    Return[{}]
  ];
  levelMatchedQ = readBooleanOption[optionList, "LevelMatched", True];
  If[levelMatchedQ === $Failed,
    Return[{}]
  ];
  If[TrueQ[levelMatchedQ],
    generateBasisLevelMatched[weight, ghostNumber, z, zbar],
    generateBasisAllSplits[weight, ghostNumber, z, zbar]
  ]
];
generateBasis[_, _, ___] := {};

(* Level-matched full basis generation:
   1) Enforce equal holomorphic/antiholomorphic weights (weight/2 each).
   2) Split ghost number across sectors subject to each sector's minimal ghost bound.
   3) Build Cartesian products at fixed equal sector weights only. *)
generateBasisLevelMatched[weight_Integer, ghostNumber_Integer, z_: 0, zbar_: 0] := Module[
  {sectorWeight, holoGhostNumberSplits, collectedOperators, basisOperators},
  If[OddQ[weight],
    Return[{}]
  ];
  sectorWeight = Quotient[weight, 2];
  holoGhostNumberSplits = Select[
    ghostSplitRange[ghostNumber, weight],
    minGhostWeightForGhostNumberBosonic[#] <= sectorWeight &&
      minGhostWeightForGhostNumberBosonic[ghostNumber - #] <= sectorWeight &
  ];
  If[holoGhostNumberSplits === {},
    Return[{}]
  ];
  collectedOperators = Reap[
    Scan[
      Function[holoGhostNumber,
        Module[{antiGhostNumber, holoBasis, antiBasis},
          antiGhostNumber = ghostNumber - holoGhostNumber;
          holoBasis = sectorBasisWithVacuum[generateBasisHolo, sectorWeight, holoGhostNumber, z];
          If[holoBasis === {}, Continue[]];
          antiBasis = sectorBasisWithVacuum[generateBasisAntiHolo, sectorWeight, antiGhostNumber, zbar];
          If[antiBasis === {}, Continue[]];
          Scan[Sow, combineSectorBases[holoBasis, antiBasis]]
        ]
      ],
      holoGhostNumberSplits
    ]
  ][[2]];
  basisOperators = If[collectedOperators === {}, {}, collectedOperators[[1]]];
  DeleteDuplicates[basisOperators]
];

generateBasisLevelMatched[_, _, ___] := {};


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
