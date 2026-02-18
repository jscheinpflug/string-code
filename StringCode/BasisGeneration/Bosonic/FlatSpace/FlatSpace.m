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

canonicalizeLorentzIndicesQ::usage =
  "Applies Lorentz-index canonicalization only when canonicalizeIndices is True.";
canonicalizeLorentzIndicesQ[canonicalizeIndices_?BooleanQ, expr_] :=
  If[TrueQ[canonicalizeIndices], canonicalizeLorentzIndices[expr], expr];

matterOperatorFromModes::usage =
  "Builds one matter-only local operator from FlatSpace matter mode data.";
matterOperatorFromModes[matterModes_List, z_, canonicalizeIndices_: True] := Module[{matterFields},
  matterFields = flatSpaceMatterModesToOperatorFields[matterModes, z];
  If[matterFields === {},
    1,
    canonicalizeLorentzIndicesQ[canonicalizeIndices, R @@ matterFields]
  ]
];

joinGhostWithMatterOperator::usage =
  "Combines ghost modes with one matter-only operator into a canonicalized local operator.";
joinGhostWithMatterOperator[ghostModes_List, matterOperator_, z_, canonicalizeIndices_: True] := Module[
  {ghostFields, matterFields, rawOperator},
  ghostFields = ghostModesToOperatorFields[ghostModes, z];
  matterFields = Which[
    matterOperator === 1, {},
    Head[matterOperator] === R, List @@ matterOperator,
    True, {matterOperator}
  ];
  rawOperator = R @@ Join[ghostFields, matterFields];
  canonicalizeLorentzIndicesQ[canonicalizeIndices, rawOperator]
];

withParsedPositionAndCanonicalize::usage =
  "Parses optional position + CanonicalizeIndices and applies a handler on success.";
withParsedPositionAndCanonicalize[args_List, defaultPosition_, handler_Function] := Module[
  {parsedArgs},
  parsedArgs = basisParsePositionAndCanonicalizeOption[args, defaultPosition, True];
  If[parsedArgs === $Failed,
    {},
    handler @@ parsedArgs
  ]
];

generateBasisMatterHolo::usage =
  "Generates holomorphic bosonic matter-only local operators at fixed weight.";
generateBasisMatterHolo[weight_Integer?NonNegative, args___] :=
  withParsedPositionAndCanonicalize[
    Flatten[{args}],
    0,
    Function[{z, canonicalizeIndices},
      Module[{matterModeConfigs, matterOperators},
        matterModeConfigs = generateMatterModeConfigs[weight];
        matterOperators = matterOperatorFromModes[#, z, canonicalizeIndices] & /@ matterModeConfigs;
        DeleteDuplicates[matterOperators]
      ]
    ]
  ];

generateBasisMatterHolo[_, ___] := {};

generateBasisMatterAntiHolo::usage =
  "Generates antiholomorphic bosonic matter-only local operators at fixed weight.";
generateBasisMatterAntiHolo[weight_Integer?NonNegative, args___] :=
  withParsedPositionAndCanonicalize[
    Flatten[{args}],
    0,
    Function[{zbar, canonicalizeIndices},
      generateBasisMatterHolo[
        weight,
        zbar,
        "CanonicalizeIndices" -> canonicalizeIndices
      ] /. dX -> dXt
    ]
  ];
generateBasisMatterAntiHolo[_, ___] := {};

generateBasisMatter::usage =
  "Alias for generateBasisMatterHolo.";
generateBasisMatter[weight_Integer?NonNegative, args___] :=
  generateBasisMatterHolo[weight, args];
generateBasisMatter[_, ___] := {};

(* Fast fail: no states can exist below the ghost lower bound at fixed ghost number. *)
generateBasisHolo[weight_Integer, ghostNumber_Integer, args___] :=
  withParsedPositionAndCanonicalize[
    Flatten[{args}],
    0,
    Function[{z, canonicalizeIndices},
      Module[{ghostSectorConfigs, collectedOperators, basisOperators},
        If[weight < minGhostWeightForGhostNumberBosonic[ghostNumber],
          Return[{}]
        ];
        (* Holomorphic basis generation strategy:
           1) Enumerate admissible ghost configs {ghostModes,ghostWeight}.
           2) Fill remaining weight with FlatSpace matter mode configs.
           3) Translate mode[...] data to local operators only at the final stage. *)
        ghostSectorConfigs = generateGhostConfigsHolo[weight, ghostNumber];
        If[ghostSectorConfigs === {},
          Return[{}]
        ];
        collectedOperators = Reap[
          Scan[
            Function[ghostConfig,
              Module[{ghostModes, ghostSectorWeight, remainingMatterWeight, matterOperators},
                {ghostModes, ghostSectorWeight} = ghostConfig;
                remainingMatterWeight = weight - ghostSectorWeight;
                If[remainingMatterWeight >= 0,
                  matterOperators = generateBasisMatterHolo[
                    remainingMatterWeight,
                    z,
                    "CanonicalizeIndices" -> canonicalizeIndices
                  ];
                  Scan[
                    Function[matterOperator,
                      Module[{candidateOperator},
                        candidateOperator = joinGhostWithMatterOperator[
                          ghostModes,
                          matterOperator,
                          z,
                          canonicalizeIndices
                        ];
                        (* Keep only non-trivial normal-ordered products. *)
                        If[candidateOperator =!= 1,
                          Sow[candidateOperator]
                        ]
                      ]
                    ],
                    matterOperators
                  ]
                ];
              ]
            ],
            ghostSectorConfigs
          ]
        ][[2]];
        basisOperators = If[collectedOperators === {}, {}, collectedOperators[[1]]];
        basisOperators
      ]
    ]
  ];
generateBasisHolo[_, _, ___] := {};

(* Anti-holomorphic basis is the same combinatorics, with symbol relabeling. *)
generateBasisAntiHolo[weight_Integer, ghostNumber_Integer, args___] :=
  withParsedPositionAndCanonicalize[
    Flatten[{args}],
    0,
    Function[{zbar, canonicalizeIndices},
      generateBasisHolo[
        weight,
        ghostNumber,
        zbar,
        "CanonicalizeIndices" -> canonicalizeIndices
      ] /. {b -> bt, c -> ct, dX -> dXt}
    ]
  ];
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
sectorBasisWithVacuum::usage =
  "Returns {1} for vacuum sectors; otherwise calls a sector generator with canonicalization option.";
sectorBasisWithVacuum[
  generator_,
  sectorWeight_Integer,
  sectorGhostNumber_Integer,
  position_,
  canonicalizeIndices_: True
] :=
  If[
    sectorGhostNumber == 0 && sectorWeight == 0,
    {1},
    generator[
      sectorWeight,
      sectorGhostNumber,
      position,
      "CanonicalizeIndices" -> canonicalizeIndices
    ]
  ];

(* Build the Cartesian product of sector bases and combine as R[holo, anti].
   Ordering matches nested loops: anti basis varies fastest for each holo element. *)
combineSectorBases::usage =
  "Builds closed operators from holo/anti lists and optionally canonicalizes Lorentz indices.";
combineSectorBases[holoBasis_List, antiBasis_List, canonicalizeIndices_: True] := Module[
  {combinedProducts},
  combinedProducts = Flatten[Outer[R, holoBasis, antiBasis], 1];
  combinedProducts = canonicalizeLorentzIndicesQ[canonicalizeIndices, #] & /@ combinedProducts;
  DeleteCases[combinedProducts, 1 | R[1, 1]]
];

(* Full basis generation without level-matching:
   1) Split total ghost number into holomorphic + anti-holomorphic sectors.
   2) Split total weight between sectors within minimal-weight bounds.
   3) Take Cartesian product of sector bases and combine with R[hol, anti].
   4) Remove duplicates from different split paths. *)
generateBasisAllSplits[weight_Integer, ghostNumber_Integer, z_: 0, zbar_: 0, canonicalizeIndices_: True] := Module[
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
              holoBasis = sectorBasisWithVacuum[
                generateBasisHolo,
                holoWeight,
                holoGhostNumber,
                z,
                canonicalizeIndices
              ];
              If[holoBasis === {}, Continue[]];
              antiBasis = sectorBasisWithVacuum[
                generateBasisAntiHolo,
                antiWeight,
                antiGhostNumber,
                zbar,
                canonicalizeIndices
              ];
              If[antiBasis === {}, Continue[]];
              Scan[Sow, combineSectorBases[holoBasis, antiBasis, canonicalizeIndices]]
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

parseBosonicFullBasisOptionsFromList::usage =
  "Parses \"LevelMatched\", \"CanonicalizeIndices\", and \"B0MinusProjected\" from a full-basis option list.";
parseBosonicFullBasisOptionsFromList[optionList_List] := Module[
  {levelMatchedQ, canonicalizeIndices, b0MinusProjectedQ},
  If[!OptionQ[optionList],
    Return[$Failed]
  ];
  levelMatchedQ = readBooleanOption[optionList, "LevelMatched", True];
  canonicalizeIndices = basisReadCanonicalizeIndicesOption[optionList, True];
  b0MinusProjectedQ = basisReadB0MinusProjectedOption[optionList, False];
  If[levelMatchedQ === $Failed || canonicalizeIndices === $Failed || b0MinusProjectedQ === $Failed,
    $Failed,
    {levelMatchedQ, canonicalizeIndices, b0MinusProjectedQ}
  ]
];

(* Public full basis API:
   - "LevelMatched" -> True (default): return only level-matched states
   - "LevelMatched" -> False: include all holomorphic/antiholomorphic weight splits *)
generateBasis[weight_Integer, ghostNumber_Integer, opts___] :=
  generateBasis[weight, ghostNumber, 0, 0, opts];
generateBasis[weight_Integer, ghostNumber_Integer, z_, zbar_, opts___] := Module[
  {
    optionList,
    parsedOptions,
    levelMatchedQ,
    canonicalizeIndices,
    b0MinusProjectedQ,
    generatedBasisOperators
  },
  optionList = Flatten[{opts}];
  parsedOptions = parseBosonicFullBasisOptionsFromList[optionList];
  If[parsedOptions === $Failed,
    Return[{}]
  ];
  {levelMatchedQ, canonicalizeIndices, b0MinusProjectedQ} = parsedOptions;
  generatedBasisOperators = If[TrueQ[levelMatchedQ],
    generateBasisLevelMatchedInternal[weight, ghostNumber, z, zbar, canonicalizeIndices],
    generateBasisAllSplits[weight, ghostNumber, z, zbar, canonicalizeIndices]
  ];
  If[TrueQ[b0MinusProjectedQ],
    basisIndependentROperatorsFromExpressions[
      basisProjectOperatorBasisByB0Minus[generatedBasisOperators]
    ],
    generatedBasisOperators
  ]
];
generateBasis[_, _, ___] := {};

(* Level-matched full basis generation:
   1) Enforce equal holomorphic/antiholomorphic weights (weight/2 each).
   2) Split ghost number across sectors subject to each sector's minimal ghost bound.
   3) Build Cartesian products at fixed equal sector weights only. *)
generateBasisLevelMatchedInternal::usage =
  "Internal helper that enumerates only level-matched closed-string states.";
generateBasisLevelMatchedInternal[
  weight_Integer,
  ghostNumber_Integer,
  z_: 0,
  zbar_: 0,
  canonicalizeIndices_: True
] := Module[
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
          holoBasis = sectorBasisWithVacuum[
            generateBasisHolo,
            sectorWeight,
            holoGhostNumber,
            z,
            canonicalizeIndices
          ];
          If[holoBasis === {}, Continue[]];
          antiBasis = sectorBasisWithVacuum[
            generateBasisAntiHolo,
            sectorWeight,
            antiGhostNumber,
            zbar,
            canonicalizeIndices
          ];
          If[antiBasis === {}, Continue[]];
          Scan[Sow, combineSectorBases[holoBasis, antiBasis, canonicalizeIndices]]
        ]
      ],
      holoGhostNumberSplits
    ]
  ][[2]];
  basisOperators = If[collectedOperators === {}, {}, collectedOperators[[1]]];
  DeleteDuplicates[basisOperators]
];

generateBasisLevelMatchedInternal[_, _, ___] := {};


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
