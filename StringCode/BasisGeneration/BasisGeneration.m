(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`BasisGeneration`"];


Needs["StringCode`Symbols`"];
Needs["StringCode`NormalOrdering`"];


(* ::Section:: *)
(*Logic*)

(* ::Input::Initialization:: *)
Begin["Private`"];

(* Shared option parser for boolean options like "LevelMatched" and
   "GSOProjected". Returns $Failed on malformed/legacy-mismatched input. *)
readBooleanOption[opts_List, optionName_String, default_] := Module[
  {optionAssociation, legacySymbolUsedQ, optionValue},
  optionAssociation = Association[opts];
  legacySymbolUsedQ = AnyTrue[
    opts,
    Function[opt,
      MatchQ[opt, _Rule] &&
        Head[First[opt]] === Symbol &&
        SymbolName[First[opt]] === optionName
    ]
  ];
  If[legacySymbolUsedQ && !KeyExistsQ[optionAssociation, optionName],
    Return[$Failed]
  ];
  optionValue = Lookup[optionAssociation, optionName, default];
  If[BooleanQ[optionValue], optionValue, $Failed]
];

(* Shared helper: minimal sum of k distinct integer modes >= minMode.
   Example: k=3, minMode=0 gives 0+1+2 = 3. *)
minDistinctModeSum[k_Integer?NonNegative, minMode_Integer?NonNegative] :=
  Quotient[k (2 minMode + k - 1), 2];

(* Shared helper: enumerate strictly increasing mode lists of fixed length and exact sum.
   Recursion is memoized and pruned by minDistinctModeSum. *)
distinctModesByExactSum[0, 0, _Integer?NonNegative] := {{}};
distinctModesByExactSum[0, _Integer, _Integer?NonNegative] := {};
distinctModesByExactSum[k_Integer?Positive, sum_Integer, minMode_Integer?NonNegative] /;
    sum < minDistinctModeSum[k, minMode] := {};
distinctModesByExactSum[k_Integer?Positive, sum_Integer, minMode_Integer?NonNegative] :=
  distinctModesByExactSum[k, sum, minMode] =
    Flatten[
      Table[
        If[sum - mode >= minDistinctModeSum[k - 1, mode + 1],
          Prepend[#, mode] & /@ distinctModesByExactSum[k - 1, sum - mode, mode + 1],
          {}
        ],
        {mode, minMode, sum}
      ],
      1
    ];

(* Shared helper: enumerate nondecreasing (bosonic) mode lists of fixed
   length and exact sum. *)
bosonicModesByExactSum[0, 0, _Integer?NonNegative] := {{}};
bosonicModesByExactSum[0, _Integer, _Integer?NonNegative] := {};
bosonicModesByExactSum[_Integer?Positive, _Integer?Negative, _Integer?NonNegative] := {};
bosonicModesByExactSum[count_Integer?Positive, sum_Integer?NonNegative, minMode_Integer?NonNegative] /;
    sum < count minMode := {};
bosonicModesByExactSum[count_Integer?Positive, sum_Integer?NonNegative, minMode_Integer?NonNegative] :=
  bosonicModesByExactSum[count, sum, minMode] =
    Flatten[
      Table[
        Prepend[#, modeOffset] & /@
          bosonicModesByExactSum[count - 1, sum - modeOffset, modeOffset],
        {modeOffset, minMode, sum}
      ],
      1
    ];

(* Shared helper: minimal ghost contribution for fixed b/c counts. *)
minGhostWeightForGhostCounts[bGhostCount_Integer?NonNegative, cGhostCount_Integer?NonNegative] :=
  2 bGhostCount + minDistinctModeSum[bGhostCount, 0] - cGhostCount + minDistinctModeSum[cGhostCount, 0];

(* Shared helper: closed-form lower bound on b/c holomorphic ghost weight at fixed ghost number. *)
minGhostWeightForGhostNumberBosonic[ghostNumber_Integer] :=
  Quotient[ghostNumber (ghostNumber - 3), 2];

(* Shared helper: upper bound for number of b ghosts compatible with (ghostNumber,maxWeight). *)
maxBCountForGhostNumber[ghostNumber_Integer, maxHolomorphicWeight_Integer] := Module[
  {bGhostCount, cGhostCount},
  bGhostCount = Max[0, -ghostNumber];
  cGhostCount = ghostNumber + bGhostCount;
  While[minGhostWeightForGhostCounts[bGhostCount, cGhostCount] <= maxHolomorphicWeight,
    bGhostCount++;
    cGhostCount = ghostNumber + bGhostCount;
  ];
  bGhostCount - 1
];

(* Shared helper: all fermionic mode configurations with fixed count and total weight <= maxWeight.
   Returns pairs {modes, weight}. *)
fermionicConfigsByMaxWeight[fieldBaseWeight_Integer, fieldCount_Integer?NonNegative, maxHolomorphicWeight_Integer] :=
  fermionicConfigsByMaxWeight[fieldBaseWeight, fieldCount, maxHolomorphicWeight] = Module[
    {minModeSum, maxModeSum},
    If[fieldCount == 0,
      Return[If[maxHolomorphicWeight >= 0, {{{}, 0}}, {}]]
    ];
    minModeSum = minDistinctModeSum[fieldCount, 0];
    maxModeSum = maxHolomorphicWeight - fieldBaseWeight fieldCount;
    If[maxModeSum < minModeSum,
      {},
      Flatten[
        Table[
          ({#, fieldBaseWeight fieldCount + modeSum} & /@
              distinctModesByExactSum[fieldCount, modeSum, 0]),
          {modeSum, minModeSum, maxModeSum}
        ],
        1
      ]
    ]
  ];

(* Shared helper: map nonnegative mode offset to oscillator mode number. *)
modeNumberFromOffset[minimalModeNumber_Integer, modeOffset_Integer?NonNegative] :=
  minimalModeNumber - modeOffset;

(* Shared helper: convert b/c mode offsets to mode[...] representation. *)
ghostModesFromOffsets[bGhostModeOffsets_List, cGhostModeOffsets_List] :=
  Join[
    mode[b, modeNumberFromOffset[-2, #]] & /@ bGhostModeOffsets,
    mode[c, modeNumberFromOffset[1, #]] & /@ cGhostModeOffsets
  ];

(* Shared b/c ghost-sector enumerator (holomorphic).
   Output shape: {ghostModes, ghostWeight}. *)
generateGhostConfigsHolo[maxHolomorphicWeight_Integer, ghostNumber_Integer] /;
    maxHolomorphicWeight < minGhostWeightForGhostNumberBosonic[ghostNumber] := {};
generateGhostConfigsHolo[maxHolomorphicWeight_Integer, ghostNumber_Integer] :=
  generateGhostConfigsHolo[maxHolomorphicWeight, ghostNumber] = Module[
    {minBGhostCount, maxBGhostCount, collectedConfigs},
    minBGhostCount = Max[0, -ghostNumber];
    maxBGhostCount = maxBCountForGhostNumber[ghostNumber, maxHolomorphicWeight];
    If[maxBGhostCount < minBGhostCount,
      {},
      collectedConfigs = Reap[
        Do[
          Module[
            {cGhostCount, minCGhostWeight, bGhostConfigs},
            cGhostCount = ghostNumber + bGhostCount;
            minCGhostWeight = -cGhostCount + minDistinctModeSum[cGhostCount, 0];
            bGhostConfigs = fermionicConfigsByMaxWeight[2, bGhostCount, maxHolomorphicWeight - minCGhostWeight];
            Scan[
              Function[bGhostConfig,
                Module[{bGhostModeOffsets, bGhostWeight, cGhostConfigs},
                  {bGhostModeOffsets, bGhostWeight} = bGhostConfig;
                  cGhostConfigs = fermionicConfigsByMaxWeight[-1, cGhostCount, maxHolomorphicWeight - bGhostWeight];
                  Scan[
                    Function[cGhostConfig,
                      Module[{cGhostModeOffsets, cGhostWeight},
                        {cGhostModeOffsets, cGhostWeight} = cGhostConfig;
                        Sow[{
                          ghostModesFromOffsets[bGhostModeOffsets, cGhostModeOffsets],
                          bGhostWeight + cGhostWeight
                        }]
                      ]
                    ],
                    cGhostConfigs
                  ]
                ]
              ],
              bGhostConfigs
            ]
          ],
          {bGhostCount, minBGhostCount, maxBGhostCount}
        ]
      ][[2]];
      If[collectedConfigs === {}, {}, collectedConfigs[[1]]]
    ]
  ];

generateGhostConfigsHolo[_, _] := {};

(* Shared helper: translate b/c ghost modes to local-operator form. *)
ghostModeToOperatorField[mode[b, modeNumber_Integer], z_] :=
  b[-2 - modeNumber, z];
ghostModeToOperatorField[mode[c, modeNumber_Integer], z_] :=
  c[1 - modeNumber, z];

(* Shared helper: build holomorphic ghost factors from mode[...] lists. *)
ghostModesToOperatorFields[ghostModes_List, z_] :=
  ghostModeToOperatorField[#, z] & /@ ghostModes;


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
