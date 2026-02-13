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

(* Shared field-mode helper tables for basis enumeration internals. *)
$basisGhostContributionFallback = <|
  "b" -> -1, "bt" -> -1,
  "c" -> 1, "ct" -> 1
|>;

$basisAntiSpeciesMap = <|
  "b" -> "bt", "bt" -> "b",
  "c" -> "ct", "ct" -> "c"
|>;

basisModeSpecies::usage = "Extracts the species symbol from mode[fieldHead, n].";
basisModeSpecies[mode[head_, _]] := If[AtomQ[head], head, Head[head]];

basisSpeciesName::usage = "Returns symbol name for a species symbol.";
basisSpeciesName[symbol_Symbol] := SymbolName[symbol];

basisGhostContribution::usage = "Returns ghost number contribution of one oscillator species.";
basisGhostContribution[symbol_Symbol] := basisGhostContribution[symbol] = Module[{ghostNumber},
  ghostNumber = fieldProperty[symbol, "GhostNumber"];
  If[NumericQ[ghostNumber],
    ghostNumber,
    Lookup[$basisGhostContributionFallback, basisSpeciesName[symbol], 0]
  ]
];

basisGhostContributionFromMode::usage = "Returns ghost number contribution of one mode[field, n].";
basisGhostContributionFromMode[modeObj : mode[_, _]] :=
  basisGhostContribution[basisModeSpecies[modeObj]];

basisModeGSOParity::usage = "Returns GSO parity contribution of one oscillator species.";
basisModeGSOParity[symbol_Symbol] := basisModeGSOParity[symbol] = Module[
  {holoParity, antiHoloParity},
  holoParity = fieldProperty[symbol, "GSOParityHolo"];
  antiHoloParity = fieldProperty[symbol, "GSOParityAntiHolo"];
  Which[
    MemberQ[{-1}, holoParity] || MemberQ[{-1}, antiHoloParity], -1,
    MemberQ[{1}, holoParity] || MemberQ[{1}, antiHoloParity], 1,
    True, 1
  ]
];

basisModeGSOParityContribution::usage = "Returns GSO parity contribution of one mode[field, n].";
basisModeGSOParityContribution[modeObj : mode[_, _]] :=
  basisModeGSOParity[basisModeSpecies[modeObj]];

basisAntiSpecies::usage = "Returns antiholomorphic partner symbol for an oscillator species.";
basisAntiSpecies[symbol_Symbol] := Module[{name, antiName},
  name = basisSpeciesName[symbol];
  antiName = Lookup[$basisAntiSpeciesMap, name, name];
  If[antiName === name, symbol, Symbol[Context[symbol] <> antiName]]
];

basisMinModeNumberForSpecies::usage = "Returns maximal creation mode number n0 for a species (modes are n0 - offset).";
basisMinModeNumberForSpecies[symbol_Symbol] := Module[{name},
  name = basisSpeciesName[symbol];
  Switch[name,
    "b" | "bt", -2,
    "c" | "ct", 1,
    _, 0
  ]
];

basisModeNumberFromOffset::usage = "Converts nonnegative offset to oscillator mode number for a species.";
basisModeNumberFromOffset[symbol_Symbol, modeOffset_Integer?NonNegative] :=
  basisMinModeNumberForSpecies[symbol] - modeOffset;

basisAntiModeFromHolo::usage = "Converts a holomorphic mode[...] object to its antiholomorphic counterpart.";
basisAntiModeFromHolo[mode[head_, modeNumber_]] := Module[
  {species, antiSpecies, antiHead},
  species = basisModeSpecies[mode[head, modeNumber]];
  antiSpecies = basisAntiSpecies[species];
  If[antiSpecies === species,
    Return[mode[head, modeNumber]]
  ];
  antiHead = If[AtomQ[head], antiSpecies, antiSpecies @@ (List @@ head)];
  mode[antiHead, modeNumber]
];

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

(* Shared helper: convert b/c mode offsets to mode[...] representation. *)
ghostModesFromOffsets[bGhostModeOffsets_List, cGhostModeOffsets_List] :=
  Join[
    mode[b, basisModeNumberFromOffset[b, #]] & /@ bGhostModeOffsets,
    mode[c, basisModeNumberFromOffset[c, #]] & /@ cGhostModeOffsets
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
  b[basisMinModeNumberForSpecies[b] - modeNumber, z];
ghostModeToOperatorField[mode[c, modeNumber_Integer], z_] :=
  c[basisMinModeNumberForSpecies[c] - modeNumber, z];

(* Shared helper: build holomorphic ghost factors from mode[...] lists. *)
ghostModesToOperatorFields[ghostModes_List, z_] :=
  ghostModeToOperatorField[#, z] & /@ ghostModes;


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
