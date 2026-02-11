(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`BasisGeneration`Bosonic`"];


Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`Bosonic`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`Bosonic`"];


(* ::Section:: *)
(*Declare public variables and methods*)

generateBasisHolo::usage =
  "generateBasisHolo[weight, ghostNumber, z:0] generates holomorphic bosonic local operators.";

generateBasisAntiHolo::usage =
  "generateBasisAntiHolo[weight, ghostNumber, zbar:0] generates antiholomorphic bosonic local operators.";

generateBasis::usage =
  "generateBasis[weight, ghostNumber, z:0, zbar:0] generates full bosonic local operators from holomorphic and antiholomorphic sectors.";


(* ::Section:: *)
(*Logic*)


(* ::Input::Initialization:: *)
Begin["Private`"];

(* Utility: minimal sum of k distinct integer modes >= minMode.
   Example: k=3, minMode=0 gives 0+1+2 = 3. *)
minDistinctModeSum[k_Integer?NonNegative, minMode_Integer?NonNegative] :=
  Quotient[k (2 minMode + k - 1), 2];

(* Enumerate strictly increasing mode lists of fixed length and exact sum.
   The recursion is memoized and prunes branches using minDistinctModeSum. *)
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

(* Minimal ghost contribution for fixed counts:
   b contributes 2 + modeOffset, c contributes -1 + modeOffset,
   where modeOffset runs over distinct nonnegative integers. *)
minGhostWeightForGhostCounts[bGhostCount_Integer?NonNegative, cGhostCount_Integer?NonNegative] :=
  2 bGhostCount + minDistinctModeSum[bGhostCount, 0] - cGhostCount + minDistinctModeSum[cGhostCount, 0];

(* Closed-form lower bound on holomorphic ghost weight at fixed ghost number. *)
minGhostWeightForGhostNumberBosonic[ghostNumber_Integer] :=
  Quotient[ghostNumber (ghostNumber - 3), 2];

(* Upper bound for number of b ghosts compatible with (ghostNumber, maxHolomorphicWeight).
   We scan upward from the minimal feasible b-ghost count until the lower bound exceeds maxHolomorphicWeight. *)
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

(* All fermionic mode configurations with fixed count and total weight <= maxWeight.
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

(* Map nonnegative mode offset to oscillator mode number:
   modeNumber = minimalModeNumber - modeOffset. *)
modeNumberFromOffset[minimalModeNumber_Integer, modeOffset_Integer?NonNegative] :=
  minimalModeNumber - modeOffset;

(* Convert ghost mode-offset data to mode[...] representation. *)
ghostModesFromOffsets[bGhostModeOffsets_List, cGhostModeOffsets_List] :=
  Join[
    mode[b, modeNumberFromOffset[-2, #]] & /@ bGhostModeOffsets,
    mode[c, modeNumberFromOffset[1, #]] & /@ cGhostModeOffsets
  ];

(* Main ghost-sector enumerator for the holomorphic side.
   Output shape: {ghostModes, ghostWeight}, where ghostModes are mode[...] objects. *)
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
            (* For fixed c-ghost count, compute a tight lower bound on c contribution
               so we only enumerate b-configs that can still fit in maxHolomorphicWeight. *)
            minCGhostWeight = -cGhostCount + minDistinctModeSum[cGhostCount, 0];
            bGhostConfigs = fermionicConfigsByMaxWeight[2, bGhostCount, maxHolomorphicWeight - minCGhostWeight];
            Scan[
              Function[bGhostConfig,
                Module[{bGhostModeOffsets, bGhostWeight, cGhostConfigs},
                  {bGhostModeOffsets, bGhostWeight} = bGhostConfig;
                  (* Given b weight, enumerate c-configs with remaining budget. *)
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

(* Translate one ghost mode to local-operator form.
   For b and c, the second operator argument is recovered directly from modeNumber. *)
ghostModeToOperatorField[mode[b, modeNumber_Integer], z_] :=
  b[-2 - modeNumber, z];
ghostModeToOperatorField[mode[c, modeNumber_Integer], z_] :=
  c[1 - modeNumber, z];

(* Build holomorphic ghost factors from mode[...] lists.
   Kept in Bosonic core so b/c-system details stay out of CFT-specific modules. *)
ghostModesToOperatorFields[ghostModes_List, z_] :=
  ghostModeToOperatorField[#, z] & /@ ghostModes;


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
