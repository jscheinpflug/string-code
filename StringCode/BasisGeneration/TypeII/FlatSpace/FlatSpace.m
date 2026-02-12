(* ::Package:: *)

(* ::Section:: *)
(*Init*)

(*
  TypeII FlatSpace Basis Generation
  =================================

  Generates basis states for Type II superstring theory in flat spacetime.

  The basis consists of states built from:
  - b/c ghost system (conformal weights 2, -1)
  - β/γ superghost system (conformal weights 3/2, -1/2 at picture 0)
  - ψ worldsheet fermions (conformal weight 1/2 in NS sector)
  - ∂X bosonic oscillators (conformal weight 1)

  States are organized by:
  - Total conformal weight (h + h̄ for closed strings)
  - Ghost number (b/c contribute ∓1, β/γ contribute ∓1)
  - Picture number (shifted by β/γ zero modes)
  - GSO parity (worldsheet fermion number mod 2)

  Output format:
  - Holomorphic: {picture, {mode[field, n], ...}}
  - Closed string: {{pictureL, pictureR}, {modeList, ...}}
*)

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
(* SECTION 1: VALIDATION & PICTURE HANDLING                     *)
(* ============================================================ *)
(*
  Picture numbers in Type II can be:
  - Integer q: NS sector (fermions have half-integer modes)
  - Half-integer q: R sector (fermions have integer modes)

  For half-integer pictures, we must also specify chirality
  ("chiral" or "antichiral") to determine the GSO projection.

  A "picture spec" is either:
  - An integer q (NS sector)
  - A pair {q, chirality} where q is half-integer (R sector)
*)

(* Test if x is a half-integer (n + 1/2 for some integer n) *)
halfIntegerQ[x_] := IntegerQ[2 x] && OddQ[2 x];

(* Valid chirality values for Ramond sector *)
validChiralityQ[chirality_] := MemberQ[{"chiral", "antichiral"}, chirality];

(* User-facing picture input: integer or half-integer *)
validPictureInputQ[picture_] := IntegerQ[picture] || halfIntegerQ[picture];

(* Internal picture spec: integer, or {half-integer, chirality} *)
validPictureSpecQ[picture_] :=
  IntegerQ[picture] ||
    MatchQ[picture, {q_ /; halfIntegerQ[q], chirality_ /; validChiralityQ[chirality]}];

(* Expand user input to internal specs.
   Half-integer pictures expand to both chiralities. *)
expandPictureSpecs[picture_Integer] := {picture};
expandPictureSpecs[picture_ /; halfIntegerQ[picture]] :=
  {{picture, "chiral"}, {picture, "antichiral"}};

(* Extract numeric picture value from spec *)
pictureValue[picture_Integer] := picture;
pictureValue[{picture_ /; halfIntegerQ[picture], chirality_ /; validChiralityQ[chirality]}] :=
  picture;

(* Extract chirality from spec (None for NS sector) *)
pictureChirality[picture_Integer] := None;
pictureChirality[{picture_ /; halfIntegerQ[picture], chirality_ /; validChiralityQ[chirality]}] :=
  chirality;

(* Valid weight: non-negative, half-integer allowed *)
validWeightQ[weight_] := NumericQ[weight] && weight >= 0 && IntegerQ[2 weight];

(* Conformal weight of the picture-q ground state |q⟩.
   NS sector (integer q): h = -q(q+2)/2
   R sector (half-integer q): h = 5/8 - q(q+2)/2  (includes R ground state weight) *)
groundStateWeight[picture_?validPictureSpecQ] := Module[{q},
  q = pictureValue[picture];
  If[IntegerQ[q],
    -1/2 q (q + 2),
    5/8 - 1/2 q (q + 2)
  ]
];

(* GSO parity of the picture-q ground state.
   NS sector: (-1)^q
   R sector: (-1)^(q+1/2) with sign flip for antichiral *)
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
(*
  To efficiently enumerate basis states, we compute lower bounds
  on conformal weight for given ghost numbers. This allows pruning
  impossible configurations early.

  Ghost number splits:
  - Total ghost number = bc ghost number + superghost number
  - Each sector has a minimum weight contribution

  The b/c system bounds come from BasisGeneration.m (Bosonic).
  The β/γ bounds depend on picture number.
*)

(* Minimum superghost weight for given superghost number at picture q.
   At picture q:
   - β modes have weight ≥ 3/2 + q (creation modes: r ≤ -3/2 - q)
   - γ modes have weight ≥ -1/2 - q (creation modes: r ≤ 1/2 + q)
   For positive superghost number: use γ modes (cheaper)
   For negative superghost number: use β modes *)
minSuperghostWeightForGhostNumber[ghostNumber_Integer, picture_?validPictureSpecQ] := Module[{q},
  q = pictureValue[picture];
  If[
    ghostNumber >= 0,
    -(1/2 + q) ghostNumber,   (* γ modes contribute -(1/2+q) each *)
    -(3/2 + q) ghostNumber    (* β modes contribute (3/2+q) each, but ghostNumber < 0 *)
  ]
];
minSuperghostWeightForGhostNumber[ghostNumber_Integer] :=
  minSuperghostWeightForGhostNumber[ghostNumber, 0];

(* Total ghost weight at a specific bc/superghost split *)
ghostWeightAtSplit[
  totalGhostNumber_Integer,
  bcGhostNumber_Integer,
  picture_?validPictureSpecQ
] :=
  minGhostWeightForGhostNumberBosonic[bcGhostNumber] +
    minSuperghostWeightForGhostNumber[totalGhostNumber - bcGhostNumber, picture];

(* Minimum ghost weight over all possible bc/superghost splits.
   The optimal split depends on picture q:
   - The bc weight is a piecewise quadratic in bcGhostNumber
   - The superghost weight is linear with slope depending on sign
   We check candidate vertices of the piecewise function. *)
minTypeIIGhostWeightForGhostNumber[ghostNumber_Integer, picture_?validPictureSpecQ] := Module[
  {q, case1Vertex, case2Vertex, case1Candidates, case2Candidates, values},
  q = pictureValue[picture];
  (* Vertices where slope changes in the combined weight function *)
  case1Vertex = 1 - q;
  case2Vertex = -q;
  (* Candidates for bcGhostNumber ≤ ghostNumber (positive superghost) *)
  case1Candidates = Select[
    DeleteDuplicates[{Floor[case1Vertex], Ceiling[case1Vertex], ghostNumber}],
    # <= ghostNumber &
  ];
  (* Candidates for bcGhostNumber > ghostNumber (negative superghost) *)
  case2Candidates = Select[
    DeleteDuplicates[{Floor[case2Vertex], Ceiling[case2Vertex], ghostNumber + 1}],
    # >= ghostNumber + 1 &
  ];
  values = Join[
    ghostWeightAtSplit[ghostNumber, #, picture] & /@ case1Candidates,
    ghostWeightAtSplit[ghostNumber, #, picture] & /@ case2Candidates
  ];
  Min[values]
];
minTypeIIGhostWeightForGhostNumber[ghostNumber_Integer] :=
  minTypeIIGhostWeightForGhostNumber[ghostNumber, 0];

(* Minimum total sector weight = ground state + minimum ghost weight *)
minSectorWeightForGhostAndPicture[ghostNumber_Integer, picture_?validPictureSpecQ] :=
  groundStateWeight[picture] + minTypeIIGhostWeightForGhostNumber[ghostNumber, picture];

(* Find contiguous range of integers where splitFeasibleQ returns True.
   Searches outward from center, then expands to find full range.
   Returns {} if no feasible split exists. *)
findFeasibleSplitRange[splitFeasibleQ_, center_Integer, maxRadius_Integer?Positive] := Module[
  {seed = Missing["NotFound"], radius = 0, candidates, minSplit, maxSplit},
  (* Find first feasible split by expanding from center *)
  While[radius <= maxRadius && MissingQ[seed],
    candidates = DeleteDuplicates[{center - radius, center + radius}];
    seed = SelectFirst[candidates, splitFeasibleQ, Missing["NotFound"]];
    radius++;
  ];
  If[MissingQ[seed],
    Return[{}]
  ];
  (* Expand to find full feasible range *)
  minSplit = seed;
  maxSplit = seed;
  While[splitFeasibleQ[minSplit - 1], minSplit--];
  While[splitFeasibleQ[maxSplit + 1], maxSplit++];
  Range[minSplit, maxSplit]
];

(* Find feasible bc ghost number splits for holomorphic sector.
   A split is feasible if bc + superghost minimum weight ≤ maxWeight. *)
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

(* Find feasible holomorphic ghost number splits for closed string.
   A split is feasible if both sectors can be realized within total weight. *)
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
(*
  Generate all possible mode configurations for each field type
  that fit within a given weight budget.

  Output format: List of {modeList, totalWeight} pairs
  - modeList: {mode[field, n], ...} where n is the mode number
  - totalWeight: sum of -n for all modes (contribution to h)

  Mode representation:
  - mode[β, n]: β superghost with mode number n
  - mode[γ, n]: γ superghost with mode number n
  - mode[ψ[μ], n]: worldsheet fermion with Lorentz index μ
  - mode[dX[μ], n]: ∂X oscillator with Lorentz index μ

  β/γ are bosonic (modes can repeat), ψ is fermionic (modes distinct).
*)

(* Convert offset lists to superghost mode objects.
   At picture q:
   - β creation modes: n = -3/2 - q - offset (offset ≥ 0)
   - γ creation modes: n = 1/2 + q - offset (offset ≥ 0) *)
generateSuperghostModes[betaOffsets_List, gammaOffsets_List, picture_?validPictureSpecQ] := Module[
  {q},
  q = pictureValue[picture];
  Join[
    mode[\[Beta], -3/2 - q - #] & /@ betaOffsets,
    mode[\[Gamma], 1/2 + q - #] & /@ gammaOffsets
  ]
];

(* Compute remaining offset budget after fixing β/γ counts.
   Returns -1 if configuration is impossible. *)
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
  (* Minimum weight = sum of base weights for all modes *)
  minWeight = betaCount - (1/2 + q) superghostNumber;
  If[minWeight > maxWeight, -1, Floor[maxWeight - minWeight]]
];

(* Enumerate all β/γ offset combinations for fixed counts.
   β/γ are bosonic: use bosonicModesByExactSum (allows repeats). *)
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
    (* Iterate over total offset sums for β and γ *)
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
        (* Cartesian product of β and γ configurations *)
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

(* Generate all superghost configurations with given ghost number and max weight.
   Iterates over possible β counts (γ count = β count + superghost number).
   Results are memoized for efficiency. *)
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
    (* β count bounds from ghost number and weight constraints *)
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

(* Convert integer partition to ∂X mode objects.
   Each part p becomes mode[dX[μ], -p] with fresh Lorentz index μ. *)
generateDXModes[matterPartition_List] := Module[{makeMatterMode},
  makeMatterMode[partWeight_Integer] := Module[{mu},
    mode[dX[mu], -partWeight]
  ];
  makeMatterMode /@ matterPartition
];

(* All ∂X configurations at fixed weight = integer partitions.
   ∂X has weight 1, so IntegerPartitions gives all combinations. *)
generateDXModeConfigs[targetWeight_Integer?NonNegative] :=
  generateDXModeConfigs[targetWeight] = Module[{partitions},
    partitions = If[targetWeight == 0, {{}}, IntegerPartitions[targetWeight]];
    generateDXModes /@ partitions
  ];

(* ψ base weight depends on sector:
   NS (integer picture): ψ has weight 1/2, modes at -1/2, -3/2, ...
   R (half-integer picture): ψ has weight 0, modes at -1, -2, ... *)
psiBaseWeight[picture_?validPictureSpecQ] := If[IntegerQ[pictureValue[picture]], 1/2, 0];
psiMinOffset[picture_?validPictureSpecQ] := If[IntegerQ[pictureValue[picture]], 0, 1];

(* Convert offset list to ψ mode objects *)
generatePsiModes[offsets_List, picture_?validPictureSpecQ] := Module[
  {baseWeight, makePsiMode},
  baseWeight = psiBaseWeight[picture];
  makePsiMode[offset_Integer?NonNegative] := Module[{mu},
    mode[\[Psi][mu], -baseWeight - offset]
  ];
  makePsiMode /@ offsets
];

(* Generate all ψ configurations up to target weight.
   ψ is fermionic: use distinctModesByExactSum (no repeats).
   Returns {modeList, weight} pairs. *)
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
      (* Iterate over number of ψ modes *)
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

(* Generate all matter (ψ + ∂X) configurations at target weight.
   Combines ψ configs with ∂X configs for remaining weight. *)
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
            (* Combine each ∂X config with this ψ config *)
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
(*
  Utility functions for working with mode[field, n] objects.

  These compute:
  - Conformal weight contribution: -n for mode[_, n]
  - Ghost number contribution: ±1 for b/c/β/γ, 0 for matter
  - GSO parity contribution: -1 for worldsheet fermions (ψ, β, γ)

  Also handles:
  - Lorentz index canonicalization (μ → μ1, μ2, ...)
  - Holomorphic → antiholomorphic conversion (b → b̃, etc.)
*)

(* Rename Lorentz indices to canonical form μ1, μ2, ...
   Ensures consistent ordering for duplicate detection. *)
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

(* Extract field type from mode object.
   mode[b, n] → b, mode[ψ[μ], n] → ψ *)
modeSpecies[mode[head_, _]] := If[AtomQ[head], head, Head[head]];

(* Conformal weight contribution: mode with number n contributes -n *)
modeWeightContribution[mode[_, modeNumber_]] := -modeNumber;

(* Ghost number contribution:
   b, b̃, β, β̃ → -1 (lower ghost number)
   c, c̃, γ, γ̃ → +1 (raise ghost number)
   matter → 0 *)
modeGhostContribution[modeObj : mode[_, _]] := Switch[
  modeSpecies[modeObj],
  b | bt | \[Beta] | \[Beta]t, -1,
  c | ct | \[Gamma] | \[Gamma]t, 1,
  _, 0
];

(* GSO parity contribution:
   Worldsheet fermions (ψ, β, γ) contribute -1
   Bosons (b, c, ∂X) contribute +1 *)
modeGSOParityContribution[modeObj : mode[_, _]] :=
  If[
    MemberQ[{\[Psi], \[Psi]t, \[Beta], \[Beta]t, \[Gamma], \[Gamma]t}, modeSpecies[modeObj]],
    -1,
    1
  ];

(* Sum ghost contributions over all modes in list *)
modeListGhostNumber[modeList_List] :=
  Total[modeGhostContribution /@ Cases[modeList, mode[_, _], Infinity]];

(* Sum weight contributions over all modes in list *)
modeListWeight[modeList_List] :=
  Total[modeWeightContribution /@ Cases[modeList, mode[_, _], Infinity]];

(* Total GSO parity = ground state parity × product of mode parities *)
gsoParityOfConfig[modeList_List, picture_?validPictureSpecQ] :=
  gsoParityOfGroundState[picture] *
    Times @@ (modeGSOParityContribution /@ Cases[modeList, mode[_, _], Infinity]);

(* Assemble holomorphic state from component mode lists.
   Returns {picture, canonicalized mode list}. *)
buildHoloState[picture_?validPictureSpecQ, bcModes_List, superghostModes_List, matterModes_List] :=
  Module[{modeList},
    modeList = canonicalizeLorentzIndicesModes[
      Join[bcModes, superghostModes, matterModes]
    ];
    {picture, modeList}
  ];

(* Convert holomorphic mode to antiholomorphic counterpart.
   b → b̃, c → c̃, β → β̃, γ → γ̃, ∂X → ∂̄X, ψ → ψ̃ *)
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
(*
  Closed string states are tensor products of left (holomorphic) and
  right (antiholomorphic) sectors.

  Parameters:
  - Total weight = h + h̄
  - Ghost number = ghost_L + ghost_R
  - Pictures = {picture_L, picture_R}

  Options:
  - "LevelMatched" -> True: enforce h = h̄ (physical states)
  - "GSOProjected" -> True: keep only GSO-even states

  Output: {{picture_L, picture_R}, {state1, state2, ...}}
  where each state is a joined mode list (holo modes ++ anti modes)
*)

(* Parse "GSOProjected" option, default True *)
parseGSOOption[opts___] := Module[{optionList, GSOProjected},
  optionList = Flatten[{opts}];
  If[!OptionQ[optionList],
    Return[$Failed]
  ];
  GSOProjected = readBooleanOption[optionList, "GSOProjected", True];
  If[GSOProjected === $Failed, $Failed, GSOProjected]
];

(* Parse both "LevelMatched" and "GSOProjected" options *)
parseFullBasisOptions[opts___] := Module[
  {optionList, levelMatched, GSOProjected},
  optionList = Flatten[{opts}];
  If[!OptionQ[optionList],
    Return[$Failed]
  ];
  levelMatched = readBooleanOption[optionList, "LevelMatched", True];
  GSOProjected = readBooleanOption[optionList, "GSOProjected", True];
  If[levelMatched === $Failed || GSOProjected === $Failed,
    $Failed,
    {levelMatched, GSOProjected}
  ]
];

(* Cartesian product of holo and anti bases.
   Each result is the concatenation of holo and anti mode lists. *)
combineHoloAntiStates[holoBasis_List, antiBasis_List] :=
  Flatten[
    Table[
      Join[holoTuple[[2]], antiTuple[[2]]],
      {holoTuple, holoBasis},
      {antiTuple, antiBasis}
    ],
    1
  ];

(* Generate all closed string states for given sector parameters.
   Combines holomorphic and antiholomorphic bases. *)
generateJoinedSectorStates[
  holoWeight_,
  holoGhostNumber_Integer,
  pictureLeft_?validPictureSpecQ,
  antiWeight_,
  antiGhostNumber_Integer,
  pictureRight_?validPictureSpecQ,
  GSOProjected_
] := Module[{holoBasis, antiBasis},
  holoBasis = generateBasisHoloForPictureSpec[
    holoWeight,
    holoGhostNumber,
    pictureLeft,
    "GSOProjected" -> GSOProjected
  ];
  If[holoBasis === {},
    Return[{}]
  ];
  antiBasis = generateBasisAntiHoloForPictureSpec[
    antiWeight,
    antiGhostNumber,
    pictureRight,
    "GSOProjected" -> GSOProjected
  ];
  If[antiBasis === {},
    Return[{}]
  ];
  combineHoloAntiStates[holoBasis, antiBasis]
];

(* Collect states with level matching: h = h̄ = weight/2.
   Iterates over ghost number splits between sectors. *)
collectLevelMatchedStates[
  weight_?validWeightQ,
  ghostNumber_Integer,
  pictureLeft_?validPictureSpecQ,
  pictureRight_?validPictureSpecQ,
  GSOProjected_,
  holoGhostSplits_List
] := Module[
  {sectorWeight, collectedStates, antiGhostNumber, joinedStates},
  sectorWeight = weight/2;
  collectedStates = Reap[
    Do[
      antiGhostNumber = ghostNumber - holoGhostNumber;
      (* Skip if either sector can't achieve required weight *)
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
        GSOProjected
      ];
      Do[Sow[joinedState], {joinedState, joinedStates}],
      {holoGhostNumber, holoGhostSplits}
    ]
  ][[2]];
  If[collectedStates === {}, {}, collectedStates[[1]]]
];

(* Collect states without level matching: all valid h + h̄ = weight splits.
   Iterates over both ghost number and weight splits. *)
collectAllSplitStates[
  weight_?validWeightQ,
  ghostNumber_Integer,
  pictureLeft_?validPictureSpecQ,
  pictureRight_?validPictureSpecQ,
  GSOProjected_,
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
      (* Compute feasible holomorphic weight range *)
      minHoloWeight = minSectorWeightForGhostAndPicture[holoGhostNumber, pictureLeft];
      maxHoloWeight =
        weight - minSectorWeightForGhostAndPicture[antiGhostNumber, pictureRight];
      If[maxHoloWeight < minHoloWeight,
        Continue[]
      ];
      (* Iterate over half-integer weight values *)
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
          GSOProjected
        ];
        Do[Sow[joinedState], {joinedState, joinedStates}],
        {holoWeight2, minHoloWeight2, maxHoloWeight2}
      ],
      {holoGhostNumber, holoGhostSplits}
    ]
  ][[2]];
  If[collectedStates === {}, {}, collectedStates[[1]]]
];

(* Format final output: {pictures, deduplicated states} *)
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
(*
  Core holomorphic basis enumeration.

  Strategy:
  1. Subtract ground state weight to get "remaining weight" budget
  2. Split ghost number between b/c and β/γ systems
  3. For each split, enumerate bc configs, then superghost configs
  4. Fill remaining weight with matter (ψ + ∂X)
  5. Validate ghost number, weight, and GSO parity
  6. Return {picture, mode list} tuples

  The enumeration is structured as nested loops:
  - bc ghost split → bc configs → superghost configs → matter configs
*)

(* Innermost loop: enumerate matter configs that complete a valid state.
   Validates ghost number, weight, and GSO projection. *)
enumerateMatterAtRemainingWeight[
  bcModes_List,
  bcWeight_,
  superghostModes_List,
  superghostWeight_,
  remainingWeight_,
  picture_?validPictureSpecQ,
  ghostNumber_Integer,
  GSOProjected_
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
      (* Validate total ghost number *)
      If[modeListGhostNumber[candidateModes] =!= ghostNumber,
        Continue[]
      ];
      (* Validate total weight (should match by construction, but check) *)
      If[groundWeight + modeListWeight[candidateModes] =!= remainingWeight + groundWeight,
        Continue[]
      ];
      (* Apply GSO projection if requested *)
      candidateParity = gsoParityOfConfig[candidateModes, picture];
      If[(!TrueQ[GSOProjected]) || candidateParity === 1,
        Sow[candidateState]
      ],
      {matterModes, matterModeConfigs}
    ]
  ][[2]];
  If[collectedTuples === {}, {}, collectedTuples[[1]]]
];

(* Middle loop: for fixed bc ghost number, enumerate all bc + superghost + matter combinations. *)
enumerateAtBcGhostSplit[
  bcGhostNumber_Integer,
  ghostNumber_Integer,
  remainingWeight_,
  picture_?validPictureSpecQ,
  GSOProjected_
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
  (* bc can use at most (remaining - min superghost) weight *)
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
        (* Delegate to matter enumeration *)
        matterTuples = enumerateMatterAtRemainingWeight[
          bcModes,
          bcWeight,
          superghostModes,
          superghostWeight,
          remainingWeight,
          picture,
          ghostNumber,
          GSOProjected
        ];
        Do[Sow[matterTuple], {matterTuple, matterTuples}],
        {superghostConfig, superghostConfigs}
      ],
      {bcConfig, bcConfigs}
    ]
  ][[2]];
  If[collectedTuples === {}, {}, collectedTuples[[1]]]
];

(* Main holomorphic basis generator for a specific picture spec.
   Outer loop iterates over bc/superghost ghost number splits. *)
generateBasisHoloForPictureSpec[
  weight_?validWeightQ,
  ghostNumber_Integer,
  picture_?validPictureSpecQ,
  opts___
] := Module[
  {
    GSOProjected,
    groundWeight,
    remainingWeight,
    bcGhostSplits,
    collectedTuples,
    basisTuples,
    bcGhostNumber,
    splitTuples,
    splitTuple
  },
  GSOProjected = parseGSOOption[opts];
  If[GSOProjected === $Failed,
    Return[{}]
  ];
  groundWeight = groundStateWeight[picture];
  remainingWeight = weight - groundWeight;
  (* Weight above ground state must be half-integer *)
  If[!IntegerQ[2 remainingWeight],
    Return[{}]
  ];
  (* Find feasible bc ghost number splits *)
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
        GSOProjected
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
(*
  Antiholomorphic basis is obtained by:
  1. Generate holomorphic basis
  2. Replace all modes with their antiholomorphic counterparts
     (b → b̃, c → c̃, β → β̃, γ → γ̃, ∂X → ∂̄X, ψ → ψ̃)
*)

generateBasisAntiHoloForPictureSpec[
  weight_?validWeightQ,
  ghostNumber_Integer,
  picture_?validPictureSpecQ,
  opts___
] := Module[{GSOProjected, holoBasis},
  GSOProjected = parseGSOOption[opts];
  If[GSOProjected === $Failed,
    Return[{}]
  ];
  holoBasis = generateBasisHoloForPictureSpec[
    weight,
    ghostNumber,
    picture,
    "GSOProjected" -> GSOProjected
  ];
  (* Map each holo state to its anti counterpart *)
  ({#[[1]], antiModeFromHolo /@ #[[2]]} &) /@ holoBasis
];

generateBasisAntiHoloForPictureSpec[___] := {};

(* ============================================================ *)
(* SECTION 8: CLOSED STRING BASIS ASSEMBLY                      *)
(* ============================================================ *)
(*
  Assemble closed string basis for specific picture specs.
  Dispatches to level-matched or all-splits collection based on options.
*)

generateBasisForPictureSpecs[
  weight_?validWeightQ,
  ghostNumber_Integer,
  pictures : {pictureLeft_?validPictureSpecQ, pictureRight_?validPictureSpecQ},
  opts___
] := Module[
  {
    parsedOptions,
    levelMatched,
    GSOProjected,
    holoGhostSplits,
    basisStates
  },
  parsedOptions = parseFullBasisOptions[opts];
  If[parsedOptions === $Failed,
    Return[{}]
  ];
  {levelMatched, GSOProjected} = parsedOptions;
  (* Level matching requires even total weight (h = h̄ = weight/2) *)
  If[TrueQ[levelMatched] && OddQ[2 weight],
    Return[{}]
  ];
  (* Find feasible ghost number splits between sectors *)
  holoGhostSplits = ghostSplitRangeClosedString[
    ghostNumber,
    weight,
    pictureLeft,
    pictureRight
  ];
  If[holoGhostSplits === {},
    Return[{}]
  ];
  (* Dispatch to appropriate collection strategy *)
  basisStates = If[TrueQ[levelMatched],
    collectLevelMatchedStates[
      weight,
      ghostNumber,
      pictureLeft,
      pictureRight,
      GSOProjected,
      holoGhostSplits
    ],
    collectAllSplitStates[
      weight,
      ghostNumber,
      pictureLeft,
      pictureRight,
      GSOProjected,
      holoGhostSplits
    ]
  ];
  formatBasisResult[pictures, basisStates]
];

generateBasisForPictureSpecs[___] := {};

(* ============================================================ *)
(* SECTION 9: PUBLIC API                                        *)
(* ============================================================ *)
(*
  User-facing functions that handle picture expansion.

  For half-integer pictures (Ramond sector), the user specifies just the
  picture number, and we automatically enumerate both chiralities.

  generateBasisHolo[weight, ghostNumber, picture, opts]
    Generate holomorphic basis states.
    Returns: {{picture, modeList}, ...}

  generateBasisAntiHolo[weight, ghostNumber, picture, opts]
    Generate antiholomorphic basis states.
    Returns: {{picture, modeList}, ...}

  generateBasis[weight, ghostNumber, {pictureL, pictureR}, opts]
    Generate closed string basis states.
    Options:
      "LevelMatched" -> True (default): enforce h = h̄
      "GSOProjected" -> True (default): keep only GSO-even states
    Returns: {{pictureL, pictureR}, {state1, state2, ...}}
*)

generateBasisHolo[
  weight_?validWeightQ,
  ghostNumber_Integer,
  picture_?validPictureInputQ,
  opts___
] := Module[{basisBySpec},
  (* Expand picture to specs (handles chirality for Ramond) *)
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
  (* Expand both pictures to handle Ramond chiralities *)
  leftSpecs = expandPictureSpecs[pictureLeft];
  rightSpecs = expandPictureSpecs[pictureRight];
  (* Generate basis for all combinations of expanded specs *)
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
  (* Format output: single result if no expansion, list otherwise *)
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
