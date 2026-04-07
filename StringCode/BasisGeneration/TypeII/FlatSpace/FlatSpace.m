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
  - Total conformal weight (h + h̄)
  - Ghost number (b/c contribute ∓1, β/γ contribute ∓1)
  - Picture number (shifted by β/γ zero modes)
  - GSO parity (worldsheet fermion number mod 2)

  Output format:
  - Holomorphic: {picture, {mode[field, n], ...}}
  - Both: {{pictureL, pictureR}, {modeList, ...}}
*)

BeginPackage["StringCode`BasisGeneration`TypeII`FlatSpace`"];


Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];
Needs["StringCode`Symbols`TypeII`FlatSpace`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`TypeII`"];
Needs["StringCode`BasisGeneration`"];
Needs["StringCode`BasisGeneration`TypeII`"];
Needs["StringCode`OPE`"];
Needs["StringCode`OPE`TypeII`"];
Needs["StringCode`Taylor`"];
Needs["StringCode`Taylor`TypeII`"];
Needs["StringCode`Taylor`TypeII`FlatSpace`"];

(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


(* ::Input::Initialization:: *)
Begin["Private`"];

$maxPsiPerLevel::usage =
  "Maximum number of ψ oscillators permitted at one mode level (equal to target-space dimension in flat TypeII).";
$maxPsiPerLevel = 10;

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
halfIntegerQ::usage = "Tests whether x is a half-integer (n + 1/2 for some integer n).";
halfIntegerQ[x_] := IntegerQ[2 x] && OddQ[2 x];

(* Valid chirality values for Ramond sector *)
validChiralityQ::usage = "Tests whether a chirality tag is valid (\"chiral\" or \"antichiral\").";
validChiralityQ[chirality_] := MemberQ[{"chiral", "antichiral"}, chirality];

(* User-facing picture input: integer or half-integer *)
validPictureInputQ::usage = "Tests whether a user-facing picture input is an integer or half-integer.";
validPictureInputQ[picture_] := IntegerQ[picture] || halfIntegerQ[picture];

(* Internal picture spec: integer, or {half-integer, chirality} *)
validPictureSpecQ::usage = "Tests whether a picture spec is an integer picture or a Ramond spec {q, chirality} with half-integer q.";
validPictureSpecQ[picture_] :=
  IntegerQ[picture] ||
    MatchQ[picture, {q_ /; halfIntegerQ[q], chirality_ /; validChiralityQ[chirality]}];

(* Expand user input to internal specs.
   Half-integer pictures expand to both chiralities. *)
expandPictureSpecs::usage = "Expands a picture input to a list of internal picture specs (half-integers expand to both chiralities).";
expandPictureSpecs[picture_Integer] := {picture};
expandPictureSpecs[picture_ /; halfIntegerQ[picture]] :=
  {{picture, "chiral"}, {picture, "antichiral"}};

(* Extract numeric picture value from spec *)
pictureValue::usage = "Extracts the numeric picture value q from a picture spec.";
pictureValue[picture_Integer] := picture;
pictureValue[{picture_ /; halfIntegerQ[picture], chirality_ /; validChiralityQ[chirality]}] :=
  picture;

(* Extract chirality from spec (None for NS sector) *)
pictureChirality::usage = "Extracts the chirality tag from a picture spec (None for integer pictures).";
pictureChirality[picture_Integer] := None;
pictureChirality[{picture_ /; halfIntegerQ[picture], chirality_ /; validChiralityQ[chirality]}] :=
  chirality;

(* Valid weight: integer or half-integer allowed, including negative picture-dressed ground states. *)
validWeightQ::usage = "Tests whether a conformal weight is integer or half-integer, allowing negative picture-dressed ground-state weights.";
validWeightQ[weight_] := NumericQ[weight] && IntegerQ[2 weight];

(* Conformal weight of the picture-q ground state |q⟩.
   NS sector (integer q): h = -q(q+2)/2
   R sector (half-integer q): h = 5/8 - q(q+2)/2  (includes R ground state weight) *)
groundStateWeight::usage = "Returns the conformal weight of the picture-q ground state for a given picture spec.";
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
gsoParityOfGroundState::usage = "Returns the GSO parity of the picture-q ground state for a given picture spec.";
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
minSuperghostWeightForGhostNumber::usage = "Lower bound on superghost conformal weight for a given superghost number at a specified picture.";
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
ghostWeightAtSplit::usage = "Computes the minimum ghost-sector weight for a fixed bc/superghost split at a specified picture.";
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
minTypeIIGhostWeightForGhostNumber::usage = "Lower bound on TypeII ghost-sector weight for a given total ghost number at a specified picture.";
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
minSectorWeightForGhostAndPicture::usage = "Lower bound on total sector weight (ground state + ghosts) for a ghost number at a specified picture.";
minSectorWeightForGhostAndPicture[ghostNumber_Integer, picture_?validPictureSpecQ] :=
  groundStateWeight[picture] + minTypeIIGhostWeightForGhostNumber[ghostNumber, picture];

(* Find contiguous range of integers where splitFeasibleQ returns True.
   Searches outward from center, then expands to find full range.
   Returns {} if no feasible split exists. *)
findFeasibleSplitRange::usage = "Finds a contiguous integer range of feasible splits by searching outward from a center and expanding to full extent.";
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
ghostSplitRangeTypeII::usage = "Returns feasible bc-ghost-number splits for a TypeII holomorphic sector under a weight budget at a specified picture.";
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
ghostSplitRangeClosedString::usage = "Returns feasible holomorphic ghost-number splits for a closed string under a total weight budget at specified pictures.";
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

minModeNumberForSpecies::usage = "Returns maximal creation mode number n0 for TypeII species at a given picture.";
minModeNumberForSpecies[symbol_Symbol, picture_?validPictureSpecQ] := Module[{q},
  q = pictureValue[picture];
  Switch[symbol,
    \[Beta] | \[Beta]t, -3/2 - q,
    \[Gamma] | \[Gamma]t, 1/2 + q,
    \[Psi] | \[Psi]t, If[IntegerQ[q], -1/2, -1],
    _, basisMinModeNumberForSpecies[symbol]
  ]
];

modeNumberFromOffset::usage = "Converts nonnegative offset to TypeII oscillator mode number.";
modeNumberFromOffset[symbol_Symbol, modeOffset_Integer?NonNegative, picture_?validPictureSpecQ] :=
  minModeNumberForSpecies[symbol, picture] - modeOffset;

(* Convert offset lists to superghost mode objects. *)
generateSuperghostModes[betaOffsets_List, gammaOffsets_List, picture_?validPictureSpecQ] :=
  Join[
    mode[\[Beta], modeNumberFromOffset[\[Beta], #, picture]] & /@ betaOffsets,
    mode[\[Gamma], modeNumberFromOffset[\[Gamma], #, picture]] & /@ gammaOffsets
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

(* Convert offset list to ψ mode objects *)
generatePsiModes[offsets_List, picture_?validPictureSpecQ] :=
  (Module[{mu},
    mode[\[Psi][mu], modeNumberFromOffset[\[Psi], #, picture]]
  ] & /@ offsets);

(* Generate all ψ configurations up to target weight.
   ψ is fermionic with Lorentz index multiplicity bound D=10 per level.
   Returns {modeList, weight} pairs. *)
generatePsiModeConfigs[targetWeight_?NumericQ, picture_?validPictureSpecQ] :=
  generatePsiModeConfigs[targetWeight, picture] = Module[
    {
      minModeNumber,
      maxPsiCount,
      psiCount,
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
    minModeNumber = minModeNumberForSpecies[\[Psi], picture];
    maxPsiCount = If[minModeNumber < 0, Max[0, Floor[targetWeight/(-minModeNumber)]], 0];
    collectedConfigs = Reap[
      Do[
        minOffsetSum = minBoundedModeSum[psiCount, 0, $maxPsiPerLevel];
        minPsiWeight = -minModeNumber psiCount + minOffsetSum;
        If[minPsiWeight > targetWeight,
          Continue[]
        ];
        maxOffsetSum = Floor[targetWeight + minModeNumber psiCount];
        If[maxOffsetSum < minOffsetSum,
          Continue[]
        ];
        Do[
          offsetConfigs = boundedModesByExactSum[psiCount, offsetSum, 0, $maxPsiPerLevel];
          Do[
            Sow[{generatePsiModes[offsets, picture], -minModeNumber psiCount + offsetSum}],
            {offsets, offsetConfigs}
          ],
          {offsetSum, minOffsetSum, maxOffsetSum}
        ]
        ,
        {psiCount, 0, maxPsiCount}
      ]
    ][[2]];
    If[collectedConfigs === {}, {}, collectedConfigs[[1]]]
  ];

generatePsiModeConfigs[_, _] := {};

derGroundStateHolo::usage =
  "Marks derivatives acting on a Ramond holomorphic charged ground state inside matter-mode output.";

derGroundStateAntiHolo::usage =
  "Marks derivatives acting on a Ramond antiholomorphic charged ground state inside matter-mode output.";

matterModeCompletions::usage =
  "Returns all dX-completion choices for fixed ψ and ground-derivative modes under the FermionOnly setting.";
matterModeCompletions[groundDerivativeModes_List, psiModes_List, remainingDXWeight_, True] :=
  If[remainingDXWeight == 0, {Join[groundDerivativeModes, psiModes]}, {}];
matterModeCompletions[groundDerivativeModes_List, psiModes_List, remainingDXWeight_Integer?NonNegative, False] :=
  Join[groundDerivativeModes, #, psiModes] & /@ generateDXModeConfigs[remainingDXWeight];

generateMatterModeConfigs[targetWeight_?NumericQ, picture_?validPictureSpecQ, fermionOnly_?BooleanQ] :=
  generateMatterModeConfigs[targetWeight, picture, fermionOnly] = Module[
    {groundDerivativeWeights},
    If[targetWeight < 0 || !IntegerQ[2 targetWeight],
      Return[{}]
    ];
    groundDerivativeWeights =
      If[IntegerQ[pictureValue[picture]] || !IntegerQ[targetWeight], {0}, Range[0, targetWeight]];
    Flatten[
      Table[
        With[
          {
            groundDerivativeModes =
              If[groundDerivativeWeight == 0, {}, {mode[derGroundStateHolo[groundDerivativeWeight], 0]}],
            psiModeConfigs = generatePsiModeConfigs[targetWeight - groundDerivativeWeight, picture]
          },
          Flatten[
            Function[{psiModes, psiWeight},
              With[{remainingDXWeight = targetWeight - groundDerivativeWeight - psiWeight},
                If[remainingDXWeight >= 0 && IntegerQ[remainingDXWeight],
                  matterModeCompletions[groundDerivativeModes, psiModes, remainingDXWeight, fermionOnly],
                  {}
                ]
              ]
            ] @@@ psiModeConfigs,
            1
          ]
        ],
        {groundDerivativeWeight, groundDerivativeWeights}
      ],
      1
    ]
  ];

generateMatterModeConfigs[_, _, _] := {};

parseMatterBasisOptionsFromList::usage =
  "Parses GSOParity and FermionOnly options for TypeII matter-basis generators.";
parseMatterBasisOptionsFromList[optionList_List] := Module[{GSOParitySelection, fermionOnly},
  If[optionList =!= {} && !OptionQ[optionList],
    Return[$Failed]
  ];
  GSOParitySelection = parseGSOParityOptionFromList[optionList];
  fermionOnly = readBooleanOption[optionList, "FermionOnly", False];
  If[GSOParitySelection === $Failed || fermionOnly === $Failed,
    $Failed,
    {GSOParitySelection, fermionOnly}
  ]
];

generateBasisMatterHoloForPictureSpecWithSelection::usage =
  "Generates a matter-only holomorphic basis for one picture spec and one GSO selector.";
generateBasisMatterHoloForPictureSpecWithSelection[
  weight_?validWeightQ,
  picture_?validPictureSpecQ,
  GSOParitySelection_String,
  fermionOnly_?BooleanQ
] :=
  generateBasisMatterHoloForPictureSpecWithSelection[weight, picture, GSOParitySelection, fermionOnly] = Module[
    {groundWeight, remainingWeight, matterModeConfigs},
    groundWeight = groundStateWeight[picture];
    remainingWeight = weight - groundWeight;
    If[remainingWeight < 0 || !IntegerQ[2 remainingWeight],
      Return[{}]
    ];
    matterModeConfigs = generateMatterModeConfigs[remainingWeight, picture, fermionOnly];
    If[matterModeConfigs === {},
      Return[{}]
    ];
    matterModeConfigs = Select[
      DeleteDuplicates[canonicalizeLorentzIndicesModes /@ matterModeConfigs],
      GSOParitySelectionMatchesQ[GSOParityOfConfig[#, picture], GSOParitySelection] &
    ];
    If[matterModeConfigs === {},
      {},
      {picture, matterModeConfigs}
    ]
  ];

generateBasisMatterHoloForPictureSpecWithSelection[___] := {};

generateBasisMatterHoloForPictureSpec::usage =
  "Parses options and generates matter-only holomorphic basis for one picture spec.";
generateBasisMatterHoloForPictureSpec[
  weight_?validWeightQ,
  picture_?validPictureSpecQ,
  opts___
] := Module[{parsedOptions},
  parsedOptions = parseMatterBasisOptionsFromList[Flatten[{opts}]];
  If[parsedOptions === $Failed,
    Return[{}]
  ];
  generateBasisMatterHoloForPictureSpecWithSelection[weight, picture, parsedOptions[[1]], parsedOptions[[2]]]
];

generateBasisMatterHoloForPictureSpec[___] := {};

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

(* Conformal weight contribution: mode with number n contributes -n *)
modeWeightContribution[mode[(derGroundStateHolo | derGroundStateAntiHolo)[weight_Integer?Positive], 0]] := weight;
modeWeightContribution[mode[_, modeNumber_]] := -modeNumber;

(* Ghost number contribution of one oscillator mode. *)
modeGhostContribution[mode[(derGroundStateHolo | derGroundStateAntiHolo)[_Integer?Positive], 0]] := 0;
modeGhostContribution[modeObj : mode[_, _]] := Switch[
  basisModeSpecies[modeObj],
  \[Beta] | \[Beta]t, -1,
  \[Gamma] | \[Gamma]t, 1,
  _, basisGhostContributionFromMode[modeObj]
];

(* GSO parity contribution of one oscillator mode. *)
modeGSOParityContribution[mode[(derGroundStateHolo | derGroundStateAntiHolo)[_Integer?Positive], 0]] := 1;
modeGSOParityContribution[modeObj : mode[_, _]] :=
  basisModeGSOParityContribution[modeObj];

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

GSOParityOfConfig::usage =
  "Alias for gsoParityOfConfig with canonical GSO capitalization.";
GSOParityOfConfig[modeList_List, picture_?validPictureSpecQ] :=
  gsoParityOfConfig[modeList, picture];

modeListGSOParityContribution::usage =
  "Returns product of oscillator GSO parity contributions (without ground-state factor).";
modeListGSOParityContribution[modeList_List] :=
  Times @@ (modeGSOParityContribution /@ Cases[modeList, mode[_, _], Infinity]);

requiredMatterGSOParitySelection::usage =
  "Converts desired total GSO selector and ghost parity into the required matter selector.";
requiredMatterGSOParitySelection["All", _Integer] := "All";
requiredMatterGSOParitySelection["Even", ghostParity_Integer] :=
  If[ghostParity === 1, "Even", "Odd"];
requiredMatterGSOParitySelection["Odd", ghostParity_Integer] :=
  If[ghostParity === 1, "Odd", "Even"];

(* Assemble holomorphic state from component mode lists.
   Returns {picture, canonicalized mode list}. *)
buildHoloState[picture_?validPictureSpecQ, bcModes_List, superghostModes_List, matterModes_List] :=
  Module[{modeList},
    modeList = canonicalizeLorentzIndicesModes[
      Join[bcModes, superghostModes, matterModes]
    ];
    {picture, modeList}
  ];

(* Convert holomorphic mode to antiholomorphic counterpart. *)
antiModeFromHolo[mode[\[Beta], modeNumber_]] := mode[\[Beta]t, modeNumber];
antiModeFromHolo[mode[\[Gamma], modeNumber_]] := mode[\[Gamma]t, modeNumber];
antiModeFromHolo[mode[dX[mu_], modeNumber_]] := mode[dXt[mu], modeNumber];
antiModeFromHolo[mode[\[Psi][mu_], modeNumber_]] := mode[\[Psi]t[mu], modeNumber];
antiModeFromHolo[mode[derGroundStateHolo[weight_Integer?Positive], 0]] :=
  mode[derGroundStateAntiHolo[weight], 0];
antiModeFromHolo[modeObj : mode[_, _]] := basisAntiModeFromHolo[modeObj];
antiModeFromHolo[modeObj_] := modeObj;

operatorFactorsFromExpression::usage =
  "Returns multiplicative operator factors from an expression, flattening one top-level R.";
operatorFactorsFromExpression[expr_] := Which[
  expr === 1, {},
  RTest[expr], List @@ expr,
  True, {expr}
];

multiplyOperatorExpressions::usage =
  "Combines two operator expressions into one normal-ordered factor when possible.";
multiplyOperatorExpressions[a_, b_] := Which[
  a === 0 || b === 0, 0,
  a === 1, b,
  b === 1, a,
  True, R[a, b]
];

canonicalizeLorentzIndicesOperators::usage =
  "Canonicalizes Lorentz placeholder symbols in operator expressions. Uses α for S and αt for St spinor indices.";
canonicalizeLorentzIndicesOperators[expr_] := Module[
  {
    lorentzSymbols,
    spinAlphaSymbolsHolo, spinAlphaSymbolsAnti,
    canonicalLorentzSymbols,
    canonicalSpinAlphaSymbolsHolo, canonicalSpinAlphaSymbolsAnti,
    lorentzRenamingRules,
    spinAlphaRenamingRules
  },
  lorentzSymbols = DeleteDuplicates @ Join[
    Cases[expr, (dX | dXt | \[Psi] | \[Psi]t)[mu_Symbol, __] :> mu, Infinity],
    Cases[
      expr,
      (S | St)[_, _, modes_List, __] :>
        Join[
          Cases[modes, {mu_Symbol, _} :> mu, Infinity],
          Cases[modes, {_, mu_Symbol} :> mu, Infinity]
        ],
      Infinity
    ] // Flatten
  ];
  spinAlphaSymbolsHolo = DeleteDuplicates @ Cases[
    expr,
    S[{alpha_Symbol, chirality : ("chiral" | "antichiral")}, __] :> alpha,
    Infinity
  ];
  spinAlphaSymbolsAnti = DeleteDuplicates @ Cases[
    expr,
    St[{alpha_Symbol, chirality : ("chiral" | "antichiral")}, __] :> alpha,
    Infinity
  ];
  canonicalLorentzSymbols = Symbol["mu" <> ToString[#]] & /@ Range[Length[lorentzSymbols]];
  canonicalSpinAlphaSymbolsHolo = Symbol["\\[Alpha]" <> ToString[#]] & /@ Range[Length[spinAlphaSymbolsHolo]];
  canonicalSpinAlphaSymbolsAnti = Symbol["\\[Alpha]t" <> ToString[#]] & /@ Range[Length[spinAlphaSymbolsAnti]];
  lorentzRenamingRules = Thread[lorentzSymbols -> canonicalLorentzSymbols];
  spinAlphaRenamingRules = Join[
    Thread[spinAlphaSymbolsHolo -> canonicalSpinAlphaSymbolsHolo],
    Thread[spinAlphaSymbolsAnti -> canonicalSpinAlphaSymbolsAnti]
  ];
  expr /. Join[lorentzRenamingRules, spinAlphaRenamingRules]
];

stripOverallMinusInOperatorExpression::usage =
  "Removes a global negative numeric prefactor from one operator expression.";
stripOverallMinusInOperatorExpression[expr_] := Module[{prefactor},
  prefactor = First[FactorTermsList[expr]];
  If[NumericQ[prefactor] && prefactor < 0, -expr, expr]
];

canonicalizeOperatorIndicesQ::usage =
  "Controls whether operator-output indices are canonicalized to mu1, mu2, ...";
canonicalizeOperatorIndicesQ[canonicalizeIndices_?BooleanQ, expr_] := Module[
  {canonicalExpression},
  canonicalExpression =
    If[TrueQ[canonicalizeIndices], canonicalizeLorentzIndicesOperators[expr], expr];
  stripOverallMinusInOperatorExpression[canonicalExpression]
];

rescaleHoloFieldByParameter::usage =
  "Rescales the holomorphic position argument(s) of one field by a parameter.";
rescaleHoloFieldByParameter[parameter_][op_ /; isField[Head[op]] && isHolomorphic[Head[op]] && isAntiHolomorphic[Head[op]]] :=
  Module[{args = List @@ op, head = Head[op]},
    head @@ Join[Drop[args, -2], parameter Take[args, -2]]
  ];
rescaleHoloFieldByParameter[parameter_][op_ /; isField[Head[op]] && isHolomorphic[Head[op]]] :=
  Module[{args = List @@ op, head = Head[op]},
    head @@ Join[Drop[args, -1], {parameter Last[args]}]
  ];
rescaleHoloFieldByParameter[_][op_] := op;

rescaleHoloExpressionByParameter::usage =
  "Rescales all holomorphic field positions in an expression by a parameter.";
rescaleHoloExpressionByParameter[expr_, parameter_] :=
  expr /. op_ /; isField[Head[op]] :> rescaleHoloFieldByParameter[parameter][op];

normalizeScalingParameterForModeProjection::usage =
  "Pulls a common scaling parameter out of additive terms when all summands carry it.";
normalizeScalingParameterForModeProjection[expr_, parameter_] := FixedPoint[
  ReplaceAll[
    #,
    {
      sum_Plus /; AllTrue[List @@ sum, MatchQ[#, parameter*__] &] :>
        parameter Total[(# / parameter) & /@ (List @@ sum)]
    }
  ] &,
  expr
];

projectScaledExpressionAtPower::usage =
  "Projects a scaled contour expression onto a fixed power around zero.";
projectScaledExpressionAtPower[scaledExpr_, targetPower_, parameter_, taylorFunction_] := Module[
  {result = 0, expandedExpr, terms, scaledTerm, termPower, expansionOrder},
  If[scaledExpr === 1,
    Return[If[targetPower === 0, 1, 0]]
  ];
  expandedExpr = Expand[scaledExpr];
  terms = If[Head[expandedExpr] === Plus, List @@ expandedExpr, {expandedExpr}];
  Scan[
    Function[term,
      scaledTerm = normalizeScalingParameterForModeProjection[term, parameter];
      termPower = Exponent[scaledTerm, parameter];
      expansionOrder = -termPower + targetPower;
      If[IntegerQ[expansionOrder] && expansionOrder >= 0,
        result = result + taylorFunction[scaledTerm, expansionOrder, 0]
      ]
    ],
    terms
  ];
  result /. parameter -> 1
];

projectScaledExpressionAtHoloPower::usage =
  "Projects a scaled holomorphic expression onto a fixed contour power around zero.";
projectScaledExpressionAtHoloPower[scaledExpr_, targetPower_, parameter_] :=
  projectScaledExpressionAtPower[scaledExpr, targetPower, parameter, TaylorAtOrderHolo];

projectScaledExpressionAtAntiHoloPower::usage =
  "Projects a scaled antiholomorphic expression onto a fixed contour power around zero.";
projectScaledExpressionAtAntiHoloPower[scaledExpr_, targetPower_, parameter_] :=
  projectScaledExpressionAtPower[scaledExpr, targetPower, parameter, TaylorAtOrderAntiHolo];

projectScaledContourContributionAtOrigin::usage =
  "Projects one pre-scaled contour expression and evaluates the insertion coordinate at 1.";
(* Mode extraction is done with scaled insertions epsilon z. After projecting
   onto the target epsilon-power, the contour coordinate itself is set to 1 so
   only the residue data is carried forward. *)
projectScaledContourContributionAtOrigin[projector_, scaledExpr_, targetPower_, parameter_, coord_] :=
  Expand @ Simplify[projector[scaledExpr, targetPower, parameter] /. coord -> 1];

spinDescendantSeedPicture::usage =
  "spinDescendantSeedPicture[q, modes] returns the shifted Ramond ground-state picture used to collapse a list of excited spin-field contours locally.";
spinDescendantSeedPicture[q_, modes_List] := q + Length[modes];

spinDescendantGeneratorHolo::usage =
  "spinDescendantGeneratorHolo[spinMode, coord] builds the bosonized holomorphic GSO-projected descendant generator e^{-phi} psi at coord.";
spinDescendantGeneratorHolo[spinMode_, coord_] :=
  Bosonize[R[exp\[Phi]f[-1, coord], \[Psi][spinDescendantModeVectorIndex[spinMode], 0, coord]]];

spinDescendantGeneratorAntiHolo::usage =
  "spinDescendantGeneratorAntiHolo[spinMode, coord] builds the bosonized antiholomorphic GSO-projected descendant generator e^{-phit} psit at coord.";
spinDescendantGeneratorAntiHolo[spinMode_, coord_] :=
  Bosonize[R[exp\[Phi]tf[-1, coord], \[Psi]t[spinDescendantModeVectorIndex[spinMode], 0, coord]]];

spinDescendantContourPower::usage =
  "spinDescendantContourPower[spinMode] returns the contour-extraction power for one excited spin-field mode under the e^{-phi} psi local collapse rule.";
spinDescendantContourPower[spinMode_] := spinDescendantModeExcitationLevel[spinMode];

applySpinDescendantModeHolo::usage =
  "applySpinDescendantModeHolo[currentState, spinMode] applies one holomorphic excited-spin contour step using the bosonized e^{-phi} psi generator.";
applySpinDescendantModeHolo[currentState_, spinMode_] := Module[{zMode = Unique["zMode"], parameter = Unique["\[Epsilon]Mode"]},
  projectScaledContourContributionAtOrigin[
    projectScaledExpressionAtHoloPower,
    OPE[spinDescendantGeneratorHolo[spinMode, parameter zMode], currentState],
    spinDescendantContourPower[spinMode],
    parameter,
    zMode
  ]
];

applySpinDescendantModeAntiHolo::usage =
  "applySpinDescendantModeAntiHolo[currentState, spinMode] applies one antiholomorphic excited-spin contour step using the bosonized e^{-phit} psit generator.";
applySpinDescendantModeAntiHolo[currentState_, spinMode_] := Module[{zbarMode = Unique["zbarMode"], parameter = Unique["\[Epsilon]Mode"]},
  projectScaledContourContributionAtOrigin[
    projectScaledExpressionAtAntiHoloPower,
    OPE[spinDescendantGeneratorAntiHolo[spinMode, parameter zbarMode], currentState],
    spinDescendantContourPower[spinMode],
    parameter,
    zbarMode
  ]
];

restoreBosonizedSpinStateHolo::usage =
  "restoreBosonizedSpinStateHolo[expr, coord] restores one locally collapsed holomorphic excited-spin state from the origin to coord.";
restoreBosonizedSpinStateHolo[expr_, coord_] :=
  Expand[(expr /. R[a___] :> Times[a]) /. {dH[i_, n_, 0] :> dH[i, n, coord], expH[charges_, 0] :> expH[charges, coord]}];

restoreBosonizedSpinStateAntiHolo::usage =
  "restoreBosonizedSpinStateAntiHolo[expr, coord] restores one locally collapsed antiholomorphic excited-spin state from the origin to coord.";
restoreBosonizedSpinStateAntiHolo[expr_, coord_] :=
  Expand[(expr /. R[a___] :> Times[a]) /. {dHt[i_, n_, 0] :> dHt[i, n, coord], expHt[charges_, 0] :> expHt[charges, coord]}];

bosonizeSpinModesHolo::usage =
  "Bosonizes a holomorphic excited Ramond spin field by sequential local contour collapse with the bosonized e^{-phi} psi generator.";
bosonizeSpinModesHolo[{spinVec_List, chirality_}, q_, modes_List, coord_] := Module[
  {state, seedPicture},
  seedPicture = spinDescendantSeedPicture[q, modes];
  state = Bosonize[R[S[{spinVec, chirality}, seedPicture, {}, 0, 0]]];
  state = Fold[applySpinDescendantModeHolo, state, modes];
  restoreBosonizedSpinStateHolo[state, coord]
];

bosonizeSpinModesAntiHolo::usage =
  "Bosonizes an antiholomorphic excited Ramond spin field by sequential local contour collapse with the bosonized e^{-phit} psit generator.";
bosonizeSpinModesAntiHolo[{spinVec_List, chirality_}, q_, modes_List, coord_] := Module[
  {state, seedPicture},
  seedPicture = spinDescendantSeedPicture[q, modes];
  state = Bosonize[R[St[{spinVec, chirality}, seedPicture, {}, 0, 0]]];
  state = Fold[applySpinDescendantModeAntiHolo, state, modes];
  restoreBosonizedSpinStateAntiHolo[state, coord]
];

modeExtractionPower::usage =
  "Returns the contour extraction power for one TypeII superghost oscillator mode.";
modeExtractionPower[mode[\[Beta], modeNumber_]] := -modeNumber - 3/2;
modeExtractionPower[mode[\[Gamma], modeNumber_]] := -modeNumber + 1/2;

superghostModePieces::usage =
  "Returns {xi/eta piece, expPhi piece, picture shift} for one superghost mode.";
superghostModePieces[mode[\[Beta], _], z_] := {\[Xi][1, z], exp\[Phi]f[-1, z], -1};
superghostModePieces[mode[\[Gamma], _], z_] := {\[Eta][0, z], exp\[Phi]f[1, z], 1};

quietKnownSuperghostProjectionWarnings::usage =
  "Suppresses known non-fatal projection warnings emitted by internal superghost/OPE manipulations.";
SetAttributes[quietKnownSuperghostProjectionWarnings, HoldFirst];
quietKnownSuperghostProjectionWarnings[expr_] := Quiet[expr, Part::partd];

intermediateGroundExponential::usage =
  "Builds the temporary exponential representation of the picture ground state.";
intermediateGroundExponential[picture_, z_] := exp\[Phi]f[picture, z];

stripGroundExponential::usage =
  "Removes one temporary exponential ground-state factor of the requested charge.";
stripGroundExponential[expr_, picture_] := expr /. {
  exp\[Phi]f[picture, 0] -> 1,
  exp\[Phi]b[picture, 0] -> 1
};

applyOneSuperghostMode::usage =
  "Applies one superghost mode to {picture, non-exp expression} via split OPE and contour projection.";
applyOneSuperghostMode[{picture_, nonExpExpr_}, superghostMode : mode[(\[Beta] | \[Gamma]), _]] := Module[
  {
    z = Unique["zMode"],
    scalingParameter = Unique["\[Epsilon]Mode"],
    incomingNonExp,
    incomingExp,
    pictureShift,
    extractionPower,
    currentNonExpR,
    groundExp,
    scaledIncomingNonExp,
    scaledIncomingExp,
    nonExpOPE,
    expOPE,
    combinedOPE,
    projectedOPE,
    newPicture,
    strippedExpr
  },
  {incomingNonExp, incomingExp, pictureShift} = superghostModePieces[superghostMode, z];
  extractionPower = modeExtractionPower[superghostMode];
  currentNonExpR = If[nonExpExpr === 1 || RTest[nonExpExpr], nonExpExpr, R[nonExpExpr]];
  groundExp = intermediateGroundExponential[picture, 0];
  scaledIncomingNonExp = rescaleHoloFieldByParameter[scalingParameter][incomingNonExp];
  scaledIncomingExp = rescaleHoloFieldByParameter[scalingParameter][incomingExp];
  nonExpOPE = OPE[R[scaledIncomingNonExp], currentNonExpR];
  expOPE = OPE[R[scaledIncomingExp], R[groundExp]];
  combinedOPE = multiplyOperatorExpressions[nonExpOPE, expOPE];
  projectedOPE = projectScaledContourContributionAtOrigin[
    projectScaledExpressionAtHoloPower,
    combinedOPE,
    extractionPower,
    scalingParameter,
    z
  ];
  newPicture = picture + pictureShift;
  strippedExpr = stripGroundExponential[projectedOPE, newPicture];
  {newPicture, strippedExpr}
];

superghostExpressionAndFinalPicture::usage =
  "Converts a list of superghost modes to a non-ground expression and final picture value.";
superghostExpressionAndFinalPicture[superghostModes_List, initialPicture_] :=
  quietKnownSuperghostProjectionWarnings[
    Fold[
      applyOneSuperghostMode,
      {initialPicture, 1},
      superghostModes
    ]
  ];

dXModeToOperatorField::usage =
  "Converts one dX mode to local-operator form at z.";
dXModeToOperatorField[mode[dX[_], modeNumber_Integer], z_] := Module[{mu},
  dX[mu, -1 - modeNumber, z]
];

psiModeToOperatorField::usage =
  "Converts one psi mode to local-operator form at z.";
psiModeToOperatorField[mode[\[Psi][_], modeNumber_], z_] := Module[{mu},
  \[Psi][mu, -1/2 - modeNumber, z]
];

psiModeToSpinMode::usage =
  "Converts one Ramond psi mode to a spin-field mode-pair entry using the actual nonpositive Ramond mode number.";
psiModeToSpinMode[mode[\[Psi][_], modeNumber_Integer]] := Module[{mu},
  {mu, modeNumber}
];

integerPictureGroundField::usage =
  "Builds the integer-picture matter ground-state exponential at z.";
integerPictureGroundField[picture_Integer, z_] :=
  If[OddQ[picture], exp\[Phi]f[picture, z], exp\[Phi]b[picture, z]];

modeListSplitForHoloConversion::usage =
  "Splits a holomorphic mode list into {bc, superghost, dX, psi, ground-derivative} subsectors.";
modeListSplitForHoloConversion[modeList_List] := Module[
  {bcModes, superghostModes, dXModes, psiModes, groundDerivativeModes},
  bcModes = Cases[modeList, mode[(b | c), _]];
  superghostModes = Cases[modeList, mode[(\[Beta] | \[Gamma]), _]];
  dXModes = Cases[modeList, mode[dX[_], _]];
  psiModes = Cases[modeList, mode[\[Psi][_], _]];
  groundDerivativeModes = Cases[modeList, mode[derGroundStateHolo[_Integer?Positive], 0]];
  {bcModes, superghostModes, dXModes, psiModes, groundDerivativeModes}
];

groundDerivativeOrderFromModes::usage =
  "Returns the total Ramond charged-ground-state derivative order carried by a mode list.";
groundDerivativeOrderFromModes[modes_List] :=
  Total[Cases[modes, mode[derGroundStateHolo[weight_Integer?Positive], 0] :> weight, Infinity]];

buildMatterOperatorFromModesAtPicture::usage =
  "Builds the matter operator factors from dX/psi modes at a specified picture value and ground-state derivative order.";
buildMatterOperatorFromModesAtPicture[
  pictureSpec_?validPictureSpecQ,
  pictureValueNow_,
  dXModes_List,
  psiModes_List,
  groundDerivativeOrder_Integer?NonNegative,
  z_,
  spinHead_Symbol
] := Module[
  {dXFields, psiFields, spinModes, chirality, spinGround},
  dXFields = dXModeToOperatorField[#, z] & /@ dXModes;
  If[IntegerQ[pictureValueNow],
    psiFields = psiModeToOperatorField[#, z] & /@ psiModes;
    Return[R @@ Join[dXFields, psiFields, {integerPictureGroundField[pictureValueNow, z]}]]
  ];
  spinModes = psiModeToSpinMode /@ psiModes;
  chirality = pictureChirality[pictureSpec];
  spinGround = Module[{\[Alpha]},
    spinHead[{\[Alpha], chirality}, pictureValueNow, spinModes, groundDerivativeOrder, z]
  ];
  R @@ Join[dXFields, {spinGround}]
];

assembleHoloOperatorFromModeList::usage =
  "Converts one holomorphic TypeII mode list into one local operator expression.";
assembleHoloOperatorFromModeList[
  pictureSpec_?validPictureSpecQ,
  modeList_List,
  z_: 0,
  canonicalizeIndices_: True
] := Module[
  {
    bcModes,
    superghostModes,
    dXModes,
    psiModes,
    groundDerivativeModes,
    bcFields,
    superghostResult,
    finalPicture,
    superghostExpr,
    matterExpr,
    rawOperator
  },
  {bcModes, superghostModes, dXModes, psiModes, groundDerivativeModes} =
    modeListSplitForHoloConversion[modeList];
  bcFields = ghostModesToOperatorFields[bcModes, z];
  superghostResult = superghostExpressionAndFinalPicture[superghostModes, pictureValue[pictureSpec]];
  finalPicture = superghostResult[[1]];
  superghostExpr = superghostResult[[2]];
  matterExpr = buildMatterOperatorFromModesAtPicture[
    pictureSpec,
    finalPicture,
    dXModes,
    psiModes,
    groundDerivativeOrderFromModes[groundDerivativeModes],
    z,
    S
  ];
  rawOperator = R @@ Join[bcFields, {superghostExpr, matterExpr}];
  canonicalizeOperatorIndicesQ[canonicalizeIndices, rawOperator]
];

holoModeFromAntiMode::usage =
  "Maps one antiholomorphic mode object to its holomorphic counterpart.";
holoModeFromAntiMode[mode[bt, modeNumber_]] := mode[b, modeNumber];
holoModeFromAntiMode[mode[ct, modeNumber_]] := mode[c, modeNumber];
holoModeFromAntiMode[mode[\[Beta]t, modeNumber_]] := mode[\[Beta], modeNumber];
holoModeFromAntiMode[mode[\[Gamma]t, modeNumber_]] := mode[\[Gamma], modeNumber];
holoModeFromAntiMode[mode[dXt[mu_], modeNumber_]] := mode[dX[mu], modeNumber];
holoModeFromAntiMode[mode[\[Psi]t[mu_], modeNumber_]] := mode[\[Psi][mu], modeNumber];
holoModeFromAntiMode[mode[derGroundStateAntiHolo[weight_Integer?Positive], 0]] :=
  mode[derGroundStateHolo[weight], 0];
holoModeFromAntiMode[modeObj_] := modeObj;

antiOperatorFromHolo::usage =
  "Maps a holomorphic operator expression to antiholomorphic symbols.";
antiOperatorFromHolo[expr_] := expr /. {
  b -> bt,
  c -> ct,
  \[Xi] -> \[Xi]t,
  \[Eta] -> \[Eta]t,
  d\[Phi] -> d\[Phi]t,
  dX -> dXt,
  \[Psi] -> \[Psi]t,
  exp\[Phi]f -> exp\[Phi]tf,
  exp\[Phi]b -> exp\[Phi]tb,
  S -> St
};

assembleAntiOperatorFromModeList::usage =
  "Converts one antiholomorphic TypeII mode list into one local operator expression.";
assembleAntiOperatorFromModeList[
  pictureSpec_?validPictureSpecQ,
  modeList_List,
  zbar_: 0,
  canonicalizeIndices_: True
] := Module[
  {holoModes, holoOperator, antiOperator},
  holoModes = holoModeFromAntiMode /@ modeList;
  holoOperator = assembleHoloOperatorFromModeList[
    pictureSpec,
    holoModes,
    zbar,
    False
  ];
  antiOperator = antiOperatorFromHolo[holoOperator];
  canonicalizeOperatorIndicesQ[canonicalizeIndices, antiOperator]
];

antiModeSpeciesQ::usage =
  "Returns True if a mode species is antiholomorphic.";
antiModeSpeciesQ[symbol_Symbol] :=
  MemberQ[{bt, ct, \[Beta]t, \[Gamma]t, dXt, \[Psi]t, derGroundStateAntiHolo}, symbol];

splitJoinedModesByChirality::usage =
  "Splits a joined closed-string mode list into {holoModes, antiModes}.";
splitJoinedModesByChirality[joinedModeList_List] := Module[{holoModes, antiModes},
  holoModes = Select[
    joinedModeList,
    MatchQ[#, mode[_, _]] && !antiModeSpeciesQ[basisModeSpecies[#]] &
  ];
  antiModes = Select[
    joinedModeList,
    MatchQ[#, mode[_, _]] && antiModeSpeciesQ[basisModeSpecies[#]] &
  ];
  {holoModes, antiModes}
];

closedOperatorFromJoinedModeList::usage =
  "Converts one joined closed-string mode list to R[holoOperator, antiOperator].";
closedOperatorFromJoinedModeList[
  pictures : {pictureLeft_?validPictureSpecQ, pictureRight_?validPictureSpecQ},
  joinedModeList_List,
  z_: 0,
  zbar_: 0,
  canonicalizeIndices_: True
] := Module[{splitModes, holoOperator, antiOperator},
  splitModes = splitJoinedModesByChirality[joinedModeList];
  holoOperator = assembleHoloOperatorFromModeList[
    pictureLeft,
    splitModes[[1]],
    z,
    canonicalizeIndices
  ];
  antiOperator = assembleAntiOperatorFromModeList[
    pictureRight,
    splitModes[[2]],
    zbar,
    canonicalizeIndices
  ];
  canonicalizeOperatorIndicesQ[canonicalizeIndices, R[holoOperator, antiOperator]]
];

convertMatterGroupToOperatorsHolo::usage =
  "Converts one matter-mode group {picture, modeLists} to OPE-basis holomorphic operators.";
groundDerivativeOPEFactorLists::usage =
  "Returns all dphi-factor lists of a fixed total weight.";
groundDerivativeOPEFactorLists[0, _, _] := {{}};
groundDerivativeOPEFactorLists[weight_Integer?Positive, derivativeHead_Symbol, coord_] :=
  (derivativeHead[# - 1, coord] & /@ #) & /@ IntegerPartitions[weight];

matterOPEOperatorsFromHoloModeList::usage =
  "Builds matter OPE-basis operators from one holomorphic matter mode list.";
matterOPEOperatorsFromHoloModeList[
  pictureSpec_?validPictureSpecQ,
  modeList_List,
  z_: 0,
  canonicalizeIndices_: True
] := Module[
  {bcModes, superghostModes, dXModes, psiModes, groundDerivativeModes, totalGroundDerivative},
  {bcModes, superghostModes, dXModes, psiModes, groundDerivativeModes} =
    modeListSplitForHoloConversion[modeList];
  totalGroundDerivative = groundDerivativeOrderFromModes[groundDerivativeModes];
  DeleteDuplicates @ DeleteCases[
    Flatten[
      Table[
        With[
          {
            matterExpr = buildMatterOperatorFromModesAtPicture[
              pictureSpec,
              pictureValue[pictureSpec],
              dXModes,
              psiModes,
              totalGroundDerivative - phiWeight,
              z,
              S
            ]
          },
          If[matterExpr === 0,
            {},
            canonicalizeOperatorIndicesQ[
              canonicalizeIndices,
              R @@ Join[#, operatorFactorsFromExpression[matterExpr]]
            ] & /@ groundDerivativeOPEFactorLists[phiWeight, d\[Phi], z]
          ]
        ],
        {phiWeight, 0, totalGroundDerivative}
      ],
      1
    ],
    0
  ]
];

matterOPEOperatorsFromAntiModeList::usage =
  "Builds matter OPE-basis operators from one antiholomorphic matter mode list.";
matterOPEOperatorsFromAntiModeList[
  pictureSpec_?validPictureSpecQ,
  modeList_List,
  zbar_: 0,
  canonicalizeIndices_: True
] := Module[{holoModes, holoOperators},
  holoModes = holoModeFromAntiMode /@ modeList;
  holoOperators = matterOPEOperatorsFromHoloModeList[pictureSpec, holoModes, zbar, False];
  canonicalizeOperatorIndicesQ[canonicalizeIndices, antiOperatorFromHolo[#]] & /@ holoOperators
];

convertMatterGroupToOperators::usage =
  "Converts one matter-mode group {picture, modeLists} using a provided mode-list to operator conversion function.";
convertMatterGroupToOperators[
  group : {picture_?validPictureSpecQ, matterModeLists_List},
  modeListConverter_,
  canonicalizeIndices_
] := Module[
  {operators},
  operators = Flatten[
    modeListConverter[picture, #, 0, canonicalizeIndices] & /@ matterModeLists,
    1
  ];
  {picture, DeleteDuplicates[operators]}
];

convertMatterGroupToOperatorsHolo[
  group : {picture_?validPictureSpecQ, matterModeLists_List},
  canonicalizeIndices_
] := convertMatterGroupToOperators[group, matterOPEOperatorsFromHoloModeList, canonicalizeIndices];

convertMatterGroupToOperatorsAnti::usage =
  "Converts one antiholomorphic matter-mode group {picture, modeLists} to OPE-basis operators.";
convertMatterGroupToOperatorsAnti[
  group : {picture_?validPictureSpecQ, matterModeLists_List},
  canonicalizeIndices_
] := convertMatterGroupToOperators[group, matterOPEOperatorsFromAntiModeList, canonicalizeIndices];

groupedResultToList::usage =
  "Normalizes grouped results to a list of groups using a single-group pattern.";
groupedResultToList[result_, singleGroupPattern_] := Which[
  result === {}, {},
  MatchQ[result, singleGroupPattern], {result},
  ListQ[result], result,
  True, {}
];

flattenGroupedOperatorEntries::usage =
  "Extracts and deduplicates operator entries from grouped results.";
flattenGroupedOperatorEntries[groupedResults_List] :=
  DeleteDuplicates[Flatten[groupedResults[[All, 2]] /. {} -> {}, 1]];

expandedOperatorSumTerms::usage =
  "Expands one operator expression and returns its additive terms.";
expandedOperatorSumTerms[expr_] := Module[{expandedExpr},
  expandedExpr = Expand[expr];
  Which[
    expandedExpr === 0, {},
    Head[expandedExpr] === Plus, List @@ expandedExpr,
    True, {expandedExpr}
  ]
];

extractROperatorFactorsFromTerm::usage =
  "Extracts top-level R[...] multiplicative factors from one additive term.";
extractROperatorFactorsFromTerm[term_] :=
  Select[
    If[Head[term] === Times, List @@ term, {term}],
    RTest
  ];

independentROperatorsFromExpression::usage =
  "Extracts structurally unique R[...] terms occurring in one operator expression.";
independentROperatorsFromExpression[expr_] :=
  DeleteDuplicates[
    Flatten[extractROperatorFactorsFromTerm /@ expandedOperatorSumTerms[expr], 1]
  ];

independentROperatorsFromExpressions::usage =
  "Extracts structurally unique R[...] terms occurring across a list of operator expressions.";
independentROperatorsFromExpressions[expressions_List] :=
  DeleteDuplicates[
    Flatten[independentROperatorsFromExpression /@ expressions, 1]
  ];

convertGroupedResultToOperators::usage =
  "Converts grouped mode results to deduplicated operator lists.";
convertGroupedResultToOperators[result_, singleGroupPattern_, convertGroupFunction_, canonicalizeIndices_] := Module[
  {groups, convertedGroups},
  groups = groupedResultToList[result, singleGroupPattern];
  convertedGroups = convertGroupFunction[#, canonicalizeIndices] & /@ groups;
  flattenGroupedOperatorEntries[convertedGroups]
];

mapGroupedResultPreservingShape::usage =
  "Maps grouped results while preserving whether input was empty, single-group, or list.";
mapGroupedResultPreservingShape[result_, singleGroupPattern_, mapGroupFunction_] := Which[
  result === {}, {},
  MatchQ[result, singleGroupPattern], mapGroupFunction[result],
  ListQ[result], mapGroupFunction /@ result,
  True, {}
];

convertSectorBasisToOperators::usage =
  "Converts sector basis tuples {pictureSpec, modeList} to deduplicated operator lists.";
convertSectorBasisToOperators[basis_List, assembleFunction_, canonicalizeIndices_] := Module[
  {convertedExpressions},
  convertedExpressions = DeleteCases[
    assembleFunction[#[[1]], #[[2]], 0, canonicalizeIndices] & /@ basis,
    0
  ];
  independentROperatorsFromExpressions[convertedExpressions]
];

collapseExpandedResult::usage =
  "Collapses expanded grouped results to a single group when expansion size is one.";
collapseExpandedResult[groupedResults_List, collapseToSingleQ_?BooleanQ] :=
  If[groupedResults === {}, {}, If[collapseToSingleQ, First[groupedResults], groupedResults]];

convertHoloBasisToRepresentation::usage =
  "Converts a holomorphic basis list to the requested representation.";
convertHoloBasisToRepresentation[basis_List, "Modes", _] := basis;
convertHoloBasisToRepresentation[basis_List, "Operators", canonicalizeIndices_] :=
  convertSectorBasisToOperators[basis, assembleHoloOperatorFromModeList, canonicalizeIndices];

convertAntiBasisToRepresentation::usage =
  "Converts an antiholomorphic basis list to the requested representation.";
convertAntiBasisToRepresentation[basis_List, "Modes", _] := basis;
convertAntiBasisToRepresentation[basis_List, "Operators", canonicalizeIndices_] :=
  convertSectorBasisToOperators[basis, assembleAntiOperatorFromModeList, canonicalizeIndices];

convertClosedGroupToOperators::usage =
  "Converts one grouped closed-string mode result to operator representation.";
convertClosedGroupToOperators[
  group : {pictures : {_?validPictureSpecQ, _?validPictureSpecQ}, states_List},
  canonicalizeIndices_
] := Module[
  {convertedExpressions, operators},
  convertedExpressions = DeleteCases[
    closedOperatorFromJoinedModeList[pictures, #, 0, 0, canonicalizeIndices] & /@ states,
    0
  ];
  operators = independentROperatorsFromExpressions[convertedExpressions];
  {pictures, DeleteDuplicates[operators]}
];

convertClosedGroupToOperatorExpressions::usage =
  "Converts one grouped closed-string mode result to full operator expressions without splitting additive terms.";
convertClosedGroupToOperatorExpressions[
  group : {pictures : {_?validPictureSpecQ, _?validPictureSpecQ}, states_List},
  canonicalizeIndices_
] := Module[
  {convertedExpressions},
  convertedExpressions = DeleteCases[
    closedOperatorFromJoinedModeList[pictures, #, 0, 0, canonicalizeIndices] & /@ states,
    0
  ];
  {pictures, DeleteDuplicates[convertedExpressions]}
];

convertClosedResultToOperatorExpressions::usage =
  "Converts grouped closed-string mode results to deduplicated full operator expressions.";
convertClosedResultToOperatorExpressions[result_, canonicalizeIndices_] :=
  convertGroupedResultToOperators[
    result,
    {{_?validPictureSpecQ, _?validPictureSpecQ}, _List},
    convertClosedGroupToOperatorExpressions,
    canonicalizeIndices
  ];

convertClosedResultToRepresentation::usage =
  "Converts closed-string grouped basis output to the requested representation.";
convertClosedResultToRepresentation[result_, "Modes", _] := result;
convertClosedResultToRepresentation[result_, "Operators", canonicalizeIndices_] :=
  convertGroupedResultToOperators[
    result,
    {{_?validPictureSpecQ, _?validPictureSpecQ}, _List},
    convertClosedGroupToOperators,
    canonicalizeIndices
  ];

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
  - "GSOParity" -> "Even"|"Odd"|"All": parity filter (default "Even")
  - "GSOProjected" -> True|False: legacy alias (True->"Even", False->"All")

  Output: {{picture_L, picture_R}, {state1, state2, ...}}
  where each state is a joined mode list (holo modes ++ anti modes)
*)

validGSOParitySelectionQ::usage =
  "Checks whether a GSO parity selector string is one of \"Even\", \"Odd\", or \"All\".";
validGSOParitySelectionQ[value_] := MemberQ[{"Even", "Odd", "All"}, value];

GSOParitySelectionMatchesQ::usage =
  "Tests whether a parity value (+/-1) passes a GSO selector.";
GSOParitySelectionMatchesQ[parity_Integer, "All"] := True;
GSOParitySelectionMatchesQ[parity_Integer, "Even"] := parity === 1;
GSOParitySelectionMatchesQ[parity_Integer, "Odd"] := parity === -1;
GSOParitySelectionMatchesQ[_, _] := False;

GSOParitySelectionFromLegacyProjection::usage =
  "Converts legacy boolean GSOProjected option to a parity selector.";
GSOParitySelectionFromLegacyProjection[projected_?BooleanQ] :=
  If[TrueQ[projected], "Even", "All"];

readGSOParityOption::usage =
  "Reads string option \"GSOParity\" and validates it; returns default when absent.";
readGSOParityOption[opts_List, default_] :=
  basisReadValidatedOption[
    opts,
    "GSOParity",
    default,
    Function[value, value === default || validGSOParitySelectionQ[value]]
  ];

parseGSOParityOptionFromList::usage =
  "Parses GSO selector from options with legacy GSOProjected compatibility.";
parseGSOParityOptionFromList[optionList_List] := Module[
  {GSOParitySelection, GSOProjected},
  If[!OptionQ[optionList],
    Return[$Failed]
  ];
  GSOParitySelection = readGSOParityOption[optionList, Missing["NotProvided"]];
  If[GSOParitySelection === $Failed,
    Return[$Failed]
  ];
  If[GSOParitySelection =!= Missing["NotProvided"],
    Return[GSOParitySelection]
  ];
  GSOProjected = readBooleanOption[optionList, "GSOProjected", True];
  If[GSOProjected === $Failed,
    $Failed,
    GSOParitySelectionFromLegacyProjection[GSOProjected]
  ]
];

parseGSOParityOption::usage =
  "Parses GSO selector from options.";
parseGSOParityOption[opts___] :=
  parseGSOParityOptionFromList[Flatten[{opts}]];

validOutputRepresentationQ::usage =
  "Checks whether an output representation selector is \"Operators\" or \"Modes\".";
validOutputRepresentationQ[value_] := MemberQ[{"Operators", "Modes"}, value];

readOutputRepresentationOption::usage =
  "Reads option \"OutputRepresentation\" and validates it.";
readOutputRepresentationOption[opts_List, default_] :=
  basisReadValidatedOption[opts, "OutputRepresentation", default, validOutputRepresentationQ];

readCanonicalizeIndicesOption::usage =
  "Reads option \"CanonicalizeIndices\" and validates it as a boolean.";
readCanonicalizeIndicesOption[optionList_List, default_] :=
  basisReadCanonicalizeIndicesOption[optionList, default];

parseRepresentationConversionOptionsFromList::usage =
  "Parses output representation and canonicalization options from an option list.";
parseRepresentationConversionOptionsFromList[optionList_List] := Module[
  {outputRepresentation, canonicalizeIndices},
  If[!OptionQ[optionList],
    Return[$Failed]
  ];
  outputRepresentation = readOutputRepresentationOption[optionList, "Operators"];
  canonicalizeIndices = readCanonicalizeIndicesOption[optionList, True];
  If[outputRepresentation === $Failed || canonicalizeIndices === $Failed,
    $Failed,
    {outputRepresentation, canonicalizeIndices}
  ]
];

(* Parse both "LevelMatched" and GSO parity options. *)
parseFullBasisOptions[opts___] := Module[
  {optionList, levelMatched, GSOParitySelection},
  optionList = Flatten[{opts}];
  If[!OptionQ[optionList],
    Return[$Failed]
  ];
  levelMatched = readBooleanOption[optionList, "LevelMatched", True];
  GSOParitySelection = parseGSOParityOptionFromList[optionList];
  If[levelMatched === $Failed || GSOParitySelection === $Failed,
    $Failed,
    {levelMatched, GSOParitySelection}
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
  GSOParitySelection_
] := Module[{holoBasis, antiBasis},
  holoBasis = generateBasisHoloForPictureSpec[
    holoWeight,
    holoGhostNumber,
    pictureLeft,
    "GSOParity" -> GSOParitySelection
  ];
  If[holoBasis === {},
    Return[{}]
  ];
  antiBasis = generateBasisAntiHoloForPictureSpec[
    antiWeight,
    antiGhostNumber,
    pictureRight,
    "GSOParity" -> GSOParitySelection
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
  GSOParitySelection_,
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
        GSOParitySelection
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
  GSOParitySelection_,
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
          GSOParitySelection
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
  GSOParitySelection_
] := Module[
  {
    remainingMatterWeight,
    ghostModes,
    ghostParity,
    requiredMatterSelection,
    matterBasis,
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
  groundWeight = groundStateWeight[picture];
  ghostModes = Join[bcModes, superghostModes];
  ghostParity = If[modeListGSOParityContribution[ghostModes] === -1, -1, 1];
  requiredMatterSelection =
    requiredMatterGSOParitySelection[GSOParitySelection, ghostParity];
  matterBasis =
    generateBasisMatterHoloForPictureSpecWithSelection[
      groundWeight + remainingMatterWeight,
      picture,
      requiredMatterSelection,
      False
    ];
  If[matterBasis === {},
    Return[{}]
  ];
  matterModeConfigs = matterBasis[[2]];
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
      (* Apply GSO selector to the full state parity. *)
      candidateParity = GSOParityOfConfig[candidateModes, picture];
      If[GSOParitySelectionMatchesQ[candidateParity, GSOParitySelection],
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
  GSOParitySelection_
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
          GSOParitySelection
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
    GSOParitySelection,
    groundWeight,
    remainingWeight,
    bcGhostSplits,
    collectedTuples,
    basisTuples,
    bcGhostNumber,
    splitTuples,
    splitTuple
  },
  GSOParitySelection = parseGSOParityOption[opts];
  If[GSOParitySelection === $Failed,
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
        GSOParitySelection
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
] := Module[{GSOParitySelection, holoBasis},
  GSOParitySelection = parseGSOParityOption[opts];
  If[GSOParitySelection === $Failed,
    Return[{}]
  ];
  holoBasis = generateBasisHoloForPictureSpec[
    weight,
    ghostNumber,
    picture,
    "GSOParity" -> GSOParitySelection
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
    GSOParitySelection,
    holoGhostSplits,
    basisStates
  },
  parsedOptions = parseFullBasisOptions[opts];
  If[parsedOptions === $Failed,
    Return[{}]
  ];
  {levelMatched, GSOParitySelection} = parsedOptions;
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
      GSOParitySelection,
      holoGhostSplits
    ],
    collectAllSplitStates[
      weight,
      ghostNumber,
      pictureLeft,
      pictureRight,
      GSOParitySelection,
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
      "GSOParity" -> "Even"|"Odd"|"All" (default "Even")
      "GSOProjected" -> True|False (legacy alias)
    Returns: {{pictureL, pictureR}, {state1, state2, ...}}
*)

generateBasisMatterModeGroups::usage =
  "Generates grouped holomorphic matter-mode results for a user-facing picture input.";
generateBasisMatterModeGroups[
  weight_?validWeightQ,
  picture_?validPictureInputQ,
  opts___
] := Module[{groupedBySpec},
  groupedBySpec = DeleteCases[
    generateBasisMatterHoloForPictureSpec[weight, #, opts] & /@ expandPictureSpecs[picture],
    {}
  ];
  collapseExpandedResult[groupedBySpec, Length[groupedBySpec] == 1]
];

generateBasisMatterModeGroups[___] := {};

generateBasisMatterHolo::usage =
  "Generates holomorphic matter-only TypeII mode states grouped with their picture ground-state label. Option \"FermionOnly\" -> True|False (default False) suppresses free-boson dX insertions.";
generateBasisMatterHolo[
  weight_?validWeightQ,
  picture_?validPictureInputQ,
  opts___
] := generateBasisMatterModeGroups[weight, picture, opts];

generateBasisMatterHolo[___] := {};

generateBasisMatterAntiHolo::usage =
  "Generates antiholomorphic matter-only TypeII mode states grouped with their picture ground-state label. Option \"FermionOnly\" -> True|False (default False) suppresses free-boson dXt insertions.";
antiMatterGroupFromHolo::usage =
  "Converts one grouped holomorphic matter-mode entry to antiholomorphic modes.";
antiMatterGroupFromHolo[group : {picture_?validPictureSpecQ, matterModeLists_List}] :=
  {picture, (antiModeFromHolo /@ #) & /@ matterModeLists};

generateBasisMatterAntiHolo[
  weight_?validWeightQ,
  picture_?validPictureInputQ,
  opts___
] := mapGroupedResultPreservingShape[
    generateBasisMatterModeGroups[weight, picture, opts],
    {_?validPictureSpecQ, _List},
    antiMatterGroupFromHolo
  ];

generateBasisMatterAntiHolo[___] := {};

generateMatterOPEFromGroups::usage =
  "Converts grouped matter-mode results to deduplicated OPE-basis operators after parsing canonicalization options.";
generateMatterOPEFromGroups[groupedModes_, convertGroupFunction_, opts___] := Module[
  {optionList, canonicalizeIndices},
  optionList = Flatten[{opts}];
  If[!OptionQ[optionList],
    Return[{}]
  ];
  canonicalizeIndices = readCanonicalizeIndicesOption[optionList, True];
  If[canonicalizeIndices === $Failed,
    Return[{}]
  ];
  convertGroupedResultToOperators[
    groupedModes,
    {_?validPictureSpecQ, _List},
    convertGroupFunction,
    canonicalizeIndices
  ]
];

generateBasisMatterHoloOPE::usage =
  "Generates holomorphic matter-only TypeII OPE-basis operators. Option \"FermionOnly\" -> True|False (default False) suppresses free-boson dX insertions.";
generateBasisMatterHoloOPE[
  weight_?validWeightQ,
  picture_?validPictureInputQ,
  opts___
] := generateMatterOPEFromGroups[
    generateBasisMatterModeGroups[weight, picture, opts],
    convertMatterGroupToOperatorsHolo,
    opts
  ];

generateBasisMatterHoloOPE[___] := {};

generateBasisMatterAntiHoloOPE::usage =
  "Generates antiholomorphic matter-only TypeII OPE-basis operators. Option \"FermionOnly\" -> True|False (default False) suppresses free-boson dXt insertions.";
generateBasisMatterAntiHoloOPE[
  weight_?validWeightQ,
  picture_?validPictureInputQ,
  opts___
] := generateMatterOPEFromGroups[
    generateBasisMatterAntiHolo[weight, picture, opts],
    convertMatterGroupToOperatorsAnti,
    opts
  ];

generateBasisMatterAntiHoloOPE[___] := {};

generateBasisHolo[
  weight_?validWeightQ,
  ghostNumber_Integer,
  picture_?validPictureInputQ,
  opts___
] := Module[
  {optionList, parsedRepresentationOptions, outputRepresentation, canonicalizeIndices, basisBySpec},
  optionList = Flatten[{opts}];
  parsedRepresentationOptions = parseRepresentationConversionOptionsFromList[optionList];
  If[parsedRepresentationOptions === $Failed,
    Return[{}]
  ];
  {outputRepresentation, canonicalizeIndices} = parsedRepresentationOptions;
  (* Expand picture to specs (handles chirality for Ramond) *)
  basisBySpec = Flatten[
    generateBasisHoloForPictureSpec[weight, ghostNumber, #, opts] & /@ expandPictureSpecs[picture],
    1
  ];
  convertHoloBasisToRepresentation[
    DeleteDuplicates[basisBySpec],
    outputRepresentation,
    canonicalizeIndices
  ]
];

generateBasisHolo[___] := {};

generateBasisAntiHolo[
  weight_?validWeightQ,
  ghostNumber_Integer,
  picture_?validPictureInputQ,
  opts___
] := Module[
  {optionList, parsedRepresentationOptions, outputRepresentation, canonicalizeIndices, basisBySpec},
  optionList = Flatten[{opts}];
  parsedRepresentationOptions = parseRepresentationConversionOptionsFromList[optionList];
  If[parsedRepresentationOptions === $Failed,
    Return[{}]
  ];
  {outputRepresentation, canonicalizeIndices} = parsedRepresentationOptions;
  basisBySpec = Flatten[
    generateBasisAntiHoloForPictureSpec[weight, ghostNumber, #, opts] & /@ expandPictureSpecs[picture],
    1
  ];
  convertAntiBasisToRepresentation[
    DeleteDuplicates[basisBySpec],
    outputRepresentation,
    canonicalizeIndices
  ]
];

generateBasisAntiHolo[___] := {};

generateBasis[
  weight_?validWeightQ,
  ghostNumber_Integer,
  pictures : {pictureLeft_?validPictureInputQ, pictureRight_?validPictureInputQ},
  opts___
] := Module[
  {
    optionList,
    parsedRepresentationOptions,
    outputRepresentation,
    canonicalizeIndices,
    b0MinusProjectedQ,
    leftSpecs,
    rightSpecs,
    groupedResults,
    groupedModeResult,
    convertedClosedBasis
  },
  optionList = Flatten[{opts}];
  parsedRepresentationOptions = parseRepresentationConversionOptionsFromList[optionList];
  If[parsedRepresentationOptions === $Failed,
    Return[{}]
  ];
  {outputRepresentation, canonicalizeIndices} = parsedRepresentationOptions;
  b0MinusProjectedQ = basisReadB0MinusProjectedOption[optionList, False];
  If[b0MinusProjectedQ === $Failed,
    Return[{}]
  ];
  If[TrueQ[b0MinusProjectedQ] && outputRepresentation === "Modes",
    Return[{}]
  ];
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
  groupedModeResult = collapseExpandedResult[
    groupedResults,
    Length[leftSpecs] == 1 && Length[rightSpecs] == 1
  ];
  If[TrueQ[b0MinusProjectedQ],
    convertedClosedBasis = convertClosedResultToOperatorExpressions[
      groupedModeResult,
      canonicalizeIndices
    ];
    basisIndependentROperatorsFromExpressions[
      basisProjectOperatorBasisByB0Minus[convertedClosedBasis]
    ],
    convertClosedResultToRepresentation[
      groupedModeResult,
      outputRepresentation,
      canonicalizeIndices
    ]
  ]
];

generateBasis[___] := {};


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
