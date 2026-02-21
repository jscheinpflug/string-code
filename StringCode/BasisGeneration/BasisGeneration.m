(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`BasisGeneration`"];


Needs["StringCode`Symbols`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`Operators`"];


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
basisReadValidatedOption::usage =
  "Reads one option with legacy-symbol safety and validates via a predicate function.";
basisReadValidatedOption[opts_List, optionName_String, default_, validatorFunction_] := Module[
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
  If[TrueQ[validatorFunction[optionValue]], optionValue, $Failed]
];

readBooleanOption::usage =
  "Reads one boolean option by name, returning $Failed on invalid input.";
readBooleanOption[opts_List, optionName_String, default_] :=
  basisReadValidatedOption[opts, optionName, default, BooleanQ];

basisReadCanonicalizeIndicesOption::usage =
  "Reads option \"CanonicalizeIndices\" as a boolean, returning $Failed on invalid input.";
basisReadCanonicalizeIndicesOption[opts_List, default_: True] :=
  readBooleanOption[opts, "CanonicalizeIndices", default];

basisReadB0MinusProjectedOption::usage =
  "Reads option \"B0MinusProjected\" as a boolean, returning $Failed on invalid input.";
basisReadB0MinusProjectedOption[opts_List, default_: False] :=
  readBooleanOption[opts, "B0MinusProjected", default];

basisParseSinglePositionAndOptions::usage =
  "Parses trailing arguments as either {position} or option rules, returning {position, optionList}.";
basisParseSinglePositionAndOptions[args_List, defaultPosition_] := Which[
  args === {}, {defaultPosition, {}},
  OptionQ[args], {defaultPosition, args},
  Length[args] >= 1 && OptionQ[Rest[args]], {First[args], Rest[args]},
  True, $Failed
];

basisParsePositionAndCanonicalizeOption::usage =
  "Parses one optional position argument plus \"CanonicalizeIndices\" option.";
basisParsePositionAndCanonicalizeOption[
  args_List,
  defaultPosition_,
  defaultCanonicalize_: True
] := Module[{parsed, position, optionList, canonicalizeIndices},
  parsed = basisParseSinglePositionAndOptions[args, defaultPosition];
  If[parsed === $Failed,
    Return[$Failed]
  ];
  {position, optionList} = parsed;
  canonicalizeIndices = basisReadCanonicalizeIndicesOption[optionList, defaultCanonicalize];
  If[canonicalizeIndices === $Failed,
    Return[$Failed]
  ];
  {position, canonicalizeIndices}
];

bmodeHolo::usage =
  "Acts one holomorphic b-ghost mode on an operator expression.";
bmodeHolo[contourCenter_][mode_][Ra_ /; RTest[Ra]] := Module[
  {result = 0, cAssociations = <||>, fermionNumber = 0, position = 1},
  Scan[
    Function[Relem,
      If[Head[Relem] === c,
        If[mode >= Relem[[1]] - 1,
          If[Relem[[2]] - contourCenter =!= 0,
            AssociateTo[
              cAssociations,
              position -> {
                Relem -> (-1)^fermionNumber
                  1/Factorial[mode - (Relem[[1]] - 1)]
                  (Relem[[2]] - contourCenter)^(mode - (Relem[[1]] - 1))
              }
            ],
            If[mode === Relem[[1]] - 1,
              AssociateTo[cAssociations, position -> {Relem -> (-1)^fermionNumber}]
            ]
          ]
        ]
      ];
      If[isFermion[Head[Relem]], fermionNumber = fermionNumber + 1];
      position = position + 1;
    ],
    Ra
  ];
  KeyValueMap[
    Function[{currentPosition, replacement},
      result = result + ReplaceAt[Ra, replacement, currentPosition]
    ],
    cAssociations
  ];
  result
];

bmodeAntiHolo::usage =
  "Acts one antiholomorphic b-ghost mode on an operator expression.";
bmodeAntiHolo[contourCenter_][mode_][Ra_ /; RTest[Ra]] := Module[
  {result = 0, cAssociations = <||>, fermionNumber = 0, position = 1},
  Scan[
    Function[Relem,
      If[Head[Relem] === ct,
        If[mode >= Relem[[1]] - 1,
          If[Relem[[2]] - contourCenter =!= 0,
            AssociateTo[
              cAssociations,
              position -> {
                Relem -> (-1)^fermionNumber
                  1/Factorial[mode - (Relem[[1]] - 1)]
                  (Relem[[2]] - contourCenter)^(mode - (Relem[[1]] - 1))
              }
            ],
            If[mode === Relem[[1]] - 1,
              AssociateTo[cAssociations, position -> {Relem -> (-1)^fermionNumber}]
            ]
          ]
        ]
      ];
      If[isFermion[Head[Relem]], fermionNumber = fermionNumber + 1];
      position = position + 1;
    ],
    Ra
  ];
  KeyValueMap[
    Function[{currentPosition, replacement},
      result = result + ReplaceAt[Ra, replacement, currentPosition]
    ],
    cAssociations
  ];
  result
];

bmodeHolo[contourCenter_][mode_][a_ + b_] :=
  bmodeHolo[contourCenter][mode][a] + bmodeHolo[contourCenter][mode][b];
bmodeHolo[contourCenter_][mode_][a_ b_] :=
  a bmodeHolo[contourCenter][mode][b] /; isScalarFactorQ[a];
bmodeHolo[contourCenter_][mode_][0] := 0;

bmodeAntiHolo[contourCenter_][mode_][a_ + b_] :=
  bmodeAntiHolo[contourCenter][mode][a] + bmodeAntiHolo[contourCenter][mode][b];
bmodeAntiHolo[contourCenter_][mode_][a_ b_] :=
  a bmodeAntiHolo[contourCenter][mode][b] /; isScalarFactorQ[a];
bmodeAntiHolo[contourCenter_][mode_][0] := 0;

actBGhostMode::usage =
  "Acts a b-ghost mode placeholder on a local-operator expression.";
actBGhostMode[a_, op1_ + op2_] := actBGhostMode[a, op1] + actBGhostMode[a, op2];
actBGhostMode[a_, b_ c_] := b actBGhostMode[a, c] /; isScalarFactorQ[b];

actBGhostMode[
  bMode : (bmodeHolo[contourCenter_][mode_] | bmodeAntiHolo[contourCenter_][mode_]),
  multiOp_ /; MultiOpTest[multiOp]
] := Module[{result = 0, opList, parities},
  opList = List @@ multiOp;
  parities = Map[parityOp, opList];
  Do[
    result = result + (-1)^(Total[Take[parities, i - 1]]) MultiOp @@ MapAt[
      actBGhostMode[bMode, #] &,
      opList,
      i
    ],
    {i, 1, Length[opList]}
  ];
  result
];

actBGhostMode[
  bmodeHolo[contourCenter_][mode_][position_],
  multiOp_ /; MultiOpTest[multiOp]
] := actBGhostMode[bmodeHolo[contourCenter][mode], multiOp];

actBGhostMode[
  bmodeAntiHolo[contourCenter_][mode_][position_],
  multiOp_ /; MultiOpTest[multiOp]
] := actBGhostMode[bmodeAntiHolo[contourCenter][mode], multiOp];

actBGhostMode[bmodeHolo[contourCenter_][mode_][position_], Ra_ /; RTest[Ra]] :=
  bmodeHolo[contourCenter][mode][Ra];
actBGhostMode[bmodeAntiHolo[contourCenter_][mode_][position_], Ra_ /; RTest[Ra]] :=
  bmodeAntiHolo[contourCenter][mode][Ra];
actBGhostMode[bmodeHolo[contourCenter_][mode_], Ra_ /; RTest[Ra]] :=
  bmodeHolo[contourCenter][mode][Ra];
actBGhostMode[bmodeAntiHolo[contourCenter_][mode_], Ra_ /; RTest[Ra]] :=
  bmodeAntiHolo[contourCenter][mode][Ra];
actBGhostMode[_, a_ /; NumericQ[a]] := 0;

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

basisApplyB0Minus::usage =
  "Applies b0m = b0 - bt0 to an operator expression using shared b-ghost mode action.";
basisApplyB0Minus[expr_] :=
  actBGhostMode[bmodeHolo[0][0], expr] - actBGhostMode[bmodeAntiHolo[0][0], expr];

basisSplitScalarAndOperatorTerm::usage =
  "Splits one expanded term into {scalarCoefficient, operatorKey} for linear-map assembly.";
basisSplitScalarAndOperatorTerm[term_] := Module[{factors, scalarFactors, operatorFactors},
  Which[
    term === 0, {0, None},
    RTest[term] || term === 1, {1, term},
    Head[term] === Times,
      factors = List @@ term;
      scalarFactors = Select[factors, isScalarFactorQ];
      operatorFactors = Select[factors, RTest];
      Which[
        Length[operatorFactors] === 1,
          {If[scalarFactors === {}, 1, Times @@ scalarFactors], First[operatorFactors]},
        operatorFactors === {} && AllTrue[factors, isScalarFactorQ],
          {Times @@ factors, 1},
        True,
          {1, term}
      ],
    isScalarFactorQ[term], {term, 1},
    True, {1, term}
  ]
];

basisExpressionToOperatorAssociation::usage =
  "Converts an operator expression to an association operatorKey -> scalarCoefficient.";
basisExpressionToOperatorAssociation[expr_] := Module[
  {expandedExpr, terms, association = <||>, coefficient, operatorKey},
  expandedExpr = Expand[expr];
  terms = Which[
    expandedExpr === 0, {},
    Head[expandedExpr] === Plus, List @@ expandedExpr,
    True, {expandedExpr}
  ];
  Scan[
    Function[term,
      {coefficient, operatorKey} = basisSplitScalarAndOperatorTerm[term];
      If[operatorKey =!= None && coefficient =!= 0,
        association[operatorKey] =
          Lookup[association, operatorKey, 0] + coefficient
      ]
    ],
    terms
  ];
  Association @ Select[Normal[association], #[[2]] =!= 0 &]
];

basisLinearMapMatrixFromAssociations::usage =
  "Builds a matrix for a linear map whose columns are operator-image associations.";
basisLinearMapMatrixFromAssociations[domainImageAssociations_List, codomainBasis_List] :=
  Table[
    Lookup[domainImageAssociations[[column]], codomainBasis[[row]], 0],
    {row, 1, Length[codomainBasis]},
    {column, 1, Length[domainImageAssociations]}
  ];

basisNumericKernelVectorQ::usage =
  "Returns True when every entry in a kernel vector is numeric.";
basisNumericKernelVectorQ[vector_List] := AllTrue[vector, NumericQ];

basisNormalizeKernelVector::usage =
  "Normalizes a kernel basis vector to a primitive integer form with deterministic sign.";
basisNormalizeKernelVector[vector_List] := Module[
  {
    rationalVector,
    nonzeroEntries,
    denominatorLCM,
    integerVector,
    integerNonzeroEntries,
    commonFactor,
    primitiveVector,
    firstNonzero
  },
  If[!basisNumericKernelVectorQ[vector],
    Return[vector]
  ];
  rationalVector = Rationalize[vector, 0];
  If[!AllTrue[rationalVector, MatchQ[#, _Integer | _Rational] &],
    Return[vector]
  ];
  nonzeroEntries = Select[rationalVector, # =!= 0 &];
  If[nonzeroEntries === {},
    Return[rationalVector]
  ];
  denominatorLCM = LCM @@ (Denominator /@ nonzeroEntries);
  integerVector = Expand[denominatorLCM rationalVector];
  integerNonzeroEntries = Select[integerVector, # =!= 0 &];
  commonFactor = GCD @@ (Abs /@ integerNonzeroEntries);
  primitiveVector = If[commonFactor === 0, integerVector, integerVector/commonFactor];
  firstNonzero = First[Select[primitiveVector, # =!= 0 &]];
  If[firstNonzero < 0, -primitiveVector, primitiveVector]
];

basisCombinationFromKernelVector::usage =
  "Builds one operator combination from a kernel vector and the original domain basis.";
basisCombinationFromKernelVector[kernelVector_List, domainBasis_List] := Total[
  MapThread[
    If[#1 === 0, 0, #1 #2] &,
    {kernelVector, domainBasis}
  ]
];

basisExpandedOperatorTerms::usage =
  "Expands an operator expression and returns additive terms.";
basisExpandedOperatorTerms[expr_] := Module[{expandedExpr},
  expandedExpr = Expand[expr];
  Which[
    expandedExpr === 0, {},
    Head[expandedExpr] === Plus, List @@ expandedExpr,
    True, {expandedExpr}
  ]
];

basisExtractROperatorFactorsFromTerm::usage =
  "Extracts top-level R[...] multiplicative factors from one additive term.";
basisExtractROperatorFactorsFromTerm[term_] :=
  Select[
    If[Head[term] === Times, List @@ term, {term}],
    RTest
  ];

basisIndependentROperatorsFromExpression::usage =
  "Extracts structurally unique R[...] terms from one operator expression.";
basisIndependentROperatorsFromExpression[expr_] :=
  DeleteDuplicates[
    Flatten[basisExtractROperatorFactorsFromTerm /@ basisExpandedOperatorTerms[expr], 1]
  ];

basisIndependentROperatorsFromExpressions::usage =
  "Extracts structurally unique R[...] terms across a list of operator expressions.";
basisIndependentROperatorsFromExpressions[expressions_List] :=
  DeleteDuplicates[
    Flatten[basisIndependentROperatorsFromExpression /@ expressions, 1]
  ];

basisProjectOperatorBasisByB0Minus::usage =
  "Projects an operator basis to the b0m-kernel and returns a basis of surviving combinations.";
basisProjectOperatorBasisByB0Minus[basisOperators_List] := Module[
  {
    domainBasis,
    imageExpressions,
    imageAssociations,
    codomainBasis,
    mapMatrix,
    kernelVectors,
    normalizedKernelVectors,
    projectedBasis
  },
  domainBasis = DeleteDuplicates[basisOperators];
  If[domainBasis === {},
    Return[{}]
  ];
  imageExpressions = Expand[basisApplyB0Minus[#]] & /@ domainBasis;
  imageAssociations = basisExpressionToOperatorAssociation /@ imageExpressions;
  codomainBasis = SortBy[
    DeleteDuplicates[Flatten[Keys /@ imageAssociations]],
    ToString[InputForm[#]] &
  ];
  If[codomainBasis === {},
    Return[domainBasis]
  ];
  mapMatrix = basisLinearMapMatrixFromAssociations[imageAssociations, codomainBasis];
  kernelVectors = NullSpace[mapMatrix];
  If[kernelVectors === {},
    Return[{}]
  ];
  normalizedKernelVectors = basisNormalizeKernelVector /@ kernelVectors;
  projectedBasis = DeleteDuplicates[
    Expand[basisCombinationFromKernelVector[#, domainBasis]] & /@ normalizedKernelVectors
  ];
  DeleteCases[projectedBasis, 0]
];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
