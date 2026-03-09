(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`OPE`TypeII`FlatSpace`CountSinglet`"];


(* ::Section:: *)
(*Declare public variables and methods*)


countSinglets::usage =
  "countSinglets[nChiral, nAntichiral, nVectors] gives the Spin(10) singlet multiplicity in 16^nChiral TensorProduct 16bar^nAntichiral TensorProduct 10^nVectors.";

countSinglets::badarg =
  "Arguments `1`, `2`, and `3` must be nonnegative integers.";


(* ::Section:: *)
(*Logic*)


Begin["Private`"];

weightRank::usage = "weightRank is the rank of the D5 weight lattice used for Spin(10) singlet counting.";
weightRank = 5;

zeroWeight::usage = "zeroWeight is the scaled zero weight on the D5 weight lattice.";
zeroWeight = ConstantArray[0, weightRank];

vectorRepresentationWeights::usage = "vectorRepresentationWeights is the scaled weight list of the 10-dimensional vector representation.";
vectorRepresentationWeights = Join[
  Table[ReplacePart[zeroWeight, i -> 2], {i, 1, weightRank}],
  Table[ReplacePart[zeroWeight, i -> -2], {i, 1, weightRank}]
];

chiralRepresentationWeights::usage = "chiralRepresentationWeights is the scaled weight list of the chiral 16-dimensional Spin(10) representation.";
chiralRepresentationWeights = Select[Tuples[{1, -1}, weightRank], EvenQ[Count[#, -1]] &];

antichiralRepresentationWeights::usage = "antichiralRepresentationWeights is the scaled weight list of the antichiral 16-dimensional Spin(10) representation.";
antichiralRepresentationWeights = Select[Tuples[{1, -1}, weightRank], OddQ[Count[#, -1]] &];

positiveRootWeights::usage = "positiveRootWeights is the scaled D5 positive-root list {2 ei +/- 2 ej} with i < j.";
positiveRootWeights = Flatten[
  Table[
    {
      ReplacePart[zeroWeight, {i -> 2, j -> 2}],
      ReplacePart[zeroWeight, {i -> 2, j -> -2}]
    },
    {i, 1, weightRank - 1},
    {j, i + 1, weightRank}
  ],
  2
];

identityCharacter::usage = "identityCharacter[] returns the sparse weight polynomial of the trivial representation.";
identityCharacter[] := <|zeroWeight -> 1|>;

shiftWeightPolynomial::usage = "shiftWeightPolynomial[poly, alpha, factor] shifts every monomial weight by alpha and rescales coefficients by factor.";
shiftWeightPolynomial[poly_Association, alpha_List, factor_: 1] :=
  Association @ KeyValueMap[(#1 + alpha) -> factor #2 &, poly];

multiplyByRootFactor::usage = "multiplyByRootFactor[poly, alpha] multiplies poly by the Weyl factor term (1 - e^alpha).";
multiplyByRootFactor[poly_Association, alpha_List] := Select[
  Merge[{poly, shiftWeightPolynomial[poly, alpha, -1]}, Total],
  # =!= 0 &
];

convolveWithWeights::usage = "convolveWithWeights[poly, weights] tensors a sparse character polynomial with a multiplicity-one weight list.";
convolveWithWeights[poly_Association, weights_List] := Module[{polyRules, reaped, i, j},
  polyRules = Normal[poly];
  reaped = Last @ Reap[
    For[i = 1, i <= Length[polyRules], i++,
      For[j = 1, j <= Length[weights], j++,
        Sow[(polyRules[[i, 1]] + weights[[j]]) -> polyRules[[i, 2]]]
      ]
    ]
  ];
  If[reaped === {}, <||>, Merge[First[reaped], Total]]
];

weylFactorPolynomial::usage = "weylFactorPolynomial[] memoizes the sparse Weyl factor Product_{alpha>0} (1 - e^alpha) for D5.";
weylFactorPolynomial[] := weylFactorPolynomial[] =
  Fold[multiplyByRootFactor, identityCharacter[], positiveRootWeights];

tensorProductCharacter::usage = "tensorProductCharacter[nChiral, nAntichiral, nVectors] memoizes the sparse character polynomial for 16^nChiral TensorProduct 16bar^nAntichiral TensorProduct 10^nVectors.";
tensorProductCharacter[0, 0, 0] = identityCharacter[];
tensorProductCharacter[nChiral_Integer?NonNegative, nAntichiral_Integer?NonNegative, nVectors_Integer?NonNegative] :=
  tensorProductCharacter[nChiral, nAntichiral, nVectors] = Which[
    nChiral > 0,
      convolveWithWeights[
        tensorProductCharacter[nChiral - 1, nAntichiral, nVectors],
        chiralRepresentationWeights
      ],
    nAntichiral > 0,
      convolveWithWeights[
        tensorProductCharacter[nChiral, nAntichiral - 1, nVectors],
        antichiralRepresentationWeights
      ],
    True,
      convolveWithWeights[
        tensorProductCharacter[nChiral, nAntichiral, nVectors - 1],
        vectorRepresentationWeights
      ]
  ];

coefficientLookup::usage = "coefficientLookup[poly, weight] returns the exact coefficient of weight in a sparse polynomial, even when weight is a list key.";
coefficientLookup[poly_Association, weight_List] := Module[{taken},
  taken = KeyTake[poly, {weight}];
  If[taken === <||>, 0, First[Values[taken]]]
];

singletMultiplicityFromCharacter::usage = "singletMultiplicityFromCharacter[character] extracts the Spin(10) singlet multiplicity from a sparse character polynomial by the Weyl constant-term formula.";
singletMultiplicityFromCharacter[character_Association] := Module[{weyl},
  weyl = weylFactorPolynomial[];
  Total[KeyValueMap[#2 coefficientLookup[weyl, -#1] &, character]]
];

countSinglets::usage =
  "countSinglets[nChiral, nAntichiral, nVectors] gives the Spin(10) singlet multiplicity in 16^nChiral TensorProduct 16bar^nAntichiral TensorProduct 10^nVectors.";
countSinglets[nChiral_, nAntichiral_, nVectors_] := Module[{},
  If[
    !And @@ (IntegerQ[#] && # >= 0 & /@ {nChiral, nAntichiral, nVectors}),
    Message[countSinglets::badarg, nChiral, nAntichiral, nVectors];
    Return[$Failed]
  ];
  countSinglets[nChiral, nAntichiral, nVectors] =
    singletMultiplicityFromCharacter[tensorProductCharacter[nChiral, nAntichiral, nVectors]]
];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
