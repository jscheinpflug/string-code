(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`OPE`TypeII`FlatSpace`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];
Needs["StringCode`Symbols`TypeII`FlatSpace`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`TypeII`"];
Needs["StringCode`Operators`"];
Needs["StringCode`OPE`"];
Needs["StringCode`BasisGeneration`TypeII`"];
Needs["StringCode`BasisGeneration`TypeII`FlatSpace`"];
Needs["StringCode`OPE`TypeII`FlatSpace`TensorStructures`"];
Needs["StringCode`OPE`TypeII`FlatSpace`TensorStructuresVisualize`"];


(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


Begin["Private`"];

projectionExponentReplacement = {\[Alpha]p -> 0};

hasSpinFieldQ::usage = "Checks whether a normal-ordered operator contains TypeII spin fields S or St.";
hasSpinFieldQ[Ra_ /; RTest[Ra]] := AnyTrue[List @@ Ra, MemberQ[{S, St}, Head[#]] &];


OPEWickList[rList_List] := Which[
  rList === {}, 1,
  Length[rList] === 1, First[rList],
  True, OPEWick[First[rList], OPEWickList[Rest[rList]]]
];

psiExpPhiHeads = {\[Psi], \[Psi]t, d\[Phi], d\[Phi]t, exp\[Phi]b, exp\[Phi]f, exp\[Phi]tb, exp\[Phi]tf};
purePsiExpPhiQ[Ra_ /; RTest[Ra]] := AllTrue[List @@ Ra, MemberQ[psiExpPhiHeads, Head[#]] &];

pictureContributionHolo::usage = "Returns the picture number contribution of a holomorphic field (S or expΦf/expΦb).";
pictureContributionHolo[field_] := Which[
  MatchQ[Head[field], S], field[[2]],
  MatchQ[Head[field], expΦf | expΦb], field[[1]],
  True, 0
];

pictureContributionAntiHolo::usage = "Returns the picture number contribution of an antiholomorphic field (St or expΦtf/expΦtb).";
pictureContributionAntiHolo[field_] := Which[
  MatchQ[Head[field], St], field[[2]],
  MatchQ[Head[field], expΦtf | expΦtb], field[[1]],
  True, 0
];

totalInputPicture::usage = "Computes total picture number from a list of R-operators using the given contribution function.";
totalInputPicture[ops_List, contributionFn_] :=
  Total[contributionFn /@ Flatten[List @@ # & /@ Select[ops, RTest]]];

extractMatterRepresentations::usage = "Extracts SO(1,9) vector and spinor indices from ψ/S (or ψt/St) fields in a normal-ordered operator.";
extractMatterRepresentations[Ra_ /; RTest[Ra], psiHead_, spinHead_] := Module[
  {fields, vectors, spinModeVecs, spinors},
  fields = List @@ Ra;
  vectors = Cases[fields, f_ /; Head[f] === psiHead :> f[[1]]];
  spinModeVecs = Flatten[
    Cases[fields, f_ /; Head[f] === spinHead :>
      Join[
        Cases[f[[3]], {n_?NumericQ, idx_ /; !NumericQ[idx]} :> idx],
        Cases[f[[3]], {idx_ /; !NumericQ[idx], n_?NumericQ} :> idx]
      ]
    ]
  ];
  vectors = Join[vectors, spinModeVecs];
  spinors = Cases[fields,
    f_ /; Head[f] === spinHead :> {f[[1, 1]], f[[1, 2]]}
  ];
  <|"vector" -> vectors, "spinor" -> spinors|>
];

mergeRepresentations::usage = "Merges a list of representation associations into a single combined association.";
mergeRepresentations[reps_List] := <|
  "vector" -> Flatten[#["vector"] & /@ reps],
  "spinor" -> Flatten[#["spinor"] & /@ reps, 1]
|>;

inputGSOParityString::usage = "Computes the product of GSO parities of input R-operators and returns \"Even\" or \"Odd\".";
inputGSOParityString[ops_List] := Module[{parity},
  parity = Times @@ (GSOParity /@ ops);
  If[parity === 1, "Even", "Odd"]
];

generateSpinFieldOPEData::usage = "Generates {operator, tensorStructures} pairs for a spin field OPE in one chiral sector.";
generateSpinFieldOPEData[
  ops_List,
  targetWeight_,
  basisGeneratorFn_,
  psiHead_, spinHead_,
  pictureContributionFn_
] := Module[
  {incomingReps, totalPicture, gsoParity, basisOps, result},

  incomingReps = mergeRepresentations[
    extractMatterRepresentations[#, psiHead, spinHead] & /@ ops
  ];

  totalPicture = totalInputPicture[ops, pictureContributionFn];
  gsoParity = inputGSOParityString[ops];

  basisOps = basisGeneratorFn[targetWeight, totalPicture,
    "GSOParity" -> gsoParity, "OutputRepresentation" -> "Operators"];
  If[basisOps === {}, Return[{}]];

  Select[
    Function[op, Module[{outReps, tensorStructures},
      outReps = extractMatterRepresentations[op, psiHead, spinHead];
      tensorStructures = Flatten[
        generateTensorStructures[incomingReps, outReps, "RepresentativesOnly" -> True], 1];
      {op, tensorStructures}
    ]] /@ basisOps,
    #[[2]] =!= {} &
  ]
];

OPE[Ra_, Rb_] := OPEWick[Ra, Rb] /; (
  RTest[Ra] && RTest[Rb] &&
  purePsiExpPhiQ[Ra] && purePsiExpPhiQ[Rb]
);

combineChiral[a_, b_] := Which[
  a === 0 || b === 0, 0,
  a === 1, b,
  b === 1, a,
  True, R[a, b]
];

opeDataToExpression::usage = "Converts {{op, {tensor, ...}}, ...} to a sum of tensor * op terms.";
opeDataToExpression[data_List] :=
  Total[Flatten[Function[{op, ts}, Table[t op, {t, ts}]] @@@ data]];

OPEProjected[wH_, wA_][Ra__ /; (And @@ (RTest /@ {Ra}) && AnyTrue[{Ra}, hasSpinFieldQ])] :=
Module[
  {localLists, splitLists, sign, holoOps, antiOps, holoData, antiData, holoExpr, antiExpr},

  localLists = List @@ # & /@ {Ra};
  splitLists = splitOperators[#, isHolomorphic, isAntiHolomorphic] & /@ localLists;
  sign = If[Flatten[localLists] === {}, 1,
    factorizationSign[Flatten[localLists], isHolomorphic, isAntiHolomorphic]
  ];

  holoOps = Select[R @@@ (splitLists[[All, 1]]), RTest];
  antiOps = Select[R @@@ (splitLists[[All, 2]]), RTest];

  holoData = If[holoOps =!= {},
    generateSpinFieldOPEData[holoOps, wH, generateBasisMatterHolo,
      ψ, S, pictureContributionHolo],
    {}
  ];
  antiData = If[antiOps =!= {},
    generateSpinFieldOPEData[antiOps, wA, generateBasisMatterAntiHolo,
      ψt, St, pictureContributionAntiHolo],
    {}
  ];

  holoExpr = Which[holoOps === {}, 1, holoData === {}, 0, True, opeDataToExpression[holoData]];
  antiExpr = Which[antiOps === {}, 1, antiData === {}, 0, True, opeDataToExpression[antiData]];

  sign combineChiral[holoExpr, antiExpr]
];

OPEProjected[wH_, wA_][Ra__ /; (And @@ (RTest /@ {Ra}) && !AnyTrue[{Ra}, hasCollapsable] && !AnyTrue[{Ra}, hasSpinFieldQ])] := Module[
  {
    \[Epsilon]Holo, \[Epsilon]AntiHolo, localLists, splitLists, sign, holoOps, antiOps,
    insertionWeightHolo, insertionWeightAntiHolo, targetWeightHolo, targetWeightAntiHolo,
    projectedHolo, projectedAntiHolo
  },
  localLists = List @@ # & /@ {Ra};
  splitLists = splitOperators[#, isHolomorphic, isAntiHolomorphic] & /@ localLists;
  insertionWeightHolo = Total[totalWeightHolo /@ {Ra}];
  insertionWeightAntiHolo = Total[totalWeightAntiHolo /@ {Ra}];
  targetWeightHolo = wH - insertionWeightHolo;
  targetWeightAntiHolo = wA - insertionWeightAntiHolo;

  sign = If[Flatten[localLists] === {}, 1, factorizationSign[Flatten[localLists], isHolomorphic, isAntiHolomorphic]];

  holoOps = Select[R @@@ (splitLists[[All, 1]]), RTest];
  antiOps = Select[R @@@ (splitLists[[All, 2]]), RTest];

  projectedHolo = projectHolo[
    OPEWickList[rescaleR[\[Epsilon]Holo] /@ holoOps],
    targetWeightHolo, \[Epsilon]Holo
  ];
  projectedAntiHolo = projectAntiHolo[
    OPEWickList[rescaleR[\[Epsilon]AntiHolo] /@ antiOps],
    targetWeightAntiHolo, \[Epsilon]AntiHolo
  ];

  sign combineChiral[projectedHolo, projectedAntiHolo]
];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
