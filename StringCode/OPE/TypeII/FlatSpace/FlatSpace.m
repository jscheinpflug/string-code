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
If[FreeQ[Options[OPEProjected], "RandomSeed" -> _], Options[OPEProjected] = Append[Options[OPEProjected], "RandomSeed" -> Automatic]];

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

getOutgoingOperatorsTensors::usage = "Returns sign and outgoing spin-field tensor data split into holomorphic/antiholomorphic sectors.";
getOutgoingOperatorsTensors[ops_List, wH_, wA_] := Module[{l, s, sign, hOps, aOps, hData, aData},
  l = List @@ # & /@ ops; s = splitOperators[#, isHolomorphic, isAntiHolomorphic] & /@ l;
  sign = If[Flatten[l] === {}, 1, factorizationSign[Flatten[l], isHolomorphic, isAntiHolomorphic]];
  hOps = Select[R @@@ (s[[All, 1]]), RTest]; aOps = Select[R @@@ (s[[All, 2]]), RTest];
  hData = If[hOps === {}, {}, generateSpinFieldOPEData[hOps, wH, generateBasisMatterHolo, ψ, S, pictureContributionHolo]];
  aData = If[aOps === {}, {}, generateSpinFieldOPEData[aOps, wA, generateBasisMatterAntiHolo, ψt, St, pictureContributionAntiHolo]];
  <|"sign" -> sign, "holoOps" -> hOps, "antiOps" -> aOps, "holoData" -> hData, "antiData" -> aData|>
];

attachCoefficients::usage = "Builds Sum[a[i] tensor op] from spin-field OPE data, returning {expr,lastUsedIndex}.";
attachCoefficients[data_List, offset_Integer : 0] := Module[{i = offset, terms},
  terms = Flatten[Function[{op, ts}, Table[i++; a[i] t op, {t, ts}]] @@@ data];
  {If[terms === {}, 0, Total[terms]], i}
];

gammaLinkVectorIndices::usage = "gammaLinkVectorIndices[link] extracts explicit vector indices from one gamma-chain link.";
gammaLinkVectorIndices[GammaUD[idx_]] := Flatten[{idx}];
gammaLinkVectorIndices[GammaDU[idx_]] := Flatten[{idx}];
gammaLinkVectorIndices[Gamma11UU[]] := {};
gammaLinkVectorIndices[Gamma11DD[]] := {};
gammaLinkVectorIndices[CUD] := {};
gammaLinkVectorIndices[CDU] := {};
gammaLinkVectorIndices[_] := {};


gammaProductSpinorChiralities::usage = "gammaProductSpinorChiralities[links] infers the endpoint chiralities carried by a GammaProduct link list.";
gammaProductSpinorChiralities[links_List] := Module[{reducedLinks, left, right},
  If[links =!= {} && First[links] === CUD, Return[{"chiral", "chiral"}]];
  If[links =!= {} && First[links] === CDU, Return[{"antichiral", "antichiral"}]];
  reducedLinks = DeleteCases[links, Gamma11UU[] | Gamma11DD[]];
  If[reducedLinks === {}, Return[{"chiral", "antichiral"}]];
  left = Which[
    Head[First[reducedLinks]] === GammaUD, "chiral",
    Head[First[reducedLinks]] === GammaDU, "antichiral",
    True, "chiral"
  ];
  right = left;
  Scan[
    Function[link,
      If[MatchQ[link, GammaUD[_] | GammaDU[_]],
        right = If[right === "chiral", "antichiral", "chiral"]
      ]
    ],
    reducedLinks
  ];
  {left, right}
];


spinSymbolChiralities::usage = "spinSymbolChiralities[obj] collects the intended chirality for symbolic spinor indices appearing in spin fields and gamma products.";
spinSymbolChiralities[obj_] := Module[{fieldPairs, gammaTriples, gammaPairs},
  fieldPairs = Cases[
    obj,
    (S | St)[{idx_Symbol, chirality : ("chiral" | "antichiral")}, __] :> (idx -> chirality),
    Infinity
  ];
  gammaTriples = Cases[obj, GammaProduct[links_List, s1_, s2_] :> {links, s1, s2}, Infinity];
  gammaPairs = Flatten[
    Function[{triple},
      Module[{pair = gammaProductSpinorChiralities[triple[[1]]]},
        Join[
          Cases[{triple[[2]]}, idx_Symbol :> (idx -> pair[[1]])],
          Cases[{triple[[3]]}, idx_Symbol :> (idx -> pair[[2]])]
        ]
      ]
    ] /@ gammaTriples,
    1
  ];
  Association[DeleteDuplicatesBy[Join[fieldPairs, gammaPairs], First]]
];


spinIterationValues::usage = "spinIterationValues[chirality] returns the explicit spin-vector basis used to randomize or sum over that chirality.";
spinIterationValues["antichiral"] := antichiralspins;
spinIterationValues[_] := chiralspins;


symbolIndexQ::usage = "symbolIndexQ[x] checks whether x is a symbolic index placeholder rather than a numeric value.";
symbolIndexQ[x_] := Head[x] === Symbol;

randomizeIndices::usage = "Randomizes singleton indices, sums repeated ones, and wraps every R[...] as Bosonize[R[...]].";
randomizeIndices[inputOps_List, hExpr_, aExpr_, seed_: Automatic] := Module[
  {obj = {inputOps, hExpr, aExpr}, typed, counts, vec, spi, free, dum, spinChiralities, run},
  typed = Join[
    Cases[obj, (ψ | ψt)[μ_, __] /; symbolIndexQ[μ] :> {μ, "v"}, Infinity],
    Cases[obj, (S | St)[{α_, ("chiral" | "antichiral")}, __] /; symbolIndexQ[α] :> {α, "s"}, Infinity],
    Flatten[Cases[obj, (S | St)[_, _, m_List, __] :> Join[
      ({#, "v"} & /@ Cases[m, {_?NumericQ, ν_ /; symbolIndexQ[ν]} :> ν]),
      ({#, "v"} & /@ Cases[m, {ν_ /; symbolIndexQ[ν], _?NumericQ} :> ν])], Infinity], 1],
    Flatten[Cases[obj, GammaProduct[links_List, s1_, s2_] :>
      Join[
        ({#, "v"} & /@ Select[Flatten[gammaLinkVectorIndices /@ links], symbolIndexQ]),
        ({#, "s"} & /@ Select[{s1, s2}, symbolIndexQ])
      ], Infinity], 1],
    Flatten[Cases[obj, Eps10[u_List, d_List] :> ({#, "v"} & /@ Select[Join[u, d], symbolIndexQ]), Infinity], 1]
  ];
  spinChiralities = spinSymbolChiralities[obj];
  counts = Counts[First /@ typed]; vec = DeleteDuplicates[First /@ Select[typed, Last[#] === "v" &]];
  spi = Complement[DeleteDuplicates[First /@ Select[typed, Last[#] === "s" &]], vec];
  free = Keys[Select[counts, # == 1 &]]; dum = Keys[Select[counts, # > 1 &]];
  run[] := Module[{rules, it, wrap, s},
    rules = Join[
      (# -> RandomInteger[{1, 10}] & /@ Intersection[vec, free]),
      (# -> RandomChoice[spinIterationValues[Lookup[spinChiralities, #, "chiral"]]] & /@ Intersection[spi, free])
    ];
    it = Join[
      ({#, 1, 10} & /@ Intersection[vec, dum]),
      ({#, spinIterationValues[Lookup[spinChiralities, #, "chiral"]]} & /@ Intersection[spi, dum])
    ];
    wrap[e_] := e /. ra_ /; RTest[ra] :> Bosonize[ra];
    s[e_] := If[it === {}, e, Apply[Sum, Prepend[it, e]]];
    {wrap /@ (s /@ (inputOps /. rules)), wrap[s[hExpr /. rules]], wrap[s[aExpr /. rules]]}
  ];
  If[seed === Automatic, run[], BlockRandom[SeedRandom[seed]; run[]]]
];

OPEProjected[wH_, wA_][Ra__ /; (And @@ (RTest /@ {Ra}) && AnyTrue[{Ra}, hasSpinFieldQ]), opts___Rule] := Module[
  {o, hExpr, aExpr, n, rIn, rH, rA, seed},
  o = getOutgoingOperatorsTensors[{Ra}, wH, wA];
  {hExpr, n} = Which[o["holoOps"] === {}, {1, 0}, o["holoData"] === {}, {0, 0}, True, attachCoefficients[o["holoData"], 0]];
  {aExpr, n} = Which[o["antiOps"] === {}, {1, n}, o["antiData"] === {}, {0, n}, True, attachCoefficients[o["antiData"], n]];
  seed = Lookup[Association[Join[Options[OPEProjected], {opts}]], "RandomSeed", Automatic];
  {rIn, rH, rA} = randomizeIndices[{Ra}, hExpr, aExpr, seed];
  <|"sign" -> o["sign"], "holo" -> rH, "anti" -> rA, "randomizedInputs" -> rIn|>
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
