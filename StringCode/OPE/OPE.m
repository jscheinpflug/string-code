(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`OPE`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`Wick`"];
Needs["StringCode`Taylor`"];
Needs["StringCode`Operators`"];


(* ::Section:: *)
(*Declare public variables and methods*)


OPE::usage = "Computes the operator product expansion";
OPEProjected::usage = "Projects an OPE of local operators onto a given holomorphic/antiholomorphic weight";
OPEProjectedHolo::usage = "Projects an OPE of local operators onto a given holomorphic weight";
OPEProjectedAntiHolo::usage = "Projects an OPE of local operators onto a given antiholomorphic weight";


(* ::Section:: *)
(*Logic*)


Begin["Private`"];

projectionExponentReplacement = {};

normalizeScalingParameter[expr_, parameter_] := FixedPoint[
  ReplaceAll[#, {
    s_Plus /; AllTrue[List @@ s, MatchQ[#, parameter*__] &] :>
      parameter Total[(# / parameter) & /@ (List @@ s)]
  }] &,
  expr
];


(* ::Subsection:: *)
(*General properties of OPE*)


OPE[a___,0,b___]:=0

(*Multilinearity of OPE*)
OPE[f_,g_]:=f g/;(!containsFieldQ[f] || !containsFieldQ[g])
OPE[a_+b_,c_]:=OPE[a,c]+OPE[b,c]
OPE[c_,a_+b_]:=OPE[c,a]+OPE[c,b]
OPE[a_ b_,c_]:=a OPE[b,c]/;(!containsFieldQ[a])
OPE[ b_,a_ c_]:=a OPE[b,c]/;(!containsFieldQ[a])


(*Nested OPE*)
OPE[c__,a_,b_]:=OPE[c,OPE[a,b]]


(*OPE of a single normal-ordered product is no OPE*)
OPE[a___/;RTest[a]]:=R[a]


(* ::Subsection:: *)
(*Split fields into collapsable/non-collapsable pieces*)


splitCollapsable[Ra_/;RTest[Ra]] := Module[
  {ops = List @@ Ra, collPositions, restPositions, sign = 1},
  collPositions = Flatten @ Position[ops, op_ /; isCollapsable[Head[op]]];
  restPositions = Complement[Range[Length[ops]], collPositions];

  Do[
    If[restPos < collPos, sign = sign regcomm[ops[[collPos]], ops[[restPos]]]],
    {collPos, collPositions},
    {restPos, restPositions}
  ];

  {
    If[collPositions === {}, 1, R @@ ops[[collPositions]]],
    If[restPositions === {}, 1, R @@ ops[[restPositions]]],
    sign
  }
];

hasCollapsable[Ra_/;RTest[Ra]] := AnyTrue[List @@ Ra, isCollapsable[Head[#]] &];

multiplyFactors[a_, b_] := Which[
  a === 0 || b === 0, 0,
  a === 1, b,
  b === 1, a,
  True, R[a, b]
];


(* ::Subsection:: *)
(*Define OPE of free fields by repeated moving of fields under a common normal ordering*)


(*When collapsable fields appear only on one side, use Wick recursion directly to preserve operator order/signs*)
OPE[Ra_, Rb_] := OPEWick[Ra, Rb] /; (RTest[Ra] && RTest[Rb] && Xor[hasCollapsable[Ra], hasCollapsable[Rb]]);


(*When collapsable fields are present, compute that sector via Wick and keep the rest symbolic*)
OPE[Ra_, Rb_] := Module[{collA, restA, signA, collB, restB, signB, opeColl, opeRest},
  {collA, restA, signA} = splitCollapsable[Ra];
  {collB, restB, signB} = splitCollapsable[Rb];

  opeColl = Which[
    collA === 1 && collB === 1, 1,
    collA === 1, collB,
    collB === 1, collA,
    True, OPEWick[collA, collB]
  ];

  opeRest = Which[
    restA === 1 && restB === 1, 1,
    restA === 1, restB,
    restB === 1, restA,
    True, OPE[restA, restB]
  ];

  signA signB multiplyFactors[opeColl, opeRest]
] /; (RTest[Ra] && RTest[Rb] && hasCollapsable[Ra] && hasCollapsable[Rb]);


(*When both normal-ordered products have length one, OPE reduces to Wick contraction + possible normal ordering*)
OPEWick[a___,0,b___]:=0;
OPEWick[f_,g_]:=f g/;(!containsFieldQ[f] || !containsFieldQ[g])
OPEWick[a_+b_,c_]:=OPEWick[a,c]+OPEWick[b,c];
OPEWick[c_,a_+b_]:=OPEWick[c,a]+OPEWick[c,b];
OPEWick[a_ b_,c_]:=a OPEWick[b,c]/;(!containsFieldQ[a]);
OPEWick[b_,a_ c_]:=a OPEWick[b,c]/;(!containsFieldQ[a]);


$OPEWickCache::usage = "State cache for OPEWick evaluation.";
$OPEWickCache = <||>;


OPEWick[Ra_,Rb_] := Module[
  {key, raFirst, rbFirst, ha, hb, result},
  key = HoldComplete[CanonicalizeToR[Ra], CanonicalizeToR[Rb]];
  If[KeyExistsQ[$OPEWickCache, key], Return[$OPEWickCache[key]]];

  raFirst = Ra[[1]];
  rbFirst = Rb[[1]];
  ha = Head[raFirst];
  hb = Head[rbFirst];

  result = Which[
    ROne[Ra] && ROne[Rb] && isSimple[ha] && isSimple[hb],
      R[Ra,Rb] + If[pairing[{ha,hb}] == 1, Wick[Ra,Rb], 0],
    ROne[Ra] && ROne[Rb] && isSimple[ha] && isComposite[hb],
      R[Ra,Rb] + If[pairing[{ha,hb}] == 1, SWick[Ra,Rb] Rb, 0],
    ROne[Ra] && ROne[Rb] && isComposite[ha] && isSimple[hb],
      R[Ra,Rb] + If[pairing[{ha,hb}] == 1, SWick[Ra,Rb] Ra, 0],
    ROne[Ra] && ROne[Rb] && isComposite[ha] && isComposite[hb],
      If[pairing[{ha,hb}] == 1, MWick[Ra,Rb], 1] R[Ra,Rb],
    ROne[Ra] && RTest[Rb] && isSimple[ha],
      DWick[Ra,Rb] + (R @@ Join[List @@ Ra, List @@ Rb]),
    ROne[Ra] && RTest[Rb] && isComposite[ha],
      R[Ra,DWick[R[raFirst],Rb]],
    !ROne[Ra] && RTest[Rb] && isSimple[ha],
      (-1)^(parity[dropFirstFromR[Ra]] parity[R[raFirst]]) OPEWick[dropFirstFromR[Ra],DWick[R[raFirst],Rb]] +
      R[R[raFirst],OPEWick[dropFirstFromR[Ra],Rb]],
    !ROne[Ra] && RTest[Rb] && isComposite[ha],
      R[R[raFirst],OPEWick[dropFirstFromR[Ra],DWick[R[raFirst],Rb]]],
    True,
      Return[Unevaluated[OPEWick[Ra,Rb]]]
  ];

  $OPEWickCache[key] = result
] /; (RTest[Ra] && RTest[Rb]);


(* ::Subsection:: *)
(*Projection helpers*)


rescalePositionBy[rescalingFactor_][op_/;isField[Head[op]] && isHolomorphic[Head[op]] && isAntiHolomorphic[Head[op]]] :=
Module[{args = List @@ op, h = Head[op]}, h @@ Join[Drop[args, -2], rescalingFactor Take[args, -2]]];

rescalePositionBy[rescalingFactor_][op_/;isField[Head[op]]] :=
Module[{args = List @@ op, h = Head[op]}, h @@ Join[Drop[args, -1], {rescalingFactor Last[args]}]];

rescaleR[rescalingFactor_][Ra_/;RTest[Ra]] := R @@ (rescalePositionBy[rescalingFactor] /@ (List @@ Ra));

opeOfRList[rList_] := Which[
  rList === {}, 1,
  Length[rList] === 1, First[rList],
  True, OPE @@ rList
];

projectHolo[OPEexpr_, weight_, weightCountingParameter_] := Module[
  {result = 0, power, expansionOrder, OPEexpanded = Expand[OPEexpr], OPEterms, scaledTerm},
  If[OPEexpr === 1, Return[If[weight === 0, 1, 0]]];
  OPEterms = If[Head[OPEexpanded] === Plus, List @@ OPEexpanded, {OPEexpanded}];
  Scan[Function[OPEterm,
    scaledTerm = normalizeScalingParameter[OPEterm, weightCountingParameter];
    power = Exponent[scaledTerm, weightCountingParameter] /. projectionExponentReplacement;
    expansionOrder = -power + weight;
    If[IntegerQ[expansionOrder] && expansionOrder >= 0, result = result + TaylorAtOrderHolo[scaledTerm, expansionOrder, 0]];
  ], OPEterms];
  result /. {weightCountingParameter -> 1}
];

projectAntiHolo[OPEexpr_, weight_, weightCountingParameter_] := Module[
  {result = 0, power, expansionOrder, OPEexpanded = Expand[OPEexpr], OPEterms, scaledTerm},
  If[OPEexpr === 1, Return[If[weight === 0, 1, 0]]];
  OPEterms = If[Head[OPEexpanded] === Plus, List @@ OPEexpanded, {OPEexpanded}];
  Scan[Function[OPEterm,
    scaledTerm = normalizeScalingParameter[OPEterm, weightCountingParameter];
    power = Exponent[scaledTerm, weightCountingParameter] /. projectionExponentReplacement;
    expansionOrder = -power + weight;
    If[IntegerQ[expansionOrder] && expansionOrder >= 0, result = result + TaylorAtOrderAntiHolo[scaledTerm, expansionOrder, 0]];
  ], OPEterms];
  result /. {weightCountingParameter -> 1}
];

factorizeForChiralSplit[operatorList_List] := Module[{factorized},
  factorized = factorizeOperator /@ operatorList;
  Flatten[
    (factorized /. {
      {holoPart_, antiHoloPart_} :> {holoPart, antiHoloPart},
      Ra_ /; RTest[Ra] :> List @@ Ra
    }),
    1
  ]
];

combineChiral[a_, b_] := Which[
  a === 0 || b === 0, 0,
  a === 1, b,
  b === 1, a,
  True, R[a, b]
];

hasSpinFieldQ::usage =
  "hasSpinFieldQ[Ra] is False by default and may be overridden by theories with specialized spin-field projected OPE logic.";
hasSpinFieldQ[_] := False;

sectorHasSpinFieldQ0::usage =
  "sectorHasSpinFieldQ0[sector, ops] is False by default and may be overridden by theories with chiral spin-field projected OPE logic.";
sectorHasSpinFieldQ0[_, _] := False;

postProcessProjectedOPE0::usage =
  "postProcessProjectedOPE0[expr] post-processes projected OPE outputs; the default is identity, and FlatSpace overrides it to recombine factorizable matter pairs.";
postProcessProjectedOPE0[expr_] := expr;


minNonCollapsableWeightHolo::usage =
  "minNonCollapsableWeightHolo[restR] returns the default holomorphic lower bound for non-collapsable remainder projections.";
minNonCollapsableWeightHolo[_] := 0;

minNonCollapsableWeightAntiHolo::usage =
  "minNonCollapsableWeightAntiHolo[restR] returns the default antiholomorphic lower bound for non-collapsable remainder projections.";
minNonCollapsableWeightAntiHolo[_] := 0;

expandedProjectedTerms0::usage =
  "expandedProjectedTerms0[expr] expands one projected OPE expression into additive terms and drops explicit zeros.";
expandedProjectedTerms0[expr_] := DeleteCases[
  With[{expanded = Expand[expr]},
    If[Head[expanded] === Plus, List @@ expanded, {expanded}]
  ],
  0
];

minProjectableWeight0::usage =
  "minProjectableWeight0[collOPE, scaleSymbol] returns a lower bound below which the chiral projector must vanish on the collapsable OPE.";
minProjectableWeight0[collOPE_, scaleSymbol_] := Module[
  {terms, powers},
  If[collOPE === 1, Return[0]];
  terms = expandedProjectedTerms0[collOPE];
  powers = (Exponent[normalizeScalingParameter[#, scaleSymbol], scaleSymbol] /. projectionExponentReplacement) & /@ terms;
  Min[powers]
];

collectProjectedSectorBuckets::usage =
  "collectProjectedSectorBuckets[collOPE, targetWeight, minRestWeight, projectFn, scaleSymbol] collects remainder-weight -> projected-collapsable pairs.";
collectProjectedSectorBuckets[collOPE_, targetWeight_, minRestWeight_, projectFn_, scaleSymbol_] := Module[
  {buckets = <||>, minColl, maxColl, projected},
  minColl = minProjectableWeight0[collOPE, scaleSymbol];
  maxColl = targetWeight - minRestWeight;
  Do[
    projected = Expand[projectFn[collOPE, coll, scaleSymbol] /. scaleSymbol -> 1];
    If[projected =!= 0, buckets[targetWeight - coll] = projected],
    {coll, minColl, maxColl}
  ];
  buckets
];

projectWithNonCollapsable::usage =
  "projectWithNonCollapsable[collOPEHolo, collOPEAnti, εHolo, εAntiHolo, wH, wA, collWH, collWA, restR, minRestWH, minRestWA, opts] combines collapsable projections with delegated remainder projections.";
projectWithNonCollapsable[
  collOPEHolo_, collOPEAnti_, εHolo_, εAntiHolo_,
  wH_, wA_, collWH_, collWA_,
  restR_List, minRestWH_, minRestWA_, opts_List
] := Module[
  {restWH, restWA, holoBuckets, antiBuckets, result = 0, collProj, restProj},
  restWH = Total[totalWeightHolo /@ restR];
  restWA = Total[totalWeightAntiHolo /@ restR];
  holoBuckets = collectProjectedSectorBuckets[collOPEHolo, wH - restWH - collWH, minRestWH - restWH, projectHolo, εHolo];
  antiBuckets = collectProjectedSectorBuckets[collOPEAnti, wA - restWA - collWA, minRestWA - restWA, projectAntiHolo, εAntiHolo];
  If[holoBuckets === <||> || antiBuckets === <||>, Return[0]];
  Do[
    collProj = combineChiral[holoBuckets[hKey], antiBuckets[aKey]];
    If[collProj =!= 0,
      restProj = OPEProjected[restWH + hKey, restWA + aKey][Sequence @@ restR, Sequence @@ opts];
      result += multiplyFactors[collProj, restProj]
    ],
    {hKey, Keys[holoBuckets]}, {aKey, Keys[antiBuckets]}
  ];
  result
];

projectWithNonCollapsableHolo::usage =
  "projectWithNonCollapsableHolo[collOPEHolo, antiExpr, εHolo, wH, collWH, restR, minRestWH] combines holomorphically projected collapsable terms with delegated holomorphic remainder projections.";
projectWithNonCollapsableHolo[
  collOPEHolo_, antiExpr_, εHolo_, wH_, collWH_, restR_List, minRestWH_
] := Module[
  {holoBuckets, result = 0, collProjected, restProjected},
  holoBuckets = collectProjectedSectorBuckets[
    collOPEHolo,
    wH - collWH,
    minRestWH,
    projectHolo,
    εHolo
  ];
  If[holoBuckets === <||>, Return[0]];
  KeyValueMap[
    Function[{restTargetWeightHolo, projectedHolo},
      collProjected = multiplyFactors[projectedHolo, antiExpr];
      If[collProjected =!= 0,
        restProjected = OPEProjectedHolo[restTargetWeightHolo][Sequence @@ restR];
        result = result + multiplyFactors[collProjected, restProjected];
      ];
    ],
    holoBuckets
  ];
  result
];

projectWithNonCollapsableAntiHolo::usage =
  "projectWithNonCollapsableAntiHolo[holoExpr, collOPEAnti, εAntiHolo, wA, collWA, restR, minRestWA] combines antiholomorphically projected collapsable terms with delegated antiholomorphic remainder projections.";
projectWithNonCollapsableAntiHolo[
  holoExpr_, collOPEAnti_, εAntiHolo_, wA_, collWA_, restR_List, minRestWA_
] := Module[
  {antiBuckets, result = 0, collProjected, restProjected},
  antiBuckets = collectProjectedSectorBuckets[
    collOPEAnti,
    wA - collWA,
    minRestWA,
    projectAntiHolo,
    εAntiHolo
  ];
  If[antiBuckets === <||>, Return[0]];
  KeyValueMap[
    Function[{restTargetWeightAntiHolo, projectedAntiHolo},
      collProjected = multiplyFactors[holoExpr, projectedAntiHolo];
      If[collProjected =!= 0,
        restProjected = OPEProjectedAntiHolo[restTargetWeightAntiHolo][Sequence @@ restR];
        result = result + multiplyFactors[collProjected, restProjected];
      ];
    ],
    antiBuckets
  ];
  result
];


(* ::Subsection:: *)
(*Projected OPE API*)


OPEProjected[wH_, wA_][a___, 0, b___] := 0;
OPEProjected[wH_, wA_][a___, x_ + y_, b___] := OPEProjected[wH, wA][a, x, b] + OPEProjected[wH, wA][a, y, b];
OPEProjected[wH_, wA_][a___, c_ x_, b___] := c OPEProjected[wH, wA][a, x, b] /; (!containsFieldQ[c]);

OPEProjected[wH_, wA_][Ra__ /; (And @@ (RTest /@ {Ra}) && AnyTrue[{Ra}, hasCollapsable]), opts___Rule] := Module[
  {
    collPieces, collR, restR, collLists, splitLists, splitSign, sign, holoOps, antiOps,
    insertionWeightHolo, insertionWeightAntiHolo, collInsertionWeightHolo, collInsertionWeightAntiHolo,
    targetWeightHolo, targetWeightAntiHolo, \[Epsilon]Holo, \[Epsilon]AntiHolo,
    collOPEHolo, collOPEAnti, optionList
  },

  insertionWeightHolo = Total[totalWeightHolo /@ {Ra}];
  insertionWeightAntiHolo = Total[totalWeightAntiHolo /@ {Ra}];
  targetWeightHolo = wH - insertionWeightHolo;
  targetWeightAntiHolo = wA - insertionWeightAntiHolo;

  collPieces = splitCollapsable /@ {Ra};
  collR = Select[collPieces[[All, 1]], # =!= 1 &];
  restR = Select[collPieces[[All, 2]], # =!= 1 &];
  splitSign = Times @@ collPieces[[All, 3]];
  collInsertionWeightHolo = Total[totalWeightHolo /@ collR];
  collInsertionWeightAntiHolo = Total[totalWeightAntiHolo /@ collR];

  collLists = factorizeForChiralSplit /@ (List @@ # & /@ collR);
  splitLists = splitOperators[#, isHolomorphic, isAntiHolomorphic] & /@ collLists;

  sign = splitSign * If[Flatten[collLists] === {}, 1,
    factorizationSign[Flatten[collLists], isHolomorphic, isAntiHolomorphic]
  ];

  holoOps = Select[R @@@ (splitLists[[All, 1]]), RTest];
  antiOps = Select[R @@@ (splitLists[[All, 2]]), RTest];
  collOPEHolo = opeOfRList[rescaleR[\[Epsilon]Holo] /@ holoOps];
  collOPEAnti = opeOfRList[rescaleR[\[Epsilon]AntiHolo] /@ antiOps];
  optionList = Flatten[{opts}];

  postProcessProjectedOPE0[
    If[restR === {},
      sign combineChiral[
        projectHolo[collOPEHolo, targetWeightHolo, \[Epsilon]Holo],
        projectAntiHolo[collOPEAnti, targetWeightAntiHolo, \[Epsilon]AntiHolo]
      ],
      sign projectWithNonCollapsable[
        collOPEHolo, collOPEAnti, \[Epsilon]Holo, \[Epsilon]AntiHolo,
        wH, wA, collInsertionWeightHolo, collInsertionWeightAntiHolo,
        restR, minNonCollapsableWeightHolo[restR], minNonCollapsableWeightAntiHolo[restR], optionList
      ]
    ]
  ]
];

OPEProjectedHolo[wH_][a___, 0, b___] := 0;
OPEProjectedHolo[wH_][a___, x_ + y_, b___] := OPEProjectedHolo[wH][a, x, b] + OPEProjectedHolo[wH][a, y, b];
OPEProjectedHolo[wH_][a___, c_ x_, b___] := c OPEProjectedHolo[wH][a, x, b] /; (!containsFieldQ[c]);

OPEProjectedHolo[wH_][Ra__ /; (And @@ (RTest /@ {Ra}) && !AnyTrue[{Ra}, hasCollapsable] && !sectorHasSpinFieldQ0["Holo", {Ra}])] := Module[
  {
    \[Epsilon]Holo, localLists, factorizedLists, splitLists, sign, holoOps, antiOps,
    insertionWeightHolo, targetWeightHolo, projectedHolo, spectatorAnti
  },
  localLists = List @@ # & /@ {Ra};
  factorizedLists = factorizeForChiralSplit /@ localLists;
  splitLists = splitOperators[#, isHolomorphic, isAntiHolomorphic] & /@ factorizedLists;
  insertionWeightHolo = Total[totalWeightHolo /@ {Ra}];
  targetWeightHolo = wH - insertionWeightHolo;
  sign = If[Flatten[factorizedLists] === {}, 1,
    factorizationSign[Flatten[factorizedLists], isHolomorphic, isAntiHolomorphic]
  ];

  holoOps = Select[R @@@ (splitLists[[All, 1]]), RTest];
  antiOps = Select[R @@@ (splitLists[[All, 2]]), RTest];
  projectedHolo = projectHolo[
    opeOfRList[rescaleR[\[Epsilon]Holo] /@ holoOps],
    targetWeightHolo, \[Epsilon]Holo
  ];
  spectatorAnti = opeOfRList[antiOps];
  postProcessProjectedOPE0[sign multiplyFactors[projectedHolo, spectatorAnti]]
];

OPEProjectedHolo[wH_][Ra__ /; (And @@ (RTest /@ {Ra}) && AnyTrue[{Ra}, hasCollapsable])] := Module[
  {
    collPieces, collR, restR, collLists, splitLists, splitSign, sign, holoOps, antiOps,
    insertionWeightHolo, targetWeightHolo, collInsertionWeightHolo,
    \[Epsilon]Holo, collOPEHolo, spectatorAnti
  },
  insertionWeightHolo = Total[totalWeightHolo /@ {Ra}];
  targetWeightHolo = wH - insertionWeightHolo;
  collPieces = splitCollapsable /@ {Ra};
  collR = Select[collPieces[[All, 1]], # =!= 1 &];
  restR = Select[collPieces[[All, 2]], # =!= 1 &];
  splitSign = Times @@ collPieces[[All, 3]];
  collInsertionWeightHolo = Total[totalWeightHolo /@ collR];
  collLists = factorizeForChiralSplit /@ (List @@ # & /@ collR);
  splitLists = splitOperators[#, isHolomorphic, isAntiHolomorphic] & /@ collLists;
  sign = splitSign * If[Flatten[collLists] === {}, 1,
    factorizationSign[Flatten[collLists], isHolomorphic, isAntiHolomorphic]
  ];
  holoOps = Select[R @@@ (splitLists[[All, 1]]), RTest];
  antiOps = Select[R @@@ (splitLists[[All, 2]]), RTest];
  collOPEHolo = opeOfRList[rescaleR[\[Epsilon]Holo] /@ holoOps];
  spectatorAnti = opeOfRList[antiOps];
  postProcessProjectedOPE0[
    If[restR === {},
      sign multiplyFactors[
        projectHolo[collOPEHolo, targetWeightHolo, \[Epsilon]Holo],
        spectatorAnti
      ],
      sign projectWithNonCollapsableHolo[
        collOPEHolo,
        spectatorAnti,
        \[Epsilon]Holo,
        wH,
        collInsertionWeightHolo,
        restR,
        minNonCollapsableWeightHolo[restR]
      ]
    ]
  ]
];


OPEProjectedAntiHolo[wA_][a___, 0, b___] := 0;
OPEProjectedAntiHolo[wA_][a___, x_ + y_, b___] := OPEProjectedAntiHolo[wA][a, x, b] + OPEProjectedAntiHolo[wA][a, y, b];
OPEProjectedAntiHolo[wA_][a___, c_ x_, b___] := c OPEProjectedAntiHolo[wA][a, x, b] /; (!containsFieldQ[c]);

OPEProjectedAntiHolo[wA_][Ra__ /; (And @@ (RTest /@ {Ra}) && !AnyTrue[{Ra}, hasCollapsable] && !sectorHasSpinFieldQ0["Anti", {Ra}])] := Module[
  {
    \[Epsilon]AntiHolo, localLists, factorizedLists, splitLists, sign, holoOps, antiOps,
    insertionWeightAntiHolo, targetWeightAntiHolo, projectedAntiHolo, spectatorHolo
  },
  localLists = List @@ # & /@ {Ra};
  factorizedLists = factorizeForChiralSplit /@ localLists;
  splitLists = splitOperators[#, isHolomorphic, isAntiHolomorphic] & /@ factorizedLists;
  insertionWeightAntiHolo = Total[totalWeightAntiHolo /@ {Ra}];
  targetWeightAntiHolo = wA - insertionWeightAntiHolo;
  sign = If[Flatten[factorizedLists] === {}, 1,
    factorizationSign[Flatten[factorizedLists], isHolomorphic, isAntiHolomorphic]
  ];

  holoOps = Select[R @@@ (splitLists[[All, 1]]), RTest];
  antiOps = Select[R @@@ (splitLists[[All, 2]]), RTest];
  projectedAntiHolo = projectAntiHolo[
    opeOfRList[rescaleR[\[Epsilon]AntiHolo] /@ antiOps],
    targetWeightAntiHolo, \[Epsilon]AntiHolo
  ];
  spectatorHolo = opeOfRList[holoOps];
  postProcessProjectedOPE0[sign multiplyFactors[spectatorHolo, projectedAntiHolo]]
];

OPEProjectedAntiHolo[wA_][Ra__ /; (And @@ (RTest /@ {Ra}) && AnyTrue[{Ra}, hasCollapsable])] := Module[
  {
    collPieces, collR, restR, collLists, splitLists, splitSign, sign, holoOps, antiOps,
    insertionWeightAntiHolo, targetWeightAntiHolo, collInsertionWeightAntiHolo,
    \[Epsilon]AntiHolo, collOPEAntiHolo, spectatorHolo
  },
  insertionWeightAntiHolo = Total[totalWeightAntiHolo /@ {Ra}];
  targetWeightAntiHolo = wA - insertionWeightAntiHolo;
  collPieces = splitCollapsable /@ {Ra};
  collR = Select[collPieces[[All, 1]], # =!= 1 &];
  restR = Select[collPieces[[All, 2]], # =!= 1 &];
  splitSign = Times @@ collPieces[[All, 3]];
  collInsertionWeightAntiHolo = Total[totalWeightAntiHolo /@ collR];
  collLists = factorizeForChiralSplit /@ (List @@ # & /@ collR);
  splitLists = splitOperators[#, isHolomorphic, isAntiHolomorphic] & /@ collLists;
  sign = splitSign * If[Flatten[collLists] === {}, 1,
    factorizationSign[Flatten[collLists], isHolomorphic, isAntiHolomorphic]
  ];
  holoOps = Select[R @@@ (splitLists[[All, 1]]), RTest];
  antiOps = Select[R @@@ (splitLists[[All, 2]]), RTest];
  collOPEAntiHolo = opeOfRList[rescaleR[\[Epsilon]AntiHolo] /@ antiOps];
  spectatorHolo = opeOfRList[holoOps];
  postProcessProjectedOPE0[
    If[restR === {},
      sign multiplyFactors[
        spectatorHolo,
        projectAntiHolo[collOPEAntiHolo, targetWeightAntiHolo, \[Epsilon]AntiHolo]
      ],
      sign projectWithNonCollapsableAntiHolo[
        spectatorHolo,
        collOPEAntiHolo,
        \[Epsilon]AntiHolo,
        wA,
        collInsertionWeightAntiHolo,
        restR,
        minNonCollapsableWeightAntiHolo[restR]
      ]
    ]
  ]
];



(* ::Section:: *)
(*End*)


End[];


EndPackage[];
