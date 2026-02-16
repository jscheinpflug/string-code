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
OPEWick[a_+b_,c_]:=OPEWick[a,c]+OPEWick[b,c];
OPEWick[c_,a_+b_]:=OPEWick[c,a]+OPEWick[c,b];
OPEWick[a_ b_,c_]:=a OPEWick[b,c]/;(!containsFieldQ[a]);
OPEWick[b_,a_ c_]:=a OPEWick[b,c]/;(!containsFieldQ[a]);
OPEWick[Ra_,Rb_] := OPEWickPolynomial[Ra, Rb] /; (RTest[Ra] && RTest[Rb]);


OPEWickLegacy::usage = "Frozen recursive OPEWick evaluator retained for benchmark A/B checks.";
OPEWickLegacy[a___,0,b___]:=0;
OPEWickLegacy[a_+b_,c_]:=OPEWickLegacy[a,c]+OPEWickLegacy[b,c];
OPEWickLegacy[c_,a_+b_]:=OPEWickLegacy[c,a]+OPEWickLegacy[c,b];
OPEWickLegacy[a_ b_,c_]:=a OPEWickLegacy[b,c]/;(!containsFieldQ[a]);
OPEWickLegacy[b_,a_ c_]:=a OPEWickLegacy[b,c]/;(!containsFieldQ[a]);
OPEWickLegacy[Ra_, Rb_] := OPEWick[Ra, Rb] /; (!RTest[Ra] || !RTest[Rb]);

OPEWickLegacy[Ra_,Rb_]:=R[Ra,Rb]+ If[pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}]==1, Wick[Ra,Rb],0] /;(ROne[Ra] && ROne[Rb] && isSimple[Head[Ra[[1]]]] && isSimple[Head[Rb[[1]]]])
OPEWickLegacy[Ra_,Rb_]:=R[Ra,Rb]+ If[pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}]==1, SWick[Ra,Rb] Rb,0] /;(ROne[Ra] && ROne[Rb] && isSimple[Head[Ra[[1]]]] && isComposite[Head[Rb[[1]]]])
OPEWickLegacy[Ra_,Rb_]:=R[Ra,Rb]+ If[pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}]==1, SWick[Ra,Rb] Ra,0]/;(ROne[Ra] && ROne[Rb] && isComposite[Head[Ra[[1]]]] && isSimple[Head[Rb[[1]]]])
OPEWickLegacy[Ra_,Rb_]:= If[pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}]==1, MWick[Ra,Rb],1]  R[Ra,Rb]/;(ROne[Ra] && ROne[Rb] && isComposite[Head[Ra[[1]]]] && isComposite[Head[Rb[[1]]]])
OPEWickLegacy[Ra_,Rb_]:= DWickLegacy[Ra,Rb] +(R @@ Join[(List @@ Ra),(List @@ Rb)])/;(ROne[Ra] && RTest[Rb]&& isSimple[Head[Ra[[1]]]] )
OPEWickLegacy[Ra_,Rb_]:= R[Ra,DWickLegacy[R[Ra[[1]]],Rb]]/;(ROne[Ra] && RTest[Rb]  && isComposite[Head[Ra[[1]]]] )
OPEWickLegacy[Ra_,Rb_]:=(-1)^(parity[dropFirstFromR[Ra]]parity[R[Ra[[1]]]]) OPEWickLegacy[dropFirstFromR[Ra],DWickLegacy[R[Ra[[1]]],Rb]] +
R[R[Ra[[1]]],OPEWickLegacy[dropFirstFromR[Ra],Rb]]/;(RTest[Ra] && RTest[Rb] &&(!ROne[Ra]) && isSimple[Head[Ra[[1]]]])
OPEWickLegacy[Ra_,Rb_]:=R[R[Ra[[1]]],OPEWickLegacy[dropFirstFromR[Ra],DWickLegacy[R[Ra[[1]]],Rb]]]/;(RTest[Ra] && RTest[Rb] &&(!ROne[Ra]) && isComposite[Head[Ra[[1]]]] )


DWickLegacy::usage = "Legacy DWick wrapper for benchmark A/B checks.";
DWickLegacy[Ra_, Rb_] := DWick[Ra, Rb];


$OPEWickPolynomialCache::usage = "State cache for polynomial OPEWick evaluation.";
$OPEWickPolynomialCache = <||>;

$DWickPolynomialCache::usage = "State cache for polynomial DWick evaluation.";
$DWickPolynomialCache = <||>;


clearOPEWickCaches::usage = "Clears internal OPEWick/DWick polynomial caches.";
clearOPEWickCaches[] := (
  $OPEWickPolynomialCache = <||>;
  $DWickPolynomialCache = <||>;
  Null
);


OPEWickStateKey::usage = "Canonical cache key for OPEWick states.";
OPEWickStateKey[Ra_, Rb_] := HoldComplete[CanonicalizeToR[Ra], CanonicalizeToR[Rb]];


DWickStateKey::usage = "Canonical cache key for DWick states.";
DWickStateKey[Ra_, Rb_] := HoldComplete[CanonicalizeToR[Ra], CanonicalizeToR[Rb]];


OPEWickPolynomial::usage = "Memoized OPEWick evaluator that reuses repeated contraction subproblems.";
OPEWickPolynomial[Ra_, Rb_] := Module[{key = OPEWickStateKey[Ra, Rb]},
  If[
    KeyExistsQ[$OPEWickPolynomialCache, key],
    $OPEWickPolynomialCache[key],
    $OPEWickPolynomialCache[key] = OPEWickPolynomialCompute[Ra, Rb]
  ]
] /; (RTest[Ra] && RTest[Rb]);


DWickPolynomial::usage = "Memoized DWick evaluator that reuses repeated contraction subproblems.";
DWickPolynomial[Ra_, Rb_] := Module[{key = DWickStateKey[Ra, Rb]},
  If[
    KeyExistsQ[$DWickPolynomialCache, key],
    $DWickPolynomialCache[key],
    $DWickPolynomialCache[key] = DWickPolynomialCompute[Ra, Rb]
  ]
] /; (RTest[Ra] && RTest[Rb]);


OPEWickPolynomialCompute::usage = "Core polynomial OPEWick recurrence preserving legacy semantics.";
OPEWickPolynomialCompute[Ra_,Rb_]:=R[Ra,Rb]+ If[pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}]==1, Wick[Ra,Rb],0] /;(ROne[Ra] && ROne[Rb] && isSimple[Head[Ra[[1]]]] && isSimple[Head[Rb[[1]]]])
OPEWickPolynomialCompute[Ra_,Rb_]:=R[Ra,Rb]+ If[pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}]==1, SWick[Ra,Rb] Rb,0] /;(ROne[Ra] && ROne[Rb] && isSimple[Head[Ra[[1]]]] && isComposite[Head[Rb[[1]]]])
OPEWickPolynomialCompute[Ra_,Rb_]:=R[Ra,Rb]+ If[pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}]==1, SWick[Ra,Rb] Ra,0]/;(ROne[Ra] && ROne[Rb] && isComposite[Head[Ra[[1]]]] && isSimple[Head[Rb[[1]]]])
OPEWickPolynomialCompute[Ra_,Rb_]:= If[pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}]==1, MWick[Ra,Rb],1]  R[Ra,Rb]/;(ROne[Ra] && ROne[Rb] && isComposite[Head[Ra[[1]]]] && isComposite[Head[Rb[[1]]]])
OPEWickPolynomialCompute[Ra_,Rb_]:= DWickPolynomial[Ra,Rb] +(R @@ Join[(List @@ Ra),(List @@ Rb)])/;(ROne[Ra] && RTest[Rb]&& isSimple[Head[Ra[[1]]]] )
OPEWickPolynomialCompute[Ra_,Rb_]:= R[Ra,DWickPolynomial[R[Ra[[1]]],Rb]]/;(ROne[Ra] && RTest[Rb]  && isComposite[Head[Ra[[1]]]] )
OPEWickPolynomialCompute[Ra_,Rb_]:=(-1)^(parity[dropFirstFromR[Ra]]parity[R[Ra[[1]]]]) OPEWick[dropFirstFromR[Ra],DWickPolynomial[R[Ra[[1]]],Rb]] +
R[R[Ra[[1]]],OPEWick[dropFirstFromR[Ra],Rb]]/;(RTest[Ra] && RTest[Rb] &&(!ROne[Ra]) && isSimple[Head[Ra[[1]]]])
OPEWickPolynomialCompute[Ra_,Rb_]:=R[R[Ra[[1]]],OPEWick[dropFirstFromR[Ra],DWickPolynomial[R[Ra[[1]]],Rb]]]/;(RTest[Ra] && RTest[Rb] &&(!ROne[Ra]) && isComposite[Head[Ra[[1]]]] )


DWickPolynomialCompute::usage = "Core polynomial DWick recurrence preserving legacy semantics.";
DWickPolynomialCompute[Ra_,Rb_]:= If[pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}] ==1, Wick[Ra,Rb], 0]/;(ROne[Ra] && ROne[Rb] && isSimple[Head[Ra[[1]]]] && isSimple[Head[Rb[[1]]]])
DWickPolynomialCompute[Ra_,Rb_]:= If[pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}] ==1, SWick[Ra,Rb] Rb, 0]/;(ROne[Ra] && ROne[Rb] && isSimple[Head[Ra[[1]]]] && isComposite[Head[Rb[[1]]]])
DWickPolynomialCompute[Ra_,Rb_]:= If[pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}] ==1, SWick[Ra,Rb], 0] +Rb/;(ROne[Ra] && ROne[Rb] && isComposite[Head[Ra[[1]]]] && isSimple[Head[Rb[[1]]]])
DWickPolynomialCompute[Ra_,Rb_]:= If[pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}]==1,  MWick[Ra,Rb], 1] Rb/;(ROne[Ra] && ROne[Rb] && isComposite[Head[Ra[[1]]]] && isComposite[Head[Rb[[1]]]])
DWickPolynomialCompute[Ra_, Rb_]:= Module[{result = 0, RbList = List @@ Rb, arePaired, RaFirst = Ra[[1]], RaHead, RbHead, sign = 1, i = 1},
RaHead = Head[RaFirst];
Scan[Function[Rbelem,
RbHead = Head[Rbelem];
arePaired = pairing[{RaHead,RbHead}]==1;
If[arePaired,
If[isComposite[RbHead],
result = result + sign SWick[RaFirst, Rbelem] Rb,
result = result + sign Wick[RaFirst, Rbelem] R@@Delete[RbList, i];
];
];
sign = sign (-1)^(parity[Ra]parity[R[Rbelem]]);
i++;
], RbList];
result]/; (ROne[Ra] && RTest[Rb] && (!ROne[Rb]) && isSimple[Head[Ra[[1]]]]);
DWickPolynomialCompute[Ra_,Rb_]:= (-1)^(parity[Ra] parity[Rb]) DWickPolynomial[Rb, Ra]/; (ROne[Rb] && RTest[Ra] && (!ROne[Ra]) && isSimple[Head[Rb[[1]]]]);
DWickPolynomialCompute[Ra_,Rb_]:= If[pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}]==1, SWick[Ra[[1]],Rb[[1]]] DWickPolynomial[Ra,dropFirstFromR[Rb]],0]+
R[Rb[[1]],DWickPolynomial[Ra,dropFirstFromR[Rb]]]/;(ROne[Ra] && RTest[Rb] &&(!ROne[Rb]) && isComposite[Head[Ra[[1]]]] && isSimple[Head[Rb[[1]]]])
DWickPolynomialCompute[Ra_,Rb_]:= If[pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}]==1, MWick[Ra[[1]],Rb[[1]]],1] R[Rb[[1]],
DWickPolynomial[Ra,dropFirstFromR[Rb]]]/;(ROne[Ra] && RTest[Rb] &&(!ROne[Rb]) && isComposite[Head[Ra[[1]]]] && isComposite[Head[Rb[[1]]]])


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


(* ::Subsection:: *)
(*Projected OPE API*)


OPEProjected[wH_, wA_][a___, 0, b___] := 0;
OPEProjected[wH_, wA_][a___, x_ + y_, b___] := OPEProjected[wH, wA][a, x, b] + OPEProjected[wH, wA][a, y, b];
OPEProjected[wH_, wA_][a___, c_ x_, b___] := c OPEProjected[wH, wA][a, x, b] /; (!containsFieldQ[c]);

OPEProjected[wH_, wA_][Ra__ /; (And @@ (RTest /@ {Ra}) && AnyTrue[{Ra}, hasCollapsable])] := Module[
  {
    collPieces, collR, restR, collLists, splitLists, sign, holoOps, antiOps,
    insertionWeightHolo, insertionWeightAntiHolo, targetWeightHolo, targetWeightAntiHolo,
    \[Epsilon]Holo, \[Epsilon]AntiHolo, projectedHolo, projectedAntiHolo, freeProjected, restProjected
  },

  insertionWeightHolo = Total[totalWeightHolo /@ {Ra}];
  insertionWeightAntiHolo = Total[totalWeightAntiHolo /@ {Ra}];
  targetWeightHolo = wH - insertionWeightHolo;
  targetWeightAntiHolo = wA - insertionWeightAntiHolo;

  collPieces = splitCollapsable /@ {Ra};
  collR = Select[collPieces[[All, 1]], # =!= 1 &];
  restR = Select[collPieces[[All, 2]], # =!= 1 &];

  collLists = factorizeForChiralSplit /@ (List @@ # & /@ collR);
  splitLists = splitOperators[#, isHolomorphic, isAntiHolomorphic] & /@ collLists;

  sign = If[Flatten[collLists] === {}, 1,
    factorizationSign[Flatten[collLists], isHolomorphic, isAntiHolomorphic]
  ];

  holoOps = Select[R @@@ (splitLists[[All, 1]]), RTest];
  antiOps = Select[R @@@ (splitLists[[All, 2]]), RTest];

  projectedHolo = projectHolo[opeOfRList[rescaleR[\[Epsilon]Holo] /@ holoOps], targetWeightHolo, \[Epsilon]Holo];
  projectedAntiHolo = projectAntiHolo[opeOfRList[rescaleR[\[Epsilon]AntiHolo] /@ antiOps], targetWeightAntiHolo, \[Epsilon]AntiHolo];

  freeProjected = sign combineChiral[projectedHolo, projectedAntiHolo];
  restProjected = If[restR === {}, 1, opeOfRList[restR]];
  multiplyFactors[freeProjected, restProjected]
];

OPEProjectedHolo[wH_][a___, 0, b___] := 0;
OPEProjectedHolo[wH_][a___, x_ + y_, b___] := OPEProjectedHolo[wH][a, x, b] + OPEProjectedHolo[wH][a, y, b];
OPEProjectedHolo[wH_][a___, c_ x_, b___] := c OPEProjectedHolo[wH][a, x, b] /; (!containsFieldQ[c]);

OPEProjectedHolo[wH_][Ra__ /; (And @@ (RTest /@ {Ra}) && AnyTrue[{Ra}, hasCollapsable])] := Module[
  {collPieces, collR, restR, insertionWeightHolo, targetWeightHolo, \[Epsilon]Holo, projectedHolo, restProjected},
  insertionWeightHolo = Total[totalWeightHolo /@ {Ra}];
  targetWeightHolo = wH - insertionWeightHolo;
  collPieces = splitCollapsable /@ {Ra};
  collR = Select[collPieces[[All, 1]], # =!= 1 &];
  restR = Select[collPieces[[All, 2]], # =!= 1 &];
  projectedHolo = projectHolo[opeOfRList[rescaleR[\[Epsilon]Holo] /@ collR], targetWeightHolo, \[Epsilon]Holo];
  restProjected = If[restR === {}, 1, opeOfRList[restR]];
  multiplyFactors[projectedHolo, restProjected]
];


OPEProjectedAntiHolo[wA_][a___, 0, b___] := 0;
OPEProjectedAntiHolo[wA_][a___, x_ + y_, b___] := OPEProjectedAntiHolo[wA][a, x, b] + OPEProjectedAntiHolo[wA][a, y, b];
OPEProjectedAntiHolo[wA_][a___, c_ x_, b___] := c OPEProjectedAntiHolo[wA][a, x, b] /; (!containsFieldQ[c]);

OPEProjectedAntiHolo[wA_][Ra__ /; (And @@ (RTest /@ {Ra}) && AnyTrue[{Ra}, hasCollapsable])] := Module[
  {collPieces, collR, restR, insertionWeightAntiHolo, targetWeightAntiHolo, \[Epsilon]AntiHolo, projectedAntiHolo, restProjected},
  insertionWeightAntiHolo = Total[totalWeightAntiHolo /@ {Ra}];
  targetWeightAntiHolo = wA - insertionWeightAntiHolo;
  collPieces = splitCollapsable /@ {Ra};
  collR = Select[collPieces[[All, 1]], # =!= 1 &];
  restR = Select[collPieces[[All, 2]], # =!= 1 &];
  projectedAntiHolo = projectAntiHolo[opeOfRList[rescaleR[\[Epsilon]AntiHolo] /@ collR], targetWeightAntiHolo, \[Epsilon]AntiHolo];
  restProjected = If[restR === {}, 1, opeOfRList[restR]];
  multiplyFactors[projectedAntiHolo, restProjected]
];



(* ::Section:: *)
(*End*)


End[];


EndPackage[];
