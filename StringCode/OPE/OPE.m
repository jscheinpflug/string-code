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


(* ::Subsection:: *)
(*Projected OPE API*)


containsScalarTerm::usage = "Checks if an OPE result contains any terms without R (scalar terms).";
containsScalarTerm[expr_] := Module[{num = Numerator[Together[expr]], expanded},
  If[num === 0, False,
    expanded = Expand[num];
    If[Head[expanded] === Plus,
      AnyTrue[List @@ expanded, FreeQ[#, R] &],
      FreeQ[expanded, R]
    ]
  ]
];

minWeightFromOPE::usage = "Computes the minimum weight from an OPE result by extracting R operators and checking for scalar terms.";
minWeightFromOPE[opeResult_, weightFn_] := Module[{extractedRs, weights},
  extractedRs = Cases[opeResult, _R, {0, Infinity}];
  weights = weightFn /@ extractedRs;
  If[containsScalarTerm[opeResult], AppendTo[weights, 0]];
  If[weights === {}, 0, Min[weights]]
];

expPhiHoloNames::usage = "Symbol names of holomorphic expΦ operators.";
expPhiHoloNames = {"exp\[Phi]b", "exp\[Phi]f"};

expPhiAntiHoloNames::usage = "Symbol names of antiholomorphic expΦ operators.";
expPhiAntiHoloNames = {"exp\[Phi]tb", "exp\[Phi]tf"};

isExpPhiHolo::usage = "Checks if a field is a holomorphic expΦ operator.";
isExpPhiHolo[op_] := MemberQ[expPhiHoloNames, SymbolName[Head[op]]];

isExpPhiAntiHolo::usage = "Checks if a field is an antiholomorphic expΦ operator.";
isExpPhiAntiHolo[op_] := MemberQ[expPhiAntiHoloNames, SymbolName[Head[op]]];

expPhiCharge::usage = "Extracts the charge (first argument) from an expΦ operator.";
expPhiCharge[op_] := op[[1]];

combinedRestWeightHolo::usage = "Computes the combined holomorphic weight for a list of non-collapsable R operators, accounting for expΦ charge combination.";
combinedRestWeightHolo[restOps_List] := Module[
  {allFields, expPhiFields, otherFields, totalCharge, expPhiWeight, otherWeight},
  If[restOps === {}, Return[0]];
  allFields = Flatten[List @@@ restOps];
  expPhiFields = Select[allFields, isExpPhiHolo];
  otherFields = Select[allFields, !isExpPhiHolo[#] &];
  totalCharge = Total[expPhiCharge /@ expPhiFields];
  expPhiWeight = If[expPhiFields === {}, 0, -1/2 * totalCharge * (totalCharge + 2)];
  otherWeight = Total[weightHolo /@ otherFields];
  expPhiWeight + otherWeight
];

combinedRestWeightAntiHolo::usage = "Computes the combined antiholomorphic weight for a list of non-collapsable R operators, accounting for expΦ charge combination.";
combinedRestWeightAntiHolo[restOps_List] := Module[
  {allFields, expPhiFields, otherFields, totalCharge, expPhiWeight, otherWeight},
  If[restOps === {}, Return[0]];
  allFields = Flatten[List @@@ restOps];
  expPhiFields = Select[allFields, isExpPhiAntiHolo];
  otherFields = Select[allFields, !isExpPhiAntiHolo[#] &];
  totalCharge = Total[expPhiCharge /@ expPhiFields];
  expPhiWeight = If[expPhiFields === {}, 0, (-1/2) * totalCharge * (totalCharge + 2)];
  otherWeight = Total[weightAntiHolo /@ otherFields];
  expPhiWeight + otherWeight
];

minCombinedWeightFromOPEHolo::usage = "Computes the minimum combined holomorphic weight from an OPE result, extracting R operators per term and accounting for expΦ charge combination.";
minCombinedWeightFromOPEHolo[opeResult_] := Module[
  {expanded, terms, weights},
  expanded = Expand[opeResult];
  terms = If[Head[expanded] === Plus, List @@ expanded, {expanded}];
  weights = Table[
    Module[{rs = Cases[term, _R, {0, Infinity}]},
      If[rs === {}, 0, combinedRestWeightHolo[rs]]
    ],
    {term, terms}
  ];
  If[weights === {}, 0, Min[weights]]
];

minCombinedWeightFromOPEAntiHolo::usage = "Computes the minimum combined antiholomorphic weight from an OPE result, extracting R operators per term and accounting for expΦ charge combination.";
minCombinedWeightFromOPEAntiHolo[opeResult_] := Module[
  {expanded, terms, weights},
  expanded = Expand[opeResult];
  terms = If[Head[expanded] === Plus, List @@ expanded, {expanded}];
  weights = Table[
    Module[{rs = Cases[term, _R, {0, Infinity}]},
      If[rs === {}, 0, combinedRestWeightAntiHolo[rs]]
    ],
    {term, terms}
  ];
  If[weights === {}, 0, Min[weights]]
];


OPEProjected[wH_, wA_][a___, 0, b___] := 0;
OPEProjected[wH_, wA_][a___, x_ + y_, b___] := OPEProjected[wH, wA][a, x, b] + OPEProjected[wH, wA][a, y, b];
OPEProjected[wH_, wA_][a___, c_ x_, b___] := c OPEProjected[wH, wA][a, x, b] /; (!containsFieldQ[c]);

OPEProjected[wH_, wA_][Ra__ /; (And @@ (RTest /@ {Ra}) && AnyTrue[{Ra}, hasCollapsable])] := Module[
  {
    collPieces, collR, restR, collLists, splitLists, restLists, restSplitLists, sign, signRest,
    holoOps, antiOps, restHoloOps, restAntiOps,
    insertionWeightHolo, insertionWeightAntiHolo, targetWeightHolo, targetWeightAntiHolo,
    \[Epsilon]Holo, \[Epsilon]AntiHolo, projectedCollHolo, projectedRestHolo, projectedCollAntiHolo, projectedRestAntiHolo,
    tableHolo, tableAntiHolo, holoProjected, antiHoloProjected, opeCollResultHolo, opeRestResultHolo, opeCollResultAnti, opeRestResultAnti, minCollWeightHolo, minRestWeightHolo, minWeightHolo, minCollWeightAntiHolo, minRestWeightAntiHolo, minWeightAntiHolo
  },

  insertionWeightHolo = Total[totalWeightHolo /@ {Ra}];
  insertionWeightAntiHolo = Total[totalWeightAntiHolo /@ {Ra}];
  targetWeightHolo = wH - insertionWeightHolo;
  targetWeightAntiHolo = wA - insertionWeightAntiHolo;

  collPieces = splitCollapsable /@ {Ra};
  collR = Select[collPieces[[All, 1]], # =!= 1 &];
  restR = Select[collPieces[[All, 2]], # =!= 1 &];

  (* Split collapsable fields into holo/antiholo *)
  collLists = factorizeForChiralSplit /@ (List @@ # & /@ collR);
  splitLists = splitOperators[#, isHolomorphic, isAntiHolomorphic] & /@ collLists;
  sign = If[Flatten[collLists] === {}, 1,
    factorizationSign[Flatten[collLists], isHolomorphic, isAntiHolomorphic]
  ];
  holoOps = Select[R @@@ (splitLists[[All, 1]]), RTest];
  antiOps = Select[R @@@ (splitLists[[All, 2]]), RTest];

  (* Split rest fields into holo/antiholo *)
  restLists = factorizeForChiralSplit /@ (List @@ # & /@ restR);
  restSplitLists = splitOperators[#, isHolomorphic, isAntiHolomorphic] & /@ restLists;
  signRest = If[Flatten[restLists] === {}, 1,
    factorizationSign[Flatten[restLists], isHolomorphic, isAntiHolomorphic]
  ];
  restHoloOps = Select[R @@@ (restSplitLists[[All, 1]]), RTest];
  restAntiOps = Select[R @@@ (restSplitLists[[All, 2]]), RTest];

  (* Holomorphic sector *)
  (* Compute OPE for each sector *)
  opeCollResultHolo = opeOfRList[rescaleR[\[Epsilon]Holo] /@ holoOps];
  opeRestResultHolo = opeOfRList[rescaleR[\[Epsilon]Holo] /@ restHoloOps];
  (* Compute minimum weight: extract from OPE for collapsable, use minCombinedWeightFromOPE for rest (expΦ charges combine) *)
  minCollWeightHolo = minWeightFromOPE[opeCollResultHolo, totalWeightHolo];
  minRestWeightHolo = minCombinedWeightFromOPEHolo[opeRestResultHolo];
  minWeightHolo = minCollWeightHolo + minRestWeightHolo;
  projectedCollHolo[i_] := projectHolo[opeCollResultHolo, targetWeightHolo - i, \[Epsilon]Holo];
  projectedRestHolo[i_] := If[restHoloOps === {}, If[i == 0, 1, 0], projectHolo[opeRestResultHolo, i, \[Epsilon]Holo]];
  tableHolo = Table[multiplyFactors[projectedCollHolo[i], projectedRestHolo[i]], {i, minWeightHolo, targetWeightHolo}];
  holoProjected = Total[tableHolo];

  (* AntiHolomorphic sector *)
  (* Compute OPE for each sector *)
  opeCollResultAnti = opeOfRList[rescaleR[\[Epsilon]AntiHolo] /@ antiOps];
  opeRestResultAnti = opeOfRList[rescaleR[\[Epsilon]AntiHolo] /@ restAntiOps];
  (* Compute minimum weight: extract from OPE for collapsable, use minCombinedWeightFromOPE for rest (expΦ charges combine) *)
  minCollWeightAntiHolo = minWeightFromOPE[opeCollResultAnti, totalWeightAntiHolo];
  minRestWeightAntiHolo = minCombinedWeightFromOPEAntiHolo[opeRestResultAnti];
  minWeightAntiHolo = minCollWeightAntiHolo + minRestWeightAntiHolo;
  projectedCollAntiHolo[i_] := projectAntiHolo[opeCollResultAnti, targetWeightAntiHolo - i, \[Epsilon]AntiHolo];
  projectedRestAntiHolo[i_] := If[restAntiOps === {}, If[i == 0, 1, 0], projectAntiHolo[opeRestResultAnti, i, \[Epsilon]AntiHolo]];
  tableAntiHolo = Table[multiplyFactors[projectedCollAntiHolo[i], projectedRestAntiHolo[i]], {i, minWeightAntiHolo, targetWeightAntiHolo}];
  antiHoloProjected = Total[tableAntiHolo];

  sign signRest combineChiral[holoProjected, antiHoloProjected]
];

OPEProjectedHolo[wH_][a___, 0, b___] := 0;
OPEProjectedHolo[wH_][a___, x_ + y_, b___] := OPEProjectedHolo[wH][a, x, b] + OPEProjectedHolo[wH][a, y, b];
OPEProjectedHolo[wH_][a___, c_ x_, b___] := c OPEProjectedHolo[wH][a, x, b] /; (!containsFieldQ[c]);

OPEProjectedHolo[wH_][Ra__ /; (And @@ (RTest /@ {Ra}) && AnyTrue[{Ra}, hasCollapsable])] := Module[
  {collPieces, collR, restR, insertionWeightHolo, targetWeightHolo, \[Epsilon]Holo, opeCollResult, opeRestResult, minCollWeightHolo, minRestWeightHolo, minWeightHolo, projectedCollHolo, projectedRestHolo, table},
  insertionWeightHolo = Total[totalWeightHolo /@ {Ra}];
  targetWeightHolo = wH - insertionWeightHolo;
  collPieces = splitCollapsable /@ {Ra};
  collR = Select[collPieces[[All, 1]], # =!= 1 &];
  restR = Select[collPieces[[All, 2]], # =!= 1 &];
  (* Compute OPE for each sector *)
  opeCollResult = opeOfRList[rescaleR[\[Epsilon]Holo] /@ collR];
  opeRestResult = opeOfRList[rescaleR[\[Epsilon]Holo] /@ restR];
  (* Compute minimum weight: extract from OPE for collapsable, use minCombinedWeightFromOPE for rest (expΦ charges combine) *)
  minCollWeightHolo = minWeightFromOPE[opeCollResult, totalWeightHolo];
  minRestWeightHolo = minCombinedWeightFromOPEHolo[opeRestResult];
  minWeightHolo = minCollWeightHolo + minRestWeightHolo;
  projectedCollHolo[i_] := projectHolo[opeCollResult, targetWeightHolo - i, \[Epsilon]Holo];
  projectedRestHolo[i_] := If[restR === {}, If[i == 0, 1, 0], projectHolo[opeRestResult, i, \[Epsilon]Holo]];
  table = Table[multiplyFactors[projectedCollHolo[i], projectedRestHolo[i]], {i, minWeightHolo, targetWeightHolo}];
  Total[table]
];


OPEProjectedAntiHolo[wA_][a___, 0, b___] := 0;
OPEProjectedAntiHolo[wA_][a___, x_ + y_, b___] := OPEProjectedAntiHolo[wA][a, x, b] + OPEProjectedAntiHolo[wA][a, y, b];
OPEProjectedAntiHolo[wA_][a___, c_ x_, b___] := c OPEProjectedAntiHolo[wA][a, x, b] /; (!containsFieldQ[c]);

OPEProjectedAntiHolo[wA_][Ra__ /; (And @@ (RTest /@ {Ra}) && AnyTrue[{Ra}, hasCollapsable])] := Module[
  {collPieces, collR, restR, insertionWeightAntiHolo, targetWeightAntiHolo, \[Epsilon]AntiHolo, opeCollResult, opeRestResult, minCollWeightAntiHolo, minRestWeightAntiHolo, minWeightAntiHolo, projectedCollAntiHolo, projectedRestAntiHolo, table},
  insertionWeightAntiHolo = Total[totalWeightAntiHolo /@ {Ra}];
  targetWeightAntiHolo = wA - insertionWeightAntiHolo;
  collPieces = splitCollapsable /@ {Ra};
  collR = Select[collPieces[[All, 1]], # =!= 1 &];
  restR = Select[collPieces[[All, 2]], # =!= 1 &];
  (* Compute OPE for each sector *)
  opeCollResult = opeOfRList[rescaleR[\[Epsilon]AntiHolo] /@ collR];
  opeRestResult = opeOfRList[rescaleR[\[Epsilon]AntiHolo] /@ restR];
  (* Compute minimum weight: extract from OPE for collapsable, use minCombinedWeightFromOPE for rest (expΦ charges combine) *)
  minCollWeightAntiHolo = minWeightFromOPE[opeCollResult, totalWeightAntiHolo];
  minRestWeightAntiHolo = minCombinedWeightFromOPEAntiHolo[opeRestResult];
  minWeightAntiHolo = minCollWeightAntiHolo + minRestWeightAntiHolo;
  projectedCollAntiHolo[i_] := projectAntiHolo[opeCollResult, targetWeightAntiHolo - i, \[Epsilon]AntiHolo];
  projectedRestAntiHolo[i_] := If[restR === {}, If[i == 0, 1, 0], projectAntiHolo[opeRestResult, i, \[Epsilon]AntiHolo]];
  table = Table[multiplyFactors[projectedCollAntiHolo[i], projectedRestAntiHolo[i]], {i, minWeightAntiHolo, targetWeightAntiHolo}];
  Total[table]
];



(* ::Section:: *)
(*End*)


End[];


EndPackage[];
