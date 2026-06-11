(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Brackets`TypeII`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`TypeII`"];
Needs["StringCode`Operators`"];
Needs["StringCode`Operators`TypeII`"];
Needs["StringCode`Taylor`"];
Needs["StringCode`Taylor`TypeII`"];
Needs["StringCode`Conventions`TypeII`"];
Needs["StringCode`OPE`"];
Needs["StringCode`OPE`TypeII`"];
Needs["StringCode`Brackets`"];


(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection::Closed:: *)
(*Define 1-bracket (action of BRST charge)*)


actBRSTHolo[Ra_ /; RTest[Ra]] := Module[
  {wH, z, result},
  wH = totalWeightHolo[Ra];
  inputAtOrigin = Expand[RAtPos[Ra, 0, 0]];
  result = OPEProjectedHolo[wH][jBRST[z], inputAtOrigin];
  Expand[z result]/.{z->0}
];

actBRSTAntiHolo[Ra_ /; RTest[Ra]] := Module[
  {wH, zBar, result},
  wH = totalWeightAntiHolo[Ra];
  inputAtOrigin = Expand[RAtPos[Ra, 0, 0]];
  result = OPEProjectedAntiHolo[wH][jBRSTbar[zBar], inputAtOrigin];
  Expand[zBar result]/.{zBar->0}
];

(*Position extraction: read the holomorphic and antiholomorphic coordinates from an R*)
extractRPos::usage = "Reads off the holomorphic and antiholomorphic coordinates of a normal-ordered product R[...], from the first field factor that exposes each.";
extractRPos[Ra_ /; RTest[Ra]] := Module[
  {holoPos = 0, antiholoPos = 0, holoFound = False, antiholoFound = False},
  Scan[
    Function[op,
      If[isField[Head[op]],
        Which[
          isHolomorphic[Head[op]] && isAntiHolomorphic[Head[op]],
            If[! holoFound, holoPos = op[[-2]]; holoFound = True];
            If[! antiholoFound, antiholoPos = op[[-1]]; antiholoFound = True],
          isHolomorphic[Head[op]],
            If[! holoFound, holoPos = Last[op]; holoFound = True],
          isAntiHolomorphic[Head[op]],
            If[! antiholoFound, antiholoPos = Last[op]; antiholoFound = True]
        ]
      ]
    ],
    Ra
  ];
  {holoPos, antiholoPos}
];

(*Position-preserving BRST wrappers: read the position off Ra, act with BRST at origin, then translate the result back via flat placement (no conformal Jacobian)*)
actBRSTHoloAtPos::usage = "Position-preserving variant of actBRSTHolo: applies BRST at origin and shifts every R[...] in the result back to Ra's original holomorphic/antiholomorphic position via placeAtPointNoScale (flat placement, no conformal Jacobian).";
actBRSTHoloAtPos[Ra_ /; RTest[Ra]] := Module[
  {zR, zbarR, brstResult},
  {zR, zbarR} = extractRPos[Ra];
  brstResult = actBRSTHolo[Ra];
  brstResult /. {Rb_ /; RTest[Rb] :> (placeAtPointNoScale[zR, zbarR] /@ Rb)}
];

actBRSTAntiHoloAtPos::usage = "Position-preserving variant of actBRSTAntiHolo.";
actBRSTAntiHoloAtPos[Ra_ /; RTest[Ra]] := Module[
  {zR, zbarR, brstResult},
  {zR, zbarR} = extractRPos[Ra];
  brstResult = actBRSTAntiHolo[Ra];
  brstResult /. {Rb_ /; RTest[Rb] :> (placeAtPointNoScale[zR, zbarR] /@ Rb)}
];

(*Graded Leibniz distribution of BRST charge over a multi-local product*)
actBRSTHolo[multiOp_ /; MultiOpTest[multiOp]] := Module[
  {opList, parities, result = 0},
  opList   = List @@ multiOp;
  parities = Map[parityOp, opList];
  Do[
    result = result + (-1)^(Total[Take[parities, i - 1]]) MultiOp @@ MapAt[
      actBRSTHoloAtPos[#] &, opList, i
    ],
    {i, 1, Length[opList]}
  ];
  result
];

actBRSTAntiHolo[multiOp_ /; MultiOpTest[multiOp]] := Module[
  {opList, parities, result = 0},
  opList   = List @@ multiOp;
  parities = Map[parityOp, opList];
  Do[
    result = result + (-1)^(Total[Take[parities, i - 1]]) MultiOp @@ MapAt[
      actBRSTAntiHoloAtPos[#] &, opList, i
    ],
    {i, 1, Length[opList]}
  ];
  result
];


(* ::Subsection:: *)
(*Define string bracket*)


Bracket[toBracket__/;AllTrue[{toBracket}, (RTest[#] || MultiOpTest[#]) &]]:= Module[{result = 0, afterApplyingBghosts, numberOfHoloPCOs, numberOfAntiHoloPCOs, afterHeldActionOfPCOs },

(*Get bosonic part of the bracket*)
afterApplyingBghosts = BracketBosonic[toBracket];

(*Apply PCO zero-modes abstractly*)
numberOfHoloPCOs = Max[0, Ceiling[Abs[Total[Map[totalHolPicture, {toBracket}]]] - 1]];
numberOfAntiHoloPCOs = Max[0, Ceiling[Abs[Total[Map[totalAntiHolPicture, {toBracket}]]] - 1]];
afterHeldActionOfPCOs = Nest[actPCObar0Hold, Nest[actPCO0Hold, afterApplyingBghosts, numberOfHoloPCOs], numberOfAntiHoloPCOs];

result = b0mHold[afterHeldActionOfPCOs];
result]


(* ::Subsection:: *)
(*Define projection of the string bracket*)


BracketProjection::usage = "Projects a string bracket onto a given holomorphic/antihlomorphic weight"
BracketProjection[bracket_, weightHolo_, weightAntiHolo_]:= 
Module[{result, numberOfHoloPCOs = 0, numberOfAntiHoloPCOs = 0, bracketNoPCOs, prefac, localOps, projectionData, projectedOPE, holoOPEWithPCOs, antiHoloOPEWithPCOs},

(*Strip off PCOs*)
bracketNoPCOs = Expand[bracket//.{actPCO0Hold[x_]:> (numberOfHoloPCOs ++; x), actPCObar0Hold[x_]:> (numberOfAntiHoloPCOs ++; x)}];

(*Loop through each multi-local term of Bracket obtained by different actions of B-ghosts [inside PCO actions]*)
result = Total @ Last @ Reap[
Scan[Function[bracketNoPCOsTerm,

prefac = extractPrefacFromMultiOpTimesConstant[bracketNoPCOsTerm];
localOps = extractListFromMultiOpTimesConstant[bracketNoPCOsTerm];
(* Shared projection logic; TypeII-specific work is only the subsequent PCO action. *)
projectionData = projectBracketLocalOps[localOps, weightHolo, weightAntiHolo];
If[projectionData[[1]] === "Factorized",
(* Fast path: project each chirality separately, then apply holomorphic/antiholomorphic PCOs. *)
{holoOPEWithPCOs, antiHoloOPEWithPCOs} = {
  Nest[actPCOHolo, prefac projectionData[[2]] projectionData[[3]], numberOfHoloPCOs],
  Nest[actPCOAntiHolo, projectionData[[4]], numberOfAntiHoloPCOs]
};
Sow[combineProjectedBracketChiral[holoOPEWithPCOs, antiHoloOPEWithPCOs]],
(* Generic path: project the unsplit local operators, then apply combined PCO action. *)
projectedOPE = prefac projectionData[[2]];
Sow[Nest[actPCO, projectedOPE, numberOfHoloPCOs + numberOfAntiHoloPCOs]]
];
], If[Head[bracketNoPCOs] === Plus, List @@ bracketNoPCOs, {bracketNoPCOs}]]
,
_,
Total[#2] &
];
result
];


(* ::Subsection:: *)
(*Define action of PCOs*)


actPCOHolo::usage = "Acts zero mode of holomorphic PCO on a local operator";
actPCOHolo[Ra_ /; RTest[Ra]] := actPCOHolo[Ra] = Module[
  {wH, z, result},
  wH = totalWeightHolo[Ra];
  inputAtOrigin = Expand[RAtPos[Ra, 0, 0]];
  result = OPEProjectedHolo[wH][PCO[z], inputAtOrigin];
  Expand[result]/.{z->0}
];


actPCOAntiHolo::usage = "Acts zero mode of antiholomorphic PCO on a local operator";
actPCOAntiHolo[Ra_ /; RTest[Ra]] := actPCOAntiHolo[Ra] = Module[
  {wH, zBar, result},
  wH = totalWeightAntiHolo[Ra];
  inputAtOrigin = Expand[RAtPos[Ra, 0, 0]];
  result = OPEProjectedAntiHolo[wH][PCObar[zBar], inputAtOrigin];
  Expand[result]/.{zBar->0}
];


(*Multilinearity of PCO zero mode actions*)
actPCOHolo[a_+b_]:=actPCOHolo[a] + actPCOHolo[b];
actPCOHolo[a_ b_]:=a actPCOHolo[b]/;(isScalarFactorQ[a])
actPCOHolo[0] := 0;

actPCOAntiHolo[a_+b_]:=actPCOAntiHolo[a] + actPCOAntiHolo[b];
actPCOAntiHolo[a_ b_]:=a actPCOAntiHolo[b]/;(isScalarFactorQ[a])
actPCOAntiHolo[0] := 0;

actPCO[a___]:= actPCOHolo[actPCOAntiHolo[a]];


(* ::Subsection:: *)
(*Determine whether OPE should be computed*)


containsCompositeHolo::usage = "Checks if contains holomorphic composite";
containsCompositeHolo[PCOelem_]:= containsCompositeHolo[PCOelem] = First@FirstPosition[PCOelem/.{R->List}, _?(MatchQ[Head[#], exp\[Phi]b | exp\[Phi]f] &)];

containsCompositeAntiHolo::usage = "Checks if contains antiholomorphic composite";
containsCompositeAntiHolo[PCOelem_]:= containsCompositeAntiHolo[PCOelem] = First@FirstPosition[PCOelem/.{R->List}, _?(MatchQ[Head[#], exp\[Phi]tb | exp\[Phi]tf] &)];


(* ::Subsubsection:: *)
(*Superghosts*)


singularity[d\[Phi][n_,z_],d\[Phi][m_,w_]]:= 2 + m + n;
singularity[d\[Phi]t[n_,z_],d\[Phi]t[m_,w_]]:= 2 + m + n;
singularity[\[Eta][n_,z_],\[Xi][m_,w_]]:= 1 + m + n;
singularity[\[Xi][m_,w_],\[Eta][n_,z_]]:= 1 + m + n;
singularity[\[Eta]t[n_,z_],\[Xi]t[m_,w_]]:= 1 + m + n;
singularity[\[Xi]t[m_,w_],\[Eta]t[n_,z_]]:=1 + m + n;
singularity[\[Beta][n_,z_],\[Gamma][m_,w_]]:= 1 + m + n;
singularity[\[Gamma][m_,w_],\[Beta][n_,z_]]:= 1 + m + n;
singularity[\[Beta]t[n_,z_],\[Gamma]t[m_,w_]]:= 1 + m + n;
singularity[\[Gamma]t[m_,w_],\[Beta]t[n_,z_]]:= 1 + m + n;

singularity[exp\[Phi]b[a_,z_],exp\[Phi]b[b_,w_]]:= a b;
singularity[exp\[Phi]b[a_,z_],exp\[Phi]f[b_,w_]]:=a b;
singularity[exp\[Phi]f[a_,z_],exp\[Phi]b[b_,w_]]:=a b;
singularity[exp\[Phi]f[a_,z_],exp\[Phi]f[b_,w_]]:=a b;
singularity[exp\[Phi]tb[a_,z_],exp\[Phi]tb[b_,w_]]:=a b;
singularity[exp\[Phi]tb[a_,z_],exp\[Phi]tf[b_,w_]]:=a b;
singularity[exp\[Phi]tf[a_,z_],exp\[Phi]tb[b_,w_]]:=a b;
singularity[exp\[Phi]tf[a_,z_],exp\[Phi]tf[b_,w_]]:=a b;

singularity[d\[Phi][a_, z_], exp\[Phi]f[b_, w_]] := 1 + a;
singularity[d\[Phi][a_, z_], exp\[Phi]b[b_, w_]] := 1 + a;
singularity[d\[Phi]t[a_, z_], exp\[Phi]tf[b_, w_]] := 1 + a;
singularity[d\[Phi]t[a_, z_], exp\[Phi]tb[b_, w_]] := 1 + a;
singularity[exp\[Phi]f[b_, z_], d\[Phi][a_, w_]] := 1 + a;
singularity[exp\[Phi]b[b_, z_], d\[Phi][a_, w_]] := 1 + a;
singularity[exp\[Phi]tf[b_, z_], d\[Phi]t[a_, w_]] := 1 + a;
singularity[exp\[Phi]tb[b_, z_], d\[Phi]t[a_, w_]] := 1 + a;


(* ::Subsection:: *)
(*PCO action on MultiOps*)
xi0ModeHolo::usage = "Acts one holomorphic xi 0-mode on an operator."

xi0ModeHolo[contourCenter_][Op_ ] := Module[{result = 0, etaAssociations = <||>, fermionNumber = 0, position = 1},
Scan[
  Function[Opelem,
  If[Head[Opelem] === \[Eta],
  If[Opelem[[2]]-contourCenter =!= 0,
  AssociateTo[etaAssociations, position -> {Opelem -> (-1)^(fermionNumber+1)(Opelem[[2]]-contourCenter)^(-1-Opelem[[1]])}]]];
  If[isFermion[Head[Opelem]], fermionNumber = fermionNumber + 1];
  position = position + 1;],
Op];
KeyValueMap[
  Function[{currentPosition, replacement},
    result = result + ReplaceAt[Op, replacement, currentPosition]],
  etaAssociations];
result
];

xi0ModeHolo[contourCenter_][a_ + b_] :=
  xi0ModeHolo[contourCenter][a] + xi0ModeHolo[contourCenter][b];
xi0ModeHolo[contourCenter_][a_ b_] :=
  a xi0ModeHolo[contourCenter][b] /; isScalarFactorQ[a];
xi0ModeHolo[contourCenter_][0] := 0;

actXi0ModeHolo::usage = "Xi 0-mode placeholder on a multi-local operator.";
actXi0ModeHolo[a_ , expr_Plus] := Map[actXi0ModeHolo[a, #] &, expr];
actXi0ModeHolo[a_, b_ c_] := b actXi0ModeHolo[a, c] /; isScalarFactorQ[b];

actXi0ModeHolo[
  xi0ModeHolo[contourCenter_],
  multiOp_ /; MultiOpTest[multiOp]
] := Module[{result = MultiOp[R[\[Xi][0,0]],multiOp] (*Result is always non-zero, even when contractions don't happen*), opList, parities },
  opList = List @@ multiOp;
  parities = Map[parityOp, opList];
  Do[ (*Graded Leibniz rule*)
      result = result + (-1)^(Total[Take[parities, i-1]]) MultiOp @@ MapAt[
        actXi0ModeHolo[xi0ModeHolo[contourCenter], #] &, opList, i
      ],
    {i,1,Length[opList]}
  ];
  result
];

actXi0ModeHolo[xi0ModeHolo[contourCenter_], Ra_ /; RTest[Ra]] := xi0ModeHolo[contourCenter][Ra];
actXi0ModeHolo[_, a_ /; NumericQ[a]] := 0;

(* Antiholomorphic mirror *)

xi0ModeAntiHolo::usage = "Acts one antiholomorphic xi 0-mode on an operator."

xi0ModeAntiHolo[contourCenter_][Op_] := Module[
  {result = 0, etaAssociations = <||>, fermionNumber = 0, position = 1},
  Scan[
    Function[Opelem,
      If[Head[Opelem] === \[Eta]t,
        If[Opelem[[2]] - contourCenter =!= 0,
          AssociateTo[etaAssociations,
            position -> {Opelem -> (-1)^(fermionNumber + 1) (Opelem[[2]] - contourCenter)^(-1 - Opelem[[1]])}
          ]
        ]
      ];
      If[isFermion[Head[Opelem]], fermionNumber = fermionNumber + 1];
      position = position + 1;
    ],
    Op
  ];
  KeyValueMap[
    Function[{currentPosition, replacement},
      result = result + ReplaceAt[Op, replacement, currentPosition]
    ],
    etaAssociations
  ];
  result
];

xi0ModeAntiHolo[contourCenter_][a_ + b_] :=
  xi0ModeAntiHolo[contourCenter][a] + xi0ModeAntiHolo[contourCenter][b];
xi0ModeAntiHolo[contourCenter_][a_ b_] :=
  a xi0ModeAntiHolo[contourCenter][b] /; isScalarFactorQ[a];
xi0ModeAntiHolo[contourCenter_][0] := 0;

actXi0ModeAntiHolo::usage = "Xi 0-mode antiholomorphic placeholder on a multi-local operator.";
actXi0ModeAntiHolo[a_, expr_Plus] := Map[actXi0ModeAntiHolo[a, #] &, expr];
actXi0ModeAntiHolo[a_, b_ c_] := b actXi0ModeAntiHolo[a, c] /; isScalarFactorQ[b];

actXi0ModeAntiHolo[
  xi0ModeAntiHolo[contourCenter_],
  multiOp_ /; MultiOpTest[multiOp]
] := Module[
  {result = MultiOp[R[\[Xi]t[0, 0]], multiOp], opList, parities},
  opList = List @@ multiOp;
  parities = Map[parityOp, opList];
  Do[
    result = result + (-1)^(Total[Take[parities, i - 1]]) MultiOp @@ MapAt[
      actXi0ModeAntiHolo[xi0ModeAntiHolo[contourCenter], #] &, opList, i
    ],
    {i, 1, Length[opList]}
  ];
  result
];

actXi0ModeAntiHolo[xi0ModeAntiHolo[contourCenter_], Ra_ /; RTest[Ra]] := xi0ModeAntiHolo[contourCenter][Ra];
actXi0ModeAntiHolo[_, a_ /; NumericQ[a]] := 0;

(* ::Subsection:: *)
(*Extend action of PCO on multilocal operators*)

actPCOHoloMultiOp::usage = "Act holomorphic PCOs on multi local operators."
actPCOAntiHoloMultiOp::usage = "Act anti-holomorphic PCOs on multi local operators."

actPCOHoloMultiOp[expr_Plus] := Map[actPCOHoloMultiOp[#] &, expr];
actPCOHoloMultiOp[b_ c_] := b actPCOHoloMultiOp[c] /; isScalarFactorQ[b];
actPCOHoloMultiOp[0] := 0;
actPCOAntiHoloMultiOp[expr_Plus] := Map[actPCOAntiHoloMultiOp[#] &, expr];
actPCOAntiHoloMultiOp[b_ c_] := b actPCOAntiHoloMultiOp[c] /; isScalarFactorQ[b];
actPCOAntiHoloMultiOp[0] := 0;

actPCOHoloMultiOp[multiOp_ /; MultiOpTest[multiOp]] := actBRSTHolo[actXi0ModeHolo[xi0ModeHolo[0], multiOp]]+ actXi0ModeHolo[xi0ModeHolo[0], actBRSTHolo[multiOp]];
actPCOAntiHoloMultiOp[multiOp_ /; MultiOpTest[multiOp]] := actBRSTAntiHolo[actXi0ModeAntiHolo[xi0ModeAntiHolo[0], multiOp]]+ actXi0ModeAntiHolo[xi0ModeAntiHolo[0],actBRSTAntiHolo[multiOp]];

(* ::Subsection:: *)
(*Define EffectiveBracket for TypeII, where PCO action on MultiOp is done directly.*)

BracketDirectPCO::usage = "Bracket nesting actPCOHolo/AntiHoloMultiOp."

BracketDirectPCO[args___, a_ + b_, rest___] :=
  BracketDirectPCO[args, a, rest] + BracketDirectPCO[args, b, rest];
BracketDirectPCO[args___, c_ d_, rest___] :=
  c BracketDirectPCO[args, d, rest] /; isScalarFactorQ[c];
BracketDirectPCO[args___, 0, rest___] := 0;

BracketDirectPCO[toBracket__ /; AllTrue[{toBracket}, (RTest[#] || MultiOpTest[#]) &]] := Module[
  {bghosted, nHolo, nAntiHolo, withPCOs},
  bghosted   = BracketBosonic[toBracket];
  nHolo      = Max[0, Ceiling[Abs[Total[Map[totalHolPicture,     {toBracket}]]] - 1]];
  nAntiHolo  = Max[0, Ceiling[Abs[Total[Map[totalAntiHolPicture, {toBracket}]]] - 1]];
  withPCOs   = Nest[actPCOAntiHoloMultiOp, Nest[actPCOHoloMultiOp, bghosted, nHolo], nAntiHolo];
  b0mHold[withPCOs]
];

projectorBarSubDirect = {ProjectorBarHold[wH_, wA_][a_] :> a - ProjectorHold[wH, wA][a]};
projectorOfBracketSubDirect = {ProjectorHold[wH_, wA_][BracketHold[a__]] :> CollapseB0m[BracketProjected[a, wH, wA]]};
propagatorSubDirect = {PropagatorHold[q_][a___] :> -ApplyPropagator[q][a]};
bracketSubDirect = {BracketHold[a__] :> CollapseB0m[BracketDirectPCO[a]]};
subsList = Join[projectorBarSubDirect, projectorOfBracketSubDirect, propagatorSubDirect, bracketSubDirect];

EffectiveBracketDirectPCO::usage = "EffectiveBracket using BracketDirectPCO."

EffectiveBracketDirectPCO[args___, a_ + b_, rest___, wH_, wA_] :=
  EffectiveBracketDirectPCO[args, a, rest, wH, wA] + EffectiveBracketDirectPCO[args, b, rest, wH, wA];
EffectiveBracketDirectPCO[args___, c_ d_, rest___, wH_, wA_] :=
  c EffectiveBracketDirectPCO[args, d, rest, wH, wA] /; isScalarFactorQ[c];

EffectiveBracketDirectPCO[fields__, wH_, wA_] :=
  EffectiveBracketHold[fields, wH, wA] //. subsList;



(*End*)


End[];


EndPackage[];
