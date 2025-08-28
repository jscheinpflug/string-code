(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Brackets`Bosonic`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`Bosonic`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`Bosonic`"];
Needs["StringCode`StringFields`"];
Needs["StringCode`StringFields`Bosonic`"];
Needs["StringCode`Operators`"];
Needs["StringCode`Operators`Bosonic`"];
Needs["StringCode`Taylor`"];
Needs["StringCode`Taylor`Bosonic`"];
Needs["StringCode`Conventions`Bosonic`"];
Needs["StringCode`OPE`"];
Needs["StringCode`Brackets`"];


(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection::Closed:: *)
(*Define 1-bracket (action of BRST charge)*)


actBRSTHolo[SFa_/; SFtest[SFa]] := Module[{result = 0, z, Ra = SFAtPos[SFa, 0,0], OPEWithBRST, power, BRSTList, singularityUpperBound, compositeInBRSTPosition},
BRSTList = List @@ jBRSTbosonicstring[z];
Scan[Function[BRSTelem,
singularityUpperBound = upperBoundSingularity[singularityMatrix[BRSTelem, Ra], 0];
If[singularityUpperBound >= 0,
If[RcontainsProfile[Ra],
OPEWithBRST = OPE[BRSTelem, Ra, 2]//Expand,
OPEWithBRST = OPE[BRSTelem, Ra]//Expand];
Scan[Function[Relem,
power = Exponent[Relem, z];
If[power == -1, result = result + Relem, 
If[power < -1, result = result + TaylorAtOrder[Relem, -power - 1, 0, 0, 0]]];
], If[Head[OPEWithBRST] === Plus, List @@ OPEWithBRST, {OPEWithBRST}]];
];], BRSTList];
(z result // Expand)/.{z->0}];

actBRSTAntiHolo[SFa_/; SFtest[SFa]] := Module[{result = 0, zBar, Ra = SFAtPos[SFa, 0,0], OPEWithBRST, power, BRSTList, singularityUpperBound, compositeInBRSTPosition},
BRSTList = List @@ jBRSTbosonicstringbar[zBar];
Scan[Function[BRSTelem,
singularityUpperBound = upperBoundSingularity[singularityMatrix[BRSTelem, Ra], 0];
If[singularityUpperBound >= 0,
If[RcontainsProfile[Ra],
OPEWithBRST = OPE[BRSTelem, Ra, 2]//Expand,
OPEWithBRST = OPE[BRSTelem, Ra]//Expand];
Scan[Function[Relem,
power = Exponent[Relem, zBar];
If[power == -1, result = result + Relem, 
If[power < -1, result = result + TaylorAtOrder[Relem, 0, -power-1, 0, 0]]];
], If[Head[OPEWithBRST] === Plus, List @@ OPEWithBRST, {OPEWithBRST}]];
];], BRSTList];
(zBar result // Expand)/.{zBar->0}];


(* ::Subsection:: *)
(*Define string bracket*)


Bracket[toBracket__/;AllTrue[{toBracket}, SFtest]]:= Module[{result = 0, SFsAtPos, localCoordinateFunctionsHol, localCoordinateFunctionsAntiHol, localCoordinateReplacement, 
moduli, bracketOrder, bracketList = {toBracket}, w, wbar, curlyBs, minCGhostModdings, minCbarGhostModdings, SFList, afterApplyingBghosts, afterHeldActionOfPCOs},
bracketOrder = Length[bracketList];

(*conformally transform the string field insertions*)
{localCoordinateFunctionsHol, localCoordinateFunctionsAntiHol, w, wbar, moduli, localCoordinateReplacement} = getLocalCoordinateData[bracketOrder];
SFsAtPos = placeSFAtPosGivenLocalCoordinates[localCoordinateFunctionsHol, localCoordinateFunctionsAntiHol, bracketList, w, wbar];
SFList = List @@ SFsAtPos;

(*create and apply the curly B-ghost insertions, one B-ghost action on the insertions for each modulus*)
If[Length[moduli] > 0,
curlyBs = createCurlyBs[SFList, localCoordinateFunctionsHol, localCoordinateFunctionsAntiHol, moduli, bracketOrder, w, wbar];
afterApplyingBghosts = applyCurlyBs[SFsAtPos, curlyBs],
afterApplyingBghosts = SFsAtPos];

result = {afterApplyingBghosts, localCoordinateReplacement};
result]


(* ::Subsubsection::Closed:: *)
(*Place string fields at positions given by local coordinates*)


placeSFAtPosGivenLocalCoordinates::usage = "Places string fields at positions given by local coordinates of a given bracket";
placeSFAtPosGivenLocalCoordinates[localCoordinateFunctionsHol__, localCoordinateFunctionsAntiHol__, SFs__, w_, wbar_]:= 
Module[{i, length = Length[SFs]},
MultiOp @@ Table[SFAtPos[SFs[[i]], localCoordinateFunctionsHol[[i]]/.{w->0}, localCoordinateFunctionsAntiHol[[i]]/.{wbar->0}],{i,1,length}]
]


(* ::Subsection:: *)
(*Define projection of the string bracket*)


BracketProjection::usage = "Projects a string bracket onto a given holomorphic/antihlomorphic weight"
BracketProjection[{bracket_, localCoordinateReplacement_}, weightHolo_, weightAntiHolo_]:= 
Module[{result = {}, prefac, bracketHolo, bracketAntiHolo, OPEHolo, OPEAntiHolo,
\[Epsilon]Holo, \[Epsilon]AntiHolo, insertionWeightHolo, insertionWeightAntiHolo, projectedOPEHolo, projectedOPEAntiHolo},

(*Split the multi-local result of the bracket into holomorphic/antiholomorphic parts*)
{bracketHolo, bracketAntiHolo, prefac} = factorizeMultiOp[bracket];

(*Rescale positions of operators in the bracket by a common \[Epsilon]Holo/\[Epsilon]AntiHolo to ease weight projection, and then perform OPE*)
{OPEHolo, OPEAntiHolo} = {OPE @@ rescaleMultiOp[bracketHolo, \[Epsilon]Holo], OPE @@ rescaleMultiOp[bracketAntiHolo, \[Epsilon]AntiHolo]};

(*Perform the level projection on each holomorphic/antiholomorphic sector separately*)
{insertionWeightHolo, insertionWeightAntiHolo} = {totalWeightHolo[R @@ bracketHolo], totalWeightAntiHolo[R @@ bracketHolo]};

{projectedOPEHolo, projectedOPEAntiHolo} = 
{projectHolo[OPEHolo, weightHolo - insertionWeightHolo, \[Epsilon]Holo], projectAntiHolo[OPEAntiHolo, weightAntiHolo - insertionWeightAntiHolo, \[Epsilon]AntiHolo]};

AppendTo[result, {projectedOPEHolo, projectedOPEAntiHolo, prefac}];

result];


(* ::Subsubsection:: *)
(*Factorize multi-local operators*)


factorizeMultiOp[multiOp_/;MultiOptest[multiOp]]:=
Module[{multiOpXSplit, localOpFactorized, localOpHolo, localOpAntiHolo, localOpsHolo = {}, localOpsAntiHolo = {}, prefac = 1},
multiOpXSplit = multiOp/.{ProfileX[profile_, ders_, z_, zbar_]:> R[ProfileXHolo[profile, ders, z], ProfileXAntiHolo[profile, ders, zbar]], expX[k_, z_, zbar_]:> R[expXHolo[k, z], expXAntiHolo[k,zbar]]};
{localOpsHolo, localOpsAntiHolo} = 
Reap[Scan[Function[localOp,
localOpFactorized = splitR[localOp];
prefac = prefac * factorizationPrefac[localOp];
{localOpHolo, localOpAntiHolo} = {localOpFactorized[[1]], localOpFactorized[[2]]};
Sow[localOpHolo, "Holo"];
Sow[localOpAntiHolo, "AntiHolo"];
], List @@ multiOpXSplit]][[2]];
{MultiOp @@ localOpsHolo, MultiOp @@ localOpsAntiHolo, prefac}]


(* ::Subsubsection:: *)
(*Factorize normal-ordered product into holomorphic and antiholomorphic parts*)


splitR[Ra_ /; Rtest[Ra]] := Module[{RHolo = {}, RAntiHolo = {}, RList = List @@ Ra},
   RHolo = R @@ Select[RList, isHolomorphic @* Head];
   RAntiHolo = R @@ Select[RList, isAntiHolomorphic @* Head];
   {RHolo, RAntiHolo}
   ];
splitR[Times[a_, Ra_/;Rtest[Ra]]] := splitR[Ra]

splitRPrefac[Times[a_, Ra_/;Rtest[Ra]]] := a;

factorizationAuxList[Ra_/; Rtest[Ra]] := Module[{result= {}},
   result = Reap[Scan[Function[Relem,
     If[isHolomorphic[Relem] && isFermion[Relem],
      Sow[fHolo]];
     If[isHolomorphic[Relem] && isBoson[Relem],
      Sow[bHolo]];
     If[isAntiHolomorphic[Relem] && isFermion[Relem],
      Sow[fAntiHolo]];
     If[isAntiHolomorphic[Relem] && isBoson[Relem],
      Sow[bAntiHolo]];
     ], Ra]][[2]]; 
     result
   ];
 
factorizationPrefac[Ra_ /;Rtest[Ra]] :=
 Module[{list = factorizationAuxList[Ra], holPositions, antiHolPositions, swaps, totalSwaps, sign},
  holPositions = Flatten[Position[list, _fHolo]];
  antiHolPositions = Flatten[Position[list, _fAntiHolo]];
  swaps = Outer[Boole[#2 < #1] &, holPositions, antiHolPositions];
  totalSwaps = Total[swaps, 2];
  sign = (-1)^totalSwaps
  ]
factorizationAuxList[Times[a_, Ra_/;Rtest[Ra]]] := factorizationAuxList[Ra];
factorizationPrefac[Times[a_, Ra_/;Rtest[Ra]]] := a*factorizationPrefac[Ra]


(* ::Subsubsection::Closed:: *)
(*Rescale all chiral local operators [position is their last argument] inside a factorized MultiOp*)


rescaleMultiOp[multiOp_/;MultiOptest[multiOp], rescalingFactor_]:= Module[{multiOpList = List @@ multiOp}, 
MultiOp @@ Map[rescaleOp[rescalingFactor], multiOpList]]


rescaleOp[rescalingFactor_][op_]:= Module[{opList = List @@ op}, 
R @@ Map[rescalePositionBy[rescalingFactor], opList]]


rescalePositionBy[rescalingFactor_][op_]:= op/.{symbol_[args__, pos_]:> symbol[args, rescalingFactor pos]};


(* ::Subsubsection:: *)
(*Project OPE onto a given weight*)


projectHolo[OPE_, weight_, weightCountingParameter_]:= Module[{result = 0, power, expansionOrder, OPEexpanded = Expand[OPE], OPEterms},
OPEterms = If[Head[OPEexpanded] === Plus, List @@ OPEexpanded, {OPEexpanded}];
Scan[Function[OPEterm,
power = (Exponent[Together[OPEterm], weightCountingParameter])/.{\[Alpha]p :> 0};
expansionOrder = -power + weight;
If[expansionOrder >= 0,
result = result + TaylorAtOrderHolo[OPEterm, expansionOrder, 0]];
],
OPEterms];
result/.{weightCountingParameter -> 1}]


projectAntiHolo[OPE_, weight_, weightCountingParameter_]:= Module[{result = 0, power, expansionOrder, OPEexpanded = Expand[OPE], OPEterms},
OPEterms = If[Head[OPEexpanded] === Plus, List @@ OPEexpanded, {OPEexpanded}];
Scan[Function[OPEterm,
power = (Exponent[Together[OPEterm], weightCountingParameter])/.{\[Alpha]p :> 0};
expansionOrder = -power + weight;
If[expansionOrder >= 0,
result = result + TaylorAtOrderAntiHolo[OPEterm, expansionOrder, 0]];
],
OPEterms];
result/.{weightCountingParameter -> 1}]


(* ::Subsection::Closed:: *)
(*Define 2-bracket*)


Bracket[SFa_/; SFtest[SFa], SFb_/;SFtest[SFb]]:= Module[{z0, z0bar, powerHol, powerAntiHol, result = 0, tayloredOPEpart, 
SFaAtPos, SFbAtPos, localCoordinateReplacement}, 
{SFaAtPos, SFbAtPos, localCoordinateReplacement, z0, z0bar} = SFsWithLocalCoordinateData[SFa, SFb];
Scan[Function[OPEpart,
powerHol = Exponent[OPEpart, z0];
powerAntiHol = Exponent[OPEpart, z0bar];
If[RtestUpToConstant[OPEpart],
tayloredOPEpart = If[powerHol < 0, 
If[powerAntiHol < 0, TaylorAtOrder[OPEpart,-powerHol, -powerAntiHol,0,0], TaylorAtOrder[OPEpart/.{z0bar->0},-powerHol, 0,0,0]], 
If[powerAntiHol < 0, TaylorAtOrder[OPEpart/.{z0->0},0,-powerAntiHol,0,0], OPEpart/.{z0->0,z0bar->0}]]//Expand;
result = result + b0m[tayloredOPEpart];,
0];
],List @@(((OPE[SFaAtPos, SFbAtPos])/.localCoordinateReplacement)//Expand)]; result];


(* ::Subsubsection:: *)
(*Place evaluation point of normal orderings in expression*)


replacePointInR[expr_, replacement_]:=Module[{replacedExpr, RHold}, 
replacedExpr = expr/.{R -> RHold};
Replace[replacedExpr,RHold[arg__]:>R@@({arg}/.replacement),{0,Infinity}]]


(* ::Subsection::Closed:: *)
(*Determine whether OPE should be computed*)


singularity[dX[\[Mu]_,n_,z_],dX[\[Nu]_,m_,w_]]:= 2 + m + n;
singularity[dXt[\[Mu]_,n_,z_],dXt[\[Nu]_,m_,w_]]:=2 + m + n;

singularity[dX[\[Mu]_,n_,z_],expX[k_,w_,wbar_]]:= 1 + n;
singularity[expX[k_,w_,wbar_],dX[\[Mu]_,n_,z_]]:= 1 + n;
singularity[dXt[\[Mu]_,n_,z_],expX[k_,w_,wbar_]]:=1 + n;
singularity[expX[k_,w_,wbar_],dXt[\[Mu]_,n_,z_]]:=1 + n;
singularity[a_,b_]:= 0 /; (isField[Head[a]] && isField[Head[b]]);


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
