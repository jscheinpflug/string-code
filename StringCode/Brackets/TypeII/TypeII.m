(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Brackets`TypeII`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`TypeII`"];
Needs["StringCode`StringFields`"];
Needs["StringCode`StringFields`TypeII`"];
Needs["StringCode`Operators`"];
Needs["StringCode`Operators`TypeII`"];
Needs["StringCode`Taylor`"];
Needs["StringCode`Taylor`TypeII`"];
Needs["StringCode`Conventions`TypeII`"];
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
BRSTList = List @@ jBRST[z];
Scan[Function[BRSTelem,
compositeInBRSTPosition = containsCompositeHolo[BRSTelem/.{z->0}];
If[compositeInBRSTPosition !=  "NotFound",
singularityUpperBound = upperBoundSingularity[singularityMatrix[BRSTelem, Ra], compositeInBRSTPosition],
singularityUpperBound = upperBoundSingularity[singularityMatrix[BRSTelem, Ra], 0]];
If[singularityUpperBound >= 0,
If[RcontainsProfile[Ra],
OPEWithBRST = OPE[BRSTelem, Ra, 1]//Expand,
OPEWithBRST = OPE[BRSTelem, Ra]//Expand];
Scan[Function[Relem,
power = Exponent[Relem, z];
If[power == -1, result = result + Relem, 
If[power < -1, result = result + TaylorAtOrder[Relem, -power - 1, 0, 0, 0]]];
], If[Head[OPEWithBRST] === Plus, List @@ OPEWithBRST, {OPEWithBRST}]];
];], BRSTList];
(z result // Expand)/.{z->0}];

actBRSTAntiHolo[SFa_/; SFtest[SFa]] := Module[{result = 0, zBar, Ra = SFAtPos[SFa, 0,0], OPEWithBRST, power, BRSTList, singularityUpperBound, compositeInBRSTPosition},
BRSTList = List @@ jBRSTbar[zBar];
Scan[Function[BRSTelem,
compositeInBRSTPosition = containsCompositeAntiHolo[BRSTelem/.{zBar->0}];
If[compositeInBRSTPosition !=  "NotFound",
singularityUpperBound = upperBoundSingularity[singularityMatrix[BRSTelem, Ra], compositeInBRSTPosition],
singularityUpperBound = upperBoundSingularity[singularityMatrix[BRSTelem, Ra], 0]];
If[singularityUpperBound >= 0,
If[RcontainsProfile[Ra],
OPEWithBRST = OPE[BRSTelem, Ra, 1]//Expand,
OPEWithBRST = OPE[BRSTelem, Ra]//Expand];
Scan[Function[Relem,
power = Exponent[Relem, zBar];
If[power == -1, result = result + Relem, 
If[power < -1, result = result + TaylorAtOrder[Relem, 0, -power-1, 0, 0]]];
], If[Head[OPEWithBRST] === Plus, List @@ OPEWithBRST, {OPEWithBRST}]];
];], BRSTList];
(zBar result // Expand)/.{zBar->0}];


(* ::Subsection::Closed:: *)
(*Define string bracket*)


Bracket[toBracket__/;AllTrue[{toBracket}, SFtest]]:= Module[{result = 0, SFsAtPos, localCoordinateFunctionsHol, localCoordinateFunctionsAntiHol, localCoordinateReplacement, 
moduli, bracketOrder, bracketList = {toBracket}, w, wbar, curlyBs, minCGhostModdings, minCbarGhostModdings, SFList, afterApplyingBghosts, numberOfHoloPCOs, numberOfAntiHoloPCOs,
afterHeldActionOfPCOs},
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

(*apply PCO zero-modes abstractly*)
numberOfHoloPCOs = Ceiling[Abs[Total[Map[totalHolPicture, SFList]]]-1];
numberOfAntiHoloPCOs = Ceiling[Abs[Total[Map[totalAntiHolPicture, SFList]]]-1];
afterHeldActionOfPCOs = Nest[actPCObar0Hold, Nest[actPCO0Hold, afterApplyingBghosts, numberOfHoloPCOs], numberOfAntiHoloPCOs];

result = {afterHeldActionOfPCOs, localCoordinateReplacement};
result]


(* ::Subsubsection:: *)
(*Apply B-ghost insertions to a MultiOp*)


applyCurlyBs[SFsAtPos_/;MultiOptest[SFsAtPos], curlyBs__]:= Module[{result = 0, intermediateResult = SFsAtPos, i, curlyBOnPosition},
Scan[Function[curlyB,
Do[
 curlyBOnPosition = curlyB[[i]];
 result = result + replaceInMultiOpAtPosition[intermediateResult, i, applyBghostModes[curlyBOnPosition]],
 {i,1,Length[curlyB]}];
 intermediateResult = result;],
 curlyBs];
result
];


replaceInMultiOpAtPosition[multiOp_/;MultiOptest[multiOp], position_, toApply_]:= Module[{multiOpList = List @@ multiOp},
MultiOp @@ ReplacePart[multiOpList, position -> toApply[multiOpList[[position]]]]];


replaceInMultiOpAtPosition[a_+b_, position_, toReplace_]:= replaceInMultiOpAtPosition[a,position,toReplace] + replaceInMultiOpAtPosition[b, position, toReplace];
replaceInMultiOpAtPosition[a_ b_, position_, toReplace_]:= a replaceInMultiOpAtPosition[b, position, toReplace]/;(Head[b] == MultiOp)


applyBghostModes[BghostModes__][Ra_/;RtestUpToConstant[Ra]] := Module[{result = 0},
Scan[Function[BghostMode,
result = result + (BghostMode/.{bmodeHolo[a_]:> bmodeHolo[a][Ra], bmodeAntiHolo[a_]:> bmodeAntiHolo[a][Ra]});
], BghostModes];
result]
applyBghostModes[BghostModes__][a_] := 0;


(* ::Subsubsection::Closed:: *)
(*Create B-ghost insertions*)


createCurlyBs[SFList__, localCoordinateFunctionsHol__, localCoordinateFunctionsAntiHol__, moduli__, bracketOrder_, w_, wbar_]:= 
Module[{i,j, minCGhostModdings,minCbarGhostModdings},
minCGhostModdings = Map[getMinCGhostModding, SFList];
minCbarGhostModdings = Map[getMinCbarGhostModding, SFList];
Table[
createB[localCoordinateFunctionsHol[[j]], localCoordinateFunctionsAntiHol[[j]], w, wbar, moduli[[i]], minCGhostModdings[[j]], minCbarGhostModdings[[j]]],
{i,1,Length[moduli]}, {j,1,bracketOrder}]
]


getMinCGhostModding[Ra_/; Rtest[Ra]]:= Module[{RList = List @@ Ra, maxOrder = "None", currentOrder},
Scan[Function[Relem,
If[Head[Relem] == c,
currentOrder = Relem/.{c[der_, z_]:> 1 - der};
If[maxOrder == "None" || currentOrder < maxOrder, maxOrder = currentOrder]
]
], RList];
maxOrder
]


getMinCbarGhostModding[Ra_/; Rtest[Ra]]:= Module[{RList = List @@ Ra, maxOrder = "None", currentOrder},
Scan[Function[Relem,
If[Head[Relem] == ct,
currentOrder = Relem/.{ct[der_, z_]:> 1 - der};
If[maxOrder == "None" || currentOrder < maxOrder, maxOrder = currentOrder]
]
], RList];
maxOrder
]


getInverseSeriesAtOrder[toInvert_, coord_, inversionCoord_, order_]:= 
(InverseSeries[Series[toInvert,{coord,0,order}]]//Normal)/.{coord->inversionCoord};


createB[localCoordinateHol_, localCoordinateAntiHol_, w_, wbar_, modulus_, minCGhostModding_, minCbarGhostModding_]:= 
Module[{result, expandedBGhostIntegrandHol,expandedBGhostIntegrandAntiHol, BGhostIntegrandListHol,BGhostIntegrandListAntiHol, wInTermsOfZ, wbarInTermsOfZbar, 
z, zbar, z0 = localCoordinateHol/.{w->0}, z0bar = localCoordinateAntiHol/.{wbar->0}, maxOrderHolo, maxOrderAntiHolo},
If[minCGhostModding != "None",
maxOrderHolo = -minCGhostModding + 1;
If[maxOrderHolo > 0,
wInTermsOfZ = getInverseSeriesAtOrder[localCoordinateHol, w,z, maxOrderHolo];
expandedBGhostIntegrandHol = Series[(D[localCoordinateHol, modulus])/.{w->wInTermsOfZ}, {z,z0,maxOrderHolo}]//Normal;
BGhostIntegrandListHol = (#/.{Times[rest___,(z-z0)^p_?NumericQ]:>bmodeHolo[p-1]*rest,Times[rest___,diff_/;diff===(z-z0)]:>bmodeHolo[0]*rest,Times[rest___,1]:>bmodeHolo[-1]*rest}) & /@ (List@@(expandedBGhostIntegrandHol)),
BGhostIntegrandListHol = {D[localCoordinateHol/.{w->0}, modulus] bmodeHolo[-1]};
],
BGhostIntegrandListHol = {};
];
If[minCbarGhostModding != "None",
maxOrderAntiHolo = -minCbarGhostModding + 1;
If[maxOrderAntiHolo > 0,
wbarInTermsOfZbar = getInverseSeriesAtOrder[localCoordinateAntiHol, wbar, zbar, maxOrderAntiHolo];
expandedBGhostIntegrandAntiHol = Series[(D[localCoordinateAntiHol, modulus])/.{wbar->wbarInTermsOfZbar}, {zbar,z0bar,maxOrderAntiHolo}]//Normal;
BGhostIntegrandListAntiHol =(#/.{Times[rest___,(zbar-z0bar)^p_?NumericQ]:>bmodeAntiHolo[p-1]*rest,Times[rest___,diff_/;diff===(zbar-z0bar)]:>bmodeAntiHolo[0]*rest,Times[rest___,1]:>bmodeBar[-1]*rest})& /@ (List@@(expandedBGhostIntegrandAntiHol)),
BGhostIntegrandListAntiHol = {D[localCoordinateAntiHol/.{wbar->0}, modulus]bmodeAntiHolo[-1]};
],
BGhostIntegrandListAntiHol = {};
];
result = Join[BGhostIntegrandListHol,BGhostIntegrandListAntiHol];
result]


(* ::Subsubsection::Closed:: *)
(*Place string fields at positions given by local coordinates*)


placeSFAtPosGivenLocalCoordinates[localCoordinateFunctionsHol__, localCoordinateFunctionsAntiHol__, SFs__, w_, wbar_]:= 
Module[{i, length = Length[SFs]},
MultiOp @@ Table[SFAtPos[SFs[[i]], localCoordinateFunctionsHol[[i]]/.{w->0}, localCoordinateFunctionsAntiHol[[i]]/.{wbar->0}],{i,1,length}]
]


(* ::Subsubsection:: *)
(*Define total picture number*)


totalHolPicture[Ra_/;Rtest[Ra]]:= Map[pictureHol, List @@ Ra]//Total;
totalAntiHolPicture[Ra_/;Rtest[Ra]]:= Map[pictureAntiHol, List @@ Ra]//Total;


(* ::Subsection:: *)
(*Define projection of the string bracket*)


BracketProjection[{bracket_, localCoordinateReplacement_}, weightHolo_, weightAntiHolo_]:= 
Module[{result = {}, numberOfHoloPCOs = 0, numberOfAntiHoloPCOs = 0, bracketNoPCOs, prefac, bracketHolo, bracketAntiHolo, OPEHolo, OPEAntiHolo,
\[Epsilon]Holo, \[Epsilon]AntiHolo,  projectedOPEHolo, projectedOPEAntiHolo,  holoOPEWithPCOs, antiHoloOPEWithPCOs},

(*Strip off PCOs*)
bracketNoPCOs = bracket//.{actPCO0Hold[x_]:> (numberOfHoloPCOs ++; x), actPCObar0Hold[x_]:> (numberOfAntiHoloPCOs ++; x)};

(*Compute bracket for each term inside of nested PCOs*)
Scan[Function[bracketNoPCOsTerm,

(*Split the multi-local result of the bracket into holomorphic/antiholomorphic parts*)
{bracketHolo, bracketAntiHolo, prefac} = factorizeMultiOp[bracketNoPCOsTerm];

(*Rescale positions of operators in the bracket by a common \[Epsilon]Holo/\[Epsilon]AntiHolo to ease weight projection, and then perform OPE*)
{OPEHolo, OPEAntiHolo} = {OPE @@ rescaleMultiOp[bracketHolo, \[Epsilon]Holo], OPE @@ rescaleMultiOp[bracketAntiHolo, \[Epsilon]AntiHolo]};

(*Perform the level projection on each holomorphic/antiholomorphic sector separately*)
{projectedOPEHolo, projectedOPEAntiHolo} = {projectHolo[OPEHolo, weightHolo, \[Epsilon]Holo], projectAntiHolo[OPEAntiHolo, weightAntiHolo, \[Epsilon]AntiHolo]};

(*Act with PCOs on each projected holomorphic/antiholomorphic sector separately*)
{holoOPEWithPCOs, antiHoloOPEWithPCOs} = {Nest[actPCOHolo, projectedOPEHolo, numberOfHoloPCOs], Nest[actPCOAntiHolo, projectedOPEAntiHolo, numberOfAntiHoloPCOs]};

AppendTo[result,{holoOPEWithPCOs, antiHoloOPEWithPCOs, prefac}];

], If[Head[bracketNoPCOs] === Plus, bracketNoPCOs/.{Plus->List}, {bracketNoPCOs}]];

result];


(* ::Subsubsection:: *)
(*Factorize multi-local operators*)


factorizeMultiOp[multiOp_/;MultiOptest[multiOp]]:=
Module[{multiOpXSplit, localOpFactorized, localOpHolo, localOpAntiHolo, localOpsHolo = {}, localOpsAntiHolo = {}, prefac = 1},
multiOpXSplit = multiOp/.{ProfileX[profile_, ders_, z_, zbar_]:> R[ProfileXHolo[profile, ders, z], ProfileXAntiHolo[profile, ders, zbar]], expX[k_, z_, zbar_]:> R[expXHolo[k, z], expXAntiHolo[k,zbar]]};
Scan[Function[localOp,
localOpFactorized = splitR[localOp];
prefac = prefac * factorizationPrefac[localOp];
{localOpHolo, localOpAntiHolo} = {localOpFactorized[[1]], localOpFactorized[[2]]};
AppendTo[localOpsHolo, localOpHolo];
AppendTo[localOpsAntiHolo, localOpAntiHolo];
], List @@ multiOpXSplit];
{MultiOp @@ localOpsHolo, MultiOp @@ localOpsAntiHolo, prefac}]


(* ::Subsubsection::Closed:: *)
(*Factorize normal-ordered product into holomorphic and antiholomorphic parts*)


splitR[Ra_ /; Rtest[Ra]] := Module[{RHolo = {}, RAntiHolo = {}, RList = List @@ Ra},
   RHolo = R @@ Select[RList, isHolomorphic @* Head];
   RAntiHolo = R @@ Select[RList, isAntiHolomorphic @* Head];
   {RHolo, RAntiHolo}
   ];
splitR[Times[a_, Ra_/;Rtest[Ra]]] := splitR[Ra]

splitRPrefac[Times[a_, Ra_/;Rtest[Ra]]] := a;

factorizationAuxList[Ra_/; Rtest[Ra]] := Module[{list = {}},
   Scan[Function[Relem,
     If[isHolomorphic[Relem] && isFermion[Relem],
      AppendTo[list, fHolo]];
     If[isHolomorphic[Relem] && isBoson[Relem],
      AppendTo[list, bHolo]];
     If[isAntiHolomorphic[Relem] && isFermion[Relem],
      AppendTo[list, fAntiHolo]];
     If[isAntiHolomorphic[Relem] && isBoson[Relem],
      AppendTo[list, bAntiHolo]];
     ], Ra]; list
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


projectHolo[OPE_, weight_, weightCountingParameter_]:= Module[{result = 0, power, OPEterms = If[Head[OPE] === Plus, OPE/.{Plus->List}, {OPE}]},
Scan[Function[OPEterm,
power = (Exponent[OPEterm, weightCountingParameter])/.{\[Alpha]p :> 0};
result = result + TaylorAtOrderHolo[OPEterm, -power, 0];
],
OPEterms];
result/.{weightCountingParameter -> 1}]


projectAntiHolo[OPE_, weight_, weightCountingParameter_]:= Module[{result = 0, power,  OPEterms = If[Head[OPE] === Plus, OPE/.{Plus->List}, {OPE}]},
Scan[Function[OPEterm,
power = (Exponent[OPEterm, weightCountingParameter])/.{\[Alpha]p :> 0};
result = result + TaylorAtOrderAntiHolo[OPEterm, -power, 0];
],
OPEterms];
result/.{weightCountingParameter -> 1}]


(* ::Subsection::Closed:: *)
(*Define 2-bracket*)


Bracket[SFa_/; SFtest[SFa], SFb_/;SFtest[SFb]]:= 
Module[{z0, z0bar, powerHol, powerAntiHol, result = 0, tayloredHoloOPEPart, tayloredAntiHoloOPEPart, holoOPEPart, antiHoloOPEPart, 
SFaAtPos, SFbAtPos, OPEOfSF, prefac, localCoordinateReplacement, pictureAdjustedTaylor, holoSplit, antiHoloSplit}, 
{SFaAtPos, SFbAtPos, localCoordinateReplacement, z0, z0bar} = SFsWithLocalCoordinateData[SFa, SFb];
OPEOfSF = OPE[SFaAtPos, SFbAtPos]/.localCoordinateReplacement;
Scan[Function[OPEpart,
powerHol = Exponent[OPEpart, z0];
powerAntiHol = Exponent[OPEpart, z0bar];
If[RtestUpToConstant[OPEpart],
{holoSplit, antiHoloSplit} = splitR[OPEpart];
holoOPEPart = R @@ holoSplit;
antiHoloOPEPart = R @@ antiHoloSplit;
prefac = factorizationSign[OPEpart];
tayloredHoloOPEPart =
If[powerHol < 0, TaylorAtOrderHolo[holoOPEPart,-powerHol,0],  replacePointInR[holoOPEPart, {z0->0}]];
tayloredAntiHoloOPEPart =
If[powerAntiHol < 0, TaylorAtOrderAntiHolo[antiHoloOPEPart,-powerAntiHol,0],  replacePointInR[antiHoloOPEPart, {z0bar->0}]];
pictureAdjustedTaylor = R[pictureAdjustHolo[tayloredHoloOPEPart], pictureAdjustAntiHolo[tayloredAntiHoloOPEPart]];
result = result + prefac cleanDoubledProfilesAtZero[pictureAdjustedTaylor, createProfileAssociation[OPEpart]];
];
],List@@(b0m[OPEOfSF]//Expand)]; 
result
];


(* ::Subsubsection::Closed:: *)
(*Place evaluation point of normal orderings in expression*)


replacePointInR[expr_, replacement_]:=Module[{replacedExpr, RHold}, 
replacedExpr = expr/.{R -> RHold};
Replace[replacedExpr,RHold[arg__]:>R@@({arg}/.replacement),{0,Infinity}]]


(* ::Subsection:: *)
(*Define action of PCOs*)


actPCOHolo[Ra_/;Rtest[Ra]] := actPCOHolo[Ra] =
 Module[{result = 0, z, OPEWithPCO, power, PCOList, singularityUpperBound, compositeInPCOPosition},
PCOList = List @@ PCO[z];
Scan[Function[PCOelem,
compositeInPCOPosition = containsCompositeHolo[PCOelem/.{z->0}];
If[compositeInPCOPosition !=  "NotFound",
singularityUpperBound = upperBoundSingularity[singularityMatrix[PCOelem, Ra], compositeInPCOPosition],
singularityUpperBound = upperBoundSingularity[singularityMatrix[PCOelem, Ra], 0]];
If[singularityUpperBound >= 0,
OPEWithPCO = OPE[PCOelem, Ra]//Expand;
Scan[Function[Relem,
power = Exponent[Relem, z];
If[power == 0, result = result + Relem, 
If[power < 0, result = result + TaylorAtOrderHolo[Relem, -power, 0]]];
], If[Head[OPEWithPCO] === Plus, List @@ OPEWithPCO, {OPEWithPCO}]];
];], PCOList];
((result // Expand) /.{z->0})];

actPCOAntiHolo[Ra_/;Rtest[Ra]] := actPCOAntiHolo[Ra] =
Module[{result = 0, zBar, OPEWithPCO, power, PCOList, singularityUpperBound, compositeInPCOPosition},
PCOList = List @@ PCObar[zBar];
Scan[Function[PCOelem,
compositeInPCOPosition = containsCompositeAntiHolo[PCOelem/.{zBar->0}];
If[compositeInPCOPosition !=  "NotFound",
singularityUpperBound = upperBoundSingularity[singularityMatrix[PCOelem, Ra], compositeInPCOPosition],
singularityUpperBound = upperBoundSingularity[singularityMatrix[PCOelem, Ra], 0]];
If[singularityUpperBound >= 0,
OPEWithPCO = OPE[PCOelem, Ra]//Expand;
Scan[Function[Relem,
power = Exponent[Relem, zBar];
If[power == 0, result = result + Relem, 
If[power < 0, result = result + TaylorAtOrderAntiHolo[Relem, -power, 0]]];
], If[Head[OPEWithPCO] === Plus, List @@ OPEWithPCO, {OPEWithPCO}]];
];], PCOList];
((result // Expand)/.{zBar->0})];


actPCOAntiHolo[a_+b_]:=actPCOAntiHolo[a] + actPCOAntiHolo[b];
actPCOAntiHolo[a_ b_]:=a actPCOAntiHolo[b]/;(And @@(FreeQ[a,#]&/@ allfields))
actPCOAntiHolo[0] := 0;
actPCOHolo[a_+b_]:=actPCOHolo[a] + actPCOHolo[b];
actPCOHolo[a_ b_]:=a actPCOHolo[b]/;(And @@(FreeQ[a,#]&/@ allfields))
actPCOHolo[0] := 0;


(* ::Subsection::Closed:: *)
(*Determine whether OPE should be computed*)


containsCompositeHolo[PCOelem_]:= containsCompositeHolo[PCOelem] = First@FirstPosition[PCOelem/.{R->List}, _?(MatchQ[Head[#], exp\[Phi]b | exp\[Phi]f] &)];
containsCompositeAntiHolo[PCOelem_]:= containsCompositeAntiHolo[PCOelem] = First@FirstPosition[PCOelem/.{R->List}, _?(MatchQ[Head[#], exp\[Phi]tb | exp\[Phi]tf] &)];


(* ::Subsubsection:: *)
(*Free boson*)


singularity[dX[\[Mu]_,n_,z_],dX[\[Nu]_,m_,w_]]:= 2 + m + n;
singularity[dXt[\[Mu]_,n_,z_],dXt[\[Nu]_,m_,w_]]:=2 + m + n;

singularity[dX[\[Mu]_,n_,z_],expX[k_,w_,wbar_]]:= 1 + n;
singularity[expX[k_,w_,wbar_],dX[\[Mu]_,n_,z_]]:= 1 + n;
singularity[dXt[\[Mu]_,n_,z_],expX[k_,w_,wbar_]]:=1 + n;
singularity[expX[k_,w_,wbar_],dXt[\[Mu]_,n_,z_]]:=1 + n;
singularity[dX[\[Mu]_,n_,z_],ProfileX[profile_,ders_, w_,wbar_]]:= 1 + n;
singularity[ProfileX[profile_,ders_, w_,wbar_],dX[\[Mu]_,n_,z_]]:= 1 + n;
singularity[dXt[\[Mu]_,n_,z_],ProfileX[profile_,ders_, w_,wbar_]]:=1 + n;
singularity[ProfileX[profile_,ders_, w_,wbar_],dXt[\[Mu]_,n_,z_]]:=1 + n;

singularity[dX[\[Mu]_,n_,z_],expXHolo[k_,w_]]:= 1 + n;
singularity[expXHolo[k_,w_],dX[\[Mu]_,n_,z_]]:= 1 + n;
singularity[dX[\[Mu]_,n_,z_],ProfileXHolo[profile_, ders_, w_]]:= 1 + n;
singularity[ProfileXHolo[profile_,ders_, w_],dX[\[Mu]_,n_,z_]]:= 1 + n;

singularity[dXt[\[Mu]_,n_,z_],expXAntiHolo[k_,wbar_]]:=1 + n;
singularity[expXAntiHolo[k_,wbar_],dXt[\[Mu]_,n_,z_]]:=1 + n;
singularity[dXt[\[Mu]_,n_,z_],ProfileXAntiHolo[profile_, ders_, wbar_]]:=1 + n;
singularity[ProfileXAntiHolo[profile_, ders_, wbar_],dXt[\[Mu]_,n_,z_]]:=1 + n;


(* ::Subsubsection::Closed:: *)
(*Free fermion*)


singularity[\[Psi][\[Mu]_,n_,z_],\[Psi][\[Nu]_,m_,w_]]:=1 + m + n;
singularity[\[Psi]t[\[Mu]_,n_,z_],\[Psi]t[\[Nu]_,m_,w_]]:=1 + m + n;


(* ::Subsubsection::Closed:: *)
(*Superghosts*)


singularity[d\[Phi][n_,z_],d\[Phi][m_,w_]]:= 2 + m + n;
singularity[d\[Phi]t[n_,z_],d\[Phi]t[m_,w_]]:= 2 + m + n;
singularity[\[Eta][n_,z_],\[Xi][m_,w_]]:= 1 + m + n;
singularity[\[Xi][m_,w_],\[Eta][n_,z_]]:= 1 + m + n;
singularity[\[Eta]t[n_,z_],\[Xi]t[m_,w_]]:= 1 + m + n;
singularity[\[Xi]t[m_,w_],\[Eta]t[n_,z_]]:=1 + m + n;

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
singularity[a_,b_]:= 0 /; (isField[Head[a]] && isField[Head[b]]);


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
