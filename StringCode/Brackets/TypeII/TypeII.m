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


(* ::Subsection:: *)
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
moduli, bracketOrder, bracketList = {toBracket}, w, wbar, curlyBs, minCGhostModdings, minCbarGhostModdings, SFList, afterApplyingBghosts, numberOfHolPCOs, numberOfAntiHolPCOs,
afterHeldActionOfPCOs},
bracketOrder = Length[bracketList];

(*conformally transform the string field insertions*)
{localCoordinateFunctionsHol, localCoordinateFunctionsAntiHol, w, wbar, moduli, localCoordinateReplacement} = getLocalCoordinateData[bracketOrder];
SFsAtPos = placeSFAtPosGivenLocalCoordinates[localCoordinateFunctionsHol, localCoordinateFunctionsAntiHol, bracketList, w, wbar];
SFList = List @@ SFsAtPos;

(*create and apply the curly B-ghost insertions, one B-ghost action on the insertions for each modulus*)
curlyBs = createCurlyBs[SFList, localCoordinateFunctionsHol, localCoordinateFunctionsAntiHol, moduli, bracketOrder, w, wbar];
afterApplyingBghosts = applyCurlyBs[SFsAtPos, curlyBs];

(*apply PCO zero-modes abstractly*)
numberOfHolPCOs = Ceiling[Abs[Total[Map[totalHolPicture, SFList]]]-1];
numberOfAntiHolPCOs = Ceiling[Abs[Total[Map[totalAntiHolPicture, SFList]]]-1];
afterHeldActionOfPCOs = 
Timing[Nest[appendPCObar0Hold, Nest[appendPCO0Hold, afterApplyingBghosts, numberOfHolPCOs], numberOfAntiHolPCOs]];

result = afterHeldActionOfPCOs;
result]


(* ::Subsubsection::Closed:: *)
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


(* ::Subsection:: *)
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


actPCOHolo[Ra_/;Rtest[Ra], \[Alpha]pOrder___] := actPCOHolo[Ra, \[Alpha]pOrder] =
 Module[{result = 0, z, OPEWithPCO, power, PCOList, singularityUpperBound, compositeInPCOPosition},
PCOList = List @@ PCO[z];
Scan[Function[PCOelem,
compositeInPCOPosition = containsCompositeHolo[PCOelem/.{z->0}];
If[compositeInPCOPosition !=  "NotFound",
singularityUpperBound = upperBoundSingularity[singularityMatrix[PCOelem, Ra], compositeInPCOPosition],
singularityUpperBound = upperBoundSingularity[singularityMatrix[PCOelem, Ra], 0]];
If[singularityUpperBound >= 0,
OPEWithPCO = OPE[PCOelem, Ra, \[Alpha]pOrder]//Expand;
Scan[Function[Relem,
power = Exponent[Relem, z];
If[power == 0, result = result + Relem, 
If[power < 0, result = result + TaylorAtOrder[Relem, -power, 0, 0, 0]]];
], If[Head[OPEWithPCO] === Plus, List @@ OPEWithPCO, {OPEWithPCO}]];
];], PCOList];
((result // Expand) /.{z->0})];

actPCOAntiHolo[Ra_/;Rtest[Ra], \[Alpha]pOrder___] := actPCOAntiHolo[Ra, \[Alpha]pOrder] =
Module[{result = 0, zBar, OPEWithPCO, power, PCOList, singularityUpperBound, compositeInPCOPosition},
PCOList = List @@ PCObar[zBar];
Scan[Function[PCOelem,
compositeInPCOPosition = containsCompositeAntiHolo[PCOelem/.{zBar->0}];
If[compositeInPCOPosition !=  "NotFound",
singularityUpperBound = upperBoundSingularity[singularityMatrix[PCOelem, Ra], compositeInPCOPosition],
singularityUpperBound = upperBoundSingularity[singularityMatrix[PCOelem, Ra], 0]];
If[singularityUpperBound >= 0,
OPEWithPCO = OPE[PCOelem, Ra, \[Alpha]pOrder]//Expand;
Scan[Function[Relem,
power = Exponent[Relem, zBar];
If[power == 0, result = result + Relem, 
If[power < 0, result = result + TaylorAtOrder[Relem, 0, -power, 0, 0]]];
], If[Head[OPEWithPCO] === Plus, List @@ OPEWithPCO, {OPEWithPCO}]];
];], PCOList];
((result // Expand)/.{zBar->0})];

totalHolPicture[Ra_/;Rtest[Ra]]:= Map[pictureHol, List @@ Ra]//Total;
totalAntiHolPicture[Ra_/;Rtest[Ra]]:= Map[pictureAntiHol, List @@ Ra]//Total;

pictureAdjustHolo[Ra_/;Rtest[Ra], \[Alpha]pOrder___] := Module[{pictureHol = totalHolPicture[Ra],  holoAdjusted},
   holoAdjusted =
   If[pictureHol < 0, Nest[actPCOHolo[#, \[Alpha]pOrder] &, Ra, Ceiling[Abs[pictureHol]] - 1], Ra];
   holoAdjusted
   ];
   
pictureAdjustAntiHolo[Ra_/;Rtest[Ra], \[Alpha]pOrder___] := Module[{pictureAntiHol = totalAntiHolPicture[Ra],  antiHoloAdjusted},
   antiHoloAdjusted =
   If[pictureAntiHol < 0, Nest[actPCOAntiHolo[#, \[Alpha]pOrder] &, Ra, Ceiling[Abs[pictureAntiHol]] - 1], Ra];
   antiHoloAdjusted
   ];


actPCOAntiHolo[a_+b_, \[Alpha]pOrder___]:=actPCOAntiHolo[a, \[Alpha]pOrder] + actPCOAntiHolo[b, \[Alpha]pOrder];
actPCOAntiHolo[a_ b_, \[Alpha]pOrder___]:=a actPCOAntiHolo[b, \[Alpha]pOrder]/;(And @@(FreeQ[a,#]&/@ allfields))
actPCOAntiHolo[0, \[Alpha]pOrder___] := 0;
actPCOHolo[a_+b_, \[Alpha]pOrder___]:=actPCOHolo[a, \[Alpha]pOrder] + actPCOHolo[b, \[Alpha]pOrder];
actPCOHolo[a_ b_, \[Alpha]pOrder___]:=a actPCOHolo[b, \[Alpha]pOrder]/;(And @@(FreeQ[a,#]&/@ allfields))
actPCOHolo[0, \[Alpha]pOrder___] := 0;
pictureAdjustHolo[a_+b_, \[Alpha]pOrder___]:=pictureAdjustHolo[a, \[Alpha]pOrder] + pictureAdjustHolo[b, \[Alpha]pOrder];
pictureAdjustHolo[a_ b_, \[Alpha]pOrder___]:=a pictureAdjustHolo[b, \[Alpha]pOrder]/;(And @@(FreeQ[a,#]&/@ allfields))
pictureAdjustHolo[0, \[Alpha]pOrder___] := 0;
pictureAdjustAntiHolo[a_+b_, \[Alpha]pOrder___]:=pictureAdjustAntiHolo[a, \[Alpha]pOrder] + pictureAdjustAntiHolo[b, \[Alpha]pOrder];
pictureAdjustAntiHolo[a_ b_, \[Alpha]pOrder___]:=a pictureAdjustAntiHolo[b, \[Alpha]pOrder]/;(And @@(FreeQ[a,#]&/@ allfields))
pictureAdjustAntiHolo[0, \[Alpha]pOrder___] := 0;


(* ::Subsubsection::Closed:: *)
(*Factorize normal-ordered product into holomorphic and antiholomorphic parts*)


splitR[Ra_ /; Rtest[Ra]] := Module[{RHolo = {}, RAntiHolo = {}, RList = List @@ Ra},
   RHolo = Select[RList, isHolomorphic @* Head];
   RAntiHolo = Select[RList, isAntiHolomorphic @* Head];
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
 
factorizationSign[Ra_ /;Rtest[Ra]] :=
 Module[{list = factorizationAuxList[Ra], holPositions, antiHolPositions, swaps, totalSwaps, sign},
  holPositions = Flatten[Position[list, _fHolo]];
  antiHolPositions = Flatten[Position[list, _fAntiHolo]];
  swaps = Outer[Boole[#2 < #1] &, holPositions, antiHolPositions];
  totalSwaps = Total[swaps, 2];
  sign = (-1)^totalSwaps
  ]
factorizationAuxList[Times[a_, Ra_/;Rtest[Ra]]] := factorizationAuxList[Ra];
factorizationSign[Times[a_, Ra_/;Rtest[Ra]]] := a*factorizationSign[Ra]


(* ::Subsubsection::Closed:: *)
(*Clean repeated Profiles*)


createProfileAssociation[Ra_/;Rtest[Ra]]:= Module[{profileList = Cases[Ra, _ProfileX], profileName, ders, z, zbar, currentDers, result = Association[]},
profileList = Cases[Ra, _ProfileX];
   Scan[Function[profile, 
   {profileName, ders, z, zbar} = List @@ profile;
   currentDers = Lookup[result,profileName, {}];
   AssociateTo[result, profileName -> Join[currentDers,ders]];
   ], profileList];
   result];

createProfileAssociation[Times[a_, Ra_/;Rtest[Ra]]] := createProfileAssociation[Ra];

mergeAssociationsKeepOverlapsOnlyFromFirst[a1_, a2_] := Module[{key, allKeys = Union[Keys[a1], Keys[a2]]},
  Association[
  Table[
      With[{list1 = Lookup[a1, key, {}], list2 = Lookup[a2, key, {}]},
        key -> DeleteDuplicates[Join[list1, Complement[list2, list1]]]
      ],
      {key, allKeys}
    ]
  ]
];

cleanDoubledProfilesAtZero[Ra_/;Rtest[Ra], initialProfileAssociation_] :=
  Module[{profileList, rest, profileAssociation = Association[], profileName, currentDers, ders, z,zbar, mergedList, result},
   rest = Cases[Ra, Except[_ProfileX]];
   profileAssociation = mergeAssociationsKeepOverlapsOnlyFromFirst[initialProfileAssociation, createProfileAssociation[Ra]];
   mergedList = Join[rest, KeyValueMap[Function[{profile, ders}, ProfileX[profile, ders, 0, 0]], profileAssociation]];
   result = R @@ mergedList];
  
cleanDoubledProfilesAtZero[Ra_ + Rb_, initialProfileAssociation_] := cleanDoubledProfilesAtZero[Ra, initialProfileAssociation] + cleanDoubledProfilesAtZero[Rb, initialProfileAssociation];
cleanDoubledProfilesAtZero[Times[a_, Ra_], initialProfileAssociation_] := a cleanDoubledProfilesAtZero[Ra, initialProfileAssociation] /; (And @@ (FreeQ[a, #] & /@ allfields));
cleanDoubledProfilesAtZero[0, initialProfileAssociation_] := 0;


(* ::Subsection::Closed:: *)
(*Determine whether OPE should be computed*)


containsCompositeHolo[PCOelem_]:= containsCompositeHolo[PCOelem] = First@FirstPosition[PCOelem/.{R->List}, _?(MatchQ[Head[#], exp\[Phi]b | exp\[Phi]f] &)];
containsCompositeAntiHolo[PCOelem_]:= containsCompositeAntiHolo[PCOelem] = First@FirstPosition[PCOelem/.{R->List}, _?(MatchQ[Head[#], exp\[Phi]tb | exp\[Phi]tf] &)];

singularity[dX[\[Mu]_,n_,z_],dX[\[Nu]_,m_,w_]]:= 2 + m + n;
singularity[dXt[\[Mu]_,n_,z_],dXt[\[Nu]_,m_,w_]]:=2 + m + n;
singularity[d\[Phi][n_,z_],d\[Phi][m_,w_]]:= 2 + m + n;
singularity[d\[Phi]t[n_,z_],d\[Phi]t[m_,w_]]:= 2 + m + n;
singularity[\[Eta][n_,z_],\[Xi][m_,w_]]:= 1 + m + n;
singularity[\[Xi][m_,w_],\[Eta][n_,z_]]:= 1 + m + n;
singularity[\[Eta]t[n_,z_],\[Xi]t[m_,w_]]:= 1 + m + n;
singularity[\[Xi]t[m_,w_],\[Eta]t[n_,z_]]:=1 + m + n;
singularity[\[Psi][\[Mu]_,n_,z_],\[Psi][\[Nu]_,m_,w_]]:=1 + m + n;
singularity[\[Psi]t[\[Mu]_,n_,z_],\[Psi]t[\[Nu]_,m_,w_]]:=1 + m + n;

singularity[dX[\[Mu]_,n_,z_],expX[k_,w_,wbar_]]:= 1 + n;
singularity[expX[k_,w_,wbar_],dX[\[Mu]_,n_,z_]]:= 1 + n;
singularity[dXt[\[Mu]_,n_,z_],expX[k_,w_,wbar_]]:=1 + n;
singularity[expX[k_,w_,wbar_],dXt[\[Mu]_,n_,z_]]:=1 + n;

singularity[dX[\[Mu]_,n_,z_],ProfileX[profile_,ders_, w_,wbar_]]:= 1 + n;
singularity[ProfileX[profile_,ders_, w_,wbar_],dX[\[Mu]_,n_,z_]]:= 1 + n;
singularity[dXt[\[Mu]_,n_,z_],ProfileX[profile_,ders_, w_,wbar_]]:=1 + n;
singularity[ProfileX[profile_,ders_, w_,wbar_],dXt[\[Mu]_,n_,z_]]:=1 + n;

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
