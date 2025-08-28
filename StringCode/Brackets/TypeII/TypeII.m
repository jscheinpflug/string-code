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
(*For each term in the BRST current, check if there is any possibility [OPE singularity is upper bounded] of it giving a nonzero contribution*)
compositeInBRSTPosition = containsCompositeHolo[BRSTelem/.{z->0}];
If[compositeInBRSTPosition !=  "NotFound",
singularityUpperBound = upperBoundSingularity[singularityMatrix[BRSTelem, Ra], compositeInBRSTPosition],
singularityUpperBound = upperBoundSingularity[singularityMatrix[BRSTelem, Ra], 0]];
If[singularityUpperBound >= 0,
(*Compute OPE with terms in the BRST current that possibly contribute*)
OPEWithBRST = OPE[BRSTelem, Ra]//Expand;
Scan[Function[Relem,
power = Exponent[Relem, z];
(*Extract first order pole from OPE*)
If[power == -1, result = result + Relem, 
If[power < -1, result = result + TaylorAtOrder[Relem, -power - 1, 0, 0, 0]]];
], If[Head[OPEWithBRST] === Plus, List @@ OPEWithBRST, {OPEWithBRST}]];
];], BRSTList];
(z result // Expand)/.{z->0}];

actBRSTAntiHolo[SFa_/; SFtest[SFa]] := Module[{result = 0, zBar, Ra = SFAtPos[SFa, 0,0], OPEWithBRST, power, BRSTList, singularityUpperBound, compositeInBRSTPosition},
BRSTList = List @@ jBRSTbar[zBar];
Scan[Function[BRSTelem,
(*For each term in the BRST current, check if there is any possibility [OPE singularity is upper bounded] of it giving a nonzero contribution*)
compositeInBRSTPosition = containsCompositeAntiHolo[BRSTelem/.{zBar->0}];
If[compositeInBRSTPosition !=  "NotFound",
singularityUpperBound = upperBoundSingularity[singularityMatrix[BRSTelem, Ra], compositeInBRSTPosition],
singularityUpperBound = upperBoundSingularity[singularityMatrix[BRSTelem, Ra], 0]];
If[singularityUpperBound >= 0,
(*Compute OPE with terms in the BRST current that possibly contribute*)
OPEWithBRST = OPE[BRSTelem, Ra]//Expand;
Scan[Function[Relem,
power = Exponent[Relem, zBar];
(*Extract first order pole from OPE*)
If[power == -1, result = result + Relem, 
If[power < -1, result = result + TaylorAtOrder[Relem, 0, -power-1, 0, 0]]];
], If[Head[OPEWithBRST] === Plus, List @@ OPEWithBRST, {OPEWithBRST}]];
];], BRSTList];
(zBar result // Expand)/.{zBar->0}];


(* ::Subsection:: *)
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
Module[{result = {}, numberOfHoloPCOs = 0, numberOfAntiHoloPCOs = 0, bracketNoPCOs, prefac, bracketHolo, bracketAntiHolo, OPEHolo, OPEAntiHolo,
\[Epsilon]Holo, \[Epsilon]AntiHolo, insertionWeightHolo, insertionWeightAntiHolo, projectedOPEHolo, projectedOPEAntiHolo,  holoOPEWithPCOs, antiHoloOPEWithPCOs},

(*Strip off PCOs*)
bracketNoPCOs = bracket//.{actPCO0Hold[x_]:> (numberOfHoloPCOs ++; x), actPCObar0Hold[x_]:> (numberOfAntiHoloPCOs ++; x)};

(*Compute bracket for each term inside of nested PCOs*)
Scan[Function[bracketNoPCOsTerm,

(*Split the multi-local result of the bracket into holomorphic/antiholomorphic parts*)
{bracketHolo, bracketAntiHolo, prefac} = factorizeMultiOp[bracketNoPCOsTerm];

(*Rescale positions of operators in the bracket by a common \[Epsilon]Holo/\[Epsilon]AntiHolo to ease weight projection, and then perform OPE*)
{OPEHolo, OPEAntiHolo} = {OPE @@ rescaleMultiOp[bracketHolo, \[Epsilon]Holo], OPE @@ rescaleMultiOp[bracketAntiHolo, \[Epsilon]AntiHolo]};

(*Perform the level projection on each holomorphic/antiholomorphic sector separately*)
{insertionWeightHolo, insertionWeightAntiHolo} = {totalWeightHolo[R @@ bracketHolo], totalWeightAntiHolo[R @@ bracketHolo]};
{projectedOPEHolo, projectedOPEAntiHolo} = 
{projectHolo[OPEHolo, weightHolo - insertionWeightHolo, \[Epsilon]Holo], projectAntiHolo[OPEAntiHolo, weightAntiHolo - insertionWeightAntiHolo, \[Epsilon]AntiHolo]};

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
power = (Exponent[OPEterm, weightCountingParameter])/.{\[Alpha]p :> 0};
expansionOrder = -power + weight;
If[expansionOrder >= 0,
result = result + TaylorAtOrderHolo[OPEterm, expansionOrder, 0]];
],
OPEterms];
result/.{weightCountingParameter -> 1}]


projectAntiHolo[OPE_, weight_, weightCountingParameter_]:= Module[{result = 0, power, expansionOrder, OPEexpanded = Expand[OPE], OPEterms},
OPEterms = If[Head[OPEexpanded] === Plus, List @@ OPEexpanded, {OPEexpanded}];
Scan[Function[OPEterm,
power = (Exponent[OPEterm, weightCountingParameter])/.{\[Alpha]p :> 0};
expansionOrder = -power + weight;
If[expansionOrder >= 0,
result = result + TaylorAtOrderAntiHolo[OPEterm, expansionOrder, 0]];
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


actPCOHolo::usage = "Acts zero mode of holomorphic PCO on a local operator";
actPCOHolo[Ra_/;Rtest[Ra]] := actPCOHolo[Ra] =
 Module[{result = 0, z, OPEWithPCO, power, PCOList, singularityUpperBound, compositeInPCOPosition},
PCOList = List @@ PCO[z];
Scan[Function[PCOelem,
(*For each term in the PCO, check if there is any possibility [OPE singularity is upper bounded] of it giving a nonzero contribution*)
compositeInPCOPosition = containsCompositeHolo[PCOelem/.{z->0}];
If[compositeInPCOPosition !=  "NotFound",
singularityUpperBound = upperBoundSingularity[singularityMatrix[PCOelem, Ra], compositeInPCOPosition],
singularityUpperBound = upperBoundSingularity[singularityMatrix[PCOelem, Ra], 0]];
If[singularityUpperBound >= 0,
(*Compute OPE with terms in the PCO that possibly contribute*)
OPEWithPCO = OPE[PCOelem, Ra]//Expand;
Scan[Function[Relem,
power = Exponent[Relem, z];
(*Extract zeroth order pole from OPE*)
If[power == 0, result = result + Relem, 
If[power < 0, result = result + TaylorAtOrderHolo[Relem, -power, 0]]];
], If[Head[OPEWithPCO] === Plus, List @@ OPEWithPCO, {OPEWithPCO}]];
];], PCOList];
((result // Expand) /.{z->0})];

actPCOAntiHolo::usage = "Acts zero mode of antiholomorphic PCO on a local operator";
actPCOAntiHolo[Ra_/;Rtest[Ra]] := actPCOAntiHolo[Ra] =
Module[{result = 0, zBar, OPEWithPCO, power, PCOList, singularityUpperBound, compositeInPCOPosition},
PCOList = List @@ PCObar[zBar];
Scan[Function[PCOelem,
(*For each term in the PCO, check if there is any possibility [OPE singularity is upper bounded] of it giving a nonzero contribution*)
compositeInPCOPosition = containsCompositeAntiHolo[PCOelem/.{zBar->0}];
If[compositeInPCOPosition !=  "NotFound",
singularityUpperBound = upperBoundSingularity[singularityMatrix[PCOelem, Ra], compositeInPCOPosition],
singularityUpperBound = upperBoundSingularity[singularityMatrix[PCOelem, Ra], 0]];
If[singularityUpperBound >= 0,
(*Compute OPE with terms in the PCO that possibly contribute*)
OPEWithPCO = OPE[PCOelem, Ra]//Expand;
Scan[Function[Relem,
power = Exponent[Relem, zBar];
(*Extract zeroth order pole from OPE*)
If[power == 0, result = result + Relem, 
If[power < 0, result = result + TaylorAtOrderAntiHolo[Relem, -power, 0]]];
], If[Head[OPEWithPCO] === Plus, List @@ OPEWithPCO, {OPEWithPCO}]];
];], PCOList];
((result // Expand)/.{zBar->0})];


(*Multilinearity of PCO zero mode actions*)
actPCOHolo[a_+b_]:=actPCOHolo[a] + actPCOHolo[b];
actPCOHolo[a_ b_]:=a actPCOHolo[b]/;(And @@(FreeQ[a,#]&/@ allfields))
actPCOHolo[0] := 0;

actPCOAntiHolo[a_+b_]:=actPCOAntiHolo[a] + actPCOAntiHolo[b];
actPCOAntiHolo[a_ b_]:=a actPCOAntiHolo[b]/;(And @@(FreeQ[a,#]&/@ allfields))
actPCOAntiHolo[0] := 0;


(* ::Subsection:: *)
(*Determine whether OPE should be computed*)


containsCompositeHolo::usage = "Checks if contains holomorphic composite";
containsCompositeHolo[PCOelem_]:= containsCompositeHolo[PCOelem] = First@FirstPosition[PCOelem/.{R->List}, _?(MatchQ[Head[#], exp\[Phi]b | exp\[Phi]f] &)];

containsCompositeAntiHolo::usage = "Checks if contains antiholomorphic composite";
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
