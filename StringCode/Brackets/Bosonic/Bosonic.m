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


Bracket[toBracket__/;AllTrue[{toBracket}, SFtest]]:= Module[{afterApplyingBghosts, localCoordinateReplacement, SFList},
{afterApplyingBghosts, localCoordinateReplacement, SFList} = BracketBosonic[toBracket];
{afterApplyingBghosts, localCoordinateReplacement}];


(* ::Subsection:: *)
(*Define projection of the string bracket*)


BracketProjection::usage = "Projects a string bracket onto a given holomorphic/antihlomorphic weight"
BracketProjection[{bracket_, localCoordinateReplacement_}, weightHolo_, weightAntiHolo_]:= 
Module[{prefac, bracketHolo, bracketAntiHolo, OPEHolo, OPEAntiHolo,
\[Epsilon]Holo, \[Epsilon]AntiHolo, insertionWeightHolo, insertionWeightAntiHolo, projectedOPEHolo, projectedOPEAntiHolo},

(*Loop through each multi-local term of Bracket obtained by different actions of B-ghosts*)
Reap[
Scan[Function[bracketTerm,

(*Split the multi-local result of the bracket into holomorphic/antiholomorphic parts*)
{bracketHolo, bracketAntiHolo, prefac} = factorizeMultiOp[bracketTerm];
(*Collapse the multi-local operator via OPE*)
{OPEHolo, OPEAntiHolo} = Collapse[bracketHolo, bracketAntiHolo, \[Epsilon]Holo, \[Epsilon]AntiHolo];

(*Perform the level projection on each holomorphic/antiholomorphic sector separately*)
{insertionWeightHolo, insertionWeightAntiHolo} = {totalWeightHolo[R @@ bracketHolo], totalWeightAntiHolo[R @@ bracketAntiHolo]};

{projectedOPEHolo, projectedOPEAntiHolo} = 
{projectHolo[OPEHolo, weightHolo - insertionWeightHolo, \[Epsilon]Holo], projectAntiHolo[OPEAntiHolo, weightAntiHolo - insertionWeightAntiHolo, \[Epsilon]AntiHolo]};

Sow[{projectedOPEHolo, projectedOPEAntiHolo, prefac}]

],  If[Head[bracket] === Plus, bracket/.{Plus->List}, {bracket}]]]
[[2]]];


(* ::Subsubsection:: *)
(*Set factorization replacement*)


(*This replacement rule is called on multi-local operator every time factorization into holomorphic/antiholomorphic parts is performed*)
factorizationReplacement = 
{ProfileX[profile_, ders_, z_, zbar_]:> R[ProfileXHolo[profile, ders, z], ProfileXAntiHolo[profile, ders, zbar]], expX[k_, z_, zbar_]:> R[expXHolo[k, z], expXAntiHolo[k,zbar]]}


(* ::Subsubsection:: *)
(*Extract weight-counting parameter power*)


extractWeightCountingParameterPower::usage = "Extract weight-counting parameter power (modulo multiples of \[Alpha]')";
extractWeightCountingParameterPower[OPEterm_, weightCountingParameter_] := (Exponent[Together[OPEterm], weightCountingParameter])/.{\[Alpha]p -> 0}


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
