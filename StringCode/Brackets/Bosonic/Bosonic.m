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
(*Define 2-bracket with ProfileX*)


BracketWithProfileX[SFa_/; SFtest[SFa], SFb_/;SFtest[SFb], \[Alpha]pOrder_/;NumericQ[\[Alpha]pOrder]]:= 
Module[{z0, z0bar, powerHol, powerAntiHol, result = 0, tayloredOPEpart, SFaAtPos, SFbAtPos, localCoordinateReplacement}, 
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
],List @@(((OPE[SFaAtPos, SFbAtPos, \[Alpha]pOrder])/.localCoordinateReplacement)//Expand)]; result/.{z0->0, z0bar->0}];


BracketWithProfileX[a_+b_,c_, \[Alpha]pOrder_/;NumericQ[\[Alpha]pOrder]]:=BracketWithProfileX[a,c, \[Alpha]pOrder]+BracketWithProfileX[b,c, \[Alpha]pOrder]
BracketWithProfileX[a_,b_+c_, \[Alpha]pOrder_/;NumericQ[\[Alpha]pOrder]]:=BracketWithProfileX[a,b, \[Alpha]pOrder]+BracketWithProfileX[a,c, \[Alpha]pOrder]
BracketWithProfileX[a_ b_,c_, \[Alpha]pOrder_/;NumericQ[\[Alpha]pOrder]]:=a BracketWithProfileX[b,c, \[Alpha]pOrder]/;(And @@(FreeQ[a,#]&/@ allfields))
BracketWithProfileX[a_,b_ c_, \[Alpha]pOrder_/;NumericQ[\[Alpha]pOrder]]:=b BracketWithProfileX[a,c, \[Alpha]pOrder]/;(And @@(FreeQ[b,#]&/@ allfields))


(* ::Subsection:: *)
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
