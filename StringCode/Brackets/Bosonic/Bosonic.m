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


Bracket[toBracket__/;AllTrue[{toBracket}, SFtest]]:= b0mHold[BracketBosonic[toBracket]];


(* ::Subsection:: *)
(*Define projection of the string bracket*)


BracketProjection::usage = "Projects a string bracket onto a given holomorphic/antihlomorphic weight"
BracketProjection[bracket__, weightHolo_, weightAntiHolo_]:= 
Module[{prefac, bracketHolo, bracketAntiHolo, bracketInteracting, OPEHolo, OPEAntiHolo, bracketHoloWeightFree, bracketAntiHoloWeightFree,
bracketHoloWeightInteracting, bracketAntiHoloWeightInteracting, \[Epsilon]Holo, \[Epsilon]AntiHolo, insertionWeightHolo, insertionWeightAntiHolo,
projectedOPEHolo, projectedOPEAntiHolo, projectedOPE, OPEInteracting, OPEInteractingSingular, result},

(*Loop through each multi-local term of Bracket obtained by different actions of B-ghosts*)
result = Reap[
Scan[Function[bracketTerm,

(*Split the free multi-local result of the bracket into holomorphic/antiholomorphic parts, and keep the interacting part unsplit*)
{bracketHolo, bracketAntiHolo, bracketInteracting, prefac} = factorizeMultiOp[bracketTerm];

bracketHoloWeightFree = totalWeightHolo[R @@ bracketHolo];
bracketAntiHoloWeightFree = totalWeightAntiHolo[R @@ bracketAntiHolo];

(*Collapse the free multi-local operator via OPE*)
{OPEHolo, OPEAntiHolo} = CollapseFree[bracketHolo, bracketAntiHolo, \[Epsilon]Holo, \[Epsilon]AntiHolo];

If[bracketInteracting === MultiOp[],
(*When there is no interacting sector, perform the level projection on each holomorphic/antiholomorphic sector separately*)
{insertionWeightHolo, insertionWeightAntiHolo} = {bracketHoloWeightFree, bracketAntiHoloWeightFree};

{projectedOPEHolo, projectedOPEAntiHolo} = 
{projectHolo[OPEHolo, weightHolo - insertionWeightHolo, \[Epsilon]Holo], projectAntiHolo[OPEAntiHolo, weightAntiHolo - insertionWeightAntiHolo, \[Epsilon]AntiHolo]};

Sow[{prefac projectedOPEHolo, projectedOPEAntiHolo}],

(*Collapse the interacting multi-local operator, assuming generic OPE, but boudedness of weight by 0 from below i.e. most singular term comes from the identity*)
bracketHoloWeightInteracting = totalWeightHolo[Interacting @@ bracketInteracting];
bracketAntiHoloWeightInteracting = totalWeightAntiHolo[Interacting @@ bracketInteracting];
OPEInteracting = OPE @@ bracketInteracting;
OPEInteractingSingular = CollapseInteracting[OPEInteracting, \[Epsilon]Holo, \[Epsilon]AntiHolo, bracketHoloWeightInteracting, bracketAntiHoloWeightInteracting];

(*Perform the level projection on both holomorphic and antiholomorphic sector together*)
{insertionWeightHolo, insertionWeightAntiHolo} = {bracketHoloWeightFree + bracketHoloWeightInteracting, bracketAntiHoloWeightFree + bracketAntiHoloWeightInteracting};

projectedOPE = projectOPE[OPEHolo, OPEAntiHolo, weightHolo - insertionWeightHolo, \[Epsilon]Holo,  weightAntiHolo - insertionWeightAntiHolo, \[Epsilon]AntiHolo,
 bracketHoloWeightInteracting + bracketAntiHoloWeightInteracting, OPEInteracting, OPEInteractingSingular];
Sow[{prefac projectedOPE}];
];

],  If[Head[bracket] === Plus, bracket/.{Plus->List}, {bracket}]]]
[[2]][[1,1,1]];
result
];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
