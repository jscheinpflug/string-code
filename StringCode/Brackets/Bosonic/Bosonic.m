(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Brackets`Bosonic`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`Bosonic`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`Bosonic`"];
Needs["StringCode`Operators`"];
Needs["StringCode`Operators`Bosonic`"];
Needs["StringCode`Taylor`"];
Needs["StringCode`Taylor`Bosonic`"];
Needs["StringCode`Conventions`Bosonic`"];
Needs["StringCode`OPE`"];
Needs["StringCode`OPE`Bosonic`"];
Needs["StringCode`Brackets`"];


(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection::Closed:: *)
(*Define 1-bracket (action of BRST charge)*)


actBRSTHolo[Ra_/;RTest[Ra]] := Module[{result = 0, z, RaPos = RAtPos[Ra, 0, 0], OPEWithBRST, power, BRSTList, singularityUpperBound, compositeInBRSTPosition},
BRSTList = List @@ jBRSTbosonicstring[z];
Scan[Function[BRSTelem,
singularityUpperBound = upperBoundSingularity[singularityMatrix[BRSTelem, RaPos], 0];
If[singularityUpperBound >= 0,
If[RcontainsProfile[RaPos],
OPEWithBRST = OPE[BRSTelem, RaPos, 2]//Expand,
OPEWithBRST = OPE[BRSTelem, RaPos]//Expand];
Scan[Function[Relem,
power = Exponent[Relem, z];
If[power == -1, result = result + Relem, 
If[power < -1, result = result + TaylorAtOrder[Relem, -power - 1, 0, 0, 0]]];
], If[Head[OPEWithBRST] === Plus, List @@ OPEWithBRST, {OPEWithBRST}]];
];], BRSTList];
(z result // Expand)/.{z->0}];

actBRSTAntiHolo[Ra_/;RTest[Ra]] := Module[{result = 0, zBar, RaPos = RAtPos[Ra, 0, 0], OPEWithBRST, power, BRSTList, singularityUpperBound, compositeInBRSTPosition},
BRSTList = List @@ jBRSTbosonicstringbar[zBar];
Scan[Function[BRSTelem,
singularityUpperBound = upperBoundSingularity[singularityMatrix[BRSTelem, RaPos], 0];
If[singularityUpperBound >= 0,
If[RcontainsProfile[RaPos],
OPEWithBRST = OPE[BRSTelem, RaPos, 2]//Expand,
OPEWithBRST = OPE[BRSTelem, RaPos]//Expand];
Scan[Function[Relem,
power = Exponent[Relem, zBar];
If[power == -1, result = result + Relem, 
If[power < -1, result = result + TaylorAtOrder[Relem, 0, -power-1, 0, 0]]];
], If[Head[OPEWithBRST] === Plus, List @@ OPEWithBRST, {OPEWithBRST}]];
];], BRSTList];
(zBar result // Expand)/.{zBar->0}];


(* ::Subsection:: *)
(*Define string bracket*)


Bracket[toBracket__/;AllTrue[{toBracket}, (RTest[#] || MultiOpTest[#]) &]]:= b0mHold[BracketBosonic[toBracket]];


(* ::Subsection:: *)
(*Define projection of the string bracket*)


BracketProjection::usage = "Projects a string bracket onto a given holomorphic/antihlomorphic weight"
BracketProjection[bracket__, weightHolo_, weightAntiHolo_]:= 
Module[{prefac, localOps, projectionData, projectedOPE, result},

(*Loop through each multi-local term of Bracket obtained by different actions of B-ghosts*)
result = Total @ Last @ Reap[
Scan[Function[bracketTerm,

prefac = extractPrefacFromMultiOpTimesConstant[bracketTerm];
localOps = extractListFromMultiOpTimesConstant[bracketTerm];
(* Shared helper decides whether to use factorized chiral projection or generic projection. *)
projectionData = projectBracketLocalOps[localOps, weightHolo, weightAntiHolo];
projectedOPE = If[
  projectionData[[1]] === "Factorized",
  (* factorization prefactor times recombined projected holomorphic/antiholomorphic pieces *)
  projectionData[[2]] combineProjectedBracketChiral[projectionData[[3]], projectionData[[4]]],
  projectionData[[2]]
];
Sow[prefac projectedOPE];

],  If[Head[bracket] === Plus, bracket/.{Plus->List}, {bracket}]]
,
_,
Total[#2] &
];
result
];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
