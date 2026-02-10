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
Needs["StringCode`OPE`Bosonic`"];
Needs["StringCode`Brackets`"];


(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection::Closed:: *)
(*Define 1-bracket (action of BRST charge)*)


actBRSTHolo[SFa_/; SFTest[SFa]] := Module[{result = 0, z, Ra = SFAtPos[SFa, 0,0], OPEWithBRST, power, BRSTList, singularityUpperBound, compositeInBRSTPosition},
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

actBRSTAntiHolo[SFa_/; SFTest[SFa]] := Module[{result = 0, zBar, Ra = SFAtPos[SFa, 0,0], OPEWithBRST, power, BRSTList, singularityUpperBound, compositeInBRSTPosition},
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


Bracket[toBracket__/;AllTrue[{toBracket}, SFTest]]:= b0mHold[BracketBosonic[toBracket]];


(* ::Subsection:: *)
(*Define projection of the string bracket*)


BracketProjection::usage = "Projects a string bracket onto a given holomorphic/antihlomorphic weight"
BracketProjection[bracket__, weightHolo_, weightAntiHolo_]:= 
Module[{prefac, localOps, dualChiralOps, factorizationPrefac, bracketHolo, bracketAntiHolo, holoLocalOps, antiLocalOps,
insertionWeightHolo, insertionWeightAntiHolo, projectedHolo, projectedAntiHolo, projectedOPE, result},

(*Loop through each multi-local term of Bracket obtained by different actions of B-ghosts*)
result = Reap[
Scan[Function[bracketTerm,

prefac = extractPrefacFromMultiOpTimesConstant[bracketTerm];
localOps = extractListFromMultiOpTimesConstant[bracketTerm];
(* Detect fields that are simultaneously holo/anti-holo and can be split into chiral factors. *)
dualChiralOps = Flatten[(extractListFromRTimesConstant /@ Select[localOps, RTestUpToConstant]), 1];
dualChiralOps = Select[dualChiralOps, isHolomorphic[Head[#]] && isAntiHolomorphic[Head[#]] &];
If[dualChiralOps =!= {} && AllTrue[dualChiralOps, isFactorizable[Head[#]] &],
(* Fast path: factorize first and project each chiral sector separately. *)
{bracketHolo, bracketAntiHolo, factorizationPrefac} = factorizeMultiOp[MultiOp @@ localOps];
holoLocalOps = Select[List @@ bracketHolo, RTest];
antiLocalOps = Select[List @@ bracketAntiHolo, RTest];
insertionWeightHolo = Total[totalWeightHolo /@ holoLocalOps];
insertionWeightAntiHolo = Total[totalWeightAntiHolo /@ antiLocalOps];
projectedHolo = If[holoLocalOps === {}, If[weightHolo - insertionWeightHolo === 0, 1, 0], OPEProjectedHolo[weightHolo - insertionWeightHolo] @@ holoLocalOps];
projectedAntiHolo = If[antiLocalOps === {}, If[weightAntiHolo - insertionWeightAntiHolo === 0, 1, 0], OPEProjectedAntiHolo[weightAntiHolo - insertionWeightAntiHolo] @@ antiLocalOps];
projectedOPE = factorizationPrefac Which[
  projectedHolo === 0 || projectedAntiHolo === 0, 0,
  projectedHolo === 1, projectedAntiHolo,
  projectedAntiHolo === 1, projectedHolo,
  True, R[projectedHolo, projectedAntiHolo]
],
(* Generic path: project without explicit chiral pre-factorization. *)
insertionWeightHolo = Total[totalWeightHolo /@ localOps];
insertionWeightAntiHolo = Total[totalWeightAntiHolo /@ localOps];
projectedOPE = OPEProjected[weightHolo - insertionWeightHolo, weightAntiHolo - insertionWeightAntiHolo] @@ localOps
];
Sow[{prefac projectedOPE}];

],  If[Head[bracket] === Plus, bracket/.{Plus->List}, {bracket}]]]
[[2]][[1,1,1]];
result
];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
