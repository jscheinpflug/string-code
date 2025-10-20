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


Bracket[toBracket__/;AllTrue[{toBracket}, SFtest]]:= Module[{result = 0, afterApplyingBghosts, localCoordinateReplacement, SFList, numberOfHoloPCOs, numberOfAntiHoloPCOs, afterHeldActionOfPCOs },

(*Get bosonic part of the bracket*)
afterApplyingBghosts = BracketBosonic[toBracket];

(*Apply PCO zero-modes abstractly*)
numberOfHoloPCOs = Ceiling[Abs[Total[Map[totalHolPicture @@ # &, {toBracket}]]]-1];
numberOfAntiHoloPCOs = Ceiling[Abs[Total[Map[totalAntiHolPicture @@ # &, {toBracket}]]]-1];
afterHeldActionOfPCOs = Nest[actPCObar0Hold, Nest[actPCO0Hold, afterApplyingBghosts, numberOfHoloPCOs], numberOfAntiHoloPCOs];

result = {b0m[afterHeldActionOfPCOs], localCoordinateReplacement};
result]


(* ::Subsection:: *)
(*Define projection of the string bracket*)


BracketProjection::usage = "Projects a string bracket onto a given holomorphic/antihlomorphic weight"
BracketProjection[bracket_, weightHolo_, weightAntiHolo_]:= 
Module[{bracketNoB0m = bracket/.{b0mHold->1}, result, numberOfHoloPCOs = 0, numberOfAntiHoloPCOs = 0, bracketNoPCOs, prefac, bracketHolo, bracketAntiHolo, bracketInteracting, bracketHoloWeightFree, 
bracketAntiHoloWeightFree, bracketHoloWeightInteracting, bracketAntiHoloWeightInteracting, OPEInteracting, OPEInteractingSingular, OPEHolo, OPEAntiHolo,
\[Epsilon]Holo, \[Epsilon]AntiHolo, insertionWeightHolo, insertionWeightAntiHolo, projectedOPEHolo, projectedOPEAntiHolo,  projectedOPE, holoOPEWithPCOs, antiHoloOPEWithPCOs},

(*Strip off PCOs*)
bracketNoPCOs = bracketNoB0m//.{actPCO0Hold[x_]:> (numberOfHoloPCOs ++; x), actPCObar0Hold[x_]:> (numberOfAntiHoloPCOs ++; x)};

(*Loop through each multi-local term of Bracket obtained by different actions of B-ghosts [inside PCO actions]*)
result = Reap[
Scan[Function[bracketNoPCOsTerm,

(*Split the multi-local result of the bracket into holomorphic/antiholomorphic parts*)
{bracketHolo, bracketAntiHolo, bracketInteracting, prefac} = factorizeMultiOp[bracketNoPCOsTerm];

bracketHoloWeightFree = totalWeightHolo[R @@ bracketHolo];
bracketAntiHoloWeightFree = totalWeightAntiHolo[R @@ bracketAntiHolo];

(*Collapse the multi-local operator via OPE*)
{OPEHolo, OPEAntiHolo} = CollapseFree[bracketHolo, bracketAntiHolo, \[Epsilon]Holo, \[Epsilon]AntiHolo];

If[bracketInteracting === MultiOp[],
(*When there is no interacting sector, perform the level projection on each holomorphic/antiholomorphic sector separately*)
{insertionWeightHolo, insertionWeightAntiHolo} = {totalWeightHolo[R @@ bracketHolo], totalWeightAntiHolo[R @@ bracketAntiHolo]};

{projectedOPEHolo, projectedOPEAntiHolo} = 
{projectHolo[prefac OPEHolo, weightHolo - insertionWeightHolo, \[Epsilon]Holo], projectAntiHolo[OPEAntiHolo, weightAntiHolo - insertionWeightAntiHolo, \[Epsilon]AntiHolo]};

(*Act with PCOs on each projected holomorphic/antiholomorphic sector separately*)
{holoOPEWithPCOs, antiHoloOPEWithPCOs} = {Nest[actPCOHolo, projectedOPEHolo, numberOfHoloPCOs], Nest[actPCOAntiHolo, projectedOPEAntiHolo, numberOfAntiHoloPCOs]};

Sow[{holoOPEWithPCOs, antiHoloOPEWithPCOs}],
(*Collapse the interacting multi-local operator, assuming generic OPE, but boudedness of weight by 0 from below i.e. most singular term comes from the identity*)
bracketHoloWeightInteracting = totalWeightHolo[Interacting @@ bracketInteracting];
bracketAntiHoloWeightInteracting = totalWeightAntiHolo[Interacting @@ bracketInteracting];
OPEInteracting = OPE @@ bracketInteracting;
OPEInteractingSingular = CollapseInteracting[prefac OPEInteracting, \[Epsilon]Holo, \[Epsilon]AntiHolo, bracketHoloWeightInteracting, bracketAntiHoloWeightInteracting];

(*Perform the level projection on both holomorphic and antiholomorphic sector together*)
{insertionWeightHolo, insertionWeightAntiHolo} = {bracketHoloWeightFree + bracketHoloWeightInteracting, bracketAntiHoloWeightFree + bracketAntiHoloWeightInteracting};

projectedOPE = projectOPE[OPEHolo, OPEAntiHolo, weightHolo - insertionWeightHolo, \[Epsilon]Holo,  weightAntiHolo - insertionWeightAntiHolo, \[Epsilon]AntiHolo,
 bracketHoloWeightInteracting + bracketAntiHoloWeightInteracting, OPEInteracting, OPEInteractingSingular];

Sow[{Nest[actPCO, projectedOPE, numberOfHoloPCOs + numberOfAntiHoloPCOs]}];
]
], If[Head[bracketNoPCOs] === Plus, bracketNoPCOs/.{Plus->List}, {bracketNoPCOs}]]]
[[2]][[1,1,1]];
b0mHold[result];
];


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


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
