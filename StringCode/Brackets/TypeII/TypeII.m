(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Brackets`TypeII`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`TypeII`"];
Needs["StringCode`Operators`"];
Needs["StringCode`Operators`TypeII`"];
Needs["StringCode`Taylor`"];
Needs["StringCode`Taylor`TypeII`"];
Needs["StringCode`Conventions`TypeII`"];
Needs["StringCode`OPE`"];
Needs["StringCode`OPE`TypeII`"];
Needs["StringCode`Brackets`"];


(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


Begin["Private`"];

hasSpinFieldQ::usage = "Checks whether a normal-ordered operator contains TypeII spin fields S or St.";
hasSpinFieldQ[Ra_ /; RTest[Ra]] := AnyTrue[List @@ Ra, MemberQ[{"S", "St"}, SymbolName[Head[#]]] &];

(* ::Subsection::Closed:: *)
(*Define 1-bracket (action of BRST charge)*)

actBRSTHolo[Ra_/; (RTest[Ra] && !hasSpinFieldQ[Ra])] := Module[{result = 0, z, RaPos = RAtPos[Ra, 0, 0], OPEWithBRST, power, BRSTList, singularityUpperBound, compositeInBRSTPosition},
BRSTList = List @@ jBRST[z];
Scan[Function[BRSTelem,
(*For each term in the BRST current, check if there is any possibility [OPE singularity is upper bounded] of it giving a nonzero contribution*)
compositeInBRSTPosition = containsCompositeHolo[BRSTelem/.{z->0}];
If[compositeInBRSTPosition !=  "NotFound",
singularityUpperBound = upperBoundSingularity[singularityMatrix[BRSTelem, RaPos], compositeInBRSTPosition],
singularityUpperBound = upperBoundSingularity[singularityMatrix[BRSTelem, RaPos], 0]];
If[singularityUpperBound >= 0,
(*Compute OPE with terms in the BRST current that possibly contribute*)
OPEWithBRST = OPE[BRSTelem, RaPos]//Expand;
Scan[Function[Relem,
power = Exponent[Relem, z];
(*Extract first order pole from OPE*)
If[power == -1, result = result + Relem, 
If[power < -1, result = result + TaylorAtOrder[Relem, -power - 1, 0, 0, 0]]];
], If[Head[OPEWithBRST] === Plus, List @@ OPEWithBRST, {OPEWithBRST}]];
];], BRSTList];
(z result // Expand)/.{z->0}];

actBRSTHolo[Ra_ /; (RTest[Ra] && hasSpinFieldQ[Ra])] := Module[
  {wH, brst, raAtOrigin, z, result},
  wH = totalWeightHolo[Ra];
  brst = jBRST[z];
  raAtOrigin = Expand[RAtPos[Ra, 0, 0]];
  result = OPEProjectedHolo[wH][brst, raAtOrigin];
  result
];

actBRSTAntiHolo[Ra_/; (RTest[Ra] && !hasSpinFieldQ[Ra])] := Module[{result = 0, zBar, RaPos = RAtPos[Ra, 0, 0], OPEWithBRST, power, BRSTList, singularityUpperBound, compositeInBRSTPosition},
BRSTList = List @@ jBRSTbar[zBar];
Scan[Function[BRSTelem,
(*For each term in the BRST current, check if there is any possibility [OPE singularity is upper bounded] of it giving a nonzero contribution*)
compositeInBRSTPosition = containsCompositeAntiHolo[BRSTelem/.{zBar->0}];
If[compositeInBRSTPosition !=  "NotFound",
singularityUpperBound = upperBoundSingularity[singularityMatrix[BRSTelem, RaPos], compositeInBRSTPosition],
singularityUpperBound = upperBoundSingularity[singularityMatrix[BRSTelem, RaPos], 0]];
If[singularityUpperBound >= 0,
(*Compute OPE with terms in the BRST current that possibly contribute*)
OPEWithBRST = OPE[BRSTelem, RaPos]//Expand;
Scan[Function[Relem,
power = Exponent[Relem, zBar];
(*Extract first order pole from OPE*)
If[power == -1, result = result + Relem, 
If[power < -1, result = result + TaylorAtOrder[Relem, 0, -power-1, 0, 0]]];
], If[Head[OPEWithBRST] === Plus, List @@ OPEWithBRST, {OPEWithBRST}]];
];], BRSTList];
(zBar result // Expand)/.{zBar->0}];

actBRSTAntiHolo[Ra_ /; (RTest[Ra] && hasSpinFieldQ[Ra])] := Module[
  {wAH, brstBar, raAtOrigin, zBar, result},
  wAH = totalWeightAntiHolo[Ra];
  brstBar = jBRSTbar[zBar];
  raAtOrigin = Expand[RAtPos[Ra, 0, 0]];
  result = OPEProjectedAntiHolo[wAH][brstBar, raAtOrigin];
  result
];


(* ::Subsection:: *)
(*Define string bracket*)


Bracket[toBracket__/;AllTrue[{toBracket}, (RTest[#] || MultiOpTest[#]) &]]:= Module[{result = 0, afterApplyingBghosts, numberOfHoloPCOs, numberOfAntiHoloPCOs, afterHeldActionOfPCOs },

(*Get bosonic part of the bracket*)
afterApplyingBghosts = BracketBosonic[toBracket];

(*Apply PCO zero-modes abstractly*)
numberOfHoloPCOs = Max[0, Ceiling[Abs[Total[Map[totalHolPicture, {toBracket}]]] - 1]];
numberOfAntiHoloPCOs = Max[0, Ceiling[Abs[Total[Map[totalAntiHolPicture, {toBracket}]]] - 1]];
afterHeldActionOfPCOs = Nest[actPCObar0Hold, Nest[actPCO0Hold, afterApplyingBghosts, numberOfHoloPCOs], numberOfAntiHoloPCOs];

result = b0mHold[afterHeldActionOfPCOs];
result]


(* ::Subsection:: *)
(*Define projection of the string bracket*)


BracketProjection::usage = "Projects a string bracket onto a given holomorphic/antihlomorphic weight"
BracketProjection[bracket_, weightHolo_, weightAntiHolo_]:=
Module[{result, numberOfHoloPCOs = 0, numberOfAntiHoloPCOs = 0, bracketNoPCOs, prefac, localOps, projectionData, projectedOPE, holoOPEWithPCOs, antiHoloOPEWithPCOs, termsList},

(*Strip off PCOs and expand to distribute any overall constants across sums*)
bracketNoPCOs = Expand[bracket//.{actPCO0Hold[x_]:> (numberOfHoloPCOs ++; x), actPCObar0Hold[x_]:> (numberOfAntiHoloPCOs ++; x)}];
termsList = If[Head[bracketNoPCOs] === Plus, List @@ bracketNoPCOs, {bracketNoPCOs}];

(*Loop through each multi-local term of Bracket obtained by different actions of B-ghosts [inside PCO actions]*)
result = Total @ Last @ Reap[
Scan[Function[bracketNoPCOsTerm,
prefac = extractPrefacFromMultiOpTimesConstant[bracketNoPCOsTerm];
localOps = extractListFromMultiOpTimesConstant[bracketNoPCOsTerm];

(* Shared projection logic; TypeII-specific work is only the subsequent PCO action. *)
projectionData = projectBracketLocalOps[localOps, weightHolo, weightAntiHolo];

If[projectionData[[1]] === "Factorized",
(* Fast path: project each chirality separately, then apply holomorphic/antiholomorphic PCOs. *)
{holoOPEWithPCOs, antiHoloOPEWithPCOs} = {
  Nest[actPCOHolo, prefac projectionData[[2]] projectionData[[3]], numberOfHoloPCOs],
  Nest[actPCOAntiHolo, projectionData[[4]], numberOfAntiHoloPCOs]
};
Sow[R[holoOPEWithPCOs, antiHoloOPEWithPCOs]],
(* Generic path: project the unsplit local operators, then apply holo/antiholo PCOs separately. *)
projectedOPE = prefac projectionData[[2]];
Sow[Nest[actPCOHolo, Nest[actPCOAntiHolo, projectedOPE, numberOfAntiHoloPCOs], numberOfHoloPCOs]]
];
], termsList]
,
_,
Total[#2] &
];

result
];


(* ::Subsection:: *)
(*Define action of PCOs*)


actPCOHolo::usage = "Acts zero mode of holomorphic PCO on a local operator";

(*Defines PCO action for string fields with spin fields - must come before general rule*)
actPCOHolo[Ra_ /; (RTest[Ra] && hasSpinFieldQ[Ra])] := Module[
  {wH, pco, raAtOrigin, z, result},
  wH = totalWeightHolo[Ra];
  pco = PCO[z];
  raAtOrigin = Expand[RAtPos[Ra, 0, 0]];
  result = OPEProjectedHolo[wH][pco, raAtOrigin];
  result
]

actPCOHolo[Ra_/; (RTest[Ra] && !hasSpinFieldQ[Ra])] := actPCOHolo[Ra] =
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

(*Defines PCO action for string fields with spin fields - must come before general rule*)
actPCOAntiHolo[Ra_ /; (RTest[Ra] && hasSpinFieldQ[Ra])] := Module[
  {wAH, pcoBar, raAtOrigin, zBar},
  wAH = totalWeightAntiHolo[Ra];
  pcoBar = PCObar[zBar];
  raAtOrigin = Expand[RAtPos[Ra, 0, 0]];
  OPEProjectedAntiHolo[wAH][pcoBar, raAtOrigin]
]

actPCOAntiHolo[Ra_/; (RTest[Ra] && !hasSpinFieldQ[Ra])] := actPCOAntiHolo[Ra] =
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
actPCOHolo[a_ b_]:=a actPCOHolo[b]/;(isScalarFactorQ[a])
actPCOHolo[0] := 0;

actPCOAntiHolo[a_+b_]:=actPCOAntiHolo[a] + actPCOAntiHolo[b];
actPCOAntiHolo[a_ b_]:=a actPCOAntiHolo[b]/;(isScalarFactorQ[a])
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
singularity[\[Beta][n_,z_],\[Gamma][m_,w_]]:= 1 + m + n;
singularity[\[Gamma][m_,w_],\[Beta][n_,z_]]:= 1 + m + n;
singularity[\[Beta]t[n_,z_],\[Gamma]t[m_,w_]]:= 1 + m + n;
singularity[\[Gamma]t[m_,w_],\[Beta]t[n_,z_]]:= 1 + m + n;

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
