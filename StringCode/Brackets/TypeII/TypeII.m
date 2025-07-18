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
If[powerAntiHol < 0,TaylorAtOrder[OPEpart,-powerHol, -powerAntiHol,0,0], TaylorAtOrder[OPEpart/.{z0bar->0},-powerHol, 0,0,0]], 
If[powerAntiHol < 0, TaylorAtOrder[OPEpart/.{z0->0},0,-powerAntiHol,0,0], OPEpart/.{z0->0,z0bar->0}]]//Expand;
result = result + pictureAdjust[b0m[tayloredOPEpart]];,
0];
],List @@(((OPE[SFaAtPos, SFbAtPos])/.localCoordinateReplacement)//Expand)]; result];


(* ::Subsubsection:: *)
(*Define 2-bracket with ProfileX*)


BracketWithProfileX[SFa_/; SFtest[SFa], SFb_/;SFtest[SFb], \[Alpha]pOrder_/;NumericQ[\[Alpha]pOrder]]:= 
Module[{z0, z0bar, powerHol, powerAntiHol, result = 0, tayloredOPEpart, SFaAtPos, SFbAtPos, localCoordinateReplacement, intermediateOrder}, 
{SFaAtPos, SFbAtPos, localCoordinateReplacement, z0, z0bar} = SFsWithLocalCoordinateData[SFa, SFb];
Scan[Function[OPEpart,
intermediateOrder = Exponent[OPEpart, \[Alpha]p];
powerHol = Exponent[OPEpart, z0];
powerAntiHol = Exponent[OPEpart, z0bar];
If[RtestUpToConstant[OPEpart],
tayloredOPEpart = If[powerHol < 0, 
If[powerAntiHol < 0, TaylorAtOrder[OPEpart,-powerHol, -powerAntiHol,0,0], TaylorAtOrder[OPEpart,-powerHol, 0,0,0]], 
If[powerAntiHol < 0, TaylorAtOrder[OPEpart,0,-powerAntiHol,0,0], OPEpart]]//Expand;
result = result + pictureAdjust[b0m[tayloredOPEpart], \[Alpha]pOrder - intermediateOrder];,
0];
],List @@(((OPE[SFaAtPos, SFbAtPos, \[Alpha]pOrder])/.localCoordinateReplacement)//Expand)]; result/.{z0->0, z0bar->0}];


BracketWithProfileX[a_+b_,c_, \[Alpha]pOrder_/;NumericQ[\[Alpha]pOrder]]:=BracketWithProfileX[a,c, \[Alpha]pOrder]+BracketWithProfileX[b,c, \[Alpha]pOrder]
BracketWithProfileX[a_,b_+c_, \[Alpha]pOrder_/;NumericQ[\[Alpha]pOrder]]:=BracketWithProfileX[a,b, \[Alpha]pOrder]+BracketWithProfileX[a,c, \[Alpha]pOrder]
BracketWithProfileX[a_ b_,c_, \[Alpha]pOrder_/;NumericQ[\[Alpha]pOrder]]:=a BracketWithProfileX[b,c, \[Alpha]pOrder]/;(And @@(FreeQ[a,#]&/@ allfields))
BracketWithProfileX[a_,b_ c_, \[Alpha]pOrder_/;NumericQ[\[Alpha]pOrder]]:=b BracketWithProfileX[a,c, \[Alpha]pOrder]/;(And @@(FreeQ[b,#]&/@ allfields))


(* ::Subsection:: *)
(*Define action of PCOs*)


actPCOHolo[Ra_/;Rtest[Ra], \[Alpha]pOrder___] := Module[{result = 0, z, OPEWithPCO, power, PCOList, singularityUpperBound, compositeInPCOPosition},
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

actPCOAntiHolo[Ra_/;Rtest[Ra], \[Alpha]pOrder___] := Module[{result = 0, zBar, OPEWithPCO, power, PCOList, singularityUpperBound, compositeInPCOPosition},
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
If[power < 0, result = result + TaylorAtOrder[Relem, -power, 0, 0, 0]]];
], If[Head[OPEWithPCO] === Plus, List @@ OPEWithPCO, {OPEWithPCO}]];
];], PCOList];
((result // Expand)/.{zBar->0})];

totalHolPicture[Ra_/;Rtest[Ra]]:= Map[pictureHol, List @@ Ra]//Total;
totalAntiHolPicture[Ra_/;Rtest[Ra]]:= Map[pictureAntiHol, List @@ Ra]//Total;

pictureAdjust[Ra_/;Rtest[Ra], \[Alpha]pOrder___] :=
  Module[{pictureHol = totalHolPicture[Ra], pictureAntiHol = totalAntiHolPicture[Ra], factorization = splitR[Ra], holoRaised, antiHoloRaised, resultdoubled, result = Ra},
   holoRaised =
    If[pictureHol < 0, Nest[actPCOHolo[#, \[Alpha]pOrder] &, R @@ factorization[[1]], Ceiling[Abs[pictureHol]] - 1], R @@ factorization[[1]]];
   antiHoloRaised =
    DeleteCases[
     If[pictureAntiHol < 0, Nest[actPCOAntiHolo[#, \[Alpha]pOrder] &, R @@ factorization[[2]], Ceiling[Abs[pictureAntiHol]] - 1], R @@ factorization[[2]]], expX[_, _, _], \[Infinity]];
   If[(pictureHol + pictureAntiHol) < 0,
   If[\[Alpha]pOrder > 0,
   result = (factorizationSign[Ra] R[holoRaised, antiHoloRaised])/.{Power[\[Alpha]p, p_/; p > \[Alpha]pOrder] -> 0},
   result = factorizationSign[Ra] R[holoRaised, antiHoloRaised];
   ];
   ];
   result
   ];



actPCOAntiHolo[a_+b_, \[Alpha]pOrder___]:=actPCOAntiHolo[a, \[Alpha]pOrder] + actPCOAntiHolo[b, \[Alpha]pOrder];
actPCOAntiHolo[a_ b_, \[Alpha]pOrder___]:=a actPCOAntiHolo[b, \[Alpha]pOrder]/;(And @@(FreeQ[a,#]&/@ allfields))
actPCOAntiHolo[0, \[Alpha]pOrder___] := 0;
actPCOHolo[a_+b_, \[Alpha]pOrder___]:=actPCOHolo[a, \[Alpha]pOrder] + actPCOHolo[b, \[Alpha]pOrder];
actPCOHolo[a_ b_, \[Alpha]pOrder___]:=a actPCOHolo[b, \[Alpha]pOrder]/;(And @@(FreeQ[a,#]&/@ allfields))
actPCOHolo[0, \[Alpha]pOrder___] := 0;
pictureAdjust[a_+b_, \[Alpha]pOrder___]:=pictureAdjust[a, \[Alpha]pOrder] + pictureAdjust[b, \[Alpha]pOrder];
pictureAdjust[a_ b_, \[Alpha]pOrder___]:=a pictureAdjust[b, \[Alpha]pOrder]/;(And @@(FreeQ[a,#]&/@ allfields))
pictureAdjust[0, \[Alpha]pOrder___] := 0;


(* ::Subsubsection::Closed:: *)
(*Factorize normal-ordered product into holomorphic and antiholomorphic parts*)


splitR[Ra_ /; Rtest[Ra]] := Module[{RHolo = {}, RAntiHolo = {}, RList = List @@ Ra},
   RHolo = Select[RList, isHolomorphic @* Head];
   RAntiHolo = Select[RList, isAntiHolomorphic @* Head];
   {RHolo, RAntiHolo}
   ];
splitR[Times[a_, Ra_/;Rtest[Ra]]] := splitR[Ra]

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
