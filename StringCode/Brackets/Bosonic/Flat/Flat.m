(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Brackets`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`StringFields`"];
Needs["StringCode`OPE`"];
Needs["StringCode`Taylor`"];
Needs["StringCode`Conventions`ConventionsIIBAshoke`"];


(* ::Section:: *)
(*Declare public variables and methods*)


Bracket::usage = "Computes the flat string bracket";


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Define 1-bracket (action of BRST charge)*)


actBRSTHolo[SFa_/; SFtest[SFa]] := Module[{result = 0, z, Ra = SFAtPos[SFa, 0,0], OPEWithBRST, power, BRSTList, singularityUpperBound, compositeInBRSTPosition},
BRSTList = List @@ jBRSTNoTD[z];
Scan[Function[BRSTelem,
compositeInBRSTPosition = containsCompositeHolo[BRSTelem/.{z->0}];
If[compositeInBRSTPosition !=  "NotFound",
singularityUpperBound = upperBoundSingularity[singularityMatrix[BRSTelem, Ra], compositeInBRSTPosition],
singularityUpperBound = upperBoundSingularity[singularityMatrix[BRSTelem, Ra], 0]];
If[singularityUpperBound >= 0,
OPEWithBRST = OPE[BRSTelem, Ra]//Expand;
Scan[Function[Relem,
power = Exponent[Relem, z];
If[power == -1, result = result + Relem, 
If[power < -1, result = result + TaylorAtOrder[Relem, -power - 1, 0, 0, 0]]];
], If[Head[OPEWithBRST] === Plus, List @@ OPEWithBRST, {OPEWithBRST}]];
];], BRSTList];
(z result // Expand)/.{z->0}];

actBRSTAntiHolo[SFa_/; SFtest[SFa]] := Module[{result = 0, zBar, Ra = SFAtPos[SFa, 0,0], OPEWithBRST, power, BRSTList, singularityUpperBound, compositeInBRSTPosition},
BRSTList = List @@ jBRSTbarNoTD[zBar];
Scan[Function[BRSTelem,
compositeInBRSTPosition = containsCompositeAntiHolo[BRSTelem/.{zBar->0}];
If[compositeInBRSTPosition !=  "NotFound",
singularityUpperBound = upperBoundSingularity[singularityMatrix[BRSTelem, Ra], compositeInBRSTPosition],
singularityUpperBound = upperBoundSingularity[singularityMatrix[BRSTelem, Ra], 0]];
If[singularityUpperBound >= 0,
OPEWithBRST = OPE[BRSTelem, Ra]//Expand;
Scan[Function[Relem,
power = Exponent[Relem, zBar];
If[power == -1, result = result + Relem, 
If[power < -1, result = result + TaylorAtOrder[Relem, 0, -power-1, 0, 0]]];
], If[Head[OPEWithBRST] === Plus, List @@ OPEWithBRST, {OPEWithBRST}]];
];], BRSTList];
(zBar result // Expand)/.{zBar->0}];


actBRST[SFa_/; SFtest[SFa]]:= actBRSTHolo[SFa] + actBRSTAntiHolo[SFa];

actBRSTAntiHolo[a_+b_]:= actBRSTAntiHolo[a] + actBRSTAntiHolo[b];
actBRSTAntiHolo[a_ b_]:= a actBRSTAntiHolo[b]/;(And @@(FreeQ[a,#]&/@ allfields))
actBRSTAntiHolo[0] := 0;
actBRSTHolo[a_+b_]:= actBRSTHolo[a] +actBRSTHolo[b];
actBRSTHolo[a_ b_]:=a actBRSTHolo[b]/;(And @@(FreeQ[a,#]&/@ allfields))
actBRSTHolo[0] := 0;
actBRST[a_+b_]:=actBRST[a] + actBRST[b];
actBRST[a_ b_]:=a actBRST[b]/;(And @@(FreeQ[a,#]&/@ allfields))
actBRST[0] := 0;


(* ::Subsection:: *)
(*Define 2-bracket*)


Bracket[SFa_/; SFtest[SFa], SFb_/;SFtest[SFb]]:= Module[{z0, z0bar,w0,w0bar, powerHol, powerAntiHol, result = 0, tayloredOPEpart}, 
Scan[Function[OPEpart,
powerHol = Exponent[OPEpart, z0];
powerAntiHol = Exponent[OPEpart, z0bar];
If[RtestUpToConstant[OPEpart],
tayloredOPEpart = If[powerHol<0, 
If[powerAntiHol< 0,TaylorAtOrder[OPEpart,-powerHol, -powerAntiHol,0,0], TaylorAtOrder[OPEpart/.{z0bar->0},-powerHol, 0,0,0]], 
If[powerAntiHol <0, TaylorAtOrder[OPEpart/.{z0->0},0, -powerAntiHol,0,0], OPEpart/.{z0->0,z0bar->0}]]//Expand;
result = result + pictureAdjust[b0m[tayloredOPEpart]];,
0];
],List @@((OPE[SFAtPos[SFa, w0, w0bar], SFAtPos[SFb,z0,z0bar]])/.{w0->-z0,w0bar->-z0bar}//Expand)]; result];


Bracket[a_+b_,c_]:=Bracket[a,c]+Bracket[b,c]
Bracket[a_,b_+c_]:=Bracket[a,b]+Bracket[a,c]
Bracket[a_ b_,c_]:=a Bracket[b,c]/;(And @@(FreeQ[a,#]&/@ allfields))
Bracket[a_,b_ c_]:=b Bracket[a,c]/;(And @@(FreeQ[b,#]&/@ allfields))


(* ::Subsection:: *)
(*Define action of b0^-*)


b0mHolo[Ra_/;Rtest[Ra]] := Module[{result, RList = List @@ Ra, pos, numberOfPassedFermions},
pos = FirstPosition[RList, c[1, 0], None];
If[pos === None, Return[0]];
numberOfPassedFermions = Count[
    Take[RList, pos[[1]] - 1],
    f_ /; MemberQ[fermions, Head[f]]
  ];
  result = (-1)^numberOfPassedFermions R @@ Delete[RList, pos[[1]]];
result];

b0mAntiHolo[Ra_/;Rtest[Ra]] := Module[{result, RList = List @@ Ra, pos, numberOfPassedFermions},
pos = FirstPosition[RList, ct[1, 0], None];
If[pos === None, Return[0]];
numberOfPassedFermions = Count[
    Take[RList, pos[[1]] - 1],
    f_ /; MemberQ[fermions, Head[f]]
  ];
  result = (-1)^numberOfPassedFermions R @@ Delete[RList, pos[[1]]];
result];

b0m[Ra_/;Rtest[Ra]] := b0mHolo[Ra] - b0mAntiHolo[Ra];
b0m[a_+b_]:=b0m[a] + b0m[b];
b0m[a_ b_]:=a b0m[b]/;(And @@(FreeQ[a,#]&/@ allfields))
b0m[0] := 0;


(* ::Subsection:: *)
(*Define action of PCOs*)


actPCOHolo[Ra_/;Rtest[Ra]] := Module[{result = 0, z, OPEWithPCO, power, PCOList, singularityUpperBound, compositeInPCOPosition},
PCOList = List @@ PCO[z];
Scan[Function[PCOelem,
compositeInPCOPosition = containsCompositeHolo[PCOelem/.{z->0}];
If[compositeInPCOPosition !=  "NotFound",
singularityUpperBound = upperBoundSingularity[singularityMatrix[PCOelem, Ra], compositeInPCOPosition],
singularityUpperBound = upperBoundSingularity[singularityMatrix[PCOelem, Ra], 0]];
If[singularityUpperBound >= 0,
OPEWithPCO = OPE[PCOelem, Ra]//Expand;
Scan[Function[Relem,
power = Exponent[Relem, z];
If[power == 0, result = result + Relem, 
If[power < 0, result = result + TaylorAtOrder[Relem, -power, 0, 0, 0]]];
], If[Head[OPEWithPCO] === Plus, List @@ OPEWithPCO, {OPEWithPCO}]];
];], PCOList];
(result // Expand)/.{z->0}];

actPCOAntiHolo[Ra_/;Rtest[Ra]] := Module[{result = 0, zBar, OPEWithPCO, power, PCOList, singularityUpperBound, compositeInPCOPosition},
PCOList = List @@ PCObar[zBar];
Scan[Function[PCOelem,
compositeInPCOPosition = containsCompositeAntiHolo[PCOelem/.{zBar->0}];
If[compositeInPCOPosition !=  "NotFound",
singularityUpperBound = upperBoundSingularity[singularityMatrix[PCOelem, Ra], compositeInPCOPosition],
singularityUpperBound = upperBoundSingularity[singularityMatrix[PCOelem, Ra], 0]];
If[singularityUpperBound >= 0,
OPEWithPCO = OPE[PCOelem, Ra]//Expand;
Scan[Function[Relem,
power = Exponent[Relem, zBar];
If[power == 0, result = result + Relem, 
If[power < 0, result = result + TaylorAtOrder[Relem, -power, 0, 0, 0]]];
], If[Head[OPEWithPCO] === Plus, List @@ OPEWithPCO, {OPEWithPCO}]];
];], PCOList];
(result // Expand)/.{zBar->0}];

totalHolPicture[Ra_/;Rtest[Ra]]:= Map[pictureHol, List @@ Ra]//Total;
totalAntiHolPicture[Ra_/;Rtest[Ra]]:= Map[pictureAntiHol, List @@ Ra]//Total;

pictureAdjust[Ra_/;Rtest[Ra]]:= Module[{pictureHol = totalHolPicture[Ra], pictureAntiHol = totalAntiHolPicture[Ra]}, 
Nest[actPCOAntiHolo, Nest[actPCOHolo, Ra, Ceiling[Abs[pictureHol]]-1], Ceiling[Abs[pictureAntiHol]]-1]];

actPCOAntiHolo[a_+b_]:=actPCOAntiHolo[a] + actPCOAntiHolo[b];
actPCOAntiHolo[a_ b_]:=a actPCOAntiHolo[b]/;(And @@(FreeQ[a,#]&/@ allfields))
actPCOAntiHolo[0] := 0;
actPCOHolo[a_+b_]:=actPCOHolo[a] + actPCOHolo[b];
actPCOHolo[a_ b_]:=a actPCOHolo[b]/;(And @@(FreeQ[a,#]&/@ allfields))
actPCOHolo[0] := 0;
pictureAdjust[a_+b_]:=pictureAdjust[a] + pictureAdjust[b];
pictureAdjust[a_ b_]:=a pictureAdjust[b]/;(And @@(FreeQ[a,#]&/@ allfields))
pictureAdjust[0] := 0;


(* ::Subsubsection:: *)
(*Determine whether OPE with PCO should be computed*)


containsCompositeHolo[PCOelem_]:= containsCompositeHolo[PCOelem] = First@FirstPosition[PCOelem/.{R->List}, _?(MatchQ[Head[#], exp\[Phi]b | exp\[Phi]f] &)];
containsCompositeAntiHolo[PCOelem_]:= containsCompositeAntiHolo[PCOelem] = First@FirstPosition[PCOelem/.{R->List}, _?(MatchQ[Head[#], exp\[Phi]tb | exp\[Phi]tf] &)];

singularity[dX[\[Mu]_,n_,z_],dX[\[Nu]_,m_,w_]]:= 2 + m + n;
singularity[dXt[\[Mu]_,n_,z_],dXt[\[Nu]_,m_,w_]]:=2 + m + n;
singularity[d\[Phi][n_,z_],d\[Phi][m_,w_]]:= 2 + m + n;
singularity[d\[Phi]t[n_,z_],d\[Phi]t[m_,w_]]:= 2 + m + n;
singularity[b[n_,z_],c[m_,w_]]:= 1 + m + n;
singularity[c[m_,w_],b[n_,z_]]:= 1 + m + n;
singularity[bt[n_,z_],ct[m_,w_]]:= 1 + m + n;
singularity[ct[m_,w_],bt[n_,z_]]:= 1 + m + n;
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

singularity[a_,b_]:= 0 /; (MemberQ[allfields, Head[a]] && MemberQ[allfields, Head[b]]);


singularityMatrix[Ra_/;Rtest[Ra], Rb_/; Rtest[Rb]]:= Table[singularity[Ra[[i]], Rb[[j]]], {i, 1, Length[Ra]}, {j, 1, Length[Rb]}];
singularityMatrix[a_ b_, c_]:= singularityMatrix[b,c]/;(And @@(FreeQ[a,#]&/@ allfields));
singularityMatrix[a_, b_ c_]:= singularityMatrix[a,c]/;(And @@(FreeQ[b,#]&/@ allfields));


(* Upper-bounds singularity given singularityMatrix, gets the position of the exp\[Phi] in PCO, on the corresponding row sums up all its entries
since an exponential can contract multiple times (importantly sums up even the negative value) and then adds the maximum from each other row. 
If there are no two operators in the string field contracting with the same operator in the PCO at the same (maximal) singularity order, the upper bound is saturated. *)
upperBoundSingularity[singularityMatrix_?MatrixQ, compositeRowNumber_] := Module[
  {n = Length[singularityMatrix], total = 0, row, negs},
  Do[
    row = singularityMatrix[[i]];
    negs = Select[row, # < 0 &];
    If[i != compositeRowNumber, total = total + Max[row], total = total + Total[row]],
    {i, n}
  ];
  total
]



(* ::Section:: *)
(*End*)


End[];


EndPackage[];
