(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Brackets`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`StringFields`"];
Needs["StringCode`OPE`"];
Needs["StringCode`Taylor`"];
Needs["StringCode`Conventions`ConventionsIIBXi`"];


(* ::Section:: *)
(*Declare public variables and methods*)


Bracket::usage = "Computes the flat string bracket";


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


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


actPCOHolo[Ra_/;Rtest[Ra]] := Module[{result = 0, z, OPEWithPCO, power},
OPEWithPCO = OPE[PCO[z], Ra]//Expand;
Scan[Function[Relem,
power = Exponent[Relem, z];
If[power == 0, result = result + Relem, 
If[power < 0, result = result + TaylorAtOrder[Relem, -power, 0, 0, 0]]];
], List @@ OPEWithPCO];
(result // Expand)/.{z->0}];

actPCOAntiHolo[Ra_/;Rtest[Ra]] := Module[{result = 0, zBar, OPEWithPCObar, power},
OPEWithPCObar = OPE[PCObar[zBar], Ra]//Expand;
Scan[Function[Relem,
power = Exponent[Relem, zBar];
If[power == 0, result = result + Relem, 
If[power < 0, result = result + TaylorAtOrder[Relem, 0, -power, 0, 0]]];
], List @@ OPEWithPCObar];
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


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
