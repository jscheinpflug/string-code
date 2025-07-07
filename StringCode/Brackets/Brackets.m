(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Brackets`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`StringFields`"];
Needs["StringCode`OPE`"];
Needs["StringCode`Taylor`"];


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
powerAntiHol = Exponent[OPEpart,z0bar];
If[RtestUpToConstant[OPEpart],
tayloredOPEpart = If[powerHol<0, 
If[powerAntiHol< 0,TaylorAtOrder[OPEpart,-powerHol, -powerAntiHol,0,0], TaylorAtOrder[OPEpart/.{z0bar->0},-powerHol, 0,0,0]], 
If[powerAntiHol <0, TaylorAtOrder[OPEpart/.{z0->0},0, -powerAntiHol,0,0], OPEpart/.{z0->0,z0bar->0}]]//Expand;
result = result + b0m[tayloredOPEpart];,
0];
],List @@((OPE[SFAtPos[SFa, w0, w0bar], SFAtPos[SFb,z0,z0bar]])/.{w0->-z0,w0bar->-z0bar}//Expand)]; result];


Bracket[a_+b_,c_]:=Bracket[a,c]+Bracket[b,c]
Bracket[a_,b_+c_]:=Bracket[a,b]+Bracket[a,c]
Bracket[a_ b_,c_]:=a Bracket[b,c]/;(And @@(FreeQ[a,#]&/@ allfields))
Bracket[a_,b_ c_]:=b Bracket[a,c]/;(And @@(FreeQ[b,#]&/@ allfields))


(* ::Subsection:: *)
(*Define action of b0^-*)


b0mHolo[Ra_/;Rtest[Ra]] := Module[{result, RList = List @@ Ra, pos, numberOfFermions},
pos = FirstPosition[RList, c[1, 0], None];
If[pos === None, Return[0]];
numberOfFermions = Count[
    Take[RList, pos[[1]] - 1],
    f_ /; MemberQ[fermions, Head[f]]
  ];
  result = (-1)^numberOfFermions R @@ Delete[RList, pos[[1]]];
  result];

b0mAntiHolo[Ra_/;Rtest[Ra]] := Module[{result, RList = List @@ Ra, pos, numberOfFermions},
pos = FirstPosition[RList, ct[1, 0], None];
If[pos === None, Return[0]];
numberOfFermions = Count[
    Take[RList, pos[[1]] - 1],
    f_ /; MemberQ[fermions, Head[f]]
  ];
  result = (-1)^numberOfFermions R @@ Delete[RList, pos[[1]]];
  result];

b0m[Ra_/;Rtest[Ra]] := b0mHolo[Ra] - b0mAntiHolo[Ra];
b0m[a_+b_]:=b0m[a] + b0m[b];
b0m[a_ b_]:=a b0m[b]/;(And @@(FreeQ[a,#]&/@ allfields))
b0m[0] := 0;


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
