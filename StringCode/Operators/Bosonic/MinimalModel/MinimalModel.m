(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Operators`Bosonic`MinimalModel`"];


Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`Bosonic`"];
Needs["StringCode`Symbols`Bosonic`MinimalModel`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`Bosonic`"];
Needs["StringCode`Operators`"];
Needs["StringCode`Operators`Bosonic`"];


(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Place operators at a position*)


placeOp[coordinateHol_, coordinateAntiHol_][V[n1_, n2_, z_, zbar_]]:= V[n1, n2, coordinateHol[z], coordinateAntiHol[zbar]];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
