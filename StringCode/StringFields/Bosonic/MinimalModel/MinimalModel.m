(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`StringFields`Bosonic`MinimalModel`"];


Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`Bosonic`"];
Needs["StringCode`Symbols`Bosonic`MinimalModel`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`Bosonic`"];
Needs["StringCode`StringFields`"];
Needs["StringCode`StringFields`Bosonic`"];


(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


(* ::Input::Initialization:: *)
Begin["Private`"];


(* ::Subsection:: *)
(*Put string field at a position*)


(* ::Input::Initialization:: *)
positionOp[localCoordinateHol_, localCoordinateAntiHol_][V[n1_, n2_]]:= V[n1,n2,  localCoordinateHol[0], localCoordinateAntiHol[0]];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
