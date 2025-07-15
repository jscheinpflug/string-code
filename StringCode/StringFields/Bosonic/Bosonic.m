(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`StringFields`Bosonic`"];


Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`Bosonic`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`Bosonic`"];


(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


(* ::Input::Initialization:: *)
Begin["Private`"];


(* ::Subsection:: *)
(*Put string field at a position*)


(* ::Input::Initialization:: *)
positionOp[z0_, z0bar_][X[\[Mu]_]]:= X[\[Mu], z0, z0bar];
positionOp[z0_, z0bar_][ProfileX[\[Mu]_, n_]]:= ProfileX[\[Mu],n, z0, z0bar];
positionOp[z0_, z0bar_][dX[\[Mu]_,n_]]:= dX[\[Mu], n, z0];
positionOp[z0_, z0bar_][dXt[\[Mu]_,n_]]:= dXt[\[Mu], n, z0bar];
positionOp[z0_, z0bar_][expX[n_]]:= expX[n, z0, z0bar];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
