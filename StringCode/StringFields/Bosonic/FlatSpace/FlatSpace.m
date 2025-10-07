(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`StringFields`Bosonic`FlatSpace`"];


Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`Bosonic`"];
Needs["StringCode`Symbols`Bosonic`FlatSpace`"];
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
positionOp[localCoordinateHol_, localCoordinateAntiHol_][ProfileX[profile_, ders_List]]:= ProfileX[profile,ders, localCoordinateHol[0], localCoordinateAntiHol[0]];
positionOp[localCoordinateHol_, localCoordinateAntiHol_][dX[\[Mu]_,n_]]:= dX[\[Mu], n, localCoordinateHol[0]];
positionOp[localCoordinateHol_, localCoordinateAntiHol_][dXt[\[Mu]_,n_]]:= dXt[\[Mu], n, localCoordinateAntiHol[0]];
positionOp[localCoordinateHol_, localCoordinateAntiHol_][expX[n_]]:= expX[n, localCoordinateHol[0], localCoordinateAntiHol[0]];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
