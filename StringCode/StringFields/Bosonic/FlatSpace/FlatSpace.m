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
mapOp[coordinateHol_, coordinateAntiHol_][ProfileX[profile_, ders_List, z_, zbar_]]:= ProfileX[profile,ders, coordinateHol[z], coordinateAntiHol[zbar]];
mapOp[coordinateHol_, coordinateAntiHol_][dX[\[Mu]_,n_, z_]]:= dX[\[Mu], n, coordinateHol[z]];
mapOp[coordinateHol_, coordinateAntiHol_][dXt[\[Mu]_,n_, zbar_]]:= dXt[\[Mu], n, coordinateAntiHol[zbar]];
mapOp[coordinateHol_, coordinateAntiHol_][expX[n_, z_, zbar_]]:= expX[n, coordinateHol[z], coordinateAntiHol[zbar]];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
