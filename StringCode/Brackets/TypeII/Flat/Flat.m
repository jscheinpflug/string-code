(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Brackets`TypeII`Flat`"];
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
Needs["StringCode`Brackets`TypeII`"];


(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Define flat 2-bracket*)


SFsWithLocalCoordinateData[SFa_/;SFtest[SFa], SFb_/;SFtest[SFb]]:= Module[{z0, z0bar, z1, z1bar, z2, z2bar}, {SFAtPos[SFa, z1, z1bar], SFAtPos[SFb,z2,z2bar], {z1->-z0, z1bar->-z0bar, z2->z0, z2bar -> z0bar}, z0, z0bar}];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
