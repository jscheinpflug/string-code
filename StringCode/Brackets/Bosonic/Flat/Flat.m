(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Brackets`Bosonic`Flat`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`Bosonic`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`Bosonic`"];
Needs["StringCode`StringFields`"];
Needs["StringCode`StringFields`Bosonic`"];
Needs["StringCode`Taylor`"];
Needs["StringCode`Taylor`Bosonic`"];
Needs["StringCode`Conventions`Bosonic`"];
Needs["StringCode`OPE`"];
Needs["StringCode`Brackets`"];


(* ::Section:: *)
(*Declare public variables and methods*)


Bracket::usage = "Computes the flat string bracket";


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
