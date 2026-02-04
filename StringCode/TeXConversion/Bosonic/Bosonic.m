(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`TeXConversion`Bosonic`"]
Needs["StringCode`TeXConversion`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`Bosonic`"];


(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* Bosonic theory has no additional TeXConversion rules beyond base ghosts *)
(* CFT-specific rules are defined in FlatSpace and MinimalModel submodules *)


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
