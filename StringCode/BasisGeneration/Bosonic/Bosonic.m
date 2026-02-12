(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`BasisGeneration`Bosonic`"];


Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`Bosonic`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`Bosonic`"];
Needs["StringCode`BasisGeneration`"];


(* ::Section:: *)
(*Declare public variables and methods*)

generateBasisHolo::usage =
  "generateBasisHolo[weight, ghostNumber, z:0] generates holomorphic bosonic local operators.";

generateBasisAntiHolo::usage =
  "generateBasisAntiHolo[weight, ghostNumber, zbar:0] generates antiholomorphic bosonic local operators.";

generateBasis::usage =
  "generateBasis[weight, ghostNumber, z:0, zbar:0, opts] generates full bosonic local operators; default option is \"LevelMatched\" -> True.";

generateBasisLevelMatched::usage =
  "generateBasisLevelMatched[weight, ghostNumber, z:0, zbar:0] generates full bosonic local operators with equal holomorphic and antiholomorphic weights.";


(* ::Section:: *)
(*Logic*)


(* ::Input::Initialization:: *)
Begin["Private`"];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
