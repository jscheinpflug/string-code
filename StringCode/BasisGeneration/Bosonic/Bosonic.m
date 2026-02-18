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

generateBasisMatterHolo::usage =
  "generateBasisMatterHolo[weight, z:0] generates holomorphic bosonic matter-only local operators.";

generateBasisMatterAntiHolo::usage =
  "generateBasisMatterAntiHolo[weight, zbar:0] generates antiholomorphic bosonic matter-only local operators.";

generateBasisMatter::usage =
  "generateBasisMatter[weight, z:0] generates holomorphic bosonic matter-only local operators.";

generateBasis::usage =
  "generateBasis[weight, ghostNumber, z:0, zbar:0, opts] generates full bosonic local operators; default option is \"LevelMatched\" -> True.";


(* ::Section:: *)
(*Logic*)


(* ::Input::Initialization:: *)
Begin["Private`"];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
