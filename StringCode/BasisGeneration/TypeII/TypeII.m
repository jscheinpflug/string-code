(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`BasisGeneration`TypeII`"];


Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`TypeII`"];
Needs["StringCode`BasisGeneration`"];


(* ::Section:: *)
(*Declare public variables and methods*)


generateBasisHolo::usage =
  "generateBasisHolo[weight, ghostNumber, picture, opts] generates holomorphic TypeII basis states as mode tuples.";


generateBasisAntiHolo::usage =
  "generateBasisAntiHolo[weight, ghostNumber, picture, opts] generates antiholomorphic TypeII basis states as mode tuples.";


generateBasis::usage =
  "generateBasis[weight, ghostNumber, {pictureHolo, pictureAntiHolo}, opts] generates {{pictureHolo,pictureAntiHolo}, basisStates}, where each basis state is one joined holo+anti mode list.";


(* ::Section:: *)
(*Logic*)


(* ::Input::Initialization:: *)
Begin["Private`"];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
