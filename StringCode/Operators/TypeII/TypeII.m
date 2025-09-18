(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Operators`TypeII`"];


Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`TypeII`"];


(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


(* ::Input::Initialization:: *)
Begin["Private`"];


(* ::Subsection:: *)
(*Compute total picture of holomorphic operator;*)


totalHolPicture::usage = "Computes total holomorphic picture";
totalAntiHolPicture::usage = "Computes total antiholomorphic picture";

totalHolPicture[Oa_/;OpTest[Oa]]:= Join[Map[pictureHol, List @@ Oa[[1]]], pictureHol @@ Oa[[2]]]//Total;
totalHolPicture[Times[a_, Oa_/;OpTest[Oa]]] := totalHolPicture[Oa];

totalAntiHolPicture[Oa_/;OpTest[Oa]]:= Join[Map[pictureAntiHol, List @@ Oa[[1]]], pictureAntiHol @@ Oa[[2]]]//Total;
totalAntiHolPicture[Times[a_, Oa_/;OpTest[Oa]]] := totalAntiHolPicture[Oa];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
