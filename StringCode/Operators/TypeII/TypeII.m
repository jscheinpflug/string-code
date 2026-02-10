(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Operators`TypeII`"];


Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`TypeII`"];
Needs["StringCode`Operators`"];


(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


(* ::Input::Initialization:: *)
Begin["Private`"];


(* ::Subsection:: *)
(*Compute total picture of multilocal operator*)


totalHolPicture::usage = "Computes total holomorphic picture";
totalAntiHolPicture::usage = "Computes total antiholomorphic picture";

totalHolPicture[Ma_/;MultiOpTest[Ma]]:= Total[Map[totalHolPicture, List @@ Ma]];
totalHolPicture[Times[a_, Ma_/;MultiOpTest[Ma]]] := totalHolPicture[Ma];

totalAntiHolPicture[Ma_/;MultiOpTest[Ma]]:= Total[Map[totalAntiHolPicture, List @@ Ma]];
totalAntiHolPicture[Times[a_, Ma_/;MultiOpTest[Ma]]] := totalAntiHolPicture[Ma];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
