(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Symbols`Bosonic`"]
Needs["StringCode`Symbols`"];


(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Define ghost numbers*)


ghostNumberHolo[a_/;isField[Head[a]]]:= 0;
ghostNumberAntiHolo[a_/;isField[Head[a]]]:= 0;


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
