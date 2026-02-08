(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Taylor`Bosonic`MinimalModel`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`Bosonic`"];
Needs["StringCode`Symbols`Bosonic`MinimalModel`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`Bosonic`"];
Needs["StringCode`Taylor`"];
Needs["StringCode`Taylor`Bosonic`"];


(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Check if field needs expanding*)


isAtPointHolo[V[n1_, n2_, z_, zbar_], z0_] := SameQ[z,z0];
isAtPointHolo[field_, z0_] := False /; isAntiHolomorphic[Head[field]];

isAtPointAntiHolo[V[n1_, n2_, z_, zbar_], z0bar_] := SameQ[zbar,z0bar];
isAtPointAntiHolo[field_, z0bar_] := False /; isHolomorphic[Head[field]];


(* ::Subsection:: *)
(*Define adding derivatives*)


addHoloDerivatives[V[n1_, n2_, z_, zbar_], ord_, z0_]:= (z-z0)^ord/Factorial[ord]V[n1+ord, n2, z0, zbar];


addAntiHoloDerivatives[V[n1_, n2_, z_, zbar_], ord_, z0_]:= (z-z0)^ord/Factorial[ord]V[n1, n2+ord,z0, zbar];


(* ::Section:: *)
(*End*)


End[];
EndPackage[];
