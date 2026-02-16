(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`TeXConversion`Bosonic`MinimalModel`"]
Needs["StringCode`TeXConversion`"];
Needs["StringCode`TeXConversion`Bosonic`"];
Needs["StringCode`Symbols`Bosonic`MinimalModel`"];


(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Minimal model primary operator*)


(* V[nHolo, nAntiHolo, z, zbar] -> \partial^nHolo \bar{\partial}^nAntiHolo V(z, zbar) *)
toTeXDispatch[V[nHolo_, nAntiHolo_, z_, zbar_], opts_Association] := Module[{holoTeX, antiHoloTeX},
  holoTeX = derivativePrefix[nHolo, True];
  antiHoloTeX = derivativePrefix[nAntiHolo, False];
  holoTeX <> antiHoloTeX <> "V" <> formatPosition[z, zbar, opts]
];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
