(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Symbols`Bosonic`MinimalModel`"]
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`Bosonic`"]


(* ::Section:: *)
(*Declare public variables and methods*)


V::usage = "The (1,3) operator in c = 1 + O(1/m) minimal model of total weight 2 + y with y = 2/(m+1)";


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Define symbols*)


DefineField[V,
  "Statistics" -> "Boson",
  "Simple" -> False,
  "Composite" -> False,
  "Holomorphic" -> False,
  "AntiHolomorphic" -> False,
  "Indexed" -> False,
  "Collapsable" -> False,
  "Factorizable" -> False,
  "RegularFermion" -> False,
  "PairsWith" -> {}
];


(* ::Subsection:: *)
(*Define weight of symbols*)


weightSymbolHolo[V] := 1;
weightSymbolAntiHolo[V] := 1;
weightHolo[V[nHolo_, nAntiHolo_, z_, zbar_]] := weightSymbolHolo[V] + nHolo;
weightAntiHolo[V[nHolo_, nAntiHolo_, z_, zbar_]] := weightSymbolAntiHolo[V] + nAntiHolo;


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
