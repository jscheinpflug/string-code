(* ::Package:: *)

BeginPackage["StringCode`"]


InitStringCode::usage = "InitStringCode[conventions] initializes StringCode with a given set of conventions";


DeclarePackage["StringCode`Symbols`",
{"expX", "dX", "dXt","d\[Phi]", "d\[Phi]t","exp\[Phi]b","exp\[Phi]tb", "exp\[Phi]f","exp\[Phi]tf","b","bt","c","ct","\[Xi]", "\[Xi]t","\[Eta]","\[Eta]t","\[Psi]","\[Psi]t", "bosons", "fermions", "allfields","regfermions","exp\[Phi]fermions","exp\[Phi]tfermions",
"simplefields", "simplefieldsnotc","compositefields","Contract","ContractDelta", "ProfileX"}];
DeclarePackage["StringCode`NormalOrdering`", {"R", "CR","Rtest","Rlength","Rone","parity","exp\[Phi]parity","exp\[Phi]tparity","regparity","regcomm"}];
DeclarePackage["StringCode`Wick`", {"Wick", "SWick","MWick","DWick","CDWick","pairing", "dot"}];
DeclarePackage["StringCode`OPE`", {"OPE"}];
DeclarePackage["StringCode`Taylor`", {"Taylor", "TaylorAtOrder", "Polar"}];
DeclarePackage["StringCode`Correlators`", {"Corr", "Vev"}];
DeclarePackage["StringCode`Conventions`ConventionsIIBXi`", {"\[Alpha]p", "fermionToBosonWickRatio", "\[Beta]ghost","\[Gamma]ghost",
"\[Delta]\[Beta]ghost","\[Delta]\[Gamma]ghost","\[Beta]ghostbar","\[Gamma]ghostbar","\[Delta]\[Beta]ghostbar","\[Delta]\[Gamma]ghostbar","Tmatter","Gmatter","Tghost","Gghost","Ttotal","Gtotal",
"Tmatterbar","Gmatterbar","Tghostbar","Gghostbar","Ttotalbar","Gtotalbar",
"jBRST","PCO","PCObar"}];
DeclarePackage["StringCode`Conventions`ConventionsIIBAshoke`",{"\[Alpha]p", "fermionToBosonWickRatio", "\[Beta]ghost","\[Gamma]ghost",
"\[Delta]\[Beta]ghost","\[Delta]\[Gamma]ghost","\[Beta]ghostbar","\[Gamma]ghostbar","\[Delta]\[Beta]ghostbar","\[Delta]\[Gamma]ghostbar","Tmatter","Gmatter","Tghost","Gghost","Ttotal","Gtotal",
"Tmatterbar","Gmatterbar","Tghostbar","Gghostbar","Ttotalbar","Gtotalbar",
"jBRST","PCO","PCObar"}];
DeclarePackage["StringCode`Conventions`ConventionsBosonicXi`", {"\[Alpha]P", "Tbosonicstring","jBRSTbosonicstring"}];


Begin["`Private`"];
InitStringCode[options_] := Module[{conventionsContext="", conventionValue = options["conventions"]},
Switch[conventionValue, 
"IIB-Xi", conventionsContext = "StringCode`Conventions`ConventionsIIBXi`",
"IIB-Ashoke", conventionsContext = "StringCode`Conventions`ConventionsIIBAshoke`",
"Bosonic-Xi", conventionsContext = "StringCode`Conventions`ConventionsBosonicXi`",
_, Print["There are no such conventions"]];
Scan[
  (AppendTo[$ContextPath, #] &) ,
  {
    "StringCode`Symbols`",
    "StringCode`NormalOrdering`",
    "StringCode`Wick`",
    "StringCode`OPE`",
    "StringCode`Correlators`",
    "StringCode`Taylor`",
    conventionsContext
  }
]];
End[];
EndPackage[];
