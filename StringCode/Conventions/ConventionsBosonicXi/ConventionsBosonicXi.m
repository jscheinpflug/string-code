(* ::Package:: *)

BeginPackage["StringCode`Conventions`ConventionsBosonicXi`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`Symbols`"];

\[Alpha]p::usage="Value of \[Alpha] prime";
Tbosonicstring::usage = "Defines the total CFT stress tensor";
jBRSTbosonicstring::usage = "Defines the total string theory BRST current";


\[Alpha]p = 1;
Tbosonicstring[z_]:=Module[{\[Mu]},-R[dX[\[Mu],0,z],dX[\[Mu],0,z]]-R[b[1,z],c[0,z]]-2R[b[0,z],c[1,z]] ];
jBRSTbosonicstring[z_]:=Module[{\[Mu]},R[c[0,z], -R[dX[\[Mu],0,z],dX[\[Mu],0,z]]]+R[b[0,z],c[0,z],c[1,z]]+3/2R[c[2,z]]]


(* ::Input:: *)
(**)


Begin["`Private`"]
End[];
EndPackage[];
