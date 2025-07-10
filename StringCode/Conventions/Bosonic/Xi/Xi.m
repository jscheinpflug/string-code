(* ::Package:: *)

BeginPackage["StringCode`Conventions`Bosonic`Xi`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`Bosonic`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`Bosonic`"];
Needs["StringCode`Conventions`Bosonic`"];


(* ::Input:: *)
(**)


Begin["Private`"]
\[Alpha]p = 1;
Tbosonicstring[z_]:=Module[{\[Mu]},-R[dX[\[Mu],0,z],dX[\[Mu],0,z]]-R[b[1,z],c[0,z]]-2R[b[0,z],c[1,z]] ];
jBRSTbosonicstring[z_]:=Module[{\[Mu]},R[c[0,z], -R[dX[\[Mu],0,z],dX[\[Mu],0,z]]]+R[b[0,z],c[0,z],c[1,z]]+3/2R[c[2,z]]]
End[];
EndPackage[];
