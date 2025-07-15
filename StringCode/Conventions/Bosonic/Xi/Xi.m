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
Tbosonicstringbar[zbar_]:=Module[{\[Mu]},-R[dXt[\[Mu],0,zbar],dXt[\[Mu],0,zbar]]-R[bt[1,zbar],ct[0,zbar]]-2R[bt[0,zbar],ct[1,zbar]] ];
jBRSTbosonicstring[z_]:=Module[{\[Mu]},R[c[0,z], -R[dX[\[Mu],0,z],dX[\[Mu],0,z]]]+R[b[0,z],c[0,z],c[1,z]]+3/2R[c[2,z]]];
jBRSTbosonicstringbar[zbar_]:=Module[{\[Mu]},R[ct[0,zbar], -R[dXt[\[Mu],0,zbar],dXt[\[Mu],0,zbar]]]+R[bt[0,zbar],ct[0,zbar],ct[1,zbar]]+3/2R[ct[2,zbar]]]
End[];
EndPackage[];
