(* ::Package:: *)

BeginPackage["StringCode`Conventions`ConventionsIIBAshoke`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`Symbols`"];

\[Alpha]p::usage="Value of \[Alpha] prime";
fermionToBosonWickRatio::usage ="Defines the ratio of coefficients in  partial X partial X and psi psi OPEs";

\[Beta]ghost::usage = "Defines the holomorphic \[Beta]-ghost";
\[Gamma]ghost::usage = "Defines the holomorphic \[Gamma]-ghost";
\[Delta]\[Beta]ghost::usage = "Defines the holomorphic delta distribution of the \[Beta]-ghost";
\[Delta]\[Gamma]ghost::usage = "Defines the holomorphic delta distribution of the \[Gamma]-ghost";

\[Beta]ghostbar::usage = "Defines the antiholomorphic \[Beta]-ghost";
\[Gamma]ghostbar::usage = "Defines the antiholomorphic \[Gamma]-ghost";
\[Delta]\[Beta]ghostbar::usage = "Defines the antiholomorphic delta distribution of the \[Beta]-ghost";
\[Delta]\[Gamma]ghostbar::usage = "Defines the antiholomorphic delta distribution of the \[Gamma]-ghost";

Tmatter::usage = "Defines the holomorphic matter CFT stress tensor";
Gmatter::usage = "Defines the holomorphic matter CFT supercurrent";
Tghost::usage = "Defines the holomorphic ghost CFT stress tensor";
Gghost::usage = "Defines the holomorphic ghost CFT supercurrent";
Ttotal::usage = "Defines the total holomorphic CFT stress tensor";
Gtotal::usage = "Defines the total holomorphic CFT supercurrent";

Tmatterbar::usage = "Defines the antiholomorphic matter CFT stress tensor";
Gmatterbar::usage = "Defines the antiholomorphic matter CFT supercurrent";
Tghostbar::usage = "Defines the antiholomorphic ghost CFT stress tensor";
Gghostbar::usage = "Defines the antiholomorphic ghost CFT supercurrent";
Ttotalbar::usage = "Defines the total antiholomorphic CFT stress tensor";
Gtotalbar::usage = "Defines the total antiholomorphic CFT supercurrent";
jBRST::usage = "Defines the string theory BRST current";
PCO::usage = "Defines the holomorphic PCO";
PCObar::usage = "Defines the antiholomorphic PCO";


Begin["`Private`"]
\[Alpha]p = 1;
fermionToBosonWickRatio = -1/2;

\[Beta]ghost[z_]:=R[\[Xi][1,z],exp\[Phi]f[-1,z]];

\[Gamma]ghost[z_]:=R[\[Eta][0,z],exp\[Phi]f[1,z]];

\[Delta]\[Beta]ghost[z_]:=R[exp\[Phi]f[1,z]];

\[Delta]\[Gamma]ghost[z_]:=R[exp\[Phi]f[-1,z]];

Tmatter[z_]:=Module[{\[Mu]},-R[dX[\[Mu],0,z],dX[\[Mu],0,z]] + R[\[Psi][\[Mu],0,z],\[Psi][\[Mu],1,z]]];

Gmatter[z_]:=Module[{\[Mu]},-R[\[Psi][\[Mu],0,z],dX[\[Mu],0,z]]];

Tghost[z_]:=-R[b[1,z],c[0,z]]-2R[b[0,z],c[1,z]] -1/2 R[d\[Phi][0,z],d\[Phi][0,z]]- R[d\[Phi][1,z]]-R[\[Eta][0,z],\[Xi][1,z]];

Gghost[z_]:=-2 R[c[0,z],exp\[Phi]f[-1,z],\[Xi][2,z]]+2 R[c[0,z],d\[Phi][0,z],exp\[Phi]f[-1,z],\[Xi][1,z]]-3 R[c[1,z],exp\[Phi]f[-1,z],\[Xi][1,z]]+R[b[0,z],\[Eta][0,z],exp\[Phi]f[1,z]];

Ttotal[z_]:=Tmatter[z]+Tghost[z];
Gtotal[z_]:=Gmatter[z]+Gghost[z];


\[Beta]ghostbar[z_]:=R[\[Xi]t[1,z],exp\[Phi]tf[-1,z]];

\[Gamma]ghostbar[z_]:=R[\[Eta]t[0,z],exp\[Phi]tf[1,z]];

\[Delta]\[Beta]ghostbar[z_]:=R[exp\[Phi]tf[1,z]];

\[Delta]\[Gamma]ghostbar[z_]:=R[exp\[Phi]tf[-1,z]];

Tmatterbar[z_]:=Module[{\[Mu]},-R[dXt[\[Mu],0,z],dXt[\[Mu],0,z]] +R[\[Psi]t[\[Mu],0,z],\[Psi]t[\[Mu],1,z]]];

Gmatterbar[z_]:=Module[{\[Mu]},-R[\[Psi]t[\[Mu],0,z],dXt[\[Mu],0,z]]];

Tghostbar[z_]:=-R[bt[1,z],ct[0,z]]-2R[bt[0,z],ct[1,z]] -1/2 R[d\[Phi]t[0,z],d\[Phi]t[0,z]]- R[d\[Phi]t[1,z]]-R[\[Eta]t[0,z],\[Xi]t[1,z]];

Gghostbar[z_]:=-2 R[ct[0,z],exp\[Phi]tf[-1,z],\[Xi]t[2,z]]+2 R[ct[0,z],d\[Phi]t[0,z],exp\[Phi]tf[-1,z],\[Xi]t[1,z]]-3 R[ct[1,z],exp\[Phi]tf[-1,z],\[Xi]t[1,z]]+R[bt[0,z],\[Eta]t[0,z],exp\[Phi]tf[1,z]];

Ttotalbar[z_]:=Tmatterbar[z]+Tghostbar[z];
Gtotalbar[z_]:=Gmatterbar[z]+Gghostbar[z];

jBRST[z_]:=R[c[0,z], Tmatter[z]]-R[exp\[Phi]f[1,z],\[Eta][0,z],Gmatter[z]]+R[b[0,z],c[0,z],c[1,z]]+
R[c[0,z],-1/2 R[d\[Phi][0,z],d\[Phi][0,z]]- R[d\[Phi][1,z]]-R[\[Eta][0,z],\[Xi][1,z]]]-1/4R[b[0,z],exp\[Phi]b[2,z],\[Eta][0,z],\[Eta][1,z]]+ 3/2R[c[1,z],d\[Phi][0,z]]+  3/2R[c[0,z],d\[Phi][1,z]];

PCO[z_]:=R[exp\[Phi]f[1,z],Gmatter[z]]+R[c[0,z],\[Xi][1,z]]-1/2R[\[Eta][1,z],exp\[Phi]b[2,z],b[0,z]]-1/4R[\[Eta][0,z],exp\[Phi]b[2,z],b[1,z]]-1/2R[\[Eta][0,z],d\[Phi][0,z],exp\[Phi]b[2,z],b[0,z]]

PCObar[z_]:=R[exp\[Phi]tf[1,z],Gmatterbar[z]]+R[ct[0,z],\[Xi]t[1,z]]-1/2R[\[Eta]t[1,z],exp\[Phi]tb[2,z],bt[0,z]]-1/4R[\[Eta]t[1,z],exp\[Phi]tb[2,z],bt[1,z]]-1/2R[\[Eta]t[1,z],d\[Phi]t[0,z],exp\[Phi]tb[2,z],bt[0,z]]


End[];
EndPackage[];
