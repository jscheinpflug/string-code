(* ::Package:: *)

BeginPackage["StringCode`Conventions`TypeII`Ashoke`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`TypeII`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];
Needs["StringCode`Conventions`TypeII`"];


Begin["Private`"]
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

jBRSTNoTD[z_]:=R[c[0,z], Tmatter[z]]-R[exp\[Phi]f[1,z],\[Eta][0,z],Gmatter[z]]+R[b[0,z],c[0,z],c[1,z]]+
R[c[0,z],-1/2 R[d\[Phi][0,z],d\[Phi][0,z]]- R[d\[Phi][1,z]]-R[\[Eta][0,z],\[Xi][1,z]]]-1/4R[b[0,z],exp\[Phi]b[2,z],\[Eta][0,z],\[Eta][1,z]];

jBRSTbar[z_]:=R[ct[0,z], Tmatterbar[z]]-R[exp\[Phi]tf[1,z],\[Eta]t[0,z],Gmatterbar[z]]+R[bt[0,z],ct[0,z],ct[1,z]]+
R[ct[0,z],-1/2 R[d\[Phi]t[0,z],d\[Phi]t[0,z]]- R[d\[Phi]t[1,z]]-R[\[Eta]t[0,z],\[Xi]t[1,z]]]-1/4R[bt[0,z],exp\[Phi]tb[2,z],\[Eta]t[0,z],\[Eta]t[1,z]]+ 3/2R[ct[1,z],d\[Phi]t[0,z]]+  3/2R[ct[0,z],d\[Phi]t[1,z]];

jBRSTbarNoTD[z_]:=R[ct[0,z], Tmatterbar[z]]-R[exp\[Phi]tf[1,z],\[Eta]t[0,z],Gmatterbar[z]]+R[bt[0,z],ct[0,z],ct[1,z]]+
R[ct[0,z],-1/2 R[d\[Phi]t[0,z],d\[Phi]t[0,z]]- R[d\[Phi]t[1,z]]-R[\[Eta]t[0,z],\[Xi]t[1,z]]]-1/4R[bt[0,z],exp\[Phi]tb[2,z],\[Eta]t[0,z],\[Eta]t[1,z]];

PCO[z_]:=R[exp\[Phi]f[1,z],Gmatter[z]]+R[c[0,z],\[Xi][1,z]]-1/2R[\[Eta][1,z],exp\[Phi]b[2,z],b[0,z]]-1/4R[\[Eta][0,z],exp\[Phi]b[2,z],b[1,z]]-1/2R[\[Eta][0,z],d\[Phi][0,z],exp\[Phi]b[2,z],b[0,z]]

PCObar[z_]:=R[exp\[Phi]tf[1,z],Gmatterbar[z]]+R[ct[0,z],\[Xi]t[1,z]]-1/2R[\[Eta]t[1,z],exp\[Phi]tb[2,z],bt[0,z]]-1/4R[\[Eta]t[1,z],exp\[Phi]tb[2,z],bt[1,z]]-1/2R[\[Eta]t[1,z],d\[Phi]t[0,z],exp\[Phi]tb[2,z],bt[0,z]]


End[];
EndPackage[];
