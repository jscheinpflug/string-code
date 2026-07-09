(* ::Package:: *)

(* ::Section:: *)
(*Lightcone Conventions for TypeII*)


BeginPackage["StringCode`Conventions`TypeII`Lightcone`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`TypeII`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];
Needs["StringCode`Symbols`TypeII`FlatSpace`"];
Needs["StringCode`Symbols`TypeII`Lightcone`"];
Needs["StringCode`Conventions`TypeII`"];


Begin["Private`"]


(* ::Subsection:: *)
(*Basic parameters*)


\[Alpha]pValue = 1;
fermionToBosonWickRatio = -1/2;


(* ::Subsection:: *)
(*Ghost sector (same as Ashoke)*)


\[Beta]ghost[z_] := R[\[Xi][1, z], exp\[Phi]f[-1, z]];

\[Gamma]ghost[z_] := R[\[Eta][0, z], exp\[Phi]f[1, z]];

\[Delta]\[Beta]ghost[z_] := R[exp\[Phi]f[1, z]];

\[Delta]\[Gamma]ghost[z_] := R[exp\[Phi]f[-1, z]];

Tghost[z_] := -R[b[1, z], c[0, z]] - 2 R[b[0, z], c[1, z]] - 1/2 R[d\[Phi][0, z], d\[Phi][0, z]] - R[d\[Phi][1, z]] - R[\[Eta][0, z], \[Xi][1, z]];

Gghost[z_] := -2 R[c[0, z], exp\[Phi]f[-1, z], \[Xi][2, z]] + 2 R[c[0, z], d\[Phi][0, z], exp\[Phi]f[-1, z], \[Xi][1, z]] - 3 R[c[1, z], exp\[Phi]f[-1, z], \[Xi][1, z]] + R[b[0, z], \[Eta][0, z], exp\[Phi]f[1, z]];


(* ::Subsection:: *)
(*Matter sector - Holomorphic (lightcone indices)*)


(* T_matter = -1/αp η^μν ∂X_μ ∂X_ν + η^μν ψ_μ ∂ψ_ν
   In lightcone: η[p,m] = η[m,p] = -1, transverse uses δT
   Symbolic version: iT is a dummy transverse index with implicit Einstein summation

   Bosonic part: ∂X_p ∂X_m = ∂X_m ∂X_p (commute), so factor of 2 from η^{pm} + η^{mp}
   Fermionic part: ψ_p ∂ψ_m ≠ ψ_m ∂ψ_p (don't commute), so 3 separate terms *)

Tmatter[z_] :=
  (* Bosonic: 2 η[p,m] since ∂X commute *)
  -1/\[Alpha]p (2 \[Eta]LC[p, m] R[dX[p, 0, z], dX[m, 0, z]] + R[dX[iT, 0, z], dX[iT, 0, z]]) +
  (* Fermionic: 3 separate terms *)
  (\[Eta]LC[p, m] R[\[Psi][p, 0, z], \[Psi][m, 1, z]] +
   \[Eta]LC[m, p] R[\[Psi][m, 0, z], \[Psi][p, 1, z]] +
   R[\[Psi][iT, 0, z], \[Psi][iT, 1, z]]);

(* G_matter = -1/√αp η^μν ψ_μ ∂X_ν *)
(* Symbolic version: iT is a dummy transverse index with implicit Einstein summation *)
Gmatter[z_] :=
  -1/Sqrt[\[Alpha]p] (
    \[Eta]LC[p, m] R[\[Psi][p, 0, z], dX[m, 0, z]] +
    \[Eta]LC[m, p] R[\[Psi][m, 0, z], dX[p, 0, z]] +
    R[\[Psi][iT, 0, z], dX[iT, 0, z]]
  );

Ttotal[z_] := Tmatter[z] + Tghost[z];
Gtotal[z_] := Gmatter[z] + Gghost[z];


(* ::Subsection:: *)
(*Ghost sector - Antiholomorphic (same as Ashoke)*)


\[Beta]ghostbar[z_] := R[\[Xi]t[1, z], exp\[Phi]tf[-1, z]];

\[Gamma]ghostbar[z_] := R[\[Eta]t[0, z], exp\[Phi]tf[1, z]];

\[Delta]\[Beta]ghostbar[z_] := R[exp\[Phi]tf[1, z]];

\[Delta]\[Gamma]ghostbar[z_] := R[exp\[Phi]tf[-1, z]];

Tghostbar[z_] := -R[bt[1, z], ct[0, z]] - 2 R[bt[0, z], ct[1, z]] - 1/2 R[d\[Phi]t[0, z], d\[Phi]t[0, z]] - R[d\[Phi]t[1, z]] - R[\[Eta]t[0, z], \[Xi]t[1, z]];

Gghostbar[z_] := -2 R[ct[0, z], exp\[Phi]tf[-1, z], \[Xi]t[2, z]] + 2 R[ct[0, z], d\[Phi]t[0, z], exp\[Phi]tf[-1, z], \[Xi]t[1, z]] - 3 R[ct[1, z], exp\[Phi]tf[-1, z], \[Xi]t[1, z]] + R[bt[0, z], \[Eta]t[0, z], exp\[Phi]tf[1, z]];


(* ::Subsection:: *)
(*Matter sector - Antiholomorphic (lightcone indices)*)


(* Symbolic version: iT is a dummy transverse index with implicit Einstein summation *)
Tmatterbar[z_] :=
  (* Bosonic: 2 η[p,m] since ∂̄X commute *)
  -1/\[Alpha]p (2 \[Eta]LC[p, m] R[dXt[p, 0, z], dXt[m, 0, z]] + R[dXt[iT, 0, z], dXt[iT, 0, z]]) +
  (* Fermionic: 3 separate terms *)
  (\[Eta]LC[p, m] R[\[Psi]t[p, 0, z], \[Psi]t[m, 1, z]] +
   \[Eta]LC[m, p] R[\[Psi]t[m, 0, z], \[Psi]t[p, 1, z]] +
   R[\[Psi]t[iT, 0, z], \[Psi]t[iT, 1, z]]);

(* Symbolic version: iT is a dummy transverse index with implicit Einstein summation *)
Gmatterbar[z_] :=
  -1/Sqrt[\[Alpha]p] (
    \[Eta]LC[p, m] R[\[Psi]t[p, 0, z], dXt[m, 0, z]] +
    \[Eta]LC[m, p] R[\[Psi]t[m, 0, z], dXt[p, 0, z]] +
    R[\[Psi]t[iT, 0, z], dXt[iT, 0, z]]
  );

Ttotalbar[z_] := Tmatterbar[z] + Tghostbar[z];
Gtotalbar[z_] := Gmatterbar[z] + Gghostbar[z];


(* ::Subsection:: *)
(*BRST currents*)


jBRST[z_] := R[c[0, z], Tmatter[z]] - R[exp\[Phi]f[1, z], \[Eta][0, z], Gmatter[z]] + R[b[0, z], c[0, z], c[1, z]] +
  R[c[0, z], -1/2 R[d\[Phi][0, z], d\[Phi][0, z]] - R[d\[Phi][1, z]] - R[\[Eta][0, z], \[Xi][1, z]]] -
  1/4 R[b[0, z], exp\[Phi]b[2, z], \[Eta][0, z], \[Eta][1, z]] + 3/2 R[c[1, z], d\[Phi][0, z]] + 3/2 R[c[0, z], d\[Phi][1, z]];

jBRSTNoTD[z_] := R[c[0, z], Tmatter[z]] - R[exp\[Phi]f[1, z], \[Eta][0, z], Gmatter[z]] + R[b[0, z], c[0, z], c[1, z]] +
  R[c[0, z], -1/2 R[d\[Phi][0, z], d\[Phi][0, z]] - R[d\[Phi][1, z]] - R[\[Eta][0, z], \[Xi][1, z]]] -
  1/4 R[b[0, z], exp\[Phi]b[2, z], \[Eta][0, z], \[Eta][1, z]];

jBRSTbar[z_] := R[ct[0, z], Tmatterbar[z]] - R[exp\[Phi]tf[1, z], \[Eta]t[0, z], Gmatterbar[z]] + R[bt[0, z], ct[0, z], ct[1, z]] +
  R[ct[0, z], -1/2 R[d\[Phi]t[0, z], d\[Phi]t[0, z]] - R[d\[Phi]t[1, z]] - R[\[Eta]t[0, z], \[Xi]t[1, z]]] -
  1/4 R[bt[0, z], exp\[Phi]tb[2, z], \[Eta]t[0, z], \[Eta]t[1, z]] + 3/2 R[ct[1, z], d\[Phi]t[0, z]] + 3/2 R[ct[0, z], d\[Phi]t[1, z]];

jBRSTbarNoTD[z_] := R[ct[0, z], Tmatterbar[z]] - R[exp\[Phi]tf[1, z], \[Eta]t[0, z], Gmatterbar[z]] + R[bt[0, z], ct[0, z], ct[1, z]] +
  R[ct[0, z], -1/2 R[d\[Phi]t[0, z], d\[Phi]t[0, z]] - R[d\[Phi]t[1, z]] - R[\[Eta]t[0, z], \[Xi]t[1, z]]] -
  1/4 R[bt[0, z], exp\[Phi]tb[2, z], \[Eta]t[0, z], \[Eta]t[1, z]];


(* ::Subsection:: *)
(*Picture changing operators*)


PCO[z_] := R[exp\[Phi]f[1, z], Gmatter[z]] + R[c[0, z], \[Xi][1, z]] -
  1/2 R[\[Eta][1, z], exp\[Phi]b[2, z], b[0, z]] - 1/4 R[\[Eta][0, z], exp\[Phi]b[2, z], b[1, z]] -
  1/2 R[\[Eta][0, z], d\[Phi][0, z], exp\[Phi]b[2, z], b[0, z]];

PCObar[z_] := R[exp\[Phi]tf[1, z], Gmatterbar[z]] + R[ct[0, z], \[Xi]t[1, z]] -
  1/2 R[\[Eta]t[1, z], exp\[Phi]tb[2, z], bt[0, z]] - 1/4 R[\[Eta]t[0, z], exp\[Phi]tb[2, z], bt[1, z]] -
  1/2 R[\[Eta]t[0, z], d\[Phi]t[0, z], exp\[Phi]tb[2, z], bt[0, z]];


End[];
EndPackage[];
