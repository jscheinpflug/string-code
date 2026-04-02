(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`TeXConversion`TypeII`Lightcone`"]
Needs["StringCode`TeXConversion`"];
Needs["StringCode`TeXConversion`TypeII`"];
Needs["StringCode`Symbols`TypeII`FlatSpace`"];
Needs["StringCode`Symbols`TypeII`Lightcone`"];


(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Lightcone index formatting*)


(* Format lightcone indices as + and - *)
formatLightconeIndex[p, opts_Association] := "+";
formatLightconeIndex[m, opts_Association] := "-";
formatLightconeIndex[i_Integer, opts_Association] /; transverseIndexQ[i] := ToString[i];
(* Symbolic transverse indices (i, j, etc.) are formatted as their symbol name *)
formatLightconeIndex[idx_Symbol, opts_Association] /; transverseIndexQ[idx] := ToString[idx];
formatLightconeIndex[idx_, opts_Association] := formatIndex[idx, opts];


(* ::Subsection:: *)
(*Lightcone metric TeX conversion*)


toTeXDispatch[\[Eta][idx1_, idx2_], opts_Association] :=
  "\\eta_{" <> formatLightconeIndex[idx1, opts] <> formatLightconeIndex[idx2, opts] <> "}";


toTeXDispatch[\[Delta]T[idx1_, idx2_], opts_Association] :=
  "\\delta^T_{" <> formatLightconeIndex[idx1, opts] <> formatLightconeIndex[idx2, opts] <> "}";


(* ::Subsection:: *)
(*Free boson conversions with lightcone indices*)


(* dX[p, n, z] -> \partial^{n+1} X^+(z) *)
toTeXDispatch[dX[p, n_, z_], opts_Association] :=
  derivativePrefix[n + 1, True] <> "X^{+}" <> formatPosition[z, opts];

toTeXDispatch[dX[m, n_, z_], opts_Association] :=
  derivativePrefix[n + 1, True] <> "X^{-}" <> formatPosition[z, opts];

toTeXDispatch[dX[i_Integer, n_, z_], opts_Association] /; transverseIndexQ[i] :=
  derivativePrefix[n + 1, True] <> "X^{" <> ToString[i] <> "}" <> formatPosition[z, opts];

toTeXDispatch[dX[i_Symbol, n_, z_], opts_Association] /; transverseIndexQ[i] :=
  derivativePrefix[n + 1, True] <> "X^{" <> ToString[i] <> "}" <> formatPosition[z, opts];

(* dXt with lightcone indices *)
toTeXDispatch[dXt[p, n_, zbar_], opts_Association] :=
  derivativePrefix[n + 1, False] <> "X^{+}" <> formatPosition[zbar, opts];

toTeXDispatch[dXt[m, n_, zbar_], opts_Association] :=
  derivativePrefix[n + 1, False] <> "X^{-}" <> formatPosition[zbar, opts];

toTeXDispatch[dXt[i_Integer, n_, zbar_], opts_Association] /; transverseIndexQ[i] :=
  derivativePrefix[n + 1, False] <> "X^{" <> ToString[i] <> "}" <> formatPosition[zbar, opts];

toTeXDispatch[dXt[i_Symbol, n_, zbar_], opts_Association] /; transverseIndexQ[i] :=
  derivativePrefix[n + 1, False] <> "X^{" <> ToString[i] <> "}" <> formatPosition[zbar, opts];


(* ::Subsection:: *)
(*Free matter fermion conversions with lightcone indices*)


(* psi[p, n, z] -> \partial^n \psi^+(z) *)
toTeXDispatch[\[Psi][p, n_, z_], opts_Association] :=
  derivativePrefix[n, True] <> "\\psi^{+}" <> formatPosition[z, opts];

toTeXDispatch[\[Psi][m, n_, z_], opts_Association] :=
  derivativePrefix[n, True] <> "\\psi^{-}" <> formatPosition[z, opts];

toTeXDispatch[\[Psi][i_Integer, n_, z_], opts_Association] /; transverseIndexQ[i] :=
  derivativePrefix[n, True] <> "\\psi^{" <> ToString[i] <> "}" <> formatPosition[z, opts];

toTeXDispatch[\[Psi][i_Symbol, n_, z_], opts_Association] /; transverseIndexQ[i] :=
  derivativePrefix[n, True] <> "\\psi^{" <> ToString[i] <> "}" <> formatPosition[z, opts];

(* psit with lightcone indices *)
toTeXDispatch[\[Psi]t[p, n_, zbar_], opts_Association] :=
  derivativePrefix[n, False] <> "\\bar{\\psi}^{+}" <> formatPosition[zbar, opts];

toTeXDispatch[\[Psi]t[m, n_, zbar_], opts_Association] :=
  derivativePrefix[n, False] <> "\\bar{\\psi}^{-}" <> formatPosition[zbar, opts];

toTeXDispatch[\[Psi]t[i_Integer, n_, zbar_], opts_Association] /; transverseIndexQ[i] :=
  derivativePrefix[n, False] <> "\\bar{\\psi}^{" <> ToString[i] <> "}" <> formatPosition[zbar, opts];

toTeXDispatch[\[Psi]t[i_Symbol, n_, zbar_], opts_Association] /; transverseIndexQ[i] :=
  derivativePrefix[n, False] <> "\\bar{\\psi}^{" <> ToString[i] <> "}" <> formatPosition[zbar, opts];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
