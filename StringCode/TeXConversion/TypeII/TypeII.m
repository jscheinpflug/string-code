(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`TeXConversion`TypeII`"]
Needs["StringCode`TeXConversion`"];
Needs["StringCode`Symbols`TypeII`"];


(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Linear dilaton conversions*)


(* dPhi[n, z] -> \partial^{n+1} \phi(z) - offset by 1 since dPhi already has one derivative *)
toTeXDispatch[d\[Phi][n_, z_], opts_Association] :=
  derivativePrefix[n + 1, True] <> "\\phi" <> formatPosition[z, opts];

(* dPhit[n, zbar] -> \bar{\partial}^{n+1} \phi(zbar) - offset by 1, no bar on phi (boson) *)
toTeXDispatch[d\[Phi]t[n_, zbar_], opts_Association] :=
  derivativePrefix[n + 1, False] <> "\\phi" <> formatPosition[zbar, opts];


(* ::Subsection:: *)
(*Superghost conversions*)


(* xi[n, z] -> \partial^n \xi(z) *)
toTeXDispatch[\[Xi][n_, z_], opts_Association] :=
  derivativePrefix[n, True] <> "\\xi" <> formatPosition[z, opts];

(* xit[n, zbar] -> \bar{\partial}^n \bar{\xi}(zbar) *)
toTeXDispatch[\[Xi]t[n_, zbar_], opts_Association] :=
  derivativePrefix[n, False] <> "\\bar{\\xi}" <> formatPosition[zbar, opts];

(* eta[n, z] -> \partial^n \eta(z) *)
toTeXDispatch[\[Eta][n_, z_], opts_Association] :=
  derivativePrefix[n, True] <> "\\eta" <> formatPosition[z, opts];

(* etat[n, zbar] -> \bar{\partial}^n \bar{\eta}(zbar) *)
toTeXDispatch[\[Eta]t[n_, zbar_], opts_Association] :=
  derivativePrefix[n, False] <> "\\bar{\\eta}" <> formatPosition[zbar, opts];

(* beta[n, z] -> \partial^n \beta(z) *)
toTeXDispatch[\[Beta][n_, z_], opts_Association] :=
  derivativePrefix[n, True] <> "\\beta" <> formatPosition[z, opts];

(* betat[n, zbar] -> \bar{\partial}^n \bar{\beta}(zbar) *)
toTeXDispatch[\[Beta]t[n_, zbar_], opts_Association] :=
  derivativePrefix[n, False] <> "\\bar{\\beta}" <> formatPosition[zbar, opts];

(* gamma[n, z] -> \partial^n \gamma(z) *)
toTeXDispatch[\[Gamma][n_, z_], opts_Association] :=
  derivativePrefix[n, True] <> "\\gamma" <> formatPosition[z, opts];

(* gammat[n, zbar] -> \bar{\partial}^n \bar{\gamma}(zbar) *)
toTeXDispatch[\[Gamma]t[n_, zbar_], opts_Association] :=
  derivativePrefix[n, False] <> "\\bar{\\gamma}" <> formatPosition[zbar, opts];


(* ::Subsection:: *)
(*Exponential phi conversions*)


(* expPhif[exp, z] -> e^{exp \phi}(z) *)
toTeXDispatch[exp\[Phi]f[exp_, z_], opts_Association] :=
  "e^{" <> toTeXDispatch[exp, opts] <> " \\phi}" <> formatPosition[z, opts];

(* expPhib[exp, z] -> e^{exp \phi}(z) *)
toTeXDispatch[exp\[Phi]b[exp_, z_], opts_Association] :=
  "e^{" <> toTeXDispatch[exp, opts] <> " \\phi}" <> formatPosition[z, opts];

(* expPhitf[exp, zbar] -> e^{exp \phi}(zbar) *)
toTeXDispatch[exp\[Phi]tf[exp_, zbar_], opts_Association] :=
  "e^{" <> toTeXDispatch[exp, opts] <> " \\phi}" <> formatPosition[zbar, opts];

(* expPhitb[exp, zbar] -> e^{exp \phi}(zbar) *)
toTeXDispatch[exp\[Phi]tb[exp_, zbar_], opts_Association] :=
  "e^{" <> toTeXDispatch[exp, opts] <> " \\phi}" <> formatPosition[zbar, opts];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
