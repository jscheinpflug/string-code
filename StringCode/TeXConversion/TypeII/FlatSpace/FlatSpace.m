(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`TeXConversion`TypeII`FlatSpace`"]
Needs["StringCode`TeXConversion`"];
Needs["StringCode`TeXConversion`TypeII`"];
Needs["StringCode`Symbols`TypeII`FlatSpace`"];


(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


formatSpinModePair::usage = "formatSpinModePair[{idx, mode}, opts] formats one spin-mode tuple.";
formatSpinModePair[{idx_, mode_?NumericQ}, opts_Association] :=
  "(" <> formatIndex[idx, opts] <> ", " <> toTeXDispatch[mode, opts] <> ")";
formatSpinModePair[{mode_?NumericQ, idx_}, opts_Association] :=
  "(" <> formatIndex[idx, opts] <> ", " <> toTeXDispatch[mode, opts] <> ")";


formatSpinModes::usage = "formatSpinModes[modes, opts] formats a list of spin-mode tuples.";
formatSpinModes[modes_List, opts_Association] :=
  "[" <> StringJoin[Riffle[formatSpinModePair[#, opts] & /@ modes, ", "]] <> "]";


(* ::Subsection:: *)
(*Free boson conversions*)


(* dX[mu, n, z] -> \partial^{n+1} X^\mu(z) - offset by 1 since dX already has one derivative *)
toTeXDispatch[dX[idx_, n_, z_], opts_Association] :=
  derivativePrefix[n + 1, True] <> "X^{" <> formatIndex[idx, opts] <> "}" <> formatPosition[z, opts];

(* dXt[mu, n, zbar] -> \bar{\partial}^{n+1} X^\mu(zbar) - offset by 1, no bar on X *)
toTeXDispatch[dXt[idx_, n_, zbar_], opts_Association] :=
  derivativePrefix[n + 1, False] <> "X^{" <> formatIndex[idx, opts] <> "}" <> formatPosition[zbar, opts];

(* expX[k, z, zbar] -> e^{i k \cdot X}(z, zbar) *)
toTeXDispatch[expX[k_, z_, zbar_], opts_Association] :=
  "e^{i " <> toTeXDispatch[k, opts] <> " \\cdot X}" <> formatPosition[z, zbar, opts];

(* expXHolo[k, z] -> e^{i k \cdot X}(z) *)
toTeXDispatch[expXHolo[k_, z_], opts_Association] :=
  "e^{i " <> toTeXDispatch[k, opts] <> " \\cdot X}" <> formatPosition[z, opts];

(* expXAntiHolo[k, zbar] -> e^{i k \cdot X}(zbar) *)
toTeXDispatch[expXAntiHolo[k_, zbar_], opts_Association] :=
  "e^{i " <> toTeXDispatch[k, opts] <> " \\cdot X}" <> formatPosition[zbar, opts];

toTeXDispatch[\[Delta][idx1_, idx2_], opts_Association] :=
  "\\delta_{" <> formatIndex[idx1, opts] <> formatIndex[idx2, opts] <> "}";


(* ::Subsection:: *)
(*Profile conversions*)


(* ProfileX[f, {derivs}, z, zbar] -> f(X)(z, zbar) with derivative info *)
toTeXDispatch[ProfileX[profile_, ders_, z_, zbar_], opts_Association] := Module[{derivTeX = ""},
  If[ders =!= {} && ders =!= {0},
    derivTeX = "\\partial_{" <> StringJoin[Riffle[formatIndex[#, opts] & /@ ders, " "]] <> "} "
  ];
  derivTeX <> mathToTeX[profile] <> formatPosition[z, zbar, opts]
];

(* ProfileXHolo[f, {derivs}, z] -> holomorphic profile *)
toTeXDispatch[ProfileXHolo[profile_, ders_, z_], opts_Association] := Module[{derivTeX = ""},
  If[ders =!= {} && ders =!= {0},
    derivTeX = "\\partial_{" <> StringJoin[Riffle[formatIndex[#, opts] & /@ ders, " "]] <> "} "
  ];
  derivTeX <> mathToTeX[profile] <> formatPosition[z, opts]
];

(* ProfileXAntiHolo[f, {derivs}, zbar] -> antiholomorphic profile *)
toTeXDispatch[ProfileXAntiHolo[profile_, ders_, zbar_], opts_Association] := Module[{derivTeX = ""},
  If[ders =!= {} && ders =!= {0},
    derivTeX = "\\bar{\\partial}_{" <> StringJoin[Riffle[formatIndex[#, opts] & /@ ders, " "]] <> "} "
  ];
  derivTeX <> mathToTeX[profile] <> formatPosition[zbar, opts]
];


(* ::Subsection:: *)
(*Free matter fermion conversions*)


(* psi[mu, n, z] -> \partial^n \psi^\mu(z) *)
toTeXDispatch[\[Psi][idx_, n_, z_], opts_Association] :=
  derivativePrefix[n, True] <> "\\psi^{" <> formatIndex[idx, opts] <> "}" <> formatPosition[z, opts];

(* psit[mu, n, zbar] -> \bar{\partial}^n \bar{\psi}^\mu(zbar) *)
toTeXDispatch[\[Psi]t[idx_, n_, zbar_], opts_Association] :=
  derivativePrefix[n, False] <> "\\bar{\\psi}^{" <> formatIndex[idx, opts] <> "}" <> formatPosition[zbar, opts];

(* Spin fields with explicit charge and full mode tuples *)
toTeXDispatch[S[{alpha_, chirality : ("chiral" | "antichiral")}, q_, modes_List, der_, z_], opts_Association] :=
  derivativePrefix[der, True] <> "S^{" <> formatIndex[alpha, opts] <> "}_{" <> toTeXDispatch[q, opts] <> "}" <> formatSpinModes[modes, opts] <> formatPosition[z, opts];

toTeXDispatch[St[{alpha_, chirality : ("chiral" | "antichiral")}, q_, modes_List, der_, zbar_], opts_Association] :=
  derivativePrefix[der, False] <> "\\bar{S}^{" <> formatIndex[alpha, opts] <> "}_{" <> toTeXDispatch[q, opts] <> "}" <> formatSpinModes[modes, opts] <> formatPosition[zbar, opts];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
