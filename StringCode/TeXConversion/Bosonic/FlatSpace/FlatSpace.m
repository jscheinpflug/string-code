(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`TeXConversion`Bosonic`FlatSpace`"]
Needs["StringCode`TeXConversion`"];
Needs["StringCode`TeXConversion`Bosonic`"];
Needs["StringCode`Symbols`Bosonic`FlatSpace`"];


(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


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


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
