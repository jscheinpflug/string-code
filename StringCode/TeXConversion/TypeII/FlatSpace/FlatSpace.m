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

(* Local helpers - duplicated from TeXConversion since they're in Private context *)
mathToTeX[expr_] := StringReplace[
  ToString[TeXForm[expr]],
  {"$" -> "", "\text{" ~~ x:Shortest[__] ~~ "}" :> x}
];

formatIndex[idx_] := mathToTeX[idx];

derivativePrefix[0, holo_:True] := "";
derivativePrefix[1, True] := "\\partial ";
derivativePrefix[1, False] := "\\bar{\\partial} ";
derivativePrefix[n_, True] := "\\partial^" <> ToString[n] <> " ";
derivativePrefix[n_, False] := "\\bar{\\partial}^" <> ToString[n] <> " ";

formatPosition[0] := "";
formatPosition[0, 0] := "(0)";
formatPosition[z_] := "(" <> mathToTeX[z] <> ")";
formatPosition[z_, zbar_] := "(" <> mathToTeX[z] <> ", " <> mathToTeX[zbar] <> ")";

formatSpinModePair[{mode_, idx_}] := "(" <> mathToTeX[mode] <> ", " <> formatIndex[idx] <> ")";
formatSpinModes[modes_List] := "[" <> StringJoin[Riffle[formatSpinModePair /@ modes, ", "]] <> "]";

(* ::Subsection:: *)
(*Free boson conversions*)


(* dX[mu, n, z] -> \\partial^{n+1} X^\\mu(z) - offset by 1 since dX already has one derivative *)
ToTeX[dX[idx_, n_, z_]] := derivativePrefix[n + 1, True] <> "X^{" <> formatIndex[idx] <> "}" <> formatPosition[z];

(* dXt[mu, n, zbar] -> \\bar{\\partial}^{n+1} X^\\mu(zbar) - offset by 1, no bar on X *)
ToTeX[dXt[idx_, n_, zbar_]] := derivativePrefix[n + 1, False] <> "X^{" <> formatIndex[idx] <> "}" <> formatPosition[zbar];

(* expX[k, z, zbar] -> e^{i k \\cdot X}(z, zbar) *)
ToTeX[expX[k_, z_, zbar_]] := "e^{i " <> ToTeX[k] <> " \\cdot X}" <> formatPosition[z, zbar];

(* expXHolo[k, z] -> e^{i k \\cdot X}(z) - holomorphic part *)
ToTeX[expXHolo[k_, z_]] := "e^{i " <> ToTeX[k] <> " \\cdot X}" <> formatPosition[z];

(* expXAntiHolo[k, zbar] -> e^{i k \\cdot X}(zbar) - antiholomorphic part *)
ToTeX[expXAntiHolo[k_, zbar_]] := "e^{i " <> ToTeX[k] <> " \\cdot X}" <> formatPosition[zbar];


(* ::Subsection:: *)
(*Profile conversions*)


(* ProfileX[f, {derivs}, z, zbar] -> f(X)(z, zbar) with derivative info *)
(* Use mathToTeX for profile to avoid recursion on arbitrary expressions *)
ToTeX[ProfileX[profile_, ders_, z_, zbar_]] := Module[{derivTeX = ""},
  If[ders =!= {} && ders =!= {0},
    derivTeX = "\\partial_{" <> StringJoin[Riffle[formatIndex /@ ders, " "]] <> "} "
  ];
  derivTeX <> mathToTeX[profile] <> formatPosition[z, zbar]
];

(* ProfileXHolo[f, {derivs}, z] -> holomorphic profile *)
ToTeX[ProfileXHolo[profile_, ders_, z_]] := Module[{derivTeX = ""},
  If[ders =!= {} && ders =!= {0},
    derivTeX = "\\partial_{" <> StringJoin[Riffle[formatIndex /@ ders, " "]] <> "} "
  ];
  derivTeX <> mathToTeX[profile] <> formatPosition[z]
];

(* ProfileXAntiHolo[f, {derivs}, zbar] -> antiholomorphic profile *)
ToTeX[ProfileXAntiHolo[profile_, ders_, zbar_]] := Module[{derivTeX = ""},
  If[ders =!= {} && ders =!= {0},
    derivTeX = "\\bar{\\partial}_{" <> StringJoin[Riffle[formatIndex /@ ders, " "]] <> "} "
  ];
  derivTeX <> mathToTeX[profile] <> formatPosition[zbar]
];


(* ::Subsection:: *)
(*Free matter fermion conversions*)


(* psi[mu, n, z] -> \\partial^n \psi^\\mu(z) *)
ToTeX[\[Psi][idx_, n_, z_]] := derivativePrefix[n, True] <> "\\psi^{" <> formatIndex[idx] <> "}" <> formatPosition[z];

(* psit[mu, n, zbar] -> \\bar{\\partial}^n \\bar{\psi}^\\mu(zbar) - barred in antiholomorphic *)
ToTeX[\[Psi]t[idx_, n_, zbar_]] := derivativePrefix[n, False] <> "\\bar{\\psi}^{" <> formatIndex[idx] <> "}" <> formatPosition[zbar];

(* Spin fields with explicit charge and full mode tuples *)
ToTeX[S[alpha_, q_, modes_List, der_, z_]] := derivativePrefix[der, True] <>
  "S^{" <> formatIndex[alpha] <> "}_{" <> mathToTeX[q] <> "}" <> formatSpinModes[modes] <> formatPosition[z];

ToTeX[St[alpha_, q_, modes_List, der_, zbar_]] := derivativePrefix[der, False] <>
  "\\bar{S}^{" <> formatIndex[alpha] <> "}_{" <> mathToTeX[q] <> "}" <> formatSpinModes[modes] <> formatPosition[zbar];


(* Fallbacks - use TeXForm for unknown expressions *)
ToTeX[s_Symbol] := mathToTeX[s];
ToTeX[s_String] := s;
ToTeX[expr_] := mathToTeX[expr] /; !AtomQ[expr];

(* ::Section:: *)
(*End*)


End[];


EndPackage[];
