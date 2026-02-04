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

(* Local helpers - duplicated from TeXConversion since they're in Private context *)
mathToTeX[expr_] := StringReplace[
  ToString[TeXForm[expr]],
  {"$" -> "", "\text{" ~~ x:Shortest[__] ~~ "}" :> x}
];

derivativePrefix[0, holo_:True] := "";
derivativePrefix[1, True] := "\\partial ";
derivativePrefix[1, False] := "\\bar{\\partial} ";
derivativePrefix[n_, True] := "\\partial^" <> ToString[n] <> " ";
derivativePrefix[n_, False] := "\\bar{\\partial}^" <> ToString[n] <> " ";

formatPosition[0] := "";
formatPosition[0, 0] := "(0)";
formatPosition[z_] := "(" <> mathToTeX[z] <> ")";
formatPosition[z_, zbar_] := "(" <> mathToTeX[z] <> ", " <> mathToTeX[zbar] <> ")";

(* ::Subsection:: *)
(*Linear dilaton conversions*)


(* dPhi[n, z] -> \\partial^{n+1} \phi(z) - offset by 1 since dPhi already has one derivative *)
ToTeX[d\[Phi][n_, z_]] := derivativePrefix[n + 1, True] <> "\\phi" <> formatPosition[z];

(* dPhit[n, zbar] -> \\bar{\\partial}^{n+1} \phi(zbar) - offset by 1, no bar on phi (boson) *)
ToTeX[d\[Phi]t[n_, zbar_]] := derivativePrefix[n + 1, False] <> "\\phi" <> formatPosition[zbar];


(* ::Subsection:: *)
(*Superghost conversions*)


(* xi[n, z] -> \\partial^n \xi(z) *)
ToTeX[\[Xi][n_, z_]] := derivativePrefix[n, True] <> "\\xi" <> formatPosition[z];

(* xit[n, zbar] -> \\bar{\\partial}^n \\bar{\xi}(zbar) - barred in antiholomorphic *)
ToTeX[\[Xi]t[n_, zbar_]] := derivativePrefix[n, False] <> "\\bar{\\xi}" <> formatPosition[zbar];

(* eta[n, z] -> \\partial^n \eta(z) *)
ToTeX[\[Eta][n_, z_]] := derivativePrefix[n, True] <> "\\eta" <> formatPosition[z];

(* etat[n, zbar] -> \\bar{\\partial}^n \\bar{\eta}(zbar) - barred in antiholomorphic *)
ToTeX[\[Eta]t[n_, zbar_]] := derivativePrefix[n, False] <> "\\bar{\\eta}" <> formatPosition[zbar];


(* ::Subsection:: *)
(*Exponential phi conversions*)


(* expPhif[exp, z] -> e^{exp \phi}(z) - fermionic *)
ToTeX[exp\[Phi]f[exp_, z_]] := "e^{" <> ToTeX[exp] <> " \\phi}" <> formatPosition[z];

(* expPhib[exp, z] -> e^{exp \phi}(z) - bosonic (same TeX as fermionic) *)
ToTeX[exp\[Phi]b[exp_, z_]] := "e^{" <> ToTeX[exp] <> " \\phi}" <> formatPosition[z];

(* expPhitf[exp, zbar] -> e^{exp \phi}(zbar) - antiholomorphic fermionic *)
ToTeX[exp\[Phi]tf[exp_, zbar_]] := "e^{" <> ToTeX[exp] <> " \\phi}" <> formatPosition[zbar];

(* expPhitb[exp, zbar] -> e^{exp \phi}(zbar) - antiholomorphic bosonic *)
ToTeX[exp\[Phi]tb[exp_, zbar_]] := "e^{" <> ToTeX[exp] <> " \\phi}" <> formatPosition[zbar];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
