(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`TeXConversion`Bosonic`MinimalModel`"]
Needs["StringCode`TeXConversion`"];
Needs["StringCode`TeXConversion`Bosonic`"];
Needs["StringCode`Symbols`Bosonic`MinimalModel`"];


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
(*Minimal model primary operator*)


(* V[nHolo, nAntiHolo, z, zbar] -> \\partial^nHolo \\bar{\\partial}^nAntiHolo V(z, zbar) *)
ToTeX[V[nHolo_, nAntiHolo_, z_, zbar_]] := Module[{holoTeX, antiHoloTeX},
  holoTeX = derivativePrefix[nHolo, True];
  antiHoloTeX = derivativePrefix[nAntiHolo, False];
  holoTeX <> antiHoloTeX <> "V" <> formatPosition[z, zbar]
];


(* Fallbacks - use TeXForm for unknown expressions *)
ToTeX[s_Symbol] := mathToTeX[s];
ToTeX[s_String] := s;
ToTeX[expr_] := mathToTeX[expr] /; !AtomQ[expr];

(* ::Section:: *)
(*End*)


End[];


EndPackage[];
