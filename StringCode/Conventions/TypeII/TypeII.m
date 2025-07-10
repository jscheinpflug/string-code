(* ::Package:: *)

BeginPackage["StringCode`Conventions`TypeII`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`TypeII`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];

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
jBRSTNoTD::usage = "Defines the string theory BRST current without total derivative term";
jBRSTbar::usage = "Defines the string antiholomorphic theory BRST current";
jBRSTbarNoTD::usage = "Defines the string antiholomorphic theory BRST current without total derivative term";
PCO::usage = "Defines the holomorphic PCO";
PCObar::usage = "Defines the antiholomorphic PCO";


Begin["Private`"]


End[];
EndPackage[];
