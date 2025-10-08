(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Brackets`TypeII`Flat`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`TypeII`"];
Needs["StringCode`StringFields`"];
Needs["StringCode`StringFields`TypeII`"];
Needs["StringCode`Taylor`"];
Needs["StringCode`Taylor`TypeII`"];
Needs["StringCode`Conventions`TypeII`"];
Needs["StringCode`OPE`"];
Needs["StringCode`Brackets`"];
Needs["StringCode`Brackets`TypeII`"];


(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Define abstract flat n-bracket data*)


flatLocalCoordinate::usage = "Creates i-th holomorphic flat local coordinate";
flatLocalCoordinate[order_, i_][moduli___][w_] := w Symbol["Private`q"][order, i][moduli] + Symbol["Private`z"][order, i][moduli];

flatLocalCoordinateBar::usage = "Creates i-th antiholomorphic flat local coordinate";
flatLocalCoordinateBar[order_, i_][moduli___][wbar_] := wbar Symbol["Private`qbar"][order, i][moduli] + Symbol["Private`zbar"][order, i][moduli];


localCoordinateReplacementElem::usage = "Replaces abstract local coordinates with their actual moduli dependence";
localCoordinateReplacementElem[order_, i_][moduli___]:= {
Symbol["Private`q"][order, i] -> Symbol["Private`q"<> "R"][order, i],
Symbol["Private`z"][order, i] -> Symbol["Private`z" <> "R"][order, i],
Symbol["Private`qbar"][order, i] -> Symbol["Private`qbar" <> "R"][order, i],
Symbol["Private`zbar"][order, i] -> Symbol["Private`zbar" <> "R"][order, i]};


(* ::Subsection:: *)
(*Define abstract n-bracket data*)


getLocalCoordinateData::usage = "Gives local coordinate data for a given number of insertions";
getLocalCoordinateData[order_]:= Module[{abstractLocalCoordinateFunctions, moduli = {}, w, wbar, 
localCoordinateFunctionsHol = {}, localCoordinateFunctionsAntiHol = {},localCoordinateReplacement = {}},

(*Create a list of moduli*)
Do[Module[{t, tbar}, AppendTo[moduli, t]; AppendTo[moduli, tbar]], order - 2];

(*Create local coordinate functions*)
{localCoordinateFunctionsHol, localCoordinateFunctionsAntiHol} = 
Reap[
Do[
Sow[flatLocalCoordinate[order, i][moduli], "Holo"];
Sow[flatLocalCoordinateBar[order, i][moduli], "AntiHolo"];

(*Create local coordinate replacement rule*)
localCoordinateReplacement = Join[localCoordinateReplacement, localCoordinateReplacementElem[order, i] @@ moduli],
{i, 1, order}
]
][[2]];
{localCoordinateFunctionsHol, localCoordinateFunctionsAntiHol, w, wbar, moduli, localCoordinateReplacement}
]


(* ::Subsection:: *)
(*Define flat 2-bracket data*)


Module[{z0, z0bar},
qR[2,1][]:= 1;
qR[2,2][]:= 1;
qbarR[2,1][]:= 1;
qbarR[2,2][]:= 1;
zR[2,1][]:= - z0;
zR[2,2][]:= z0;
zbarR[2,1][]:= - z0bar;
zbarR[2,2][]:= z0bar;
];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
