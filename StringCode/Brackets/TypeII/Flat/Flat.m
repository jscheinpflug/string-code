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


Begin["Private`"];


(* ::Subsection:: *)
(*Define abstract flat n-bracket data*)


flatLocalCoordinate[i_][w_][moduli___] := w Symbol["Private`q" <> ToString[i]][moduli] + Symbol["Private`z" <> ToString[i]][moduli];


flatLocalCoordinateBar[i_][wbar_][moduli___] := wbar Symbol["Private`qbar" <> ToString[i]][moduli] + Symbol["Private`zbar" <> ToString[i]][moduli];


localCoordinateReplacementElem[i_][moduli___]:= {
Symbol["Private`q" <> ToString[i]] -> Symbol["Private`q" <> ToString[i] <> "R"],
Symbol["Private`z" <> ToString[i]] -> Symbol["Private`z" <> ToString[i] <> "R"],
Symbol["Private`qbar" <> ToString[i]] -> Symbol["Private`qbar" <> ToString[i] <> "R"],
Symbol["Private`zbar" <> ToString[i]] -> Symbol["Private`zbar" <> ToString[i] <> "R"]};


(* ::Subsection:: *)
(*Define abstract n-bracket data*)


getLocalCoordinateData[order_]:= Module[{abstractLocalCoordinateFunctions, moduli = {}, w, wbar, 
localCoordinateFunctionsHol = {}, localCoordinateFunctionsAntiHol = {},localCoordinateReplacement = {}},
Do[Module[{t, tbar}, AppendTo[moduli, t]; AppendTo[moduli, tbar]], order - 2];
{localCoordinateFunctionsHol, localCoordinateFunctionsAntiHol} = 
Reap[Do[
  Sow[flatLocalCoordinate[i][w] @@ moduli, "Holo"];
  Sow[flatLocalCoordinateBar[i][wbar] @@ moduli, "AntiHolo"];
  localCoordinateReplacement = Join[localCoordinateReplacement, localCoordinateReplacementElem[i] @@ moduli],
  {i, 1, order}
  ]][[2]];
{localCoordinateFunctionsHol, localCoordinateFunctionsAntiHol, w, wbar, moduli, localCoordinateReplacement}
]


(* ::Subsection:: *)
(*Define flat 2-bracket data*)


Module[{z0, z0bar},
q1R[]:= 1;
q2R[]:= 1;
qbar1R[]:= 1;
qbar2R[]:= 1;
z1R[]:= - z0;
z2R[]:= z0;
zbar1R[]:= - z0bar;
zbar2R[]:= z0bar;
];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
