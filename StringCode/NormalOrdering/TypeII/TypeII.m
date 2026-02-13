(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`NormalOrdering`TypeII`"];


Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];
Needs["StringCode`NormalOrdering`"]


(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Define Grassmann parity*)


regcomm::usage = "Give Grassmann sign under commutation";
regcomm[f_,g_]:=(-1)^(parity[f] parity[g])(-1)^(exp\[Phi]parity[f] exp\[Phi]parity[g])(-1)^(exp\[Phi]tparity[f] exp\[Phi]tparity[g])

exp\[Phi]parity::usage = "Compute Grassmann parity of exp\[Phi]";
containsExpPhiHoloFermionQ[expr_] := !FreeQ[expr, field_ /; fieldProperty[field, "ExpPhiFermionFamily"] === "Holo"];
exp\[Phi]parity[f_]:=0/;!containsExpPhiHoloFermionQ[f]
exp\[Phi]parity[f_]:=1/;containsExpPhiHoloFermionQ[f]
exp\[Phi]parity[R[f__,g__]]:=Mod[exp\[Phi]parity[R[f]]+exp\[Phi]parity[R[g]],2]
exp\[Phi]parity[R[f_]]:=exp\[Phi]parity[f]

exp\[Phi]tparity::usage = "Compute Grassmann parity of exp\[Phi]t";
containsExpPhiAntiHoloFermionQ[expr_] := !FreeQ[expr, field_ /; fieldProperty[field, "ExpPhiFermionFamily"] === "AntiHolo"];
exp\[Phi]tparity[f_]:=0/;!containsExpPhiAntiHoloFermionQ[f]
exp\[Phi]tparity[f_]:=1/;containsExpPhiAntiHoloFermionQ[f]
exp\[Phi]tparity[R[f__,g__]]:=Mod[exp\[Phi]tparity[R[f]]+exp\[Phi]tparity[R[g]],2]
exp\[Phi]tparity[R[f_]]:=exp\[Phi]tparity[f]


(* ::Subsection::Closed:: *)
(*Define normal-ordered product*)


R[ c___,a_,a_,d___]:=R[c,exp\[Phi]b[2a[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]f)
R[ c___,a_,a_,d___]:=R[c,exp\[Phi]tb[2a[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]tf)
R[ c___,a_,b_,d___]:=R[c,exp\[Phi]b[a[[1]]+b[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]b && Head[b]==exp\[Phi]b && a[[2]]==b[[2]])
R[ c___,a_,b_,d___]:=R[c,exp\[Phi]tb[a[[1]]+b[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]tb && Head[b]==exp\[Phi]tb && a[[2]]==b[[2]])
R[ c___,a_,b_,d___]:=R[c,exp\[Phi]b[a[[1]]+b[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]f && Head[b]==exp\[Phi]f && a[[2]]==b[[2]])
R[ c___,a_,b_,d___]:=R[c,exp\[Phi]tb[a[[1]]+b[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]tf && Head[b]==exp\[Phi]tf && a[[2]]==b[[2]])
R[ c___,a_,b_,d___]:=R[c,exp\[Phi]f[a[[1]]+b[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]b && Head[b]==exp\[Phi]f && a[[2]]==b[[2]])
R[ c___,a_,b_,d___]:=R[c,exp\[Phi]tf[a[[1]]+b[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]tb && Head[b]==exp\[Phi]tf && a[[2]]==b[[2]])

(* ::Subsection:: *)
(*Define total picture number*)


totalHolPicture::usage = "Computes total holomorphic picture";
totalAntiHolPicture::usage = "Computes total antiholomorphic picture";

totalHolPicture[Ra_/;RTest[Ra]]:= Map[pictureHol, List @@ Ra]//Total;
totalHolPicture[Times[a_, Ra_/;RTest[Ra]]] := totalHolPicture[Ra];

totalAntiHolPicture[Ra_/;RTest[Ra]]:= Map[pictureAntiHol, List @@ Ra]//Total;
totalAntiHolPicture[Times[a_, Ra_/;RTest[Ra]]] := totalAntiHolPicture[Ra];

GSOParity[Ra_/;RTest[Ra]]:= Times @@ Map[GSOParity, List @@ Ra];
GSOParity[Times[a_, Ra_/;RTest[Ra]]] := GSOParity[Ra];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
