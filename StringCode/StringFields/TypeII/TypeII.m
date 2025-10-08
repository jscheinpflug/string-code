(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`StringFields`TypeII`"];


Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`TypeII`"];
Needs["StringCode`StringFields`"];


(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


(* ::Input::Initialization:: *)
Begin["Private`"];


(* ::Subsection::Closed:: *)
(*Define string fields*)


(* ::Input::Initialization:: *)
SF[ c___,a_,a_,d___]:=SF[c,exp\[Phi]b[2a[[1]]],d]/;(Head[a]==exp\[Phi]f)
SF[ c___,a_,a_,d___]:=SF[c,exp\[Phi]tb[2a[[1]]],d]/;(Head[a]==exp\[Phi]tf)
SF[ c___,a_,b_,d___]:=SF[c,exp\[Phi]b[a[[1]]+b[[1]]],d]/;(Head[a]==exp\[Phi]f && Head[b]==exp\[Phi]f)
SF[ c___,a_,b_,d___]:=SF[c,exp\[Phi]tb[a[[1]]+b[[1]]],d]/;(Head[a]==exp\[Phi]tf && Head[b]==exp\[Phi]tf)
SF[ c___,a_,b_,d___]:=SF[c,exp\[Phi]f[a[[1]]+b[[1]]],d]/;(Head[a]==exp\[Phi]b && Head[b]==exp\[Phi]f)
SF[ c___,a_,b_,d___]:=SF[c,exp\[Phi]tf[a[[1]]+b[[1]]],d]/;(Head[a]==exp\[Phi]tb && Head[b]==exp\[Phi]tf)


(* ::Subsection:: *)
(*Put string field at a position*)


(* ::Input::Initialization:: *)
mapOp[coordinateHol_, coordinateAntiHol_][\[Eta][n_, z_]]:= \[Eta][n, coordinateHol[z]];
mapOp[coordinateHol_, coordinateAntiHol_][\[Xi][n_, z_]]:= \[Xi][n, coordinateHol[z]];
mapOp[coordinateHol_, coordinateAntiHol_][exp\[Phi]b[n_, z_]]:= exp\[Phi]b[n, coordinateHol[z]];
mapOp[coordinateHol_, coordinateAntiHol_][exp\[Phi]f[n_, z_]]:= exp\[Phi]f[n, coordinateHol[z]];
mapOp[coordinateHol_, coordinateAntiHol_][\[Eta]t[n_, zbar_]]:= \[Eta]t[n, coordinateAntiHol[zbar]];
mapOp[coordinateHol_, coordinateAntiHol_][\[Xi]t[n_, zbar_]]:= \[Xi]t[n, coordinateAntiHol[zbar]];
mapOp[coordinateHol_, coordinateAntiHol_][exp\[Phi]tb[n_, zbar_]]:= exp\[Phi]tb[n, coordinateAntiHol[zbar]];
mapOp[coordinateHol_, coordinateAntiHol_][exp\[Phi]tf[n_, zbar_]]:= exp\[Phi]tf[n, coordinateAntiHol[zbar]];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
