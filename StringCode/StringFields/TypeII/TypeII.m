(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`StringFields`TypeII`"];


Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`TypeII`"];


(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


(* ::Input::Initialization:: *)
Begin["Private`"];


(* ::Subsection:: *)
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
positionOp[z0_, z0bar_][\[Eta][n_]]:= \[Eta][n, z0];
positionOp[z0_, z0bar_][\[Xi][n_]]:= \[Xi][n, z0];
positionOp[z0_, z0bar_][\[Psi][\[Mu]_,n_]]:= \[Psi][\[Mu], n, z0];
positionOp[z0_, z0bar_][X[\[Mu]_]]:= X[\[Mu], z0, z0bar];
positionOp[z0_, z0bar_][ProfileX[\[Mu]_, n_]]:= ProfileX[\[Mu],n, z0, z0bar];
positionOp[z0_, z0bar_][dX[\[Mu]_,n_]]:= dX[\[Mu], n, z0];
positionOp[z0_, z0bar_][exp\[Phi]b[n_]]:= exp\[Phi]b[ n, z0];
positionOp[z0_, z0bar_][exp\[Phi]f[n_]]:= exp\[Phi]f[ n, z0];
positionOp[z0_, z0bar_][\[Eta]t[n_]]:= \[Eta]t[n, z0bar];
positionOp[z0_, z0bar_][\[Xi]t[n_]]:= \[Xi]t[n, z0bar];
positionOp[z0_, z0bar_][\[Psi]t[\[Mu]_,n_]]:= \[Psi]t[\[Mu], n, z0bar];
positionOp[z0_, z0bar_][exp\[Phi]tb[n_]]:= exp\[Phi]tb[ n, z0bar];
positionOp[z0_, z0bar_][exp\[Phi]tf[n_]]:= exp\[Phi]tf[ n, z0bar];
positionOp[z0_, z0bar_][dXt[\[Mu]_,n_]]:= dXt[\[Mu], n, z0bar];
positionOp[z0_, z0bar_][expX[n_]]:= expX[n, z0, z0bar];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
