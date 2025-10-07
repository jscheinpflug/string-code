(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`StringFields`TypeII`FlatSpace`"];


Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];
Needs["StringCode`Symbols`TypeII`FlatSpace`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`TypeII`"];
Needs["StringCode`StringFields`"];
Needs["StringCode`StringFields`TypeII`"];


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


(* ::Subsubsection:: *)
(*Free boson*)


(* ::Input::Initialization:: *)
positionOp[localCoordinateHol_, localCoordinateAntiHol_][ProfileX[profile_, ders_List]]:= ProfileX[profile,ders, localCoordinateHol[0], localCoordinateAntiHol[0]];
positionOp[localCoordinateHol_, localCoordinateAntiHol_][dX[\[Mu]_,n_]]:= dX[\[Mu], n, localCoordinateHol[0]];
positionOp[localCoordinateHol_, localCoordinateAntiHol_][dXt[\[Mu]_,n_]]:= dXt[\[Mu], n, localCoordinateAntiHol[0]];
positionOp[localCoordinateHol_, localCoordinateAntiHol_][expX[n_]]:= expX[n, localCoordinateHol[0], localCoordinateAntiHol[0]];


(* ::Subsubsection:: *)
(*Free fermion*)


positionOp[localCoordinateHol_, localCoordinateAntiHol_][\[Psi][\[Mu]_,n_]]:= \[Psi][\[Mu], n, localCoordinateHol[0]];
positionOp[localCoordinateHol_, localCoordinateAntiHol_][\[Psi]t[\[Mu]_,n_]]:= \[Psi]t[\[Mu], n, localCoordinateAntiHol[0]];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
