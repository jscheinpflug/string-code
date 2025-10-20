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
mapOp[coordinateHol_, coordinateAntiHol_][ProfileX[profile_, ders_List, z_, zbar_]]:= ProfileX[profile,ders, coordinateHol[z], coordinateAntiHol[zbar]];
mapOp[coordinateHol_, coordinateAntiHol_][dX[\[Mu]_,n_, z_]]:= dX[\[Mu], n, coordinateHol[z]];
mapOp[coordinateHol_, coordinateAntiHol_][dXt[\[Mu]_,n_, zbar_]]:= dXt[\[Mu], n, coordinateAntiHol[zbar]];
mapOp[coordinateHol_, coordinateAntiHol_][expX[n_, z_, zbar_]]:= expX[n, coordinateHol[z], coordinateAntiHol[zbar]];


(* ::Subsubsection:: *)
(*Free fermion*)


mapOp[coordinateHol_, coordinateAntiHol_][\[Psi][\[Mu]_,n_, z_]]:= \[Psi][\[Mu], n, coordinateHol[z]];
mapOp[cordinateHol_, coordinateAntiHol_][\[Psi]t[\[Mu]_,n_, zbar_]]:= \[Psi]t[\[Mu], n, coordinateAntiHol[zbar]];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
