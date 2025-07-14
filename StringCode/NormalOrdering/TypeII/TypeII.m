(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`NormalOrdering`TypeII`"];


Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];
Needs["StringCode`NormalOrdering`"]


(* ::Section:: *)
(*Declare public variables and methods*)


exp\[Phi]parity::usage = "Define Grassmann parity for holomorphic exponentials of \[Phi]";
exp\[Phi]tparity::usage = "Define Grassmann parity for antiholomorphic exponentials of \[Phi]";


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Define Grassmann parity*)


regcomm[f_,g_]:=(-1)^(parity[f] parity[g])(-1)^(exp\[Phi]parity[f] exp\[Phi]parity[g])(-1)^(exp\[Phi]tparity[f] exp\[Phi]tparity[g])


exp\[Phi]parity[f_]:=0/;(And @@(FreeQ[f,#]&/@ exp\[Phi]fermions))
exp\[Phi]parity[f_]:=1/;(!(And @@(FreeQ[f,#]&/@ exp\[Phi]fermions)))
exp\[Phi]parity[R[f__,g__]]:=Mod[exp\[Phi]parity[R[f]]+exp\[Phi]parity[R[g]],2]
exp\[Phi]parity[R[f_]]:=exp\[Phi]parity[f]


exp\[Phi]tparity[f_]:=0/;(And @@(FreeQ[f,#]&/@ exp\[Phi]tfermions))
exp\[Phi]tparity[f_]:=1/;(!(And @@(FreeQ[f,#]&/@ exp\[Phi]tfermions)))
exp\[Phi]tparity[R[f__,g__]]:=Mod[exp\[Phi]tparity[R[f]]+exp\[Phi]tparity[R[g]],2]
exp\[Phi]tparity[R[f_]]:=exp\[Phi]tparity[f]


(* ::Subsection:: *)
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
(*Define CR*)


CR[ c___,a_,a_,d___]:=CR[c,exp\[Phi]b[2a[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]f)
CR[ c___,a_,a_,d___]:=CR[c,exp\[Phi]tb[2a[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]tf)
CR[ c___,a_,b_,d___]:=CR[c,exp\[Phi]b[a[[1]]+b[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]f && Head[b]==exp\[Phi]f && a[[2]]==b[[2]])
CR[ c___,a_,b_,d___]:=CR[c,exp\[Phi]tb[a[[1]]+b[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]tf && Head[b]==exp\[Phi]tf && a[[2]]==b[[2]])
CR[ c___,a_,b_,d___]:=CR[c,exp\[Phi]f[a[[1]]+b[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]b && Head[b]==exp\[Phi]f && a[[2]]==b[[2]])
CR[ c___,a_,b_,d___]:=CR[c,exp\[Phi]tf[a[[1]]+b[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]tb && Head[b]==exp\[Phi]tf && a[[2]]==b[[2]])


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
