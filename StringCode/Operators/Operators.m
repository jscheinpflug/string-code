(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Operators`"];


Needs["StringCode`Symbols`"];
Needs["StringCode`NormalOrdering`"];


(* ::Section:: *)
(*Declare public variables and methods*)


MultiOp::usage = "A nonlocal operators consisting of local operators at different points"


(* ::Section:: *)
(*Logic*)


(* ::Input::Initialization:: *)
Begin["Private`"];


(* ::Subsection:: *)
(*Define MultiOp*)


(* ::Input::Initialization:: *)
MultiOp[c___,b_,a_,d___]:=regcomm[a,b] MultiOp[c,a,b,d]/;(!OrderedQ[{b,a}])
MultiOp[ c___,a_,a_,d___]:=0/;(regparity[a]==1)
MultiOp[c___,a_+b_,d___]:=MultiOp[c,a,d]+MultiOp[c,b,d]
MultiOp[c___,a_ f_,d___]:=a MultiOp[c,f,d]/;(And @@(FreeQ[a,#]&/@ allfields))
MultiOp[c___,a_ ,d___]:=a MultiOp[c,d]/;(And @@(FreeQ[a,#]&/@ allfields))


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
