(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Operators`"];


Needs["StringCode`Symbols`"];
Needs["StringCode`NormalOrdering`"];


(* ::Section:: *)
(*Declare public variables and methods*)


MultiOp::usage = "A nonlocal operators consisting of local operators at different points";
MultiOptest::usage = "Test if is MultiOp";
MultiOplength::usage = "Test if is MultiOp and has nonzero length";
MultiOpone::usage = "Test if is MultiOp of length one";


(* ::Section:: *)
(*Logic*)


(* ::Input::Initialization:: *)
Begin["Private`"];


(* ::Subsection:: *)
(*Define MultiOp*)


(* ::Input::Initialization:: *)
MultiOp[c___,a_+b_,d___]:=MultiOp[c,a,d]+MultiOp[c,b,d]
MultiOp[c___,0,d___]:=0


(* ::Subsection:: *)
(*Test MultiOp and length*)


MultiOptest[f_]:=(Head[f]==MultiOp)
MultiOplength[f_]:=If[MultiOptest[f],Length[List @@ f],0]
MultiOpone[f_]:=(MultiOplength[f]==1)


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
