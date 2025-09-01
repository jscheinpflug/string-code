(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Operators`"];


Needs["StringCode`Symbols`"];
Needs["StringCode`NormalOrdering`"];


(* ::Section:: *)
(*Declare public variables and methods*)


MultiOp::usage = "A multilocal operator consisting of local operators at different points";


(* ::Section:: *)
(*Logic*)


(* ::Input::Initialization:: *)
Begin["Private`"];


(* ::Subsection:: *)
(*Define MultiOp*)


(* ::Input::Initialization:: *)
MultiOp[c___,a_+b_,d___]:=MultiOp[c,a,d]+MultiOp[c,b,d]
MultiOp[c___,0,d___]:=0
MultiOp[c___, s_?nonOperatorQ f_, d___] := s MultiOp[c, f, d];
MultiOp[c___, s_?nonOperatorQ,   d___] := s MultiOp[c, d];

nonOperatorQ[expr_]:= FreeQ[expr, R];


(* ::Subsection:: *)
(*Test MultiOp and length*)


MultiOptest::usage = "Test if is MultiOp";
MultiOptest[f_]:=(Head[f]==MultiOp)

MultiOplength::usage = "Test if is MultiOp and has nonzero length";
MultiOplength[f_]:=If[MultiOptest[f],Length[List @@ f],0]

MultiOpone::usage = "Test if is MultiOp of length one";
MultiOpone[f_]:=(MultiOplength[f]==1)


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
