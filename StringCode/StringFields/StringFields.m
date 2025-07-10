(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`StringFields`"];


Needs["StringCode`Symbols`"];
Needs["StringCode`NormalOrdering`"];


(* ::Section:: *)
(*Declare public variables and methods*)


SF::usage = "A string field";
SFAtPos::usage = "A string field at a given position";
SFtest::usage = "Test if is string field";
SFlength::usage = "Test if is string field and has nonzero length";
SFone::usage = "Test if is string field of length one";


(* ::Section:: *)
(*Logic*)


(* ::Input::Initialization:: *)
Begin["Private`"];


(* ::Subsection:: *)
(*Define string fields*)


(* ::Input::Initialization:: *)
SF[c___,b_,a_,d___]:=regcomm[a,b] SF[c,a,b,d]/;(!OrderedQ[{b,a}])
SF[ c___,a_,a_,d___]:=0/;(regparity[a]==1)
SF[c___,a_+b_,d___]:=SF[c,a,d]+SF[c,b,d]
SF[c___,a_ f_,d___]:=a SF[c,f,d]/;(And @@(FreeQ[a,#]&/@ allfields))
SF[c___,a_ ,d___]:=a SF[c,d]/;(And @@(FreeQ[a,#]&/@ allfields))
SF[]:=1
SF[a___,SF[b___],c___]:=SF[a,b,c]
SF[g___,a_ f_,h___]:=SF[g,a,f,h]/;MemberQ[bosons,Head[a]]
SF[g___,a_^n_ f_,h___]:=SF[g,(SF@@ ConstantArray[a,n]),f,h]/;MemberQ[bosons,Head[a]]
SF[g___,a_^n_,h___]:=SF[g,(R @@ ConstantArray[a,n]),h]/;MemberQ[bosons,Head[a]]


(* ::Subsection:: *)
(*Put string field at a position*)


(* ::Input::Initialization:: *)
SFAtPos[SFa_/;SFtest[SFa], z0_, z0bar_]:= Module[{SFlist = List @@ SFa},R @@ Map[positionOp[z0,z0bar],SFlist]];


(* ::Input::Initialization:: *)
positionOp[z0_, z0bar_][b[n_]]:= b[n, z0];
positionOp[z0_, z0bar_][c[n_]]:= c[n, z0];
positionOp[z0_, z0bar_][bt[n_]]:= bt[n, z0bar];
positionOp[z0_, z0bar_][ct[n_]]:= ct[n, z0bar];


(* ::Subsection:: *)
(*Test string field and length*)


SFtest[f_]:=(Head[f]==SF)
SFlength[f_]:=If[SFtest[f],Length[List @@ f],0]
SFone[f_]:=(SFlength[f]==1)


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
