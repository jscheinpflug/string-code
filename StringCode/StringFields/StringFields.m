(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`StringFields`"];


Needs["StringCode`Symbols`"];
Needs["StringCode`NormalOrdering`"];


(* ::Section:: *)
(*Declare public variables and methods*)


SF::usage = "A string field";


(* ::Section:: *)
(*Logic*)


(* ::Input::Initialization:: *)
Begin["Private`"];


(* ::Subsection:: *)
(*Define string fields*)


SF[c___,b_,a_,d___]:=regcomm[a,b] SF[c,a,b,d]/;(!OrderedQ[{b,a}])
SF[ c___,a_,a_,d___]:=0/;(regparity[a]==1)
SF[c___,a_+b_,d___]:=SF[c,a,d]+SF[c,b,d]
SF[c___,a_ f_,d___]:=a SF[c,f,d]/;(And @@(FreeQ[a,#]&/@ allOperators))
SF[c___,a_ ,d___]:=a SF[c,d]/;(And @@(FreeQ[a,#]&/@ allOperators))
SF[]:=1
SF[a___,SF[b___],c___]:=SF[a,b,c]
SF[g___,a_ f_,h___]:=SF[g,a,f,h]/;MemberQ[bosons,Head[a]]
SF[g___,a_^n_ f_,h___]:=SF[g,(SF@@ ConstantArray[a,n]),f,h]/;MemberQ[bosons,Head[a]]
SF[g___,a_^n_,h___]:=SF[g,(R @@ ConstantArray[a,n]),h]/;MemberQ[bosons,Head[a]]


(* ::Subsection:: *)
(*Put string field at a position*)


SFAtPos::usage = "A string field at a given position";
SFAtPos[SFa_/;SFtest[SFa], z0_, z0bar_]:= Module[{SFlist = List @@ SFa, positionedSFs, SplitSFs, sign}, 
positionedSFs = Map[positionOp[z0,z0bar],SFlist];
SplitSFs = splitOperators[positionedSFs, isField, isInteracting];
sign = factorizationSign[positionedSFs, isField, isInteracting];
sign Op[R @@ SplitSFs[[1]]][Interacting @@ SplitSFs[[2]]]
];


positionOp::usage = "Place operator at a given position";

positionOp[z0_, z0bar_][b[n_]]:= b[n, z0];
positionOp[z0_, z0bar_][c[n_]]:= c[n, z0];
positionOp[z0_, z0bar_][bt[n_]]:= bt[n, z0bar];
positionOp[z0_, z0bar_][ct[n_]]:= ct[n, z0bar];


(* ::Subsection:: *)
(*Factorize a list of operators according to two boolean valued functions*)


splitOperators::usage = "Factorize list of operators into groups given by two boolean valued functions f1, f2";
splitOperators[operatorList_, f1_, f2_] := Module[{operators1, operators2},
   operators1 = Select[operatorList, f1 @* Head];
   operators2 = Select[operatorList, f2 @* Head];
   {operators1, operators2}
   ];

fermionPositions::usage = "Gives positions of fermions graded by two boolean-valued functions f1, f2 defined on symbols";
fermionPositions[operatorList__, f1_, f2_]:= Module[{result, operatorListLength = Length[operatorList], operatorListElem}, 
result = Flatten[Reap[Do[
operatorListElem = Head[operatorList[[i]]];
If[f1[operatorListElem] && isFermion[operatorListElem],
Sow[i, "1"];];
If[f2[operatorListElem] && isFermion[operatorListElem],
Sow[i, "2"];]
, {i,1,operatorListLength}], {"1", "2"}][[2]],1];
result
]
 
factorizationSign::usage = "Collect a possible sign that arises when factorizing a list of operators";
factorizationSign[operatorList__, f1_, f2_] :=
 Module[{fermionPositionLists = fermionPositions[operatorList, f1, f2], swaps, totalSwaps, sign},
  If[Length[fermionPositionLists]== 2,
  swaps = Outer[Boole[#2 < #1] &, fermionPositionLists[[1]], fermionPositionLists[[2]]];
  totalSwaps = Total[swaps, 2];
  sign = (-1)^totalSwaps;,
  sign = 1;];
  sign
  ]


(* ::Subsection:: *)
(*Test string field and length*)


SFtest::usage = "Test if is string field";
SFtest[f_]:=(Head[f]==SF)

SFlength::usage = "Test if is string field and has nonzero length";
SFlength[f_]:=If[SFtest[f],Length[List @@ f],0]

SFone::usage = "Test if is string field of length one";
SFone[f_]:=(SFlength[f]==1)


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
