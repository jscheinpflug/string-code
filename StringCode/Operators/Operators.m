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


MultiOp[c___,a_+b_,d___]:=MultiOp[c,a,d]+MultiOp[c,b,d]
MultiOp[c___,0,d___]:=0
MultiOp[c___, s_?nonOperatorQ f_, d___] := s MultiOp[c, f, d];
MultiOp[c___, s_?nonOperatorQ,   d___] := s MultiOp[c, d];

MultiOp[x___, MultiOp[y___], z___] := MultiOp[x, y, z]

nonOperatorQ[expr_]:= FreeQ[expr, R];


(* ::Subsection:: *)
(*Define parity of MultiOp and R*)


parityOp::usage = "Computes the parity of a local operator";
scalarQ[x_] := FreeQ[x, _MultiOp | _R]
parityOp[expr_Times] := parityOp[SelectFirst[List @@ expr, !scalarQ[#] &]]

parityOp[Ma_/;MultiOpTest[Ma]]:= Mod[Total @ (parityOp /@ List @@ Ma),2];
parityOp[Ra_/;RTest[Ra]]:= Mod[parity[Ra],2];


(* ::Subsection:: *)
(*Define weight of operators*)


totalWeightHolo::usage = "Computes total holomorphic weight of a normal-ordered product";
totalWeightAntiHolo::usage = "Computes total holomorphic weight of a normal-ordered product";
totalWeight::usage = "Computes total weight of a normal-ordered product";

totalWeightHolo[Times[a_, MultiOpa_/;MultiOpTest[MultiOpa]]] := totalWeightHolo[MultiOpa];
totalWeightHolo[MultiOpa_/;MultiOpTest[MultiOpa]] := Total[Map[totalWeightHolo, List @@ MultiOpa]];

totalWeightAntiHolo[Times[a_, MultiOpa_/;MultiOpTest[MultiOpa]]] := totalWeightAntiHolo[MultiOpa];
totalWeightAntiHolo[MultiOpa_/;MultiOpTest[MultiOpa]] := Total[Map[totalWeightAntiHolo, List @@ MultiOpa]];

totalWeightHolo[a_/;NumericQ[a]]:=0;
totalWeightAntiHolo[a_/;NumericQ[a]]:=0;

totalWeight[Times[a_, MultiOpa_/;MultiOpTest[MultiOpa]]] := totalWeight[MultiOpa];
totalWeight[MultiOpa_/;MultiOpTest[MultiOpa]] := {totalWeightHolo[MultiOpa], totalWeightAntiHolo[MultiOpa]};

totalWeight[a_/;NumericQ[a]]:=0;


(* ::Subsection:: *)
(*Test MultiOp and length*)


MultiOpTest::usage = "Test if is MultiOp";
MultiOpTest[f_]:=(Head[f]===MultiOp)

MultiOpLength::usage = "Test if is MultiOp and has nonzero length";
MultiOpLength[f_]:=If[MultiOpTest[f],Length[List @@ f],0]

MultiOpOne::usage = "Test if is MultiOp of length one";
MultiOpOne[f_]:=(MultiOpLength[f]===1)


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
