(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Operators`"];


Needs["StringCode`Symbols`"];
Needs["StringCode`NormalOrdering`"];


(* ::Section:: *)
(*Declare public variables and methods*)


MultiOp::usage = "A multilocal operator consisting of local operators at different points";
Op::usage = "A local operator";
Interacting::usage = "Wrapper for interacting operators";


(* ::Section:: *)
(*Logic*)


(* ::Input::Initialization:: *)
Begin["Private`"];


(* ::Subsection::Closed:: *)
(*Define MultiOp*)


MultiOp[c___,a_+b_,d___]:=MultiOp[c,a,d]+MultiOp[c,b,d]
MultiOp[c___,0,d___]:=0
MultiOp[c___, s_?nonOperatorQ f_, d___] := s MultiOp[c, f, d];
MultiOp[c___, s_?nonOperatorQ,   d___] := s MultiOp[c, d];

MultiOp[x___, MultiOp[y___], z___] := MultiOp[x, y, z]

nonOperatorQ[expr_]:= FreeQ[expr, R] && FreeQ[expr, Interacting];


(* ::Subsection:: *)
(*Define Op*)


Op[a_ + b_, c___]:= Op[a, c] + Op[b, c];
Op[a___, b_ + c_]:= Op[a, b] + Op[a, c];
Op[0, a___]:= 0;
Op[a___, 0]:= 0;
Op[a_ f__?(Not[Rtest[#]] & ), b_]:= f Op[a, b];
Op[a_, b_ f__?(Not[InteractingTest[#]] &)]:= f Op[a, b];
Op[a_/;Not[Rtest[a]], b_]:= a b;
Op[a_, b_/;Not[InteractingTest[b]]]:= a b;
Op[1,1]:= 1;


(* ::Subsubsection:: *)
(*Define Interacting*)


Interacting[c___,b_,a_,d___]:=regcomm[a,b] Interacting[c,a,b,d]/;(!OrderedQ[{b,a}])
Interacting[ c___,a_,a_,d___]:=0/;(regparity[a]==1)


Interacting[c___,a_+b_,d___]:=Interacting[c,a,d]+Interacting[c,b,d]
Interacting[a___,Interacting[b___],c___]:= Interacting[a,b,c]
Interacting[c___, s_?nonInteractingQ f_, d___] := s Interacting[c, f, d];
Interacting[c___, s_?nonInteractingQ, d___] := s Interacting[c, d];
Interacting[]:=1

nonInteractingQ[expr_]:= !isInteracting[Head[expr]];


Interacting[g___,a_ f_,h___]:=Interacting[g,a,f,h]/;MemberQ[bosons,Head[a]]
Interacting[g___,a_^n_ f_,h___]:=Interacting[g,(Interacting @@ ConstantArray[a,n]),f,h]/;isBoson[Head[a]]
Interacting[g___,a_^n_,h___]:=Interacting[g,(Interacting @@ ConstantArray[a,n]),h]/;isBoson[Head[a]]


(* ::Subsubsection:: *)
(*Define tests of properties of Interacting*)


InteractingTest::usage = "Test if is interacting";
InteractingTest[f_]:=(Head[f]===Interacting)

InteractingLength::usage = "Test if is interacting and has nonzero length";
InteractingLength[f_]:=If[Interactingtest[f],Length[List @@ f],0]

InteractingOne::usage = "Test if is interacting of length one";
Interactingone[f_]:=(InteractingLength[f]==1)


InteractingTestUpToConstant::usage = "Test if product is interacting up to a constant prefactor";

InteractingTestUpToConstant[c___,a_ f_,d___]:=RtestUpToConstant[c,f,d]/;(And @@(FreeQ[a,#]&/@ interactingOperators))
InteractingTestUpToConstant[c___,a_ ,d___]:= RtestUpToConstant[c,d]/;(And @@(FreeQ[a,#]&/@ interactingOperators))
InteractingTestUpToConstant[f_]:=InteractingTest[f];
InteractingTestUpToConstant[]:=False;


(* ::Subsection:: *)
(*Define parity of Op*)


parityOp::usage = "Computes the parity of a local operator";
parityOp[op_/;OpTest[op]]:= Mod[parity[op[[1]]] + parity[op[[2]]],2];
parityOp[Ra_/;Rtest[Ra]]:= Mod[parity[Ra],2];
parityOp[Ia_/;InteractingTest[Ia]]:= Mod[parity[Ia],2];


(* ::Subsection:: *)
(*Define weight of Interacting operators*)


totalWeightHolo::usage = "Computes total holomorphic weight of a normal-ordered product";
totalWeightAntiHolo::usage = "Computes total holomorphic weight of a normal-ordered product";
totalWeight::usage = "Computes total weight of a normal-ordered product";

totalWeightHolo[Times[a_, Ia_/;InteractingTest[Ia]]] := totalWeightHolo[Ia];
totalWeightHolo[Ia_/;InteractingTest[Ia]] := Map[weightHolo, List @@ Ia] // Total;

totalWeightAntiHolo[Times[a_, Ia_/;InteractingTest[Ia]]] := totalWeightAntiHolo[Ia];
totalWeightAntiHolo[Ia_/;InteractingTest[Ia]] := Map[weightAntiHolo, List @@ Ia] // Total;

totalWeight[Times[a_, Ia_/;InteractingTest[Ia]]] := totalWeight[Ia];
totalWeight[Ia_/;InteractingTest[Ia]] := {totalWeightHolo[Ia], totalWeightAntiHolo[Ia]};


(* ::Subsection:: *)
(*Test MultiOp and length*)


MultiOptest::usage = "Test if is MultiOp";
MultiOptest[f_]:=(Head[f]===MultiOp)

MultiOplength::usage = "Test if is MultiOp and has nonzero length";
MultiOplength[f_]:=If[MultiOptest[f],Length[List @@ f],0]

MultiOpone::usage = "Test if is MultiOp of length one";
MultiOpone[f_]:=(MultiOplength[f]===1)


(* ::Subsection:: *)
(*Test Op and length*)


OpTest::usage = "Test if is Op";
OpTest[f_]:=(Head[f]===Op)

OpLength::usage = "Test if is Op and has nonzero length";
OpLength[f_]:=If[OpTest[f],Length[List @@ f],0]

OpOne::usage = "Test if is Op of length one";
OpOne[f_]:=(OpLength[f]===1)

OpTestUpToConstant::usage = "Test if is operator up to a constant prefactor";

OpTestUpToConstant[c___,a_ f_,d___]:=OpTestUpToConstant[c,f,d]/;(And @@(FreeQ[a,#]&/@ allOperators))
OpTestUpToConstant[c___,a_ ,d___]:= OpTestUpToConstant[c,d]/;(And @@(FreeQ[a,#]&/@ allOperators))
OpTestUpToConstant[f_]:=(Head[f]===Op)
OpTestUpToConstant[]:=False;


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
