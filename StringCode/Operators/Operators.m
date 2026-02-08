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


(* ::Subsection:: *)
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
Op[a_ f__?(Not[RTest[#]] & ), b_]:= f Op[a, b];
Op[a_, b_ f__?(Not[InteractingTest[#]] &)]:= f Op[a, b];
Op[a_/;Not[RTest[a]], b_]:= a b;
Op[a_, b_/;Not[InteractingTest[b]]]:= a b;
Op[1,1]:= 1;


(* ::Subsubsection:: *)
(*Define Interacting*)


Interacting[c___,b_,a_,d___]:=regcomm[a,b] Interacting[c,a,b,d]/;(!OrderedQ[{b,a}])
Interacting[ c___,a_,a_,d___]:=0/;(regparity[a]==1)


Interacting[c___, a_, d___] := (Interacting[c, #, d] & /@ a) /; Head[a] == Plus
Interacting[c___,a_ f_,d___]:=a Interacting[c,f,d]/;(And @@(FreeQ[a,#]&/@ interactingOperators) && interactingOperators=!={})
Interacting[c___,a_ ,d___]:=a Interacting[c,d]/;(And @@(FreeQ[a,#]&/@ interactingOperators && interactingOperators=!={}))
Interacting[]:=1
Interacting[a___,Interacting[b___],c___]:= Interacting[a,b,c]


Interacting[g___,a_ f_,h___]:=Interacting[g,a,f,h]/;MemberQ[bosons,Head[a]]
Interacting[g___,a_^n_ f_,h___]:=Interacting[g,(Interacting @@ ConstantArray[a,n]),f,h]/;isBoson[Head[a]]
Interacting[g___,a_^n_,h___]:=Interacting[g,(Interacting @@ ConstantArray[a,n]),h]/;isBoson[Head[a]]


(* ::Subsubsection:: *)
(*Define tests of properties of Interacting*)


InteractingTest::usage = "Test if is interacting";
InteractingTest[f_]:=(Head[f]===Interacting)

InteractingLength::usage = "Test if is interacting and has nonzero length";
InteractingLength[f_]:=If[InteractingTest[f],Length[List @@ f],0]

InteractingOne::usage = "Test if is interacting of length one";
InteractingOne[f_]:=(InteractingLength[f]==1)


InteractingTestUpToConstant::usage = "Test if product is interacting up to a constant prefactor";

InteractingTestUpToConstant[c___,a_ f_,d___]:=InteractingTestUpToConstant[c,f,d]/;(And @@(FreeQ[a,#]&/@ interactingOperators))
InteractingTestUpToConstant[c___,a_ ,d___]:= InteractingTestUpToConstant[c,d]/;(And @@(FreeQ[a,#]&/@ interactingOperators))
InteractingTestUpToConstant[f_]:=InteractingTest[f];
InteractingTestUpToConstant[]:=False;


(* ::Subsection:: *)
(*Define parity of MultiOp and Op*)


parityOp::usage = "Computes the parity of a local operator";
scalarQ[x_] := FreeQ[x, _MultiOp | _Op | _R | _Interacting]
parityOp[expr_Times] := parityOp[SelectFirst[List @@ expr, !scalarQ[#] &]]

parityOp[Ma_/;MultiOpTest[Ma]]:= Mod[Total @ (parityOp /@ List @@ Ma),2];
parityOp[Oa_/;OpTest[Oa]]:= Mod[parity[Oa[[1]]] + parity[Oa[[2]]],2];
parityOp[Ra_/;RTest[Ra]]:= Mod[parity[Ra],2];
parityOp[Ia_/;InteractingTest[Ia]]:= Mod[parity[Ia],2];


(* ::Subsection:: *)
(*Define weight of operators*)


totalWeightHolo::usage = "Computes total holomorphic weight of a normal-ordered product";
totalWeightAntiHolo::usage = "Computes total holomorphic weight of a normal-ordered product";
totalWeight::usage = "Computes total weight of a normal-ordered product";

totalWeightHolo[Times[a_, MultiOpa_/;MultiOpTest[MultiOpa]]] := totalWeightHolo[MultiOpa];
totalWeightHolo[MultiOpa_/;MultiOpTest[MultiOpa]] := Total[Map[totalWeightHolo, List @@ MultiOpa]];

totalWeightAntiHolo[Times[a_, MultiOpa_/;MultiOpTest[MultiOpa]]] := totalWeightAntiHolo[MultiOpa];
totalWeightAntiHolo[MultiOpa_/;MultiOpTest[MultiOpa]] := Total[Map[totalWeightAntiHolo, List @@ MultiOpa]];

totalWeightHolo[Times[a_, Opa_/;OpTest[Opa]]] := totalWeightHolo[Opa];
totalWeightHolo[Opa_/;OpTest[Opa]] := totalWeightHolo[Opa[[1]]] + totalWeightHolo[Opa[[2]]];

totalWeightAntiHolo[Times[a_, Opa_/;OpTest[Opa]]] := totalWeightAntiHolo[Opa];
totalWeightAntiHolo[Opa_/;OpTest[Opa]] := totalWeightAntiHolo[Opa[[1]]] + totalWeightAntiHolo[Opa[[2]]];

totalWeightHolo[Times[a_, Ia_/;InteractingTest[Ia]]] := totalWeightHolo[Ia];
totalWeightHolo[Ia_/;InteractingTest[Ia]] := Map[weightHolo, List @@ Ia] // Total;

totalWeightAntiHolo[Times[a_, Ia_/;InteractingTest[Ia]]] := totalWeightAntiHolo[Ia];
totalWeightAntiHolo[Ia_/;InteractingTest[Ia]] := Map[weightAntiHolo, List @@ Ia] // Total;

totalWeightHolo[a_/;NumericQ[a]]:=0;
totalWeightAntiHolo[a_/;NumericQ[a]]:=0;

totalWeight[Times[a_, MultiOpa_/;MultiOpTest[MultiOpa]]] := totalWeight[MultiOpa];
totalWeight[MultiOpa_/;MultiOpTest[MultiOpa]] := {totalWeightHolo[MultiOpa], totalWeightAntiHolo[MultiOpa]};

totalWeight[Times[a_, Opa_/;OpTest[Opa]]] := totalWeight[Opa];
totalWeight[Opa_/;OpTest[Opa]] := {totalWeightHolo[Opa], totalWeightAntiHolo[Opa]};

totalWeight[Times[a_, Ia_/;InteractingTest[Ia]]] := totalWeight[Ia];
totalWeight[Ia_/;InteractingTest[Ia]] := {totalWeightHolo[Ia], totalWeightAntiHolo[Ia]};

totalWeight[a_/;NumericQ[a]]:=0;


(* ::Subsection:: *)
(*Test MultiOp and length*)


MultiOpTest::usage = "Test if is MultiOp";
MultiOpTest[f_]:=(Head[f]===MultiOp)

MultiOpLength::usage = "Test if is MultiOp and has nonzero length";
MultiOpLength[f_]:=If[MultiOpTest[f],Length[List @@ f],0]

MultiOpOne::usage = "Test if is MultiOp of length one";
MultiOpOne[f_]:=(MultiOpLength[f]===1)


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
