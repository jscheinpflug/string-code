(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`NormalOrdering`"];


Needs["StringCode`Symbols`"];


(* ::Section:: *)
(*Declare public variables and methods*)


R::usage = "A sorted normal-ordered product of fields";


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Test normal-ordering and length*)


RTest::usage = "Test if product is normal-ordered";
RTest[f_]:=(Head[f]===R)

RLength::usage = "Test if is normal-ordered and has nonzero length";
RLength[f_]:=If[RTest[f],Length[List @@ f],0]

ROne::usage = "Test if is normal-ordered of length one";
ROne[f_]:=(RLength[f]==1)


RTestUpToConstant::usage = "Test if product is normal-ordered up to a constant prefactor";

RTestUpToConstant[c___,a_ f_,d___]:=RTestUpToConstant[c,f,d]/;(And @@(FreeQ[a,#]&/@ allfields))
RTestUpToConstant[c___,a_ ,d___]:= RTestUpToConstant[c,d]/;(And @@(FreeQ[a,#]&/@ allfields))
RTestUpToConstant[f_]:=(Head[f]===R)
RTestUpToConstant[]:=False;


(* ::Subsection::Closed:: *)
(*Define Grassmann parity*)


parity::usage = "Define Grassmann parity for fields including composites";

parity[f_]:=0/;(And @@(FreeQ[f,#]&/@ fermions))
parity[f_+g_]:=parity[f]
parity[f_ g_]:=parity[g]/;(And @@(FreeQ[f,#]&/@ fermions))
parity[R[f__,g__]]:=Mod[parity[R[f]]+parity[R[g]],2]
parity[R[f_]]:=1/;(!(And @@(FreeQ[f,#]&/@ fermions)))
parity[f_]:=1/;(!(And @@(FreeQ[f,#]&/@ fermions)))


regparity::usage = "Define Grassmann parity for fundamental fields";

regparity[f_+g_]:=regparity[f]
regparity[f_ g_]:=regparity[g]/;(And @@(FreeQ[f,#]&/@ regfermions))
regparity[f_]:=0/;(And @@(FreeQ[f,#]&/@ regfermions))
regparity[f_]:=1/;(!(And @@(FreeQ[f,#]&/@ regfermions)))


(* ::Subsection:: *)
(*Define normal-ordered product*)


R[c___,b_,a_,d___]:=regcomm[a,b] R[c,a,b,d]/;(!OrderedQ[{b,a}])
R[ c___,a_,a_,d___]:=0/;(regparity[a]==1)


R[c___, a_, d___] := (R[c, #, d] & /@ a) /; Head[a] == Plus
R[c___,a_ f_,d___]:=a R[c,f,d]/;(And @@(FreeQ[a,#]&/@ allfields))
R[c___,a_ ,d___]:=a R[c,d]/;(And @@(FreeQ[a,#]&/@ allfields))
R[]:=1
R[a___,R[b___],c___]:=R[a,b,c]


R[g___,a_ f_,h___]:=R[g,a,f,h]/;MemberQ[bosons,Head[a]]
R[g___,a_^n_ f_,h___]:=R[g,(R @@ ConstantArray[a,n]),f,h]/;isBoson[Head[a]]
R[g___,a_^n_,h___]:=R[g,(R @@ ConstantArray[a,n]),h]/;isBoson[Head[a]]


(* ::Subsection::Closed:: *)
(*Define total ghost number*)


totalHolGhostNumber::usage = "Computes total holomorphic ghost number";
totalAntiHolGhostNumber::usage = "Computes total antiholomorphic ghost number";

totalHolGhostNumber[Ra_/;RTest[Ra]]:= Map[ghostNumberHolo, List @@ Ra]//Total;
totalHolGhostNumber[Times[a_, Ra_/;RTest[Ra]]] := totalHolGhostNumber[Ra];

totalAntiHolGhostNumber[Ra_/;RTest[Ra]]:= Map[ghostNumberAntiHolo, List @@ Ra]//Total;
totalAntiHolGhostNumber[Times[a_, Ra_/;RTest[Ra]]] := totalAntiHolGhostNumber[Ra];


(* ::Subsection::Closed:: *)
(*Define cached dropping of normal-ordered product elements*)


dropFirstFromR::usage = "Drops first element from normal-ordered product";
dropFirstFromR[Ra_]:= dropFirstFromR[Ra] = R @@ (Drop[(List @@ Ra),1])


(* ::Subsection::Closed:: *)
(*Define weight of normal-ordered product*)


totalWeightHolo::usage = "Computes total holomorphic weight of a normal-ordered product";
totalWeightAntiHolo::usage = "Computes total holomorphic weight of a normal-ordered product";
totalWeight::usage = "Computes total weight of a normal-ordered product";

totalWeightHolo[Times[a_, Ra_/;RTest[Ra]]] := totalWeightHolo[Ra];
totalWeightHolo[Ra_/;RTest[Ra]] := Map[weightHolo, List @@ Ra] // Total;

totalWeightAntiHolo[Times[a_, Ra_/;RTest[Ra]]] := totalWeightAntiHolo[Ra];
totalWeightAntiHolo[Ra_/;RTest[Ra]] := Map[weightAntiHolo, List @@ Ra] // Total;

totalWeight[Times[a_, Ra_/;RTest[Ra]]] := totalWeight[Ra];
totalWeight[Ra_/;RTest[Ra]] := {totalWeightHolo[Ra], totalWeightAntiHolo[Ra]};

(* ::Section:: *)
(*End*)


End[];


EndPackage[];
