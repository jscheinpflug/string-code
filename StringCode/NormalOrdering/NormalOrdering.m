(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`NormalOrdering`"];


Needs["StringCode`Symbols`"];


(* ::Section:: *)
(*Declare public variables and methods*)


R::usage = "A sorted normal-ordered product of fields";
Rtest::usage = "Test if product is normal-ordered";
RtestUpToConstant::usage = "Test if product is normal-ordered up to a constant prefactor";
Rlength::usage = "Test if is normal-ordered and has nonzero length";
Rone::usage = "Test if is normal-ordered of length one";
parity::usage = "Define Grassmann parity for fields including composites";
exp\[Phi]parity::usage = "Define Grassmann parity for holomorphic exponentials of \[Phi]";
exp\[Phi]tparity::usage = "Define Grassmann parity for antiholomorphic exponentials of \[Phi]";
regparity::usage = "Define Grassmann parity for fundamental fields";
regcomm::usage = "Give Grassmann sign under commutation";
CR::usage = "A normal-ordered product for correlators";


(* ::Section:: *)
(*Logic*)


Begin["`Private`"];


(* ::Subsection:: *)
(*Test normal-ordering and length*)


Rtest[f_]:=(Head[f]==R)
Rlength[f_]:=If[Rtest[f],Length[List @@ f],0]
Rone[f_]:=(Rlength[f]==1)


RtestUpToConstant[c___,a_ f_,d___]:=RtestUpToConstant[c,f,d]/;(And @@(FreeQ[a,#]&/@ allfields))
RtestUpToConstant[c___,a_ ,d___]:= RtestUpToConstant[c,d]/;(And @@(FreeQ[a,#]&/@ allfields))
RtestUpToConstant[f_]:=(Head[f]==R)
RtestUpToConstant[]:=False;


(* ::Subsection::Closed:: *)
(*Define Grassmann parity*)


parity[f_]:=0/;(And @@(FreeQ[f,#]&/@ fermions))
parity[f_+g_]:=parity[f]
parity[f_ g_]:=parity[g]/;(And @@(FreeQ[f,#]&/@ fermions))
parity[R[f__,g__]]:=Mod[parity[R[f]]+parity[R[g]],2]
parity[R[f_]]:=1/;(!(And @@(FreeQ[f,#]&/@ fermions)))

parity[f_]:=1/;(!(And @@(FreeQ[f,#]&/@ fermions)))

exp\[Phi]parity[f_]:=0/;(And @@(FreeQ[f,#]&/@ exp\[Phi]fermions))
exp\[Phi]parity[f_]:=1/;(!(And @@(FreeQ[f,#]&/@ exp\[Phi]fermions)))
exp\[Phi]parity[R[f__,g__]]:=Mod[exp\[Phi]parity[R[f]]+exp\[Phi]parity[R[g]],2]
exp\[Phi]parity[R[f_]]:=exp\[Phi]parity[f]


exp\[Phi]tparity[f_]:=0/;(And @@(FreeQ[f,#]&/@ exp\[Phi]tfermions))
exp\[Phi]tparity[f_]:=1/;(!(And @@(FreeQ[f,#]&/@ exp\[Phi]tfermions)))
exp\[Phi]tparity[R[f__,g__]]:=Mod[exp\[Phi]tparity[R[f]]+exp\[Phi]tparity[R[g]],2]
exp\[Phi]tparity[R[f_]]:=exp\[Phi]tparity[f]


regparity[f_+g_]:=regparity[f]
regparity[f_ g_]:=regparity[g]/;(And @@(FreeQ[f,#]&/@ regfermions))
regparity[f_]:=0/;(And @@(FreeQ[f,#]&/@ regfermions))

regparity[f_]:=1/;(!(And @@(FreeQ[f,#]&/@ regfermions)))

regcomm[f_,g_]:=(-1)^(parity[f] parity[g])(-1)^(exp\[Phi]parity[f] exp\[Phi]parity[g])(-1)^(exp\[Phi]tparity[f] exp\[Phi]tparity[g])


(* ::Subsection:: *)
(*Define normal-ordered product*)


R[c___,b_,a_,d___]:=regcomm[a,b] R[c,a,b,d]/;(!OrderedQ[{b,a}])
R[ c___,a_,a_,d___]:=0/;(regparity[a]==1)


R[c___,a_+b_,d___]:=R[c,a,d]+R[c,b,d]
R[c___,a_ f_,d___]:=a R[c,f,d]/;(And @@(FreeQ[a,#]&/@ allfields))
R[c___,a_ ,d___]:=a R[c,d]/;(And @@(FreeQ[a,#]&/@ allfields))
R[]:=1
R[a___,R[b___],c___]:=R[a,b,c]


R[g___,a_ f_,h___]:=R[g,a,f,h]/;MemberQ[bosons,Head[a]]
R[g___,a_^n_ f_,h___]:=R[g,(R @@ ConstantArray[a,n]),f,h]/;MemberQ[bosons,Head[a]]
R[g___,a_^n_,h___]:=R[g,(R @@ ConstantArray[a,n]),h]/;MemberQ[bosons,Head[a]]


R[ c___,a_,a_,d___]:=R[c,exp\[Phi]b[2a[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]f)
R[ c___,a_,a_,d___]:=R[c,exp\[Phi]tb[2a[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]tf)
R[ c___,a_,b_,d___]:=R[c,exp\[Phi]b[a[[1]]+b[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]b && Head[b]==exp\[Phi]b && a[[2]]==b[[2]])
R[ c___,a_,b_,d___]:=R[c,exp\[Phi]tb[a[[1]]+b[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]tb && Head[b]==exp\[Phi]tb && a[[2]]==b[[2]])
R[ c___,a_,b_,d___]:=R[c,exp\[Phi]b[a[[1]]+b[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]f && Head[b]==exp\[Phi]f && a[[2]]==b[[2]])
R[ c___,a_,b_,d___]:=R[c,exp\[Phi]tb[a[[1]]+b[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]tf && Head[b]==exp\[Phi]tf && a[[2]]==b[[2]])
R[ c___,a_,b_,d___]:=R[c,exp\[Phi]f[a[[1]]+b[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]b && Head[b]==exp\[Phi]f && a[[2]]==b[[2]])
R[ c___,a_,b_,d___]:=R[c,exp\[Phi]tf[a[[1]]+b[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]tb && Head[b]==exp\[Phi]tf && a[[2]]==b[[2]])


(* ::Subsection::Initialization::Closed:: *)
(*Define CR*)


(* ::Input::Initialization:: *)
CR[c___,b_,a_,d___]:=regcomm[a,b] CR[c,a,b,d]/;(!OrderedQ[{b,a}])
CR[ c___,a_,a_,d___]:=0/;(regparity[a]==1)
CR[ c___,a_,d___]:=0/;MemberQ[simplefieldsnotc,Head[a]]
 
CR[c___,a_+b_,d___]:=CR[c,a,d]+CR[c,b,d]
CR[c___,a_ f_,d___]:=a CR[c,f,d]/;(And @@(FreeQ[a,#]&/@ allfields))
CR[c___,a_ ,d___]:=a CR[c,d]/;(And @@(FreeQ[a,#]&/@ allfields))
CR[]:=1
CR[a___,R[b___],c___]:=CR[a,b,c]

CR[g___,a_ f_,h___]:=CR[g,a,f,h]/;MemberQ[bosons,Head[a]]
CR[g___,a_^n_ f_,h___]:=CR[g,(R @@ ConstantArray[a,n]),f,h]/;MemberQ[bosons,Head[a]]
CR[g___,a_^n_,h___]:=CR[g,(R @@ ConstantArray[a,n]),h]/;MemberQ[bosons,Head[a]]


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
