(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`OPE`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`Wick`"];


(* ::Section:: *)
(*Declare public variables and methods*)


OPE::usage = "Computes the operator product expansion";


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Define OPE by repeated moving of fields under a common normal ordering*)


OPE[a___,0,b___]:=0

OPE[a___,b_/;containsProfile[b],c___, maxDerivativeOrder_]:= OPEWithReplacedProfileX[a,b,c,maxDerivativeOrder];

OPE[Ra_,Rb_]:=R[Ra,Rb]+ pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}] Wick[Ra,Rb] /;(Rone[Ra] && Rone[Rb] && isSimple[Head[Ra[[1]]]] && isSimple[Head[Rb[[1]]]])

OPE[Ra_,Rb_]:=R[Ra,Rb]+ pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}] SWick[Ra,Rb] Rb /;(Rone[Ra] && Rone[Rb] && isSimple[Head[Ra[[1]]]] && isComposite[Head[Rb[[1]]]])

OPE[Ra_,Rb_]:=R[Ra,Rb]+ pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}] SWick[Ra,Rb] Ra/;(Rone[Ra] && Rone[Rb] && isComposite[Head[Ra[[1]]]] && isSimple[Head[Rb[[1]]]])

OPE[Ra_,Rb_]:= If[pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}]==1, MWick[Ra,Rb],1]  R[Ra,Rb]/;(Rone[Ra] && Rone[Rb] && isComposite[Head[Ra[[1]]]] && isComposite[Head[Rb[[1]]]])


OPE[Ra_,Rb_]:=DWick[Ra,Rb] +(R @@ Join[(List @@ Ra),(List @@ Rb)])/;(Rone[Ra] && Rtest[Rb]&& isSimple[Head[Ra[[1]]]] )

OPE[Ra_,Rb_]:= R[Ra,DWick[R[Ra[[1]]],Rb]]/;(Rone[Ra] && Rtest[Rb]  && isComposite[Head[Ra[[1]]]] )

OPE[Ra_,Rb_]:=(-1)^(parity[(R @@ (Drop[(List @@ Ra),1]))]parity[R[Ra[[1]]]]) OPE[(R @@ (Drop[(List @@ Ra),1])),DWick[R[Ra[[1]]],Rb]] +R[R[Ra[[1]]],OPE[(R @@ (Drop[(List @@ Ra),1])),Rb]]/;(Rtest[Ra] && Rtest[Rb] &&(!Rone[Ra]) && isSimple[Head[Ra[[1]]]]) 

OPE[Ra_,Rb_]:=R[R[Ra[[1]]],OPE[(R @@ (Drop[(List @@ Ra),1])),DWick[R[Ra[[1]]],Rb]]]/;(Rtest[Ra] && Rtest[Rb] &&(!Rone[Ra]) && isComposite[Head[Ra[[1]]]] )


OPE[f_,g_]:=f g/;((And @@(FreeQ[f,#]&/@ allfields))||(And @@(FreeQ[g,#]&/@ allfields)))
OPE[a_+b_,c_]:=OPE[a,c]+OPE[b,c]
OPE[c_,a_+b_]:=OPE[c,a]+OPE[c,b]
OPE[a_ b_,c_]:=a OPE[b,c]/;(And @@(FreeQ[a,#]&/@ allfields))
OPE[ b_,a_ c_]:=a OPE[b,c]/;(And @@(FreeQ[a,#]&/@ allfields))


OPE[c__,a_,b_]:=OPE[c,OPE[a,b]]


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
