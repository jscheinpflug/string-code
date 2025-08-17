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

(*When both normal-ordered products have length one, OPE reduces to Wick contraction + possible normal ordering*)
OPE[Ra_,Rb_]:=R[Ra,Rb]+ If[pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}]==1, Wick[Ra,Rb],0] /;(Rone[Ra] && Rone[Rb] && isSimple[Head[Ra[[1]]]] && isSimple[Head[Rb[[1]]]])
OPE[Ra_,Rb_]:=R[Ra,Rb]+ If[pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}]==1, SWick[Ra,Rb] Rb,0] /;(Rone[Ra] && Rone[Rb] && isSimple[Head[Ra[[1]]]] && isComposite[Head[Rb[[1]]]])
OPE[Ra_,Rb_]:=R[Ra,Rb]+ If[pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}]==1, SWick[Ra,Rb] Ra,0]/;(Rone[Ra] && Rone[Rb] && isComposite[Head[Ra[[1]]]] && isSimple[Head[Rb[[1]]]])
OPE[Ra_,Rb_]:= If[pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}]==1, MWick[Ra,Rb],1]  R[Ra,Rb]/;(Rone[Ra] && Rone[Rb] && isComposite[Head[Ra[[1]]]] && isComposite[Head[Rb[[1]]]])


(*When first normal-ordered product has one simple element, compute DWick and add a non-contracted term*)
OPE[Ra_,Rb_]:= DWick[Ra,Rb] +(R @@ Join[(List @@ Ra),(List @@ Rb)])/;(Rone[Ra] && Rtest[Rb]&& isSimple[Head[Ra[[1]]]] )

(*When first normal-ordered product has one composite element, compute DWick*)
OPE[Ra_,Rb_]:= R[Ra,DWick[R[Ra[[1]]],Rb]]/;(Rone[Ra] && Rtest[Rb]  && isComposite[Head[Ra[[1]]]] )

(*When the first element of Ra is simple, commute it through, then compute DWick with Rb, add a non-contracted term, continue with OPE of other terms in Ra*)
OPE[Ra_,Rb_]:=(-1)^(parity[dropFirstFromR[Ra]]parity[R[Ra[[1]]]]) OPE[dropFirstFromR[Ra],DWick[R[Ra[[1]]],Rb]] +
R[R[Ra[[1]]],OPE[dropFirstFromR[Ra],Rb]]/;(Rtest[Ra] && Rtest[Rb] &&(!Rone[Ra]) && isSimple[Head[Ra[[1]]]]) 

(*When the first element of Ra is composite, commute it through, then compute DWick with Rb, commute it back [producing no net sign], 
  and continue with OPE of other terms in Ra*)
OPE[Ra_,Rb_]:=R[R[Ra[[1]]],OPE[dropFirstFromR[Ra],DWick[R[Ra[[1]]],Rb]]]/;(Rtest[Ra] && Rtest[Rb] &&(!Rone[Ra]) && isComposite[Head[Ra[[1]]]] )


(*Multilinearity of OPE*)
OPE[f_,g_]:=f g/;((And @@(FreeQ[f,#]&/@ allfields))||(And @@(FreeQ[g,#]&/@ allfields)))
OPE[a_+b_,c_]:=OPE[a,c]+OPE[b,c]
OPE[c_,a_+b_]:=OPE[c,a]+OPE[c,b]
OPE[a_ b_,c_]:=a OPE[b,c]/;(And @@(FreeQ[a,#]&/@ allfields))
OPE[ b_,a_ c_]:=a OPE[b,c]/;(And @@(FreeQ[a,#]&/@ allfields))


(*Nested OPE*)
OPE[c__,a_,b_]:=OPE[c,OPE[a,b]]


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
