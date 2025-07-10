(* ::Package:: *)

(* ::Section::Initialization:: *)
(*(*Init*)*)


BeginPackage["StringCode`Correlators`"]
Needs["StringCode`Symbols`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`Wick`"];
Needs["StringCode`OPE`"];


(* ::Section::Initialization:: *)
(*(*Declare public methods*)*)


Corr::usage = "Computes correlation functions in the worldsheet CFT";
Vev::usage = "Computes VEV in the worldsheet CFT";


(* ::Section::Initialization:: *)
(*(*Logic*)*)


Begin["Private`"];


(* ::Subsection::Initialization:: *)
(*(*Define Vev*)*)


(* ::Input::Initialization:: *)
Vev[f_]:=Block[{i},f/.{b[n_,z_]:>0,c[n_,z_]:>Sum[If[i==0,1,z^i/i!] c[n+i,0],{i,0,2}],\[Eta][n_,z_]:>0,\[Xi][n_,z_]:>0,d\[Phi][n_,z_]:>0,dX[\[Mu]_,n_,z_]:>0,\[Psi][\[Mu]_,n_,z_]:>0,exp\[Phi]f[a_,z_]:>exp\[Phi]f[a,0],exp\[Phi]b[a_,z_]:>exp\[Phi]b[a,0],bt[n_,z_]:>0,ct[n_,z_]:>Sum[If[i==0,1,z^i/i!]ct[n+i,0],{i,0,2}],\[Eta]t[n_,z_]:>0,\[Xi]t[n_,z_]:>0,d\[Phi]t[n_,z_]:>0,dXt[\[Mu]_,n_,z_]:>0,\[Psi]t[\[Mu]_,n_,z_]:>0,exp\[Phi]tf[a_,z_]:>exp\[Phi]tf[a,0],exp\[Phi]tb[a_,z_]:>exp\[Phi]tb[a,0],expX[k_,z_,zbar_]:>expX[k,0,0]}]


(* ::Subsection::Initialization::Closed:: *)
(*(*Define Corr*)*)


(* ::Input::Initialization:: *)
Corr[a___,0,b___]:=0
Corr[Ra_,Rb_]:=CR[Ra,Rb]+ pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}] Wick[Ra,Rb] /;(Rone[Ra] && Rone[Rb] && MemberQ[simplefields,Head[Ra[[1]]]] && MemberQ[simplefields,Head[Rb[[1]]]])

Corr[Ra_,Rb_]:=CR[Ra,Rb]+ pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}] SWick[Ra,Rb] Rb /;(Rone[Ra] && Rone[Rb] && MemberQ[simplefields,Head[Ra[[1]]]] && MemberQ[compositefields,Head[Rb[[1]]]])

Corr[Ra_,Rb_]:=CR[Ra,Rb]+ pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}] SWick[Ra,Rb] Ra/;(Rone[Ra] && Rone[Rb] && MemberQ[compositefields,Head[Ra[[1]]]] && MemberQ[simplefields,Head[Rb[[1]]]])

Corr[Ra_,Rb_]:= If[pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}]==1, MWick[Ra,Rb],1]  CR[Ra,Rb]/;(Rone[Ra] && Rone[Rb] && MemberQ[compositefields,Head[Ra[[1]]]] && MemberQ[compositefields,Head[Rb[[1]]]])


(* ::Input::Initialization:: *)
Corr[Ra_,Rb_]:=CDWick[Ra,Rb] +(CR @@ Join[(List @@ Ra),(List @@ Rb)])/;(Rone[Ra] && Rtest[Rb]&& MemberQ[simplefields,Head[Ra[[1]]]])

Corr[Ra_,Rb_]:= CR[Ra,DWick[R[Ra[[1]]],Rb]]/;(Rone[Ra] && Rtest[Rb]  && MemberQ[compositefields,Head[Ra[[1]]]] )

Corr[Ra_,Rb_]:=(-1)^(parity[(R @@ (Drop[(List @@ Ra),1]))]parity[R[Ra[[1]]]]) Corr[(R @@ (Drop[(List @@ Ra),1])),DWick[R[Ra[[1]]],Rb]] +CR[R[Ra[[1]]],OPE[(R @@ (Drop[(List @@ Ra),1])),Rb]]/;(Rtest[Ra] && Rtest[Rb] &&(!Rone[Ra]) && MemberQ[simplefields,Head[Ra[[1]]]] )

Corr[Ra_,Rb_]:=CR[R[Ra[[1]]],OPE[(R @@ (Drop[(List @@ Ra),1])),DWick[R[Ra[[1]]],Rb]]]/;(Rtest[Ra] && Rtest[Rb] &&(!Rone[Ra]) && MemberQ[compositefields,Head[Ra[[1]]]] )

Corr[f_,g_]:=f g/;((And @@(FreeQ[f,#]&/@ allfields))||(And @@(FreeQ[g,#]&/@ allfields)))
Corr[a_+b_,c_]:=Corr[a,c]+Corr[b,c]
Corr[c_,a_+b_]:=Corr[c,a]+Corr[c,b]
Corr[a_ b_,c_]:=a Corr[b,c]/;(And @@(FreeQ[a,#]&/@ allfields))
Corr[ b_,a_ c_]:=a Corr[b,c]/;(And @@(FreeQ[a,#]&/@ allfields))


(* ::Section::Initialization:: *)
(*(*End*)*)


End[];


EndPackage[];
