(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Wick`"]
Needs["StringCode`Symbols`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`Conventions`ConventionsIIBAshoke`"];


(* ::Section:: *)
(*Declare public methods*)


Wick::usage = "A Wick contraction between two fundamental fields";


SWick::usage = "A Wick contraction between a fundamental and composite field";


MWick::usage = "A Wick contraction between two composite fields";


DWick::usage = "A Wick contraction for OPE";


CDWick::usage = "A Wick contraction for correlators";


pairing::usage = "Determines whether two fields can be Wick contracted";


dot::usage = "Symbol for dot product";


(* ::Section:: *)
(*Logic*)


Begin["`Private`"];


(* ::Subsection:: *)
(*Define Wick*)


Wick[dX[\[Mu]_,n_,z_],dX[\[Nu]_,m_,w_]]:= Module[{zd}, \[Delta][\[Mu], \[Nu]] (-1)^m D[(-1/2)*\[Alpha]p/(zd - w)^2, {zd, n + m}] /. zd -> z];
Wick[dXt[\[Mu]_,n_,z_],dXt[\[Nu]_,m_,w_]]:= Module[{zd}, \[Delta][\[Mu], \[Nu]] (-1)^m D[(-1/2)*\[Alpha]p/(zd - w)^2, {zd, n + m}] /. zd -> z];
Wick[d\[Phi][n_, z_], d\[Phi][m_, w_]] := Module[{zd}, (-1)^m D[-1/(zd - w)^2, {zd, n + m}] /. zd -> z]
Wick[d\[Phi][n_, z_], d\[Phi][m_, w_]] := Module[{zd}, (-1)^m D[-1/(zd - w)^2, {zd, n + m} /. zd -> z]]
Wick[d\[Phi]t[n_, z_], d\[Phi]t[m_, w_]] := Module[{zd}, (-1)^m D[-1/(zd - w)^2, {zd, n + m}] /. zd -> z]
Wick[b[n_, z_], c[m_, w_]] := Module[{zd}, (-1)^m D[1/(zd - w), {zd, n + m}] /. zd -> z]
Wick[c[m_, w_], b[n_, z_]] := Module[{zd}, -(-1)^m D[1/(zd - w), {zd, n + m}] /. zd -> z]
Wick[bt[n_, z_], ct[m_, w_]] :=Module[{zd}, (-1)^m D[1/(zd - w), {zd, n + m}] /. zd -> z]
Wick[ct[m_, w_], bt[n_, z_]] := Module[{zd}, -(-1)^m D[1/(zd - w), {zd, n + m}] /. zd -> z]
Wick[\[Eta][n_, z_], \[Xi][m_, w_]] := Module[{zd}, (-1)^m D[1/(zd - w), {zd, n + m}] /. zd -> z]
Wick[\[Xi][m_, w_], \[Eta][n_, z_]] := Module[{zd}, -(-1)^m D[1/(zd - w), {zd, n + m}] /. zd -> z]
Wick[\[Eta]t[n_, z_], \[Xi]t[m_, w_]] :=Module[{zd}, (-1)^m D[1/(zd - w), {zd, n + m}] /. zd -> z]
Wick[\[Xi]t[m_, w_], \[Eta]t[n_, z_]] := Module[{zd}, - (-1)^m D[1/(zd - w), {zd, n + m}] /. zd -> z]
Wick[\[Psi][\[Mu]_, n_, z_], \[Psi][\[Nu]_, m_, w_]] := Module[{zd}, \[Delta][\[Mu], \[Nu]] (-1)^m D[\[Alpha]p fermionToBosonWickRatio/(zd - w), {zd, n + m}] /. zd -> z]
Wick[\[Psi]t[\[Mu]_, n_, z_], \[Psi]t[\[Nu]_, m_, w_]] := Module[{zd}, \[Delta][\[Mu], \[Nu]] (-1)^m D[\[Alpha]p fermionToBosonWickRatio/(zd - w), {zd, n + m}] /. zd -> z]
Wick[Ra_?Rone, Rb_?Rone] := Wick[Ra[[1]],Rb[[1]]]


(* ::Subsection:: *)
(*Define SWick*)


SWick[dX[\[Mu]_, n_, z_], expX[k_, w_, wbar_]] := Module[{zd}, (-\[Alpha]p/2 I k[\[Mu]]) D[1/(zd - w), {zd, n}] /. zd -> z]
SWick[expX[k_, w_, wbar_], dX[\[Mu]_, n_, z_]] := Module[{zd}, (-\[Alpha]p/2 I k[\[Mu]]) D[1/(zd - w), {zd, n}] /. zd -> z]
SWick[dXt[\[Mu]_, n_, z_], expX[k_, w_, wbar_]] := Module[{zd}, (-\[Alpha]p/2 I k[\[Mu]]) D[1/(zd - wbar), {zd, n}] /. zd -> z]
SWick[expX[k_, w_, wbar_], dXt[\[Mu]_, n_, z_]] := Module[{zd}, (-\[Alpha]p/2 I k[\[Mu]]) D[1/(zd - wbar), {zd, n}] /. zd -> z]


SWick[d\[Phi][n_, z_], exp\[Phi]b[a_, w_]] := Module[{zd}, (-a) D[1/(zd - w), {zd, n}] /. zd -> z]
SWick[exp\[Phi]b[a_, w_], d\[Phi][n_, z_]] := Module[{zd}, (-a) D[1/(zd - w), {zd, n}] /. zd -> z]
SWick[d\[Phi][n_, z_], exp\[Phi]f[a_, w_]] := Module[{zd}, (-a) D[1/(zd - w), {zd, n}] /. zd -> z]
SWick[exp\[Phi]f[a_, w_], d\[Phi][n_, z_]] := Module[{zd}, (-a) D[1/(zd - w), {zd, n}] /. zd -> z]


SWick[d\[Phi]t[n_, z_], exp\[Phi]tb[a_, w_]] := Module[{zd}, (-a) D[1/(zd - w), {zd, n}] /. zd -> z]
SWick[exp\[Phi]tb[a_, w_], d\[Phi]t[n_, z_]] := Module[{zd}, (-a) D[1/(zd - w), {zd, n}] /. zd -> z]
SWick[d\[Phi]t[n_, z_], exp\[Phi]tf[a_, w_]] := Module[{zd}, (-a) D[1/(zd - w), {zd, n}] /. zd -> z]
SWick[exp\[Phi]tf[a_, w_], d\[Phi]t[n_, z_]] := Module[{zd}, (-a) D[1/(zd - w), {zd, n}] /. zd -> z]


SWick[Ra_?Rone, Rb_?Rone] := SWick[Ra[[1]],Rb[[1]]]


(* ::Subsection:: *)
(*Define MWick*)


MWick[expX[p_,z_,zbar_],expX[k_,w_,wbar_]]:=((z-w) (zbar-wbar))^(\[Alpha]p/2 dot[p,k])


MWick[exp\[Phi]b[a_,z_],exp\[Phi]b[b_,w_]]:=(z-w)^(-a b)
MWick[exp\[Phi]b[a_,z_],exp\[Phi]f[b_,w_]]:=(z-w)^(-a b)
MWick[exp\[Phi]f[a_,z_],exp\[Phi]b[b_,w_]]:=(z-w)^(-a b)
MWick[exp\[Phi]f[a_,z_],exp\[Phi]f[b_,w_]]:=(z-w)^(-a b)


MWick[exp\[Phi]tb[a_,z_],exp\[Phi]tb[b_,w_]]:=(z-w)^(-a b)
MWick[exp\[Phi]tb[a_,z_],exp\[Phi]tf[b_,w_]]:=(z-w)^(-a b)
MWick[exp\[Phi]tf[a_,z_],exp\[Phi]tb[b_,w_]]:=(z-w)^(-a b)
MWick[exp\[Phi]tf[a_,z_],exp\[Phi]tf[b_,w_]]:=(z-w)^(-a b)


MWick[Ra_?Rone, Rb_?Rone] := MWick[Ra[[1]],Rb[[1]]]


(* ::Subsection:: *)
(*Define DWick: Wick contractions for normal-ordered products of fields*)


DWick[Ra_,Rb_]:= pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}] Wick[Ra,Rb]/;(Rone[Ra] && Rone[Rb] && MemberQ[simplefields,Head[Ra[[1]]]] && MemberQ[simplefields,Head[Rb[[1]]]])

DWick[Ra_,Rb_]:= pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}] SWick[Ra,Rb] Rb/;(Rone[Ra] && Rone[Rb] && MemberQ[simplefields,Head[Ra[[1]]]] && MemberQ[compositefields,Head[Rb[[1]]]])

DWick[Ra_,Rb_]:=pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}] SWick[Ra,Rb]+Rb/;(Rone[Ra] && Rone[Rb] && MemberQ[compositefields,Head[Ra[[1]]]] && MemberQ[simplefields,Head[Rb[[1]]]])

DWick[Ra_,Rb_]:= If[pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}]==1, MWick[Ra,Rb],1] Rb/;(Rone[Ra] && Rone[Rb] && MemberQ[compositefields,Head[Ra[[1]]]] && MemberQ[compositefields,Head[Rb[[1]]]])

DWick[Ra_,Rb_]:= pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}] SWick[Ra[[1]],Rb[[1]]] Rb+(-1)^(parity[Ra]parity[R[Rb[[1]]]]) R[Rb[[1]],
DWick[Ra,(R @@ (Drop[(List @@ Rb),1]))]]/;(Rone[Ra] && Rtest[Rb] &&(!Rone[Rb]) && MemberQ[simplefields,Head[Ra[[1]]]] && MemberQ[compositefields,Head[Rb[[1]]]])

DWick[Ra_,Rb_]:= pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}] Wick[Ra[[1]],Rb[[1]]] (R @@ (Drop[(List @@ Rb),1]))+(-1)^(parity[Ra]parity[R[Rb[[1]]]]) R[Rb[[1]],
DWick[Ra,(R @@ (Drop[(List @@ Rb),1]))]]/;(Rone[Ra] && Rtest[Rb] &&(!Rone[Rb]) && MemberQ[simplefields,Head[Ra[[1]]]] && MemberQ[simplefields,Head[Rb[[1]]]])

DWick[Ra_,Rb_]:= pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}] SWick[Ra[[1]],Rb[[1]]] DWick[Ra,(R @@ (Drop[(List @@ Rb),1]))]+ R[Rb[[1]],
DWick[Ra,(R @@ (Drop[(List @@ Rb),1]))]]/;(Rone[Ra] && Rtest[Rb] &&(!Rone[Rb]) && MemberQ[compositefields,Head[Ra[[1]]]] && MemberQ[simplefields,Head[Rb[[1]]]])

DWick[Ra_,Rb_]:= If[pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}]==1, MWick[Ra[[1]],Rb[[1]]],1] R[Rb[[1]],
DWick[Ra,(R @@ (Drop[(List @@ Rb),1]))]]/;(Rone[Ra] && Rtest[Rb] &&(!Rone[Rb]) && MemberQ[compositefields,Head[Ra[[1]]]] && MemberQ[compositefields,Head[Rb[[1]]]])



(* ::Subsection::Initialization:: *)
(*(*(*Define CDWick*)*)*)


(* ::Input::Initialization:: *)
CDWick[Ra_,Rb_]:= pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}] Wick[Ra,Rb]/;(Rone[Ra] && Rone[Rb] && MemberQ[simplefields,Head[Ra[[1]]]] && MemberQ[simplefields,Head[Rb[[1]]]])

CDWick[Ra_,Rb_]:= pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}] SWick[Ra,Rb] (CR @@ Rb)/;(Rone[Ra] && Rone[Rb] && MemberQ[simplefields,Head[Ra[[1]]]] && MemberQ[compositefields,Head[Rb[[1]]]])

CDWick[Ra_,Rb_]:= pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}] SWick[Ra[[1]],Rb[[1]]] (CR @@ Rb)+(-1)^(parity[Ra]parity[R[Rb[[1]]]]) CR[Rb[[1]],DWick[Ra,(R @@ (Drop[(List @@ Rb),1]))]]/;(Rone[Ra] && Rtest[Rb] &&(!Rone[Rb]) && MemberQ[simplefields,Head[Ra[[1]]]] && MemberQ[compositefields,Head[Rb[[1]]]])

CDWick[Ra_,Rb_]:= pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}] Wick[Ra[[1]],Rb[[1]]] (CR @@ (Drop[(List @@ Rb),1]))+(-1)^(parity[Ra]parity[R[Rb[[1]]]]) CR[Rb[[1]],DWick[Ra,(R @@ (Drop[(List @@ Rb),1]))]]/;(Rone[Ra] && Rtest[Rb] &&(!Rone[Rb]) && MemberQ[simplefields,Head[Ra[[1]]]] && MemberQ[simplefields,Head[Rb[[1]]]])


(* ::Subsection:: *)
(*Define Pairing: determines whether two fields can be contracted*)


pairing[pair_]:=If[MemberQ[{{expX,expX},{dX,expX},{dXt,expX},{dX,dX},
{dXt,dXt},{d\[Phi],d\[Phi]},{d\[Phi]t,d\[Phi]t},{exp\[Phi]b,exp\[Phi]b},{d\[Phi],exp\[Phi]b},{exp\[Phi]tb,exp\[Phi]tb},
{d\[Phi]t,exp\[Phi]tb},{d\[Phi],exp\[Phi]f},{exp\[Phi]f,exp\[Phi]f},{exp\[Phi]b,exp\[Phi]f},{d\[Phi]t,exp\[Phi]tf},
{exp\[Phi]tf,exp\[Phi]tf},{exp\[Phi]tb,exp\[Phi]tf},{\[Psi],\[Psi]},{\[Psi]t,\[Psi]t},{b,c},{bt,ct},{\[Eta],\[Xi]},{\[Eta]t,\[Xi]t}},
Sort[pair]],1,0]


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
