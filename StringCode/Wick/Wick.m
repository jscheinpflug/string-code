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


Wick[dX[\[Mu]_,n_,z_],dX[\[Nu]_,m_,w_]]:= Wick[dX[\[Mu],n,z], dX[\[Nu],m,w]] = Module[{zd}, \[Delta][\[Mu], \[Nu]] (-1)^m D[(-1/2)*\[Alpha]p/(zd - w)^2, {zd, n + m}] /. {zd -> z}];
Wick[dXt[\[Mu]_,n_,z_],dXt[\[Nu]_,m_,w_]]:= Wick[dXt[\[Mu],n,z],dXt[\[Nu],m,w]] = Module[{zd}, \[Delta][\[Mu], \[Nu]] (-1)^m D[(-1/2)*\[Alpha]p/(zd - w)^2, {zd, n + m}] /. {zd -> z}];
Wick[d\[Phi][n_, z_], d\[Phi][m_, w_]] := Wick[d\[Phi][n, z], d\[Phi][m, w]] = Module[{zd}, (-1)^m D[-1/(zd - w)^2, {zd, n + m}]/. {zd -> z}]
Wick[d\[Phi]t[n_, z_], d\[Phi]t[m_, w_]] := Wick[d\[Phi]t[n, z], d\[Phi]t[m, w]] = Module[{zd}, (-1)^m D[-1/(zd - w)^2, {zd, n + m}] /. {zd -> z}]
Wick[b[n_, z_], c[m_, w_]] := Wick[b[n, z], c[m, w]] = Module[{zd}, (-1)^m D[1/(zd - w), {zd, n + m}] /. {zd -> z}]
Wick[c[m_, w_], b[n_, z_]] := Wick[c[m, w], b[n, z]] = Module[{zd}, -(-1)^m D[1/(zd - w), {zd, n + m}] /. {zd -> z}]
Wick[bt[n_, z_], ct[m_, w_]] := Wick[bt[n, z], ct[m, w]] = Module[{zd}, (-1)^m D[1/(zd - w), {zd, n + m}] /. {zd -> z}]
Wick[ct[m_, w_], bt[n_, z_]] := Wick[ct[m, w], bt[n, z]] = Module[{zd}, -(-1)^m D[1/(zd - w), {zd, n + m}] /. {zd -> z}]
Wick[\[Eta][n_, z_], \[Xi][m_, w_]] := Wick[\[Eta][n, z], \[Xi][m, w]] = Module[{zd}, (-1)^m D[1/(zd - w), {zd, n + m}] /. {zd -> z}]
Wick[\[Xi][m_, w_], \[Eta][n_, z_]] := Wick[\[Xi][m, w], \[Eta][n, z]] = Module[{zd}, -(-1)^m D[1/(zd - w), {zd, n + m}] /. {zd -> z}]
Wick[\[Eta]t[n_, z_], \[Xi]t[m_, w_]] := Wick[\[Eta]t[n, z], \[Xi]t[m, w]] = Module[{zd}, (-1)^m D[1/(zd - w), {zd, n + m}] /. {zd -> z}]
Wick[\[Xi]t[m_, w_], \[Eta]t[n_, z_]] := Wick[\[Xi]t[m, w], \[Eta]t[n, z]] = Module[{zd}, - (-1)^m D[1/(zd - w), {zd, n + m}] /. {zd -> z}]
Wick[\[Psi][\[Mu]_, n_, z_], \[Psi][\[Nu]_, m_, w_]] := Wick[\[Psi][\[Mu], n, z], \[Psi][\[Nu], m, w]] = Module[{zd}, \[Delta][\[Mu], \[Nu]] (-1)^m D[\[Alpha]p fermionToBosonWickRatio/(zd - w), {zd, n + m}] /. {zd -> z}]
Wick[\[Psi]t[\[Mu]_, n_, z_], \[Psi]t[\[Nu]_, m_, w_]] := Wick[\[Psi]t[\[Mu], n, z], \[Psi]t[\[Nu], m, w]] = Module[{zd}, \[Delta][\[Mu], \[Nu]] (-1)^m D[\[Alpha]p fermionToBosonWickRatio/(zd - w), {zd, n + m}] /. {zd -> z}]
Wick[Ra_?Rone, Rb_?Rone] := Wick[Ra[[1]],Rb[[1]]]


(* ::Subsection:: *)
(*Define SWick*)


SWick[dX[\[Mu]_, n_, z_], expX[k_, w_, wbar_]] := SWick[dX[\[Mu], n, z], expX[k, w, wbar]] = Module[{zd}, (-\[Alpha]p/2 I k[\[Mu]]) D[1/(zd - w), {zd, n}] /. {zd -> z}]
SWick[expX[k_, w_, wbar_], dX[\[Mu]_, n_, z_]] := SWick[expX[k, w, wbar], dX[\[Mu], n, z]] = Module[{zd}, (-\[Alpha]p/2 I k[\[Mu]]) D[1/(zd - w), {zd, n}] /. {zd -> z}]
SWick[dXt[\[Mu]_, n_, z_], expX[k_, w_, wbar_]] := SWick[dXt[\[Mu], n, z], expX[k, w, wbar]] = Module[{zd}, (-\[Alpha]p/2 I k[\[Mu]]) D[1/(zd - wbar), {zd, n}] /. {zd -> z}]
SWick[expX[k_, w_, wbar_], dXt[\[Mu]_, n_, z_]] := SWick[expX[k, w, wbar], dXt[\[Mu], n, z]] = Module[{zd}, (-\[Alpha]p/2 I k[\[Mu]]) D[1/(zd - wbar), {zd, n}] /. {zd -> z}]


SWick[d\[Phi][n_, z_], exp\[Phi]b[a_, w_]] := SWick[d\[Phi][n, z], exp\[Phi]b[a, w]] = Module[{zd}, (-a) D[1/(zd - w), {zd, n}] /. {zd -> z}]
SWick[exp\[Phi]b[a_, w_], d\[Phi][n_, z_]] := SWick[exp\[Phi]b[a, w], d\[Phi][n, z]] = Module[{zd}, (-a) D[1/(zd - w), {zd, n}] /. {zd -> z}]
SWick[d\[Phi][n_, z_], exp\[Phi]f[a_, w_]] := SWick[d\[Phi][n, z], exp\[Phi]f[a, w]] = Module[{zd}, (-a) D[1/(zd - w), {zd, n}] /. {zd -> z}]
SWick[exp\[Phi]f[a_, w_], d\[Phi][n_, z_]] := SWick[exp\[Phi]f[a, w], d\[Phi][n, z]] = Module[{zd}, (-a) D[1/(zd - w), {zd, n}] /. {zd -> z}]


SWick[d\[Phi]t[n_, z_], exp\[Phi]tb[a_, w_]] := SWick[d\[Phi]t[n, z], exp\[Phi]tb[a, w]] = Module[{zd}, (-a) D[1/(zd - w), {zd, n}] /. {zd -> z}]
SWick[exp\[Phi]tb[a_, w_], d\[Phi]t[n_, z_]] := SWick[exp\[Phi]tb[a, w], d\[Phi]t[n, z]] = Module[{zd}, (-a) D[1/(zd - w), {zd, n}] /. {zd -> z}]
SWick[d\[Phi]t[n_, z_], exp\[Phi]tf[a_, w_]] := SWick[d\[Phi]t[n, z], exp\[Phi]tf[a, w]] = Module[{zd}, (-a) D[1/(zd - w), {zd, n}] /. {zd -> z}]
SWick[exp\[Phi]tf[a_, w_], d\[Phi]t[n_, z_]] := SWick[exp\[Phi]tf[a, w], d\[Phi]t[n, z]] = Module[{zd}, (-a) D[1/(zd - w), {zd, n}] /. {zd -> z}]


SWick[Ra_?Rone, Rb_?Rone] := SWick[Ra[[1]],Rb[[1]]]


(* ::Subsection:: *)
(*Define MWick*)


MWick[expX[p_,z_,zbar_],expX[k_,w_,wbar_]]:=MWick[expX[p,z,zbar],expX[k,w,wbar]] = ((z-w) (zbar-wbar))^(\[Alpha]p/2 dot[p,k])


MWick[exp\[Phi]b[a_,z_],exp\[Phi]b[b_,w_]]:= MWick[exp\[Phi]b[a,z],exp\[Phi]b[b,w]] = (z-w)^(-a b)
MWick[exp\[Phi]b[a_,z_],exp\[Phi]f[b_,w_]]:= MWick[exp\[Phi]b[a,z],exp\[Phi]f[b,w]] = (z-w)^(-a b)
MWick[exp\[Phi]f[a_,z_],exp\[Phi]b[b_,w_]]:= MWick[exp\[Phi]f[a,z],exp\[Phi]b[b,w]] = (z-w)^(-a b)
MWick[exp\[Phi]f[a_,z_],exp\[Phi]f[b_,w_]]:= MWick[exp\[Phi]f[a,z],exp\[Phi]f[b,w]] = (z-w)^(-a b)


MWick[exp\[Phi]tb[a_,z_],exp\[Phi]tb[b_,w_]]:= MWick[exp\[Phi]tb[a,z],exp\[Phi]tb[b,w]] = (z-w)^(-a b)
MWick[exp\[Phi]tb[a_,z_],exp\[Phi]tf[b_,w_]]:= MWick[exp\[Phi]tb[a,z],exp\[Phi]tf[b,w]] = (z-w)^(-a b)
MWick[exp\[Phi]tf[a_,z_],exp\[Phi]tb[b_,w_]]:= MWick[exp\[Phi]tf[a,z],exp\[Phi]tb[b,w]] = (z-w)^(-a b)
MWick[exp\[Phi]tf[a_,z_],exp\[Phi]tf[b_,w_]]:= MWick[exp\[Phi]tf[a,z],exp\[Phi]tf[b,w]] = (z-w)^(-a b)


MWick[Ra_?Rone, Rb_?Rone] := MWick[Ra[[1]],Rb[[1]]]


(* ::Subsection:: *)
(*Define DWick: Wick contractions for normal-ordered products of fields*)


DWick[Ra_,Rb_]:= pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}] Wick[Ra,Rb]/;(Rone[Ra] && Rone[Rb] && isSimple[Head[Ra[[1]]]] && isSimple[Head[Rb[[1]]]])

DWick[Ra_,Rb_]:= pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}] SWick[Ra,Rb] Rb/;(Rone[Ra] && Rone[Rb] && isSimple[Head[Ra[[1]]]] && isComposite[Head[Rb[[1]]]])

DWick[Ra_,Rb_]:=pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}] SWick[Ra,Rb]+Rb/;(Rone[Ra] && Rone[Rb] && isComposite[Head[Ra[[1]]]] && isSimple[Head[Rb[[1]]]])

DWick[Ra_,Rb_]:= If[pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}]==1, MWick[Ra,Rb],1] Rb/;(Rone[Ra] && Rone[Rb] && isComposite[Head[Ra[[1]]]] && isComposite[Head[Rb[[1]]]])

DWick[Ra_,Rb_]:= pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}] SWick[Ra[[1]],Rb[[1]]] Rb+(-1)^(parity[Ra]parity[R[Rb[[1]]]]) R[Rb[[1]],
DWick[Ra,(R @@ (Drop[(List @@ Rb),1]))]]/;(Rone[Ra] && Rtest[Rb] &&(!Rone[Rb]) && isSimple[Head[Ra[[1]]]] && isComposite[Head[Rb[[1]]]])

DWick[Ra_,Rb_]:= pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}] Wick[Ra[[1]],Rb[[1]]] (R @@ (Drop[(List @@ Rb),1]))+(-1)^(parity[Ra]parity[R[Rb[[1]]]]) R[Rb[[1]],
DWick[Ra,(R @@ (Drop[(List @@ Rb),1]))]]/;(Rone[Ra] && Rtest[Rb] &&(!Rone[Rb]) && isSimple[Head[Ra[[1]]]] && isSimple[Head[Rb[[1]]]])

DWick[Ra_,Rb_]:= pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}] SWick[Ra[[1]],Rb[[1]]] DWick[Ra,(R @@ (Drop[(List @@ Rb),1]))]+ R[Rb[[1]],
DWick[Ra,(R @@ (Drop[(List @@ Rb),1]))]]/;(Rone[Ra] && Rtest[Rb] &&(!Rone[Rb]) && isComposite[Head[Ra[[1]]]] && isSimple[Head[Rb[[1]]]])

DWick[Ra_,Rb_]:= If[pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}]==1, MWick[Ra[[1]],Rb[[1]]],1] R[Rb[[1]],
DWick[Ra,(R @@ (Drop[(List @@ Rb),1]))]]/;(Rone[Ra] && Rtest[Rb] &&(!Rone[Rb]) && isComposite[Head[Ra[[1]]]] && isComposite[Head[Rb[[1]]]])



(* ::Subsection::Initialization:: *)
(*Define CDWick*)


(* ::Input::Initialization:: *)
CDWick[Ra_,Rb_]:= pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}] Wick[Ra,Rb]/;(Rone[Ra] && Rone[Rb] && isSimple[Head[Ra[[1]]]] && isSimple[Head[Rb[[1]]]])

CDWick[Ra_,Rb_]:= pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}] SWick[Ra,Rb] (CR @@ Rb)/;(Rone[Ra] && Rone[Rb] && isSimple[Head[Ra[[1]]]] && isComposite[Head[Rb[[1]]]])

CDWick[Ra_,Rb_]:= pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}] SWick[Ra[[1]],Rb[[1]]] (CR @@ Rb)+(-1)^(parity[Ra]parity[R[Rb[[1]]]]) CR[Rb[[1]],DWick[Ra,(R @@ (Drop[(List @@ Rb),1]))]]/;(Rone[Ra] && Rtest[Rb] &&(!Rone[Rb]) && isSimple[Head[Ra[[1]]]] && isComposite[Head[Rb[[1]]]])

CDWick[Ra_,Rb_]:= pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}] Wick[Ra[[1]],Rb[[1]]] (CR @@ (Drop[(List @@ Rb),1]))+(-1)^(parity[Ra]parity[R[Rb[[1]]]]) CR[Rb[[1]],DWick[Ra,(R @@ (Drop[(List @@ Rb),1]))]]/;(Rone[Ra] && Rtest[Rb] &&(!Rone[Rb]) && isSimple[Head[Ra[[1]]]] && isSimpleHead[Rb[[1]]])


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
