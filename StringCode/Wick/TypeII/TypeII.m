(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Wick`TypeII`"]
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`TypeII`"];
Needs["StringCode`Wick`"];
Needs["StringCode`Conventions`TypeII`"];


(* ::Section:: *)
(*Declare public methods*)


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Define Wick*)


(* ::Subsubsection:: *)
(*Free boson*)


Wick[dX[\[Mu]_,n_,z_],dX[\[Nu]_,m_,w_]]:= Wick[dX[\[Mu],n,z], dX[\[Nu],m,w]] = Module[{zd}, \[Delta][\[Mu], \[Nu]] (-1)^m D[(-1/2)*\[Alpha]p/(zd - w)^2, {zd, n + m}] /. {zd -> z}];
Wick[dXt[\[Mu]_,n_,z_],dXt[\[Nu]_,m_,w_]]:= Wick[dXt[\[Mu],n,z],dXt[\[Nu],m,w]] = Module[{zd}, \[Delta][\[Mu], \[Nu]] (-1)^m D[(-1/2)*\[Alpha]p/(zd - w)^2, {zd, n + m}] /. {zd -> z}];


(* ::Subsubsection:: *)
(*Free fermion*)


Wick[\[Psi][\[Mu]_, n_, z_], \[Psi][\[Nu]_, m_, w_]] := Wick[\[Psi][\[Mu], n, z], \[Psi][\[Nu], m, w]] = Module[{zd}, \[Delta][\[Mu], \[Nu]] (-1)^m D[fermionToBosonWickRatio/(zd - w), {zd, n + m}] /. {zd -> z}]
Wick[\[Psi]t[\[Mu]_, n_, z_], \[Psi]t[\[Nu]_, m_, w_]] := Wick[\[Psi]t[\[Mu], n, z], \[Psi]t[\[Nu], m, w]] = Module[{zd}, \[Delta][\[Mu], \[Nu]] (-1)^m D[fermionToBosonWickRatio/(zd - w), {zd, n + m}] /. {zd -> z}]


(* ::Subsubsection:: *)
(*Superghosts*)


Wick[d\[Phi][n_, z_], d\[Phi][m_, w_]] := Wick[d\[Phi][n, z], d\[Phi][m, w]] = Module[{zd}, (-1)^m D[-1/(zd - w)^2, {zd, n + m}]/. {zd -> z}]
Wick[d\[Phi]t[n_, z_], d\[Phi]t[m_, w_]] := Wick[d\[Phi]t[n, z], d\[Phi]t[m, w]] = Module[{zd}, (-1)^m D[-1/(zd - w)^2, {zd, n + m}] /. {zd -> z}]
Wick[\[Eta][n_, z_], \[Xi][m_, w_]] := Wick[\[Eta][n, z], \[Xi][m, w]] = Module[{zd}, (-1)^m D[1/(zd - w), {zd, n + m}] /. {zd -> z}]
Wick[\[Xi][m_, w_], \[Eta][n_, z_]] := Wick[\[Xi][m, w], \[Eta][n, z]] = Module[{zd}, -(-1)^m D[1/(zd - w), {zd, n + m}] /. {zd -> z}]
Wick[\[Eta]t[n_, z_], \[Xi]t[m_, w_]] := Wick[\[Eta]t[n, z], \[Xi]t[m, w]] = Module[{zd}, (-1)^m D[1/(zd - w), {zd, n + m}] /. {zd -> z}]
Wick[\[Xi]t[m_, w_], \[Eta]t[n_, z_]] := Wick[\[Xi]t[m, w], \[Eta]t[n, z]] = Module[{zd}, - (-1)^m D[1/(zd - w), {zd, n + m}] /. {zd -> z}]


(* ::Subsection:: *)
(*Define SWick*)


(* ::Subsubsection:: *)
(*Free boson*)


SWick[dX[\[Mu]_, n_, z_], expX[k_, w_, wbar_]] := SWick[dX[\[Mu], n, z], expX[k, w, wbar]] = Module[{zd}, (-\[Alpha]p/2 I k[\[Mu]]) D[1/(zd - w), {zd, n}] /. {zd -> z}]
SWick[expX[k_, w_, wbar_], dX[\[Mu]_, n_, z_]] := SWick[expX[k, w, wbar], dX[\[Mu], n, z]] = Module[{zd}, (-\[Alpha]p/2 I k[\[Mu]]) D[1/(zd - w), {zd, n}] /. {zd -> z}]
SWick[dX[\[Mu]_, n_, z_], expXHolo[k_, w_]] := SWick[dX[\[Mu], n, z], expXHolo[k, w]] = Module[{zd}, (-\[Alpha]p/2 I k[\[Mu]]) D[1/(zd - w), {zd, n}] /. {zd -> z}]
SWick[expXHolo[k_, w_], dX[\[Mu]_, n_, z_]] := SWick[expX[k, w], dX[\[Mu], n, z]] = Module[{zd}, (-\[Alpha]p/2 I k[\[Mu]]) D[1/(zd - w), {zd, n}] /. {zd -> z}]

SWick[dXt[\[Mu]_, n_, z_], expX[k_, w_, wbar_]] := SWick[dXt[\[Mu], n, z], expX[k, w, wbar]] = Module[{zd}, (-\[Alpha]p/2 I k[\[Mu]]) D[1/(zd - wbar), {zd, n}] /. {zd -> z}]
SWick[expX[k_, w_, wbar_], dXt[\[Mu]_, n_, z_]] := SWick[expX[k, w, wbar], dXt[\[Mu], n, z]] = Module[{zd}, (-\[Alpha]p/2 I k[\[Mu]]) D[1/(zd - wbar), {zd, n}] /. {zd -> z}]
SWick[dXt[\[Mu]_, n_, z_], expXAntiHolo[k_, wbar_]] := SWick[dXt[\[Mu], n, z], expXAntiHolo[k, wbar]] = Module[{zd}, (-\[Alpha]p/2 I k[\[Mu]]) D[1/(zd - wbar), {zd, n}] /. {zd -> z}]
SWick[expXAntiHolo[k_, wbar_], dXt[\[Mu]_, n_, z_]] := SWick[expXAntiHolo[k, wbar], dXt[\[Mu], n, z]] = Module[{zd}, (-\[Alpha]p/2 I k[\[Mu]]) D[1/(zd - wbar), {zd, n}] /. {zd -> z}]

SWick[dX[\[Mu]_, n_, z_], ProfileX[profile_, ders_, w_, wbar_]] := SWick[dX[\[Mu], n, z], ProfileX[profile, ders, w, wbar]] = 
Module[{zd}, (-\[Alpha]p/2 der[profile][\[Mu]]) D[1/(zd - w), {zd, n}] /. {zd -> z}]
SWick[ProfileX[profile_, ders_, w_, wbar_], dX[\[Mu]_, n_, z_]] := SWick[ProfileX[profile, ders, w, wbar], dX[\[Mu], n, z]] =
 Module[{zd}, (-\[Alpha]p/2 der[profile][\[Mu]]) D[1/(zd - w), {zd, n}] /. {zd -> z}]
SWick[dX[\[Mu]_, n_, z_], ProfileXHolo[profile_, ders_, w_]] := SWick[dX[\[Mu], n, z], ProfileXHolo[profile, ders, w]] = 
Module[{zd}, (-\[Alpha]p/2 der[profile][\[Mu]]) D[1/(zd - w), {zd, n}] /. {zd -> z}]
SWick[ProfileXHolo[profile_, ders_, w_], dX[\[Mu]_, n_, z_]] := SWick[ProfileXHolo[profile, ders, w], dX[\[Mu], n, z]] =
 Module[{zd}, (-\[Alpha]p/2 der[profile][\[Mu]]) D[1/(zd - w), {zd, n}] /. {zd -> z}]

SWick[dXt[\[Mu]_, n_, z_], ProfileX[profile_, ders_, w_, wbar_]] := SWick[dXt[\[Mu], n, z], ProfileX[profile, ders, w, wbar]] = 
Module[{zd}, (-\[Alpha]p/2 der[profile][\[Mu]]) D[1/(zd - wbar), {zd, n}] /. {zd -> z}]
SWick[ProfileX[profile_, ders_, w_, wbar_], dXt[\[Mu]_, n_, z_]] := SWick[ProfileX[profile, ders, w, wbar], dXt[\[Mu], n, z]] =
 Module[{zd}, (-\[Alpha]p/2 der[profile][\[Mu]]) D[1/(zd - wbar), {zd, n}] /. {zd -> z}]
SWick[dXt[\[Mu]_, n_, z_], ProfileXAntiHolo[profile_, ders_, wbar_]] := SWick[dXt[\[Mu], n, z], ProfileXAntiHolo[profile, ders, wbar]] = 
Module[{zd}, (-\[Alpha]p/2 der[profile][\[Mu]]) D[1/(zd - wbar), {zd, n}] /. {zd -> z}]
SWick[ProfileXAntiHolo[profile_, ders_, wbar_], dXt[\[Mu]_, n_, z_]] := SWick[ProfileXAntiHolo[profile, ders, wbar], dXt[\[Mu], n, z]] =
 Module[{zd}, (-\[Alpha]p/2 der[profile][\[Mu]]) D[1/(zd - wbar), {zd, n}] /. {zd -> z}]


(* ::Subsubsection:: *)
(*Superghosts*)


SWick[d\[Phi][n_, z_], exp\[Phi]b[a_, w_]] := SWick[d\[Phi][n, z], exp\[Phi]b[a, w]] = Module[{zd}, (-a) D[1/(zd - w), {zd, n}] /. {zd -> z}]
SWick[exp\[Phi]b[a_, w_], d\[Phi][n_, z_]] := SWick[exp\[Phi]b[a, w], d\[Phi][n, z]] = Module[{zd}, (-a) D[1/(zd - w), {zd, n}] /. {zd -> z}]
SWick[d\[Phi][n_, z_], exp\[Phi]f[a_, w_]] := SWick[d\[Phi][n, z], exp\[Phi]f[a, w]] = Module[{zd}, (-a) D[1/(zd - w), {zd, n}] /. {zd -> z}]
SWick[exp\[Phi]f[a_, w_], d\[Phi][n_, z_]] := SWick[exp\[Phi]f[a, w], d\[Phi][n, z]] = Module[{zd}, (-a) D[1/(zd - w), {zd, n}] /. {zd -> z}]


SWick[d\[Phi]t[n_, z_], exp\[Phi]tb[a_, w_]] := SWick[d\[Phi]t[n, z], exp\[Phi]tb[a, w]] = Module[{zd}, (-a) D[1/(zd - w), {zd, n}] /. {zd -> z}]
SWick[exp\[Phi]tb[a_, w_], d\[Phi]t[n_, z_]] := SWick[exp\[Phi]tb[a, w], d\[Phi]t[n, z]] = Module[{zd}, (-a) D[1/(zd - w), {zd, n}] /. {zd -> z}]
SWick[d\[Phi]t[n_, z_], exp\[Phi]tf[a_, w_]] := SWick[d\[Phi]t[n, z], exp\[Phi]tf[a, w]] = Module[{zd}, (-a) D[1/(zd - w), {zd, n}] /. {zd -> z}]
SWick[exp\[Phi]tf[a_, w_], d\[Phi]t[n_, z_]] := SWick[exp\[Phi]tf[a, w], d\[Phi]t[n, z]] = Module[{zd}, (-a) D[1/(zd - w), {zd, n}] /. {zd -> z}]


(* ::Subsection:: *)
(*Define MWick*)


(* ::Subsubsection:: *)
(*Free boson*)


MWick[expX[p_,z_,zbar_],expX[k_,w_,wbar_]]:=MWick[expX[p,z,zbar],expX[k,w,wbar]] = ((z-w) (zbar-wbar))^(\[Alpha]p/2 dot[p,k])
MWick[expX[p_,z_,zbar_],ProfileX[profile_, ders_, w_,wbar_]]:=MWick[expX[p,z,zbar],ProfileX[profile, ders, w,wbar]] = ((z-w) (zbar-wbar))^(-I \[Alpha]p/2 dot[p,der[profile]])
MWick[ProfileX[profile_, ders_, z_,zbar_],expX[p_,w_,wbar_]]:=MWick[ProfileX[profile, ders, z,zbar], expX[p,w,wbar]] = ((z-w) (zbar-wbar))^(-I \[Alpha]p/2 dot[p,der[profile]])
MWick[ProfileX[profile1_, ders1_, z_,zbar_],ProfileX[profile2_, ders2_, w_,wbar_]]:=MWick[ProfileX[profile1, ders1,z,zbar],ProfileX[profile2, ders2, w,wbar]] = 
((z-w) (zbar-wbar))^(-\[Alpha]p/2 dot[der[profile1],der[profile2]])

MWick[expXHolo[p_,z_],expXHolo[k_,w_]]:=MWick[expXHolo[p,z],expXHolo[k,w]] = (z-w)^(\[Alpha]p/2 dot[p,k])
MWick[expXHolo[p_,z_],ProfileXHolo[profile_, ders_, w_]]:=MWick[expXHolo[p,z],ProfileXHolo[profile, ders, w]] = (z-w)^(-I \[Alpha]p/2 dot[p,der[profile]])
MWick[ProfileXHolo[profile_, ders_, z_],expXHolo[p_,w_]]:=MWick[ProfileXHolo[profile, ders, z], expXHolo[p,w]] = (z-w)^(-I \[Alpha]p/2 dot[p,der[profile]])
MWick[ProfileXHolo[profile1_, ders1_, z_],ProfileXHolo[profile2_, ders2_, w_]]:=MWick[ProfileXHolo[profile1, ders1,z],ProfileXHolo[profile2, ders2, w]] = 
(z-w)^(-\[Alpha]p/2 dot[der[profile1],der[profile2]])

MWick[expXAntiHolo[p_,zbar_],expXAntiHolo[k_,wbar_]]:=MWick[expXAntiHolo[p,zbar],expXAntiHolo[k,wbar]] = (zbar-wbar)^(\[Alpha]p/2 dot[p,k])
MWick[expXAntiHolo[p_,zbar_],ProfileXAntiHolo[profile_, ders_, wbar_]]:=MWick[expXAntiHolo[p,zbar],ProfileXAntiHolo[profile, ders, wbar]] = 
(zbar-wbar)^(-I \[Alpha]p/2 dot[p,der[profile]])
MWick[ProfileXAntiHolo[profile_, ders_, zbar_],expXAntiHolo[p_,wbar_]]:=MWick[ProfileXAntiHolo[profile, ders, zbar], expXAntiHolo[p,wbar]] = 
(zbar-wbar)^(-I \[Alpha]p/2 dot[p,der[profile]])
MWick[ProfileXAntiHolo[profile1_, ders1_, zbar_],ProfileXAntiHolo[profile2_, ders2_, wbar_]]:=
MWick[ProfileXAntiHolo[profile1, ders1,zbar],ProfileXAntiHolo[profile2, ders2, wbar]] = (zbar-wbar)^(-\[Alpha]p/2 dot[der[profile1],der[profile2]])


(* ::Subsubsection:: *)
(*Superghosts*)


MWick[exp\[Phi]b[a_,z_],exp\[Phi]b[b_,w_]]:= MWick[exp\[Phi]b[a,z],exp\[Phi]b[b,w]] = (z-w)^(-a b)
MWick[exp\[Phi]b[a_,z_],exp\[Phi]f[b_,w_]]:= MWick[exp\[Phi]b[a,z],exp\[Phi]f[b,w]] = (z-w)^(-a b)
MWick[exp\[Phi]f[a_,z_],exp\[Phi]b[b_,w_]]:= MWick[exp\[Phi]f[a,z],exp\[Phi]b[b,w]] = (z-w)^(-a b)
MWick[exp\[Phi]f[a_,z_],exp\[Phi]f[b_,w_]]:= MWick[exp\[Phi]f[a,z],exp\[Phi]f[b,w]] = (z-w)^(-a b)


MWick[exp\[Phi]tb[a_,z_],exp\[Phi]tb[b_,w_]]:= MWick[exp\[Phi]tb[a,z],exp\[Phi]tb[b,w]] = (z-w)^(-a b)
MWick[exp\[Phi]tb[a_,z_],exp\[Phi]tf[b_,w_]]:= MWick[exp\[Phi]tb[a,z],exp\[Phi]tf[b,w]] = (z-w)^(-a b)
MWick[exp\[Phi]tf[a_,z_],exp\[Phi]tb[b_,w_]]:= MWick[exp\[Phi]tf[a,z],exp\[Phi]tb[b,w]] = (z-w)^(-a b)
MWick[exp\[Phi]tf[a_,z_],exp\[Phi]tf[b_,w_]]:= MWick[exp\[Phi]tf[a,z],exp\[Phi]tf[b,w]] = (z-w)^(-a b)


(* ::Subsection:: *)
(*Extend pairingList: determines whether two fields can be contracted*)


pairingList = Map[Sort,Join[pairingList, {
{ProfileXHolo, ProfileXHolo}, {ProfileXAntiHolo, ProfileXAntiHolo},{ProfileX,ProfileX},
{expXHolo, expXHolo}, {expXAntiHolo, expXAntiHolo},{expX,expX},
{ProfileXHolo, expXHolo}, {ProfileXAntiHolo, expXAntiHolo},{ProfileX, expX},
{dX,expX},{dXt,expX},{dX,ProfileX},{dXt,ProfileX},
{dX,expXHolo},{dXt,expXAntiHolo},{dX,ProfileXHolo},{dXt,ProfileXAntiHolo},
{dX,dX}, {dXt,dXt},
{d\[Phi],d\[Phi]},{d\[Phi]t,d\[Phi]t},{exp\[Phi]b,exp\[Phi]b},{d\[Phi],exp\[Phi]b},{exp\[Phi]tb,exp\[Phi]tb}, {d\[Phi]t,exp\[Phi]tb},{d\[Phi],exp\[Phi]f},{exp\[Phi]f,exp\[Phi]f},{exp\[Phi]b,exp\[Phi]f},{d\[Phi]t,exp\[Phi]tf},
{exp\[Phi]tf,exp\[Phi]tf},{exp\[Phi]tb,exp\[Phi]tf},{\[Psi],\[Psi]},{\[Psi]t,\[Psi]t},{\[Eta],\[Xi]},{\[Eta]t,\[Xi]t}}]];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
