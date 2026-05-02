(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Wick`Bosonic`FlatSpace`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`Bosonic`"];
Needs["StringCode`Symbols`Bosonic`FlatSpace`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`Bosonic`"];
Needs["StringCode`Wick`"];
Needs["StringCode`Wick`Bosonic`"];
Needs["StringCode`Conventions`Bosonic`"];


(* ::Section:: *)
(*Declare public methods*)


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Define Wick*)


Wick[dX[\[Mu]_,n_,z_],dX[\[Nu]_,m_,w_]]:= Wick[dX[\[Mu],n,z], dX[\[Nu],m,w]] = Module[{zd}, flatSpaceMetricTensor[\[Mu], \[Nu]] (-1)^m D[(-1/2)*\[Alpha]p/(zd - w)^2, {zd, n + m}] /. {zd -> z}];
Wick[dXt[\[Mu]_,n_,z_],dXt[\[Nu]_,m_,w_]]:= Wick[dXt[\[Mu],n,z], dXt[\[Nu],m,w]] = Module[{zd}, flatSpaceMetricTensor[\[Mu], \[Nu]] (-1)^m D[(-1/2)*\[Alpha]p/(zd - w)^2, {zd, n + m}] /. {zd -> z}];


(* ::Subsection:: *)
(*Define SWick*)


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


(* ::Subsection:: *)
(*Define MWick*)


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


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
