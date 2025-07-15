(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Wick`Bosonic`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`Bosonic`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`Bosonic`"];
Needs["StringCode`Wick`"];
Needs["StringCode`Conventions`Bosonic`"];


(* ::Section:: *)
(*Declare public methods*)


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


Wick[X[\[Mu]_,z_, zbar_],X[\[Nu]_,w_,wbar_]]:= Wick[X[\[Mu],z, zbar], X[\[Nu],w,wbar]] = \[Delta][\[Mu], \[Nu]] (-1/2)*\[Alpha]p (Log[z-w]+Log[zbar-wbar]);
Wick[X[\[Mu]_,z_, zbar_],dX[\[Nu]_,n_,w_]]:= Wick[X[\[Mu],z, zbar], dX[\[Nu],n,w]] = Module[{wd}, \[Delta][\[Mu], \[Nu]] D[(-1/2)*\[Alpha]p (-1/(z-wd)), {wd, n}] /. {wd -> w}];
Wick[dX[\[Nu]_,n_,z_], X[\[Mu]_,w_, wbar_]]:= Wick[dX[\[Nu],n,z], X[\[Mu],w, wbar]] = Module[{zd}, \[Delta][\[Mu], \[Nu]] D[(-1/2)*\[Alpha]p 1/(zd-w), {zd, n}] /. {zd -> z}];
Wick[X[\[Mu]_,z_, zbar_],dXt[\[Nu]_,n_,w_]]:= Wick[X[\[Mu],z, zbar], dXt[\[Nu],n,w]] = Module[{wd}, \[Delta][\[Mu], \[Nu]] D[(-1/2)*\[Alpha]p (-1/(zbar-wd)), {wd, n}] /. {wd -> w}];
Wick[dXt[\[Nu]_,n_,z_], X[\[Mu]_,w_, wbar_]]:= Wick[dXt[\[Nu],n,z], X[\[Mu],w, wbar]] = Module[{zd}, \[Delta][\[Mu], \[Nu]] D[(-1/2)*\[Alpha]p 1/(zd-wbar), {zd, n}] /. {zd -> z}];
Wick[dX[\[Mu]_,n_,z_],dX[\[Nu]_,m_,w_]]:= Wick[dX[\[Mu],n,z], dX[\[Nu],m,w]] = Module[{zd}, \[Delta][\[Mu], \[Nu]] (-1)^m D[(-1/2)*\[Alpha]p/(zd - w)^2, {zd, n + m}] /. {zd -> z}];
Wick[dXt[\[Mu]_,n_,z_],dXt[\[Nu]_,m_,w_]]:= Wick[dXt[\[Mu],n,z],dXt[\[Nu],m,w]] = Module[{zd}, \[Delta][\[Mu], \[Nu]] (-1)^m D[(-1/2)*\[Alpha]p/(zd - w)^2, {zd, n + m}] /. {zd -> z}];


(* ::Subsection:: *)
(*Define SWick*)


SWick[X[\[Mu]_, z_, zbar_], expX[k_, w_, wbar_]] := SWick[X[\[Mu], z, zbar], expX[k, w, wbar]] = (-\[Alpha]p/2 I k[\[Mu]]) (Log[z-w]+Log[zbar-wbar])
SWick[expX[k_, w_, wbar_], X[\[Mu]_, z_, zbar_]] := SWick[expX[k, w, wbar], X[\[Mu], z, zbar]] = (-\[Alpha]p/2 I k[\[Mu]]) (Log[w-z]+Log[wbar-zbar])
SWick[dX[\[Mu]_, n_, z_], expX[k_, w_, wbar_]] := SWick[dX[\[Mu], n, z], expX[k, w, wbar]] = Module[{zd}, (-\[Alpha]p/2 I k[\[Mu]]) D[1/(zd - w), {zd, n}] /. {zd -> z}]
SWick[expX[k_, w_, wbar_], dX[\[Mu]_, n_, z_]] := SWick[expX[k, w, wbar], dX[\[Mu], n, z]] = Module[{zd}, (-\[Alpha]p/2 I k[\[Mu]]) D[1/(zd - w), {zd, n}] /. {zd -> z}]
SWick[dXt[\[Mu]_, n_, z_], expX[k_, w_, wbar_]] := SWick[dXt[\[Mu], n, z], expX[k, w, wbar]] = Module[{zd}, (-\[Alpha]p/2 I k[\[Mu]]) D[1/(zd - wbar), {zd, n}] /. {zd -> z}]
SWick[expX[k_, w_, wbar_], dXt[\[Mu]_, n_, z_]] := SWick[expX[k, w, wbar], dXt[\[Mu], n, z]] = Module[{zd}, (-\[Alpha]p/2 I k[\[Mu]]) D[1/(zd - wbar), {zd, n}] /. {zd -> z}]


(* ::Subsection:: *)
(*Define MWick*)


MWick[expX[p_,z_,zbar_],expX[k_,w_,wbar_]]:=MWick[expX[p,z,zbar],expX[k,w,wbar]] = ((z-w) (zbar-wbar))^(\[Alpha]p/2 dot[p,k])


(* ::Subsection:: *)
(*Extend pairingList: determines whether two fields can be contracted*)


pairingList = Map[Sort,Join[pairingList, {{X, expX}, {X,X},{X,dX}, {X, dXt},{expX,expX},{dX,expX},{dXt,expX},{dX,dX}, {dXt,dXt}}]];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
