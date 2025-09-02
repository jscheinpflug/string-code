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
{d\[Phi],d\[Phi]},{d\[Phi]t,d\[Phi]t},{exp\[Phi]b,exp\[Phi]b},{d\[Phi],exp\[Phi]b},{exp\[Phi]tb,exp\[Phi]tb}, {d\[Phi]t,exp\[Phi]tb},{d\[Phi],exp\[Phi]f},{exp\[Phi]f,exp\[Phi]f},{exp\[Phi]b,exp\[Phi]f},{d\[Phi]t,exp\[Phi]tf},
{exp\[Phi]tf,exp\[Phi]tf},{exp\[Phi]tb,exp\[Phi]tf}, {\[Eta],\[Xi]},{\[Eta]t,\[Xi]t}}]];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
