(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Wick`"]
Needs["StringCode`Symbols`"];
Needs["StringCode`NormalOrdering`"];


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


Begin["Private`"];


(* ::Subsection:: *)
(*Define Wick*)


Wick[b[n_, z_], c[m_, w_]] := Wick[b[n, z], c[m, w]] = Module[{zd}, (-1)^m D[1/(zd - w), {zd, n + m}] /. {zd -> z}];
Wick[c[m_, w_], b[n_, z_]] := Wick[c[m, w], b[n, z]] = Module[{zd}, -(-1)^m D[1/(zd - w), {zd, n + m}] /. {zd -> z}];
Wick[bt[n_, z_], ct[m_, w_]] := Wick[bt[n, z], ct[m, w]] = Module[{zd}, (-1)^m D[1/(zd - w), {zd, n + m}] /. {zd -> z}];
Wick[ct[m_, w_], bt[n_, z_]] := Wick[ct[m, w], bt[n, z]] = Module[{zd}, -(-1)^m D[1/(zd - w), {zd, n + m}] /. {zd -> z}];
Wick[Ra_?Rone, Rb_?Rone] := Wick[Ra[[1]],Rb[[1]]]


(* ::Subsection:: *)
(*Define SWick*)


SWick[Ra_?Rone, Rb_?Rone] := SWick[Ra[[1]],Rb[[1]]]


(* ::Subsection:: *)
(*Define MWick*)


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


(* ::Subsection:: *)
(*Define CDWick*)


CDWick[Ra_,Rb_]:= pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}] Wick[Ra,Rb]/;(Rone[Ra] && Rone[Rb] && isSimple[Head[Ra[[1]]]] && isSimple[Head[Rb[[1]]]])

CDWick[Ra_,Rb_]:= pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}] SWick[Ra,Rb] (CR @@ Rb)/;(Rone[Ra] && Rone[Rb] && isSimple[Head[Ra[[1]]]] && isComposite[Head[Rb[[1]]]])

CDWick[Ra_,Rb_]:= pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}] SWick[Ra[[1]],Rb[[1]]] (CR @@ Rb)+(-1)^(parity[Ra]parity[R[Rb[[1]]]]) CR[Rb[[1]],DWick[Ra,(R @@ (Drop[(List @@ Rb),1]))]]/;(Rone[Ra] && Rtest[Rb] &&(!Rone[Rb]) && isSimple[Head[Ra[[1]]]] && isComposite[Head[Rb[[1]]]])

CDWick[Ra_,Rb_]:= pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}] Wick[Ra[[1]],Rb[[1]]] (CR @@ (Drop[(List @@ Rb),1]))+(-1)^(parity[Ra]parity[R[Rb[[1]]]]) CR[Rb[[1]],DWick[Ra,(R @@ (Drop[(List @@ Rb),1]))]]/;(Rone[Ra] && Rtest[Rb] &&(!Rone[Rb]) && isSimple[Head[Ra[[1]]]] && isSimple[Head[Rb[[1]]]])


(* ::Subsection:: *)
(*Define Pairing: determines whether two fields can be contracted*)


pairingList = {{b,c},{bt,ct}};

pairing[pair_]:= pairing[pair] = If[MemberQ[pairingList,Sort[pair]],1,0]


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
