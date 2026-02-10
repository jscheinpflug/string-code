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


DWick::usage = "Computes Wick contractions between normal-ordered products";


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Define Wick*)


Wick[b[n_, z_], c[m_, w_]] := Wick[b[n, z], c[m, w]] = Module[{zd}, (-1)^m D[1/(zd - w), {zd, n + m}] /. {zd -> z}];
Wick[c[m_, w_], b[n_, z_]] := Wick[c[m, w], b[n, z]] = Module[{zd}, -(-1)^m D[1/(zd - w), {zd, n + m}] /. {zd -> z}];
Wick[bt[n_, z_], ct[m_, w_]] := Wick[bt[n, z], ct[m, w]] = Module[{zd}, (-1)^m D[1/(zd - w), {zd, n + m}] /. {zd -> z}];
Wick[ct[m_, w_], bt[n_, z_]] := Wick[ct[m, w], bt[n, z]] = Module[{zd}, -(-1)^m D[1/(zd - w), {zd, n + m}] /. {zd -> z}];
Wick[Ra_?ROne, Rb_?ROne] := Wick[Ra[[1]],Rb[[1]]]


(* ::Subsection:: *)
(*Define SWick*)


SWick[Ra_?ROne, Rb_?ROne] := SWick[Ra[[1]],Rb[[1]]]


(* ::Subsection:: *)
(*Define MWick*)


MWick[Ra_?ROne, Rb_?ROne] := MWick[Ra[[1]],Rb[[1]]]


(* ::Subsection:: *)
(*Define DWick: Wick contractions for normal-ordered products of fields*)


(*Reduces to Wick/SWick/MWick when both normal-ordered products have length one*)
DWick[Ra_,Rb_]:= If[pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}] ==1, Wick[Ra,Rb], 0]/;(ROne[Ra] && ROne[Rb] && isSimple[Head[Ra[[1]]]] && isSimple[Head[Rb[[1]]]])
DWick[Ra_,Rb_]:= If[pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}] ==1, SWick[Ra,Rb] Rb, 0]/;(ROne[Ra] && ROne[Rb] && isSimple[Head[Ra[[1]]]] && isComposite[Head[Rb[[1]]]])
DWick[Ra_,Rb_]:= If[pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}] ==1, SWick[Ra,Rb], 0] +Rb/;(ROne[Ra] && ROne[Rb] && isComposite[Head[Ra[[1]]]] && isSimple[Head[Rb[[1]]]])
DWick[Ra_,Rb_]:= If[pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}]==1,  MWick[Ra,Rb], 1] Rb/;(ROne[Ra] && ROne[Rb] && isComposite[Head[Ra[[1]]]] && isComposite[Head[Rb[[1]]]])

(*Computes contractions between a simple field in first position and a normal-ordered product in the second position: non-recursive*)
DWick[Ra_, Rb_]:= Module[{result = 0, RbList = List @@ Rb, arePaired, RaFirst = Ra[[1]], RaHead, RbHead, sign = 1, i = 1},
RaHead = Head[RaFirst];
(*Loop through the elements of the normal-ordered product*)
Scan[Function[Rbelem,
RbHead = Head[Rbelem];
arePaired = pairing[{RaHead,RbHead}]==1;
If[arePaired,
(*If paired, compute Wick contractions with sign*)
If[isComposite[RbHead],
(*When composite, do not delete from Rb*)
result = result + sign SWick[RaFirst, Rbelem] Rb,
(*When simple, delete from Rb*)
result = result + sign Wick[RaFirst, Rbelem] R@@Delete[RbList, i];
];
];
(*Keep track of sign as you pass through fermions*)
sign = sign (-1)^(parity[Ra]parity[R[Rbelem]]);
i++;
], RbList];
result]/; (ROne[Ra] && RTest[Rb] && (!ROne[Rb]) && isSimple[Head[Ra[[1]]]]);

(*Computes contractions between a normal-ordered product in the first position and a simple field in second position recycling the above function*)
DWick[Ra_,Rb_]:= (-1)^(parity[Ra] parity[Rb]) DWick[Rb, Ra]/; (ROne[Rb] && RTest[Ra] && (!ROne[Ra]) && isSimple[Head[Rb[[1]]]]);

(*Computes contractions between a single composite field and a normal-ordered product*)

(*When first element of Rb is simple, drop the latter when contracted, and pass through it when not contracted, do not give signs as in the end, one commutes the
  composite all the way back where it was in the beggining of contractions*)
DWick[Ra_,Rb_]:= If[pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}]==1, SWick[Ra[[1]],Rb[[1]]] DWick[Ra,dropFirstFromR[Rb]],0]+ 
R[Rb[[1]],DWick[Ra,dropFirstFromR[Rb]]]/;(ROne[Ra] && RTest[Rb] &&(!ROne[Rb]) && isComposite[Head[Ra[[1]]]] && isSimple[Head[Rb[[1]]]])

(*When first element of Rb is composite, do not drop the latter when contracted, again no signs as above*)
DWick[Ra_,Rb_]:= If[pairing[{Head[Ra[[1]]],Head[Rb[[1]]]}]==1, MWick[Ra[[1]],Rb[[1]]],1] R[Rb[[1]],
DWick[Ra,dropFirstFromR[Rb]]]/;(ROne[Ra] && RTest[Rb] &&(!ROne[Rb]) && isComposite[Head[Ra[[1]]]] && isComposite[Head[Rb[[1]]]])


(* ::Subsection:: *)
(*Define Pairing: determines whether two fields can be contracted*)


pairing::usage = "Determines whether two fields can be Wick contracted";


pairingList = {{b,c},{bt,ct}};

pairing[pair_]:= pairing[pair] = If[MemberQ[pairingList,Sort[pair]],1,0]


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
