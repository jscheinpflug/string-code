(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`OPE`Bosonic`MinimalModel`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`Bosonic`"];
Needs["StringCode`Symbols`Bosonic`MinimalModel`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`Bosonic`"];
Needs["StringCode`OPE`"];


(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


toLocalList[op_] := If[RTest[op], List @@ op, {op}];
allVSectorR[ops_List] := AllTrue[ops, (RTest[#] || Head[#] === V) &] && AllTrue[Flatten[toLocalList /@ ops], Head[#] === V &];
opeToVList[expr_] := Flatten[expr /. {OPE -> List, R -> List}];

OPEProjected[0, 0][Ra__ /; allVSectorR[{Ra}]] := Corr @@ opeToVList[OPE @@ {Ra}];
OPEProjected[1, 1][Ra__ /; allVSectorR[{Ra}]] := Corr @@ Join[opeToVList[OPE @@ {Ra}], {V[0,0,Infinity,Infinity]}] V[0,0,0,0];
OPEProjected[wH_, wA_][Ra__ /; (allVSectorR[{Ra}] && (wH + wA > 2))] := 0;

Corr[V[0,0,z1_,z1Bar_]]:= OnePointCorr[z1,z1Bar];
Corr[V[0,0,z1_,z1Bar_], V[0,0,z2_,z2Bar_], V[0,0,Infinity,Infinity]]:= CVVV 1/(z1-z2)/(z1Bar-z2Bar);
Corr[V[0,0,z1_,z1Bar_], V[0,0,z2_,z2Bar_], V[0,0,z3_,z3Bar_]]:= CVVV 1/((z1-z2)(z1-z3)(z2-z3))/((z1Bar-z2Bar)(z1Bar-z3Bar)(z2Bar-z3Bar));
Corr[V[0,0,z1_,z1Bar_], V[0,0,z2_,z2Bar_], V[0,0,z3_,z3Bar_], V[0,0,Infinity,Infinity]]:= 
FourPointWithInfinity[z1, z2, z3, z1Bar, z2Bar, z3Bar];
Corr[V[0,0,z1_,z1Bar_], V[0,0,Infinity,Infinity]]:= CVV1;
Corr[V[0,0,z1_,z1Bar_], V[0,0,z2_,z2Bar_]]:= CVV1 1/(z1-z2)^2/(z1Bar-z2Bar)^2;


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
