(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Operators`TypeII`Lightcone`"];


Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];
Needs["StringCode`Symbols`TypeII`FlatSpace`"];
Needs["StringCode`Symbols`TypeII`Lightcone`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`TypeII`"];
Needs["StringCode`Operators`"];
Needs["StringCode`Operators`TypeII`"];


(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsubsection:: *)
(*Free boson with lightcone indices*)


placeOp[coordinateHol_, coordinateAntiHol_][dX[p, n_, z_]] := dX[p, n, coordinateHol[z]];
placeOp[coordinateHol_, coordinateAntiHol_][dX[m, n_, z_]] := dX[m, n, coordinateHol[z]];
placeOp[coordinateHol_, coordinateAntiHol_][dX[i_, n_, z_]] /; transverseIndexQ[i] := dX[i, n, coordinateHol[z]];

placeOp[coordinateHol_, coordinateAntiHol_][dXt[p, n_, zbar_]] := dXt[p, n, coordinateAntiHol[zbar]];
placeOp[coordinateHol_, coordinateAntiHol_][dXt[m, n_, zbar_]] := dXt[m, n, coordinateAntiHol[zbar]];
placeOp[coordinateHol_, coordinateAntiHol_][dXt[i_, n_, zbar_]] /; transverseIndexQ[i] := dXt[i, n, coordinateAntiHol[zbar]];


(* ::Subsubsection:: *)
(*Free fermion with lightcone indices*)


placeOp[coordinateHol_, coordinateAntiHol_][\[Psi][p, n_, z_]] := \[Psi][p, n, coordinateHol[z]];
placeOp[coordinateHol_, coordinateAntiHol_][\[Psi][m, n_, z_]] := \[Psi][m, n, coordinateHol[z]];
placeOp[coordinateHol_, coordinateAntiHol_][\[Psi][i_, n_, z_]] /; transverseIndexQ[i] := \[Psi][i, n, coordinateHol[z]];

placeOp[coordinateHol_, coordinateAntiHol_][\[Psi]t[p, n_, zbar_]] := \[Psi]t[p, n, coordinateAntiHol[zbar]];
placeOp[coordinateHol_, coordinateAntiHol_][\[Psi]t[m, n_, zbar_]] := \[Psi]t[m, n, coordinateAntiHol[zbar]];
placeOp[coordinateHol_, coordinateAntiHol_][\[Psi]t[i_, n_, zbar_]] /; transverseIndexQ[i] := \[Psi]t[i, n, coordinateAntiHol[zbar]];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
