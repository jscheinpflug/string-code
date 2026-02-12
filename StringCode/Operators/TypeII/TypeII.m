(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Operators`TypeII`"];


Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`TypeII`"];
Needs["StringCode`Operators`"];


(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


(* ::Input::Initialization:: *)
Begin["Private`"];


(* ::Subsection:: *)
(*Compute total picture of multilocal operator*)


totalHolPicture::usage = "Computes total holomorphic picture";
totalAntiHolPicture::usage = "Computes total antiholomorphic picture";

totalHolPicture[Ma_/;MultiOpTest[Ma]]:= Total[Map[totalHolPicture, List @@ Ma]];
totalHolPicture[Times[a_, Ma_/;MultiOpTest[Ma]]] := totalHolPicture[Ma];

totalAntiHolPicture[Ma_/;MultiOpTest[Ma]]:= Total[Map[totalAntiHolPicture, List @@ Ma]];
totalAntiHolPicture[Times[a_, Ma_/;MultiOpTest[Ma]]] := totalAntiHolPicture[Ma];


(* ::Subsection:: *)
(*TypeII mapOp specializations*)


mapOp[coordinateHol_, coordinateAntiHol_][\[Eta][n_, z_]]:= \[Eta][n, coordinateHol[z]];
mapOp[coordinateHol_, coordinateAntiHol_][\[Xi][n_, z_]]:= \[Xi][n, coordinateHol[z]];
mapOp[coordinateHol_, coordinateAntiHol_][exp\[Phi]b[n_, z_]]:= exp\[Phi]b[n, coordinateHol[z]];
mapOp[coordinateHol_, coordinateAntiHol_][exp\[Phi]f[n_, z_]]:= exp\[Phi]f[n, coordinateHol[z]];
mapOp[coordinateHol_, coordinateAntiHol_][\[Eta]t[n_, zbar_]]:= \[Eta]t[n, coordinateAntiHol[zbar]];
mapOp[coordinateHol_, coordinateAntiHol_][\[Xi]t[n_, zbar_]]:= \[Xi]t[n, coordinateAntiHol[zbar]];
mapOp[coordinateHol_, coordinateAntiHol_][exp\[Phi]tb[n_, zbar_]]:= exp\[Phi]tb[n, coordinateAntiHol[zbar]];
mapOp[coordinateHol_, coordinateAntiHol_][exp\[Phi]tf[n_, zbar_]]:= exp\[Phi]tf[n, coordinateAntiHol[zbar]];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
