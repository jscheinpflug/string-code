(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Taylor`TypeII`Lightcone`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];
Needs["StringCode`Symbols`TypeII`FlatSpace`"];
Needs["StringCode`Symbols`TypeII`Lightcone`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`TypeII`"];
Needs["StringCode`Wick`"];
Needs["StringCode`Wick`TypeII`"];
Needs["StringCode`Wick`TypeII`Lightcone`"];
Needs["StringCode`Taylor`"];
Needs["StringCode`Taylor`TypeII`"];


(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Check if field needs expanding - lightcone indexed fields*)


(* ::Subsubsection:: *)
(*Free boson with lightcone indices*)


isAtPointHolo[dX[p, n_, z_], z0_] := SameQ[z, z0];
isAtPointHolo[dX[m, n_, z_], z0_] := SameQ[z, z0];
isAtPointHolo[dX[i_, n_, z_], z0_] /; transverseIndexQ[i] := SameQ[z, z0];

isAtPointAntiHolo[dXt[p, n_, zbar_], z0bar_] := SameQ[zbar, z0bar];
isAtPointAntiHolo[dXt[m, n_, zbar_], z0bar_] := SameQ[zbar, z0bar];
isAtPointAntiHolo[dXt[i_, n_, zbar_], z0bar_] /; transverseIndexQ[i] := SameQ[zbar, z0bar];


(* ::Subsubsection:: *)
(*Free fermion with lightcone indices*)


isAtPointHolo[\[Psi][p, n_, z_], z0_] := SameQ[z, z0];
isAtPointHolo[\[Psi][m, n_, z_], z0_] := SameQ[z, z0];
isAtPointHolo[\[Psi][i_, n_, z_], z0_] /; transverseIndexQ[i] := SameQ[z, z0];

isAtPointAntiHolo[\[Psi]t[p, n_, zbar_], z0bar_] := SameQ[zbar, z0bar];
isAtPointAntiHolo[\[Psi]t[m, n_, zbar_], z0bar_] := SameQ[zbar, z0bar];
isAtPointAntiHolo[\[Psi]t[i_, n_, zbar_], z0bar_] /; transverseIndexQ[i] := SameQ[zbar, z0bar];


(* ::Subsection:: *)
(*Define adding derivatives - lightcone indexed fields*)


(* ::Subsubsection:: *)
(*Free boson*)


addHoloDerivatives[dX[p, n_, z_], ord_, z0_] := taylorDerivativePrefactor[z - z0, ord] dX[p, n + ord, z0];
addHoloDerivatives[dX[m, n_, z_], ord_, z0_] := taylorDerivativePrefactor[z - z0, ord] dX[m, n + ord, z0];
addHoloDerivatives[dX[i_, n_, z_], ord_, z0_] /; transverseIndexQ[i] := taylorDerivativePrefactor[z - z0, ord] dX[i, n + ord, z0];

addAntiHoloDerivatives[dXt[p, n_, z_], ord_, z0bar_] := taylorDerivativePrefactor[z - z0bar, ord] dXt[p, n + ord, z0bar];
addAntiHoloDerivatives[dXt[m, n_, z_], ord_, z0bar_] := taylorDerivativePrefactor[z - z0bar, ord] dXt[m, n + ord, z0bar];
addAntiHoloDerivatives[dXt[i_, n_, z_], ord_, z0bar_] /; transverseIndexQ[i] := taylorDerivativePrefactor[z - z0bar, ord] dXt[i, n + ord, z0bar];


(* ::Subsubsection:: *)
(*Free fermion*)


addHoloDerivatives[\[Psi][p, n_, z_], ord_, z0_] := taylorDerivativePrefactor[z - z0, ord] \[Psi][p, n + ord, z0];
addHoloDerivatives[\[Psi][m, n_, z_], ord_, z0_] := taylorDerivativePrefactor[z - z0, ord] \[Psi][m, n + ord, z0];
addHoloDerivatives[\[Psi][i_, n_, z_], ord_, z0_] /; transverseIndexQ[i] := taylorDerivativePrefactor[z - z0, ord] \[Psi][i, n + ord, z0];

addAntiHoloDerivatives[\[Psi]t[p, n_, z_], ord_, z0bar_] := taylorDerivativePrefactor[z - z0bar, ord] \[Psi]t[p, n + ord, z0bar];
addAntiHoloDerivatives[\[Psi]t[m, n_, z_], ord_, z0bar_] := taylorDerivativePrefactor[z - z0bar, ord] \[Psi]t[m, n + ord, z0bar];
addAntiHoloDerivatives[\[Psi]t[i_, n_, z_], ord_, z0bar_] /; transverseIndexQ[i] := taylorDerivativePrefactor[z - z0bar, ord] \[Psi]t[i, n + ord, z0bar];


(* ::Section:: *)
(*End*)


End[];
EndPackage[];
