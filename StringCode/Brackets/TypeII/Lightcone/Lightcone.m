(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Brackets`TypeII`Lightcone`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];
Needs["StringCode`Symbols`TypeII`FlatSpace`"];
Needs["StringCode`Symbols`TypeII`Lightcone`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`Operators`TypeII`Lightcone`"];
Needs["StringCode`Operators`"];
Needs["StringCode`Operators`TypeII`"];
Needs["StringCode`Taylor`"];
Needs["StringCode`Taylor`TypeII`"];
Needs["StringCode`Taylor`TypeII`Lightcone`"];
Needs["StringCode`Conventions`TypeII`"];
Needs["StringCode`OPE`"];
Needs["StringCode`OPE`TypeII`"];
Needs["StringCode`OPE`TypeII`Lightcone`"];
Needs["StringCode`Brackets`"];
Needs["StringCode`Brackets`TypeII`"];


(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Determine whether OPE should be computed*)


(* ::Subsubsection:: *)
(*Free boson with lightcone indices*)


singularity[dX[p, n_, z_], dX[m, m_, w_]] := 2 + m + n;
singularity[dX[m, n_, z_], dX[p, m_, w_]] := 2 + m + n;
singularity[dX[p, n_, z_], dX[p, m_, w_]] := 0;
singularity[dX[m, n_, z_], dX[m, m_, w_]] := 0;
singularity[dX[i_, n_, z_], dX[j_, m_, w_]] /; transverseIndexQ[i] && transverseIndexQ[j] := 2 + m + n;

singularity[dXt[p, n_, z_], dXt[m, m_, w_]] := 2 + m + n;
singularity[dXt[m, n_, z_], dXt[p, m_, w_]] := 2 + m + n;
singularity[dXt[p, n_, z_], dXt[p, m_, w_]] := 0;
singularity[dXt[m, n_, z_], dXt[m, m_, w_]] := 0;
singularity[dXt[i_, n_, z_], dXt[j_, m_, w_]] /; transverseIndexQ[i] && transverseIndexQ[j] := 2 + m + n;

(* Mixed lightcone-transverse *)
singularity[dX[p, n_, z_], dX[i_, m_, w_]] /; transverseIndexQ[i] := 0;
singularity[dX[m, n_, z_], dX[i_, m_, w_]] /; transverseIndexQ[i] := 0;
singularity[dX[i_, n_, z_], dX[p, m_, w_]] /; transverseIndexQ[i] := 0;
singularity[dX[i_, n_, z_], dX[m, m_, w_]] /; transverseIndexQ[i] := 0;

singularity[dXt[p, n_, z_], dXt[i_, m_, w_]] /; transverseIndexQ[i] := 0;
singularity[dXt[m, n_, z_], dXt[i_, m_, w_]] /; transverseIndexQ[i] := 0;
singularity[dXt[i_, n_, z_], dXt[p, m_, w_]] /; transverseIndexQ[i] := 0;
singularity[dXt[i_, n_, z_], dXt[m, m_, w_]] /; transverseIndexQ[i] := 0;

(* Profiles with lightcone indices *)
singularity[dX[p, n_, z_], ProfileX[profile_, ders_, w_, wbar_]] := 1 + n;
singularity[ProfileX[profile_, ders_, w_, wbar_], dX[p, n_, z_]] := 1 + n;
singularity[dX[m, n_, z_], ProfileX[profile_, ders_, w_, wbar_]] := 1 + n;
singularity[ProfileX[profile_, ders_, w_, wbar_], dX[m, n_, z_]] := 1 + n;
singularity[dX[i_, n_, z_], ProfileX[profile_, ders_, w_, wbar_]] /; transverseIndexQ[i] := 1 + n;
singularity[ProfileX[profile_, ders_, w_, wbar_], dX[i_, n_, z_]] /; transverseIndexQ[i] := 1 + n;

singularity[dXt[p, n_, z_], ProfileX[profile_, ders_, w_, wbar_]] := 1 + n;
singularity[ProfileX[profile_, ders_, w_, wbar_], dXt[p, n_, z_]] := 1 + n;
singularity[dXt[m, n_, z_], ProfileX[profile_, ders_, w_, wbar_]] := 1 + n;
singularity[ProfileX[profile_, ders_, w_, wbar_], dXt[m, n_, z_]] := 1 + n;
singularity[dXt[i_, n_, z_], ProfileX[profile_, ders_, w_, wbar_]] /; transverseIndexQ[i] := 1 + n;
singularity[ProfileX[profile_, ders_, w_, wbar_], dXt[i_, n_, z_]] /; transverseIndexQ[i] := 1 + n;


(* ::Subsubsection:: *)
(*Free fermion with lightcone indices*)


singularity[\[Psi][p, n_, z_], \[Psi][m, m_, w_]] := 1 + m + n;
singularity[\[Psi][m, n_, z_], \[Psi][p, m_, w_]] := 1 + m + n;
singularity[\[Psi][p, n_, z_], \[Psi][p, m_, w_]] := 0;
singularity[\[Psi][m, n_, z_], \[Psi][m, m_, w_]] := 0;
singularity[\[Psi][i_, n_, z_], \[Psi][j_, m_, w_]] /; transverseIndexQ[i] && transverseIndexQ[j] := 1 + m + n;

singularity[\[Psi]t[p, n_, z_], \[Psi]t[m, m_, w_]] := 1 + m + n;
singularity[\[Psi]t[m, n_, z_], \[Psi]t[p, m_, w_]] := 1 + m + n;
singularity[\[Psi]t[p, n_, z_], \[Psi]t[p, m_, w_]] := 0;
singularity[\[Psi]t[m, n_, z_], \[Psi]t[m, m_, w_]] := 0;
singularity[\[Psi]t[i_, n_, z_], \[Psi]t[j_, m_, w_]] /; transverseIndexQ[i] && transverseIndexQ[j] := 1 + m + n;

(* Mixed lightcone-transverse *)
singularity[\[Psi][p, n_, z_], \[Psi][i_, m_, w_]] /; transverseIndexQ[i] := 0;
singularity[\[Psi][m, n_, z_], \[Psi][i_, m_, w_]] /; transverseIndexQ[i] := 0;
singularity[\[Psi][i_, n_, z_], \[Psi][p, m_, w_]] /; transverseIndexQ[i] := 0;
singularity[\[Psi][i_, n_, z_], \[Psi][m, m_, w_]] /; transverseIndexQ[i] := 0;

singularity[\[Psi]t[p, n_, z_], \[Psi]t[i_, m_, w_]] /; transverseIndexQ[i] := 0;
singularity[\[Psi]t[m, n_, z_], \[Psi]t[i_, m_, w_]] /; transverseIndexQ[i] := 0;
singularity[\[Psi]t[i_, n_, z_], \[Psi]t[p, m_, w_]] /; transverseIndexQ[i] := 0;
singularity[\[Psi]t[i_, n_, z_], \[Psi]t[m, m_, w_]] /; transverseIndexQ[i] := 0;


(* ::Subsubsection:: *)
(*Rescale local operators with lightcone indices*)


rescalePositionBy[rescalingFactor_][op_ /; Head[op] === ProfileX] :=
  op /. {symbol_[args__, pos1_, pos2_] :> symbol[args, rescalingFactor pos1, rescalingFactor pos2]};


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
