(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`OPE`TypeII`Lightcone`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];
Needs["StringCode`Symbols`TypeII`FlatSpace`"];
Needs["StringCode`Symbols`TypeII`Lightcone`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`TypeII`"];
Needs["StringCode`Operators`"];
Needs["StringCode`OPE`"];
Needs["StringCode`Taylor`"];
Needs["StringCode`BasisGeneration`TypeII`"];
Needs["StringCode`Wick`TypeII`Lightcone`"];


(* ::Section:: *)
(*Declare public variables and methods*)


validLightconeGammaIndexQ::usage = "validLightconeGammaIndexQ[idx] returns True if idx is a valid lightcone gamma matrix index (p, m, or 1..8)";


ContractGammaLightcone::usage = "ContractGammaLightcone[expr] applies lightcone metric contractions to gamma matrix structures";


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Lightcone gamma index validation*)


validLightconeGammaIndexQ[p] := True;
validLightconeGammaIndexQ[m] := True;
validLightconeGammaIndexQ[i_Integer] := 1 <= i <= 8;
validLightconeGammaIndexQ[_] := False;


(* ::Subsection:: *)
(*Symbolic gamma matrices for lightcone*)


(* GammaUDHold[p], GammaUDHold[m] stay inert - no numerical evaluation.
   Results contain symbolic gamma structures like:
   GammaAntisymmetricProductHold[{GammaUDHold[p], GammaDUHold[m]}, alpha, beta]

   The lightcone gamma matrices are NOT computed numerically from:
   gamma^+ = (gamma^1 + gamma^10)/sqrt(2)
   gamma^- = (gamma^1 - gamma^10)/sqrt(2)

   Instead, they remain symbolic and the eta metric handles contractions. *)


(* ::Subsection:: *)
(*Gamma contraction rules for lightcone*)


(* When vector indices contract in gamma structures, the eta metric appears.
   For example, psi[p] * GammaUDHold[m] contracts to give eta[p,m] factors. *)

gammaLightconeContractRules::usage = "gammaLightconeContractRules contains replacement rules for gamma index contractions with lightcone metric";
gammaLightconeContractRules = {
  (* Vector index summation with lightcone metric *)
  (* These rules handle cases where gamma indices need to be contracted *)
};


ContractGammaLightcone[expr_] := ContractLightcone[expr];


(* ::Subsection:: *)
(*Extend OPE singularity rules for lightcone indices*)


(* Free boson singularities *)
singularity[dX[p, n_, z_], dX[m, m_, w_]] := 2 + m + n;
singularity[dX[m, n_, z_], dX[p, m_, w_]] := 2 + m + n;
singularity[dX[p, n_, z_], dX[p, m_, w_]] := 0;  (* No singularity: eta[p,p] = 0 *)
singularity[dX[m, n_, z_], dX[m, m_, w_]] := 0;  (* No singularity: eta[m,m] = 0 *)
singularity[dX[i_, n_, z_], dX[j_, m_, w_]] /; transverseIndexQ[i] && transverseIndexQ[j] := 2 + m + n;

singularity[dXt[p, n_, z_], dXt[m, m_, w_]] := 2 + m + n;
singularity[dXt[m, n_, z_], dXt[p, m_, w_]] := 2 + m + n;
singularity[dXt[p, n_, z_], dXt[p, m_, w_]] := 0;
singularity[dXt[m, n_, z_], dXt[m, m_, w_]] := 0;
singularity[dXt[i_, n_, z_], dXt[j_, m_, w_]] /; transverseIndexQ[i] && transverseIndexQ[j] := 2 + m + n;

(* Mixed lightcone-transverse have no singularity *)
singularity[dX[p, n_, z_], dX[i_, m_, w_]] /; transverseIndexQ[i] := 0;
singularity[dX[m, n_, z_], dX[i_, m_, w_]] /; transverseIndexQ[i] := 0;
singularity[dX[i_, n_, z_], dX[p, m_, w_]] /; transverseIndexQ[i] := 0;
singularity[dX[i_, n_, z_], dX[m, m_, w_]] /; transverseIndexQ[i] := 0;

singularity[dXt[p, n_, z_], dXt[i_, m_, w_]] /; transverseIndexQ[i] := 0;
singularity[dXt[m, n_, z_], dXt[i_, m_, w_]] /; transverseIndexQ[i] := 0;
singularity[dXt[i_, n_, z_], dXt[p, m_, w_]] /; transverseIndexQ[i] := 0;
singularity[dXt[i_, n_, z_], dXt[m, m_, w_]] /; transverseIndexQ[i] := 0;

(* Free fermion singularities *)
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

(* Mixed lightcone-transverse have no singularity *)
singularity[\[Psi][p, n_, z_], \[Psi][i_, m_, w_]] /; transverseIndexQ[i] := 0;
singularity[\[Psi][m, n_, z_], \[Psi][i_, m_, w_]] /; transverseIndexQ[i] := 0;
singularity[\[Psi][i_, n_, z_], \[Psi][p, m_, w_]] /; transverseIndexQ[i] := 0;
singularity[\[Psi][i_, n_, z_], \[Psi][m, m_, w_]] /; transverseIndexQ[i] := 0;

singularity[\[Psi]t[p, n_, z_], \[Psi]t[i_, m_, w_]] /; transverseIndexQ[i] := 0;
singularity[\[Psi]t[m, n_, z_], \[Psi]t[i_, m_, w_]] /; transverseIndexQ[i] := 0;
singularity[\[Psi]t[i_, n_, z_], \[Psi]t[p, m_, w_]] /; transverseIndexQ[i] := 0;
singularity[\[Psi]t[i_, n_, z_], \[Psi]t[m, m_, w_]] /; transverseIndexQ[i] := 0;


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
