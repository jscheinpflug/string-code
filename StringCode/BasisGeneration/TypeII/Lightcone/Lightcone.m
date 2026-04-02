(* ::Package:: *)

(* ::Section:: *)
(*Init*)

(*
  TypeII Lightcone Basis Generation
  =================================

  Generates basis states for Type II superstring theory in lightcone gauge.

  The basis consists of states built from:
  - b/c ghost system (conformal weights 2, -1)
  - beta/gamma superghost system (conformal weights 3/2, -1/2 at picture 0)
  - psi worldsheet fermions with lightcone indices (p, m, 1..8)
  - dX bosonic oscillators with lightcone indices

  States are organized by:
  - Total conformal weight (h + hbar)
  - Ghost number
  - Picture number
  - GSO parity

  The main difference from FlatSpace is the use of lightcone indices
  p (plus), m (minus), and transverse 1..8 instead of mu = 1..10.
*)

BeginPackage["StringCode`BasisGeneration`TypeII`Lightcone`"];


Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];
Needs["StringCode`Symbols`TypeII`FlatSpace`"];
Needs["StringCode`Symbols`TypeII`Lightcone`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`TypeII`"];
Needs["StringCode`BasisGeneration`"];
Needs["StringCode`BasisGeneration`TypeII`"];
Needs["StringCode`OPE`"];
Needs["StringCode`OPE`TypeII`"];
Needs["StringCode`Taylor`"];
Needs["StringCode`Taylor`TypeII`"];
Needs["StringCode`Taylor`TypeII`Lightcone`"];


(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* Maximum number of psi oscillators at one mode level for transverse directions *)
$maxPsiPerLevelTransverse::usage =
  "Maximum number of transverse psi oscillators permitted at one mode level (equals 8 in lightcone gauge).";
$maxPsiPerLevelTransverse = 8;


(* Lightcone basis generation extends the TypeII basis generation.
   The main machinery is inherited; lightcone-specific index handling
   uses the predicates from Symbols`TypeII`Lightcone. *)


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
