(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Symbols`TypeII`Lightcone`"]
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];
Needs["StringCode`Symbols`TypeII`FlatSpace`"];


(* ::Section:: *)
(*Declare public variables and methods*)


p::usage = "Plus lightcone index (+)";


m::usage = "Minus lightcone index (-)";


iT::usage = "Dummy transverse index for implicit Einstein summation in Tmatter, Gmatter, etc.";


\[Eta]::usage = "Lightcone metric tensor: \[Eta][p,m] = \[Eta][m,p] = -1, \[Eta][p,p] = \[Eta][m,m] = 0, \[Eta][i,j] = \[Delta]T[i,j] for transverse";


\[Delta]T::usage = "Transverse Kronecker delta for indices i,j = 1..8";


ContractLightcone::usage = "Evaluates lightcone metric contractions: \[Eta][p,m] -> -1, etc.";


ContractDeltaT::usage = "Contracts transverse delta tensors with expressions";


lightconeIndexQ::usage = "lightconeIndexQ[idx] returns True if idx is a lightcone index (p or m)";


transverseIndexQ::usage = "transverseIndexQ[idx] returns True if idx is a transverse index (1..8, symbolic i1..i8, or any generic symbol not p or m)";


validLightconeVectorIndexQ::usage = "validLightconeVectorIndexQ[idx] returns True for any valid lightcone vector index (p, m, or transverse)";


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Index predicates*)


lightconeIndexQ[p] := True;
lightconeIndexQ[m] := True;
lightconeIndexQ[_] := False;


transverseIndexQ[i_Integer] := 1 <= i <= 8;
(* Any symbol that is not p or m is treated as a transverse index (similar to FlatSpace mu, nu) *)
transverseIndexQ[i_Symbol] := !MemberQ[{p, m}, i];
transverseIndexQ[_] := False;


validLightconeVectorIndexQ[idx_] := lightconeIndexQ[idx] || transverseIndexQ[idx];


(* ::Subsection:: *)
(*Lightcone metric - kept symbolic until contracted*)


(* The metric is kept inert by default so that expressions remain symbolic.
   Use ContractLightcone to evaluate metric components. *)


(* ::Subsection:: *)
(*Transverse delta - same-index evaluates to 1*)


\[Delta]T[i_, i_] := 1 /; transverseIndexQ[i];
\[Delta]T[i_, j_] := 0 /; transverseIndexQ[i] && transverseIndexQ[j] && i =!= j && IntegerQ[i] && IntegerQ[j];


(* ::Subsection:: *)
(*Contraction rules*)


lightconeContractRules::usage = "lightconeContractRules contains replacement rules for evaluating lightcone metric components";
lightconeContractRules = {
  \[Eta][p, m] -> -1,
  \[Eta][m, p] -> -1,
  \[Eta][p, p] -> 0,
  \[Eta][m, m] -> 0,
  (* Mixed lightcone-transverse vanishes *)
  \[Eta][p, i_] /; transverseIndexQ[i] -> 0,
  \[Eta][m, i_] /; transverseIndexQ[i] -> 0,
  \[Eta][i_, p] /; transverseIndexQ[i] -> 0,
  \[Eta][i_, m] /; transverseIndexQ[i] -> 0,
  (* Transverse-transverse uses delta *)
  \[Eta][i_, j_] /; transverseIndexQ[i] && transverseIndexQ[j] :> \[Delta]T[i, j]
};


ContractLightcone[expr_] := expr //. lightconeContractRules;


deltaTContractRules::usage = "deltaTContractRules contains replacement rules for contracting transverse deltas";
deltaTContractRules[dim_:8] := {
  \[Delta]T[i_, i_] :> dim,
  \[Delta]T[i_, j_]^2 :> dim
};


ContractDeltaT[expr_] := expr /. deltaTContractRules[];
ContractDeltaT[expr_, dim_] := expr /. deltaTContractRules[dim];


(* ::Subsection:: *)
(*FlatSpace contraction rules extended for lightcone*)


(* Extend the FlatSpace Contract function to handle lightcone indices *)
flatSpaceContractRules[dim_] := Join[
  {\[Delta][\[Mu]_, \[Mu]_] :> dim, \[Delta][\[Mu]_, \[Nu]_]^2 :> dim},
  lightconeContractRules
];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
