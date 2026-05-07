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


\[Eta]LC::usage = "Lightcone metric tensor: \[Eta]LC[p,m] = \[Eta]LC[m,p] = -1, \[Eta]LC[p,p] = \[Eta]LC[m,m] = 0, \[Eta]LC[i,j] = \[Delta]T[i,j] for transverse";


\[Delta]T::usage = "Transverse Kronecker delta for indices i,j = 1..8";


ContractLightcone::usage = "Evaluates lightcone metric contractions: \[Eta]LC[p,m] -> -1, etc.";


ContractDeltaT::usage = "Contracts transverse delta tensors with expressions";


ContractTransverseDelta::usage = "ContractTransverseDelta[f] contracts transverse delta indices, replacing \[Delta]T[\[Mu],\[Mu]1] g -> g /. {\[Mu]->\[Mu]1}";


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
  \[Eta]LC[p, m] -> -1,
  \[Eta]LC[m, p] -> -1,
  \[Eta]LC[p, p] -> 0,
  \[Eta]LC[m, m] -> 0,
  (* Mixed lightcone-transverse vanishes *)
  \[Eta]LC[p, i_] /; transverseIndexQ[i] -> 0,
  \[Eta]LC[m, i_] /; transverseIndexQ[i] -> 0,
  \[Eta]LC[i_, p] /; transverseIndexQ[i] -> 0,
  \[Eta]LC[i_, m] /; transverseIndexQ[i] -> 0,
  (* Transverse-transverse uses delta *)
  \[Eta]LC[i_, j_] /; transverseIndexQ[i] && transverseIndexQ[j] :> \[Delta]T[i, j]
};


ContractLightcone[expr_] := expr //. lightconeContractRules;


deltaTContractRules::usage = "deltaTContractRules contains replacement rules for contracting transverse deltas";
deltaTContractRules[dim_:8] := {
  \[Delta]T[i_, i_] :> dim,
  \[Delta]T[i_, j_]^2 :> dim
};


ContractDeltaT[expr_] := expr /. deltaTContractRules[];
ContractDeltaT[expr_, dim_] := expr /. deltaTContractRules[dim];


ContractTransverseDelta[f_] := f //. {
  g_ \[Delta]T[\[Mu]_, \[Mu]1_] :> (g /. {\[Mu] -> \[Mu]1}) /; !FreeQ[g, \[Mu]],
  g_ \[Delta]T[\[Mu]1_, \[Mu]_] :> (g /. {\[Mu] -> \[Mu]1}) /; !FreeQ[g, \[Mu]]
};


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
