(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`NormalOrdering`Bosonic`"];


Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`Bosonic`"];
Needs["StringCode`NormalOrdering`"]


(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Define Grassmann parity*)


regcomm::usage = "Give Grassmann sign under commutation";
regcomm[f_,g_]:=(-1)^(parity[f] parity[g])


(* ::Subsection:: *)
(*Optimized normal-ordering code*)


oddBosChirFieldQ[x_]:= False;
oddBosAntiChFieldQ[x_]:= False;
bosExpRules = {};


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
