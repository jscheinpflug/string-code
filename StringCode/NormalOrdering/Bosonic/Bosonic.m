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

oddBosChirFieldQ::usage = "Bosonic theories have no odd chiral bosonized fields.";
oddBosChirFieldQ[_] := False;

oddBosAntiChFieldQ::usage = "Bosonic theories have no odd antichiral bosonized fields.";
oddBosAntiChFieldQ[_] := False;

bosExpRules::usage = "Bosonic theories have no bosonized exponential merge rules.";
bosExpRules = {};


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
