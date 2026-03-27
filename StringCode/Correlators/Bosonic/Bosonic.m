(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Correlators`Bosonic`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`Bosonic`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`Bosonic`"];
Needs["StringCode`Operators`"];
Needs["StringCode`Correlators`"];


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* The shared correlator package already hosts the universal bc VEV sectors. 
   Keep the standard Bosonic theory module split so later Bosonic-specific 
   correlator rules land here rather than in the shared package. *)


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
