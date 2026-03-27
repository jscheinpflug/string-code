(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Correlators`Bosonic`FlatSpace`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`Bosonic`"];
Needs["StringCode`Symbols`Bosonic`FlatSpace`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`Bosonic`"];
Needs["StringCode`Operators`"];
Needs["StringCode`Operators`Bosonic`FlatSpace`"];
Needs["StringCode`Correlators`"];
Needs["StringCode`Correlators`Bosonic`"];
Needs["StringCode`Wick`Bosonic`FlatSpace`"];
Needs["StringCode`OPE`Bosonic`FlatSpace`"];


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* The shared correlator engine already covers the current Bosonic FlatSpace
   free-field sector. Keep this module so the correlator package hierarchy
   matches the rest of the Bosonic FlatSpace stack and future CFT-specific
   hooks have a dedicated home. *)


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
