(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Brackets`Bosonic`FlatSpace`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`Bosonic`"];
Needs["StringCode`Symbols`Bosonic`FlatSpace`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`Bosonic`"];
Needs["StringCode`Operators`Bosonic`FlatSpace`"];
Needs["StringCode`Operators`"];
Needs["StringCode`Operators`Bosonic`"];
Needs["StringCode`Taylor`"];
Needs["StringCode`Taylor`Bosonic`"];
Needs["StringCode`Taylor`Bosonic`FlatSpace`"];
Needs["StringCode`Conventions`Bosonic`"];
Needs["StringCode`OPE`"];
Needs["StringCode`OPE`Bosonic`"];
Needs["StringCode`OPE`Bosonic`FlatSpace`"];
Needs["StringCode`Brackets`"];
Needs["StringCode`Brackets`Bosonic`"];


(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsubsection:: *)
(*Rescale local operators*)


rescalePositionBy::usage = "Rescales a local operator";

rescalePositionBy[rescalingFactor_][op_/;Head[op]===ProfileX]:= op/.{symbol_[args__, pos1_, pos2_]:> symbol[args, rescalingFactor pos1, rescalingFactor pos2]};
rescalePositionBy[rescalingFactor_][op_/;Head[op]===ProfileXHolo]:= op/.{symbol_[args__, pos1_, pos2_]:> symbol[args, rescalingFactor pos1, rescalingFactor pos2]};
rescalePositionBy[rescalingFactor_][op_/;Head[op]===ProfileXAntiHolo]:= op/.{symbol_[args__, pos1_, pos2_]:> symbol[args, rescalingFactor pos1, rescalingFactor pos2]};
rescalePositionBy[rescalingFactor_][op_/;Head[op]===expX]:= op/.{symbol_[args__, pos1_, pos2_]:> symbol[args, rescalingFactor pos1, rescalingFactor pos2]};
rescalePositionBy[rescalingFactor_][op_/;Head[op]===expXHolo]:= op/.{symbol_[args__, pos1_, pos2_]:> symbol[args, rescalingFactor pos1, rescalingFactor pos2]};
rescalePositionBy[rescalingFactor_][op_/;Head[op]===expXAntiHolo]:= op/.{symbol_[args__, pos1_, pos2_]:> symbol[args, rescalingFactor pos1, rescalingFactor pos2]};

(*The default chiral case*)
rescalePositionBy[rescalingFactor_][op_]:= op/.{symbol_[args__, pos_]:> symbol[args, rescalingFactor pos]};


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
