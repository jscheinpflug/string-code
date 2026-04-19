(* ::Package:: *)

Begin["StringCode`Brackets`"];
Needs["StringCode`OPE`" -> "ope`"];

BracketFromOPE::usage = "Toy bracket from OPE projection.";

Begin["`Private`"];
BracketFromOPE[wH_, wA_, term_] := ope`OPEProjected[wH, wA][term];

End[];

End[];
