(* ::Package:: *)

BeginPackage["StringCode`OPE`"];

OPEProjected::usage = "Toy OPE projection function.";

Begin["`Private`"];
projectTerm[wH_, wA_][term_] := {"projected", wH, wA, term};
End[];

OPEProjected[wH_, wA_][term_] := StringCode`OPE`Private`projectTerm[wH, wA][term];

EndPackage[];
