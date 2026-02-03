(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Brackets`Bosonic`FlatSpace`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`Bosonic`"];
Needs["StringCode`Symbols`Bosonic`FlatSpace`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`Bosonic`"];
Needs["StringCode`StringFields`"];
Needs["StringCode`StringFields`Bosonic`"];
Needs["StringCode`StringFields`Bosonic`FlatSpace`"];
Needs["StringCode`Operators`"];
Needs["StringCode`Operators`Bosonic`"];
Needs["StringCode`Taylor`"];
Needs["StringCode`Taylor`Bosonic`"];
Needs["StringCode`Taylor`Bosonic`FlatSpace`"];
Needs["StringCode`Conventions`Bosonic`"];
Needs["StringCode`OPE`"];
Needs["StringCode`Brackets`"];
Needs["StringCode`Brackets`Bosonic`"];


(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsubsection::Closed:: *)
(*Extract weight-counting parameter power*)


extractWeightCountingParameterPower::usage = "Extract weight-counting parameter power (modulo multiples of \[Alpha]')";
extractWeightCountingParameterPower[OPEterm_, weightCountingParameter_] := (Exponent[Together[OPEterm], weightCountingParameter])/.{\[Alpha]p -> 0}


(* ::Subsubsection:: *)
(*Set factorization replacement*)


(*This replacement rule is called on multi-local operator every time factorization into holomorphic/antiholomorphic parts is performed*)
factorizationReplacement = 
{ProfileX[profile_, ders_, z_, zbar_]:> R[ProfileXHolo[profile, ders, z], ProfileXAntiHolo[profile, ders, zbar]], expX[k_, z_, zbar_]:> R[expXHolo[k, z], expXAntiHolo[k,zbar]]}


(* ::Subsubsection:: *)
(*Rescale local operators*)


rescalePositionBy::usage = "Rescales a local operator";

rescalePositionBy[rescalingFactor_][op_/;Head[op]===ProfileX]:= op/.{symbol_[args__, pos1_, pos2_]:> symbol[args, rescalingFactor pos1, rescalingFactor pos2]};
rescalePositionBy[rescalingFactor_][op_/;Head[op]===expX]:= op/.{symbol_[args__, pos1_, pos2_]:> symbol[args, rescalingFactor pos1, rescalingFactor pos2]};

(*The default chiral case*)
rescalePositionBy[rescalingFactor_][op_]:= op/.{symbol_[args__, pos_]:> symbol[args, rescalingFactor pos]};


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
