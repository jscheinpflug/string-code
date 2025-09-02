(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Brackets`Bosonic`FlatSpace`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`Bosonic`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`Bosonic`"];
Needs["StringCode`StringFields`"];
Needs["StringCode`StringFields`Bosonic`"];
Needs["StringCode`Operators`"];
Needs["StringCode`Operators`Bosonic`"];
Needs["StringCode`Taylor`"];
Needs["StringCode`Taylor`Bosonic`"];
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


(* ::Subsubsection::Closed:: *)
(*Set factorization replacement*)


(*This replacement rule is called on multi-local operator every time factorization into holomorphic/antiholomorphic parts is performed*)
factorizationReplacement = 
{ProfileX[profile_, ders_, z_, zbar_]:> R[ProfileXHolo[profile, ders, z], ProfileXAntiHolo[profile, ders, zbar]], expX[k_, z_, zbar_]:> R[expXHolo[k, z], expXAntiHolo[k,zbar]]}


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
