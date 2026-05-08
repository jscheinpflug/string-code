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

recombineFlatSpaceBracketROps0::usage =
  "recombineFlatSpaceBracketROps0[ops] recombines factorized FlatSpace profile and plane-wave operator pairs inside one normal-ordered operator list.";
recombineFlatSpaceBracketROps0[ops_List] := FixedPoint[
  Replace[#, {
    {left___, ProfileXHolo[profile_, ders_, z_], middle___, ProfileXAntiHolo[profile_, ders_, zbar_], right___} :>
      {left, ProfileX[profile, ders, z, zbar], middle, right},
    {left___, ProfileXAntiHolo[profile_, ders_, zbar_], middle___, ProfileXHolo[profile_, ders_, z_], right___} :>
      {left, ProfileX[profile, ders, z, zbar], middle, right},
    {left___, expXHolo[p_, z_], middle___, expXAntiHolo[p_, zbar_], right___} :>
      {left, expX[p, z, zbar], middle, right},
    {left___, expXAntiHolo[p_, zbar_], middle___, expXHolo[p_, z_], right___} :>
      {left, expX[p, z, zbar], middle, right}
  }] &,
  ops
];

recombineFlatSpaceBracketR0::usage =
  "recombineFlatSpaceBracketR0[ra] recombines factorized FlatSpace profile and plane-wave pairs inside one normal-ordered product.";
recombineFlatSpaceBracketR0[ra_ /; RTest[ra]] := With[
  {ops = recombineFlatSpaceBracketROps0[List @@ ra]},
  R @@ ops
];

postProcessBracketResult0::usage =
  "postProcessBracketResult0[expr] recombines factorized FlatSpace profile and plane-wave fields after chiral bracket/OPE projection.";
postProcessBracketResult0[expr_] := FixedPoint[
  Expand[# /. ra_ /; RTest[ra] :> recombineFlatSpaceBracketR0[ra]] &,
  Expand[expr]
];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
