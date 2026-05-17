(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`OPE`Bosonic`FlatSpace`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`Bosonic`"];
Needs["StringCode`Symbols`Bosonic`FlatSpace`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`Bosonic`"];
Needs["StringCode`OPE`"];


(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


Begin["Private`"];

projectionExponentReplacement = {\[Alpha]p -> 0};

recombineProjectedFlatSpaceROps0::usage =
  "recombineProjectedFlatSpaceROps0[ops] recombines factorized FlatSpace profile and plane-wave operator pairs inside one normal-ordered operator list.";
recombineProjectedFlatSpaceROps0[ops_List] := FixedPoint[
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

recombineProjectedFlatSpaceR0::usage =
  "recombineProjectedFlatSpaceR0[ra] recombines factorized FlatSpace profile and plane-wave pairs inside one projected normal-ordered product.";
recombineProjectedFlatSpaceR0[ra_ /; RTest[ra]] := With[
  {ops = recombineProjectedFlatSpaceROps0[List @@ ra]},
  R @@ ops
];

postProcessProjectedOPE0::usage =
  "postProcessProjectedOPE0[expr] recombines factorized FlatSpace profile and plane-wave fields in projected OPE outputs. Module-generated dummy indices, Kronecker delta contractions, and der[F][\[Mu]] folding into ProfileX are all deferred to the outermost BracketProjection boundary for performance reasons.";
postProcessProjectedOPE0[expr_] := FixedPoint[
  Expand[# /. ra_ /; RTest[ra] :> recombineProjectedFlatSpaceR0[ra]] &,
  Expand[expr]
];

(* ::Section:: *)
(*End*)


End[];


EndPackage[];
