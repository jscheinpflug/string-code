(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Brackets`TypeII`FlatSpace`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];
Needs["StringCode`Symbols`TypeII`FlatSpace`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`Operators`TypeII`FlatSpace`"];
Needs["StringCode`Operators`"];
Needs["StringCode`Operators`TypeII`"];
Needs["StringCode`Taylor`"];
Needs["StringCode`Taylor`TypeII`"];
Needs["StringCode`Taylor`TypeII`FlatSpace`"];
Needs["StringCode`Conventions`TypeII`"];
Needs["StringCode`OPE`"];
Needs["StringCode`OPE`TypeII`"];
Needs["StringCode`OPE`TypeII`FlatSpace`"];
Needs["StringCode`Brackets`"];
Needs["StringCode`Brackets`TypeII`"];


(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Determine whether OPE should be computed*)


(* ::Subsubsection::Closed:: *)
(*Free boson*)


singularity[dX[\[Mu]_,n_,z_],dX[\[Nu]_,m_,w_]]:= 2 + m + n;
singularity[dXt[\[Mu]_,n_,z_],dXt[\[Nu]_,m_,w_]]:=2 + m + n;

singularity[dX[\[Mu]_,n_,z_],expX[k_,w_,wbar_]]:= 1 + n;
singularity[expX[k_,w_,wbar_],dX[\[Mu]_,n_,z_]]:= 1 + n;
singularity[dXt[\[Mu]_,n_,z_],expX[k_,w_,wbar_]]:=1 + n;
singularity[expX[k_,w_,wbar_],dXt[\[Mu]_,n_,z_]]:=1 + n;
singularity[dX[\[Mu]_,n_,z_],ProfileX[profile_,ders_, w_,wbar_]]:= 1 + n;
singularity[ProfileX[profile_,ders_, w_,wbar_],dX[\[Mu]_,n_,z_]]:= 1 + n;
singularity[dXt[\[Mu]_,n_,z_],ProfileX[profile_,ders_, w_,wbar_]]:=1 + n;
singularity[ProfileX[profile_,ders_, w_,wbar_],dXt[\[Mu]_,n_,z_]]:=1 + n;

singularity[dX[\[Mu]_,n_,z_],expXHolo[k_,w_]]:= 1 + n;
singularity[expXHolo[k_,w_],dX[\[Mu]_,n_,z_]]:= 1 + n;
singularity[dX[\[Mu]_,n_,z_],ProfileXHolo[profile_, ders_, w_]]:= 1 + n;
singularity[ProfileXHolo[profile_,ders_, w_],dX[\[Mu]_,n_,z_]]:= 1 + n;

singularity[dXt[\[Mu]_,n_,z_],expXAntiHolo[k_,wbar_]]:=1 + n;
singularity[expXAntiHolo[k_,wbar_],dXt[\[Mu]_,n_,z_]]:=1 + n;
singularity[dXt[\[Mu]_,n_,z_],ProfileXAntiHolo[profile_, ders_, wbar_]]:=1 + n;
singularity[ProfileXAntiHolo[profile_, ders_, wbar_],dXt[\[Mu]_,n_,z_]]:=1 + n;


(* ::Subsubsection:: *)
(*Free fermion*)


singularity[\[Psi][\[Mu]_,n_,z_],\[Psi][\[Nu]_,m_,w_]]:=1 + m + n;
singularity[\[Psi]t[\[Mu]_,n_,z_],\[Psi]t[\[Nu]_,m_,w_]]:=1 + m + n;


singularity[a_,b_]:= 0 /; (isField[Head[a]] && isField[Head[b]]);


(* ::Subsubsection:: *)
(*Rescale local operators*)


rescalePositionBy::usage = "Rescales a local operator";

rescalePositionBy[rescalingFactor_][op_/;Head[op]===ProfileX]:= op/.{symbol_[args__, pos1_, pos2_]:> symbol[args, rescalingFactor pos1, rescalingFactor pos2]};
rescalePositionBy[rescalingFactor_][op_/;Head[op]===expX]:= op/.{symbol_[args__, pos1_, pos2_]:> symbol[args, rescalingFactor pos1, rescalingFactor pos2]};

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
