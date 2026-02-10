(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Brackets`TypeII`FlatSpace`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];
Needs["StringCode`Symbols`TypeII`FlatSpace`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`StringFields`"];
Needs["StringCode`StringFields`TypeII`"];
Needs["StringCode`StringFields`TypeII`FlatSpace`"];
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


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
