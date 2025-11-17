(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Brackets`Bosonic`MinimalModel`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`Bosonic`"];
Needs["StringCode`Symbols`Bosonic`MinimalModel`"];
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


(* ::Subsection:: *)
(*Interacting projection*)


InteractingProjection[a_, 0]:= Corr @@ Flatten[a/.{OPE->List}];
InteractingProjection[a_, 2]:= Corr @@ Join[Flatten[a/.{OPE->List}], {Interacting[V[0,0,Infinity,Infinity]]}] Interacting[V[0,0,0,0]];
InteractingProjection[a_, b_/; b>2]:= 0;

Corr[Interacting[V[0,0,z1_,z1Bar_]]]:= OnePointCorr[z1,z1Bar];
Corr[Interacting[V[0,0,z1_,z1Bar_]], Interacting[V[0,0,z2_,z2Bar_]], Interacting[V[0,0,Infinity,Infinity]] ]:= CVVV 1/(z1-z2)/(z1Bar-z2Bar)
Corr[Interacting[V[0,0,z1_,z1Bar_]], Interacting[V[0,0,z2_,z2Bar_]], Interacting[V[0,0,z3_,z3Bar_]] ]:= CVVV 1/((z1-z2)(z1-z3)(z2-z3))/((z1Bar-z2Bar)(z1Bar-z3Bar)(z2Bar-z3Bar))
Corr[Interacting[V[0,0,z1_,z1Bar_]], Interacting[V[0,0,z2_,z2Bar_]], Interacting[V[0,0,z3_,z3Bar_]],Interacting[V[0,0,Infinity,Infinity]] ]:= 
FourPointWithInfinity[z1, z2, z3, z1Bar, z2Bar, z3Bar];
Corr[Interacting[V[0,0,z1_,z1Bar_]], Interacting[V[0,0,Infinity,Infinity]]]:= CVV1;
Corr[Interacting[V[0,0,z1_,z1Bar_]], Interacting[V[0,0,z2_,z2Bar_]]]:= CVV1 1/(z1-z2)^2/(z1Bar-z2Bar)^2


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
