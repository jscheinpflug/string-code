(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`BasisGeneration`Bosonic`"];


Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`Bosonic`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`Bosonic`"];
Needs["StringCode`BasisGeneration`"];


(* ::Section:: *)
(*Declare public variables and methods*)

generateBasisHolo::usage =
  "generateBasisHolo[weight, ghostNumber, z:0, opts] generates holomorphic bosonic local operators. Option \"CanonicalizeIndices\" -> True|False (default True) controls Lorentz-index canonicalization.";

generateBasisAntiHolo::usage =
  "generateBasisAntiHolo[weight, ghostNumber, zbar:0, opts] generates antiholomorphic bosonic local operators. Option \"CanonicalizeIndices\" -> True|False (default True) controls Lorentz-index canonicalization.";

generateBasisMatterHolo::usage =
  "generateBasisMatterHolo[weight, z:0, opts] generates holomorphic bosonic matter-only local operators. Option \"CanonicalizeIndices\" -> True|False (default True) controls Lorentz-index canonicalization.";

generateBasisMatterAntiHolo::usage =
  "generateBasisMatterAntiHolo[weight, zbar:0, opts] generates antiholomorphic bosonic matter-only local operators. Option \"CanonicalizeIndices\" -> True|False (default True) controls Lorentz-index canonicalization.";

generateBasisMatter::usage =
  "generateBasisMatter[weight, z:0, opts] generates holomorphic bosonic matter-only local operators. Option \"CanonicalizeIndices\" -> True|False (default True) controls Lorentz-index canonicalization.";

generateBasis::usage =
  "generateBasis[weight, ghostNumber, z:0, zbar:0, opts] generates full bosonic local operators; defaults are \"LevelMatched\" -> True and \"CanonicalizeIndices\" -> True.";


(* ::Section:: *)
(*Logic*)


(* ::Input::Initialization:: *)
Begin["Private`"];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
