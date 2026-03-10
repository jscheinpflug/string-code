(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`BasisGeneration`TypeII`"];


Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`TypeII`"];
Needs["StringCode`BasisGeneration`"];


(* ::Section:: *)
(*Declare public variables and methods*)


generateBasisHolo::usage =
  "generateBasisHolo[weight, ghostNumber, picture, opts] generates holomorphic TypeII basis states. Option \"OutputRepresentation\" -> \"Operators\" (default) or \"Modes\" controls output form. Option \"CanonicalizeIndices\" -> True|False (default True) controls operator-index canonicalization.";


generateBasisAntiHolo::usage =
  "generateBasisAntiHolo[weight, ghostNumber, picture, opts] generates antiholomorphic TypeII basis states. Option \"OutputRepresentation\" -> \"Operators\" (default) or \"Modes\" controls output form. Option \"CanonicalizeIndices\" -> True|False (default True) controls operator-index canonicalization.";

generateBasisMatterHolo::usage =
  "generateBasisMatterHolo[weight, picture, opts] generates holomorphic TypeII matter-only mode states grouped by picture.";

generateBasisMatterAntiHolo::usage =
  "generateBasisMatterAntiHolo[weight, picture, opts] generates antiholomorphic TypeII matter-only mode states grouped by picture.";

generateBasisMatterHoloOPE::usage =
  "generateBasisMatterHoloOPE[weight, picture, opts] generates holomorphic TypeII matter-only OPE-basis operators. Option \"CanonicalizeIndices\" -> True|False (default True) controls operator-index canonicalization.";

generateBasisMatterAntiHoloOPE::usage =
  "generateBasisMatterAntiHoloOPE[weight, picture, opts] generates antiholomorphic TypeII matter-only OPE-basis operators. Option \"CanonicalizeIndices\" -> True|False (default True) controls operator-index canonicalization.";

generateBasis::usage =
  "generateBasis[weight, ghostNumber, {pictureHolo, pictureAntiHolo}, opts] generates grouped TypeII closed-string basis states. Option \"OutputRepresentation\" -> \"Operators\" (default) or \"Modes\" controls output form. Option \"CanonicalizeIndices\" -> True|False (default True) controls operator-index canonicalization. Option \"B0MinusProjected\" -> True|False (default False) is supported only for operator output.";


(* ::Section:: *)
(*Logic*)


(* ::Input::Initialization:: *)
Begin["Private`"];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
