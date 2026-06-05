(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`OPE`TypeII`FlatSpace`GammaMatrices`GammaProductGrammar`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`FlatSpace`"];


(* ::Section:: *)
(*Logic*)


Begin["Private`"];

gammaProductFactorQ::usage = "gammaProductFactorQ[expr] is True when expr is one GammaAntisymmetricProductHold factor.";
gammaProductFactorQ[expr_] := Head[expr] === GammaAntisymmetricProductHold;

deltaFactorQ::usage = "deltaFactorQ[expr] is True when expr is one inert vector-contraction factor \\[Delta][mu, nu].";
deltaFactorQ[expr_] := MemberQ[{\[Delta], Eta}, Head[expr]] && Length[expr] == 2;

candidateFactorQ::usage = "candidateFactorQ[expr] is True when expr is a supported tensor-structure factor.";
candidateFactorQ[expr_] := gammaProductFactorQ[expr] || deltaFactorQ[expr];

candidateFactors::usage = "candidateFactors[expr] returns the multiplicative factor list for one candidate expression.";
candidateFactors[expr_] := If[Head[expr] === Times, List @@ expr, {expr}];

candidateCacheKey::usage = "candidateCacheKey[expr] builds a deterministic cache key for one candidate expression.";
(* Cache keys are consumed across selector/evaluator caches and must be stable across kernels. *)
candidateCacheKey[expr_] := ToString[InputForm[expr]];

gammaVectorLinkQ::usage = "gammaVectorLinkQ[link] is True when link is GammaUDHold or GammaDUHold.";
gammaVectorLinkQ[link_] := MatchQ[link, GammaUDHold[_] | GammaDUHold[_]];

gammaVectorIndexSymbol::usage = "gammaVectorIndexSymbol[idx] unwraps a gamma vector-index variance marker and returns the underlying index.";
gammaVectorIndexSymbol[GammaIndexUp[idx_]] := idx;
gammaVectorIndexSymbol[GammaIndexDown[idx_]] := idx;
gammaVectorIndexSymbol[idx_] := idx;

gammaLinkIndexSelector::usage = "gammaLinkIndexSelector[link] extracts the vector payload from one GammaUDHold or GammaDUHold link.";
gammaLinkIndexSelector[GammaUDHold[idx_]] := gammaVectorIndexSymbol[idx];
gammaLinkIndexSelector[GammaDUHold[idx_]] := gammaVectorIndexSymbol[idx];
gammaLinkIndexSelector[_] := None;

gammaLinkVectorIndices::usage = "gammaLinkVectorIndices[link] extracts explicit vector indices from one gamma-chain link.";
gammaLinkVectorIndices[GammaUDHold[idx_]] := Flatten[{gammaVectorIndexSymbol[idx]}];
gammaLinkVectorIndices[GammaDUHold[idx_]] := Flatten[{gammaVectorIndexSymbol[idx]}];
gammaLinkVectorIndices[_] := {};

toggleSpinorChirality::usage = "toggleSpinorChirality[chirality] toggles between \"chiral\" and \"antichiral\".";
toggleSpinorChirality["chiral"] := "antichiral";
toggleSpinorChirality["antichiral"] := "chiral";
toggleSpinorChirality[other_] := other;

gammaProductSpinorChiralities::usage = "gammaProductSpinorChiralities[links] infers the endpoint chiralities carried by one GammaAntisymmetricProductHold link list.";
gammaProductSpinorChiralities[links_List] := Module[{cTag, coreLinks, vectorLinks, tailLinks, left},
  cTag = If[links =!= {} && MatchQ[First[links], CUDHold | CDUHold], First[links], None];
  coreLinks = If[cTag === None, links, Rest[links]];
  vectorLinks = Select[coreLinks, gammaVectorLinkQ];
  tailLinks = Select[coreLinks, !gammaVectorLinkQ[#] &];
  If[cTag === CUDHold,
    Return[{"chiral", Nest[toggleSpinorChirality, "antichiral", Length[vectorLinks]]}]
  ];
  If[cTag === CDUHold,
    Return[{"antichiral", Nest[toggleSpinorChirality, "chiral", Length[vectorLinks]]}]
  ];
  If[vectorLinks === {} && tailLinks =!= {} && AllTrue[tailLinks, # === Gamma11UUHold[] &], Return[{"chiral", "chiral"}]];
  If[vectorLinks === {} && tailLinks =!= {} && AllTrue[tailLinks, # === Gamma11DDHold[] &], Return[{"antichiral", "antichiral"}]];
  If[vectorLinks === {}, Return[{"chiral", "antichiral"}]];
  left = Which[
    Head[First[vectorLinks]] === GammaUDHold, "chiral",
    Head[First[vectorLinks]] === GammaDUHold, "antichiral",
    True, "chiral"
  ];
  {left, Nest[toggleSpinorChirality, left, Length[vectorLinks]]}
];

gammaFactorPartsSelector::usage = "gammaFactorPartsSelector[factor] parses one GammaAntisymmetricProductHold factor into an association used by the selector.";
gammaFactorPartsSelector[factor_ /; gammaProductFactorQ[factor]] := Module[
  {links, cTag, coreLinks, vectorLinks},
  links = factor[[1]];
  cTag = If[links =!= {} && MatchQ[First[links], CUDHold | CDUHold], First[links], None];
  coreLinks = If[cTag === None, links, Rest[links]];
  vectorLinks = Select[coreLinks, gammaVectorLinkQ];
  <|
    "Kind" -> "Gamma",
    "CTag" -> cTag,
    "VectorLinks" -> vectorLinks,
    "VectorSymbols" -> (gammaLinkIndexSelector /@ vectorLinks),
    "TailLinks" -> Select[coreLinks, !gammaVectorLinkQ[#] &],
    "Spinors" -> {factor[[2]], factor[[3]]},
    "SpinorChiralities" -> gammaProductSpinorChiralities[links]
  |>
];
gammaFactorPartsSelector[_] := $Failed;

gammaFactorMetadataSelector::usage = "gammaFactorMetadataSelector[factor] extracts only selector metadata fields from one GammaAntisymmetricProductHold factor.";
gammaFactorMetadataSelector[factor_ /; gammaProductFactorQ[factor]] := Module[{links, vectorLinks},
  links = factor[[1]];
  vectorLinks = Select[links, gammaVectorLinkQ];
  <|
    "Kind" -> "Gamma",
    "Spinors" -> {factor[[2]], factor[[3]]},
    "SpinorChiralities" -> gammaProductSpinorChiralities[links],
    "VectorSymbols" -> (gammaLinkIndexSelector /@ vectorLinks)
  |>
];
gammaFactorMetadataSelector[_] := $Failed;

deltaFactorPartsSelector::usage = "deltaFactorPartsSelector[factor] parses one \\[Delta][mu, nu] factor into selector/evaluator metadata.";
deltaFactorPartsSelector[factor_ /; deltaFactorQ[factor]] := <|
  "Kind" -> "Delta",
  "VectorSymbols" -> List @@ factor,
  "Spinors" -> {},
  "SpinorChiralities" -> {}
|>;
deltaFactorPartsSelector[_] := $Failed;

deltaFactorMetadataSelector::usage = "deltaFactorMetadataSelector[factor] extracts selector metadata from one \\[Delta][mu, nu] factor.";
deltaFactorMetadataSelector[factor_ /; deltaFactorQ[factor]] := <|
  "Kind" -> "Delta",
  "Spinors" -> {},
  "SpinorChiralities" -> {},
  "VectorSymbols" -> List @@ factor
|>;
deltaFactorMetadataSelector[_] := $Failed;

factorPartsSelector::usage = "factorPartsSelector[factor] parses one supported tensor-structure factor into reusable metadata.";
factorPartsSelector[factor_] := Which[
  gammaProductFactorQ[factor], gammaFactorPartsSelector[factor],
  deltaFactorQ[factor], deltaFactorPartsSelector[factor],
  True, $Failed
];

factorMetadataSelector::usage = "factorMetadataSelector[factor] extracts selector metadata from one supported tensor-structure factor.";
factorMetadataSelector[factor_] := Which[
  gammaProductFactorQ[factor], gammaFactorMetadataSelector[factor],
  deltaFactorQ[factor], deltaFactorMetadataSelector[factor],
  True, $Failed
];

candidateSpinorChiralities::usage = "candidateSpinorChiralities[data] infers external spinor chiralities from one candidate expression or parsed-factor list.";
candidateSpinorChiralities[parts_List] := Merge[
  Flatten[
    Function[part,
      Pick[
        Thread[part["Spinors"] -> part["SpinorChiralities"]],
        (Head[#] === Symbol &) /@ part["Spinors"]
      ]
    ] /@ Select[parts, MatchQ[#, _Association] &],
    1
  ],
  First
];
candidateSpinorChiralities[expr_] := candidateSpinorChiralities[factorMetadataSelector /@ candidateFactors[expr]];

generatedDummyVectorSymbolQ::usage = "generatedDummyVectorSymbolQ[sym] identifies TensorStructures dummy vector symbols built from \\[Nu]i names.";
(* Generated \[Nu]i symbols are local contraction dummies and must not contribute to external-vector counting. *)
generatedDummyVectorSymbolQ[sym_Symbol] := With[
  {name = SymbolName[Unevaluated[sym]], context = Context[Unevaluated[sym]]},
  context === "StringCode`OPE`TypeII`FlatSpace`TensorStructures`" && StringStartsQ[name, "\[Nu]"]
];
generatedDummyVectorSymbolQ[_] := False;

candidateExternalVectors::usage = "candidateExternalVectors[data] extracts external vector symbols from one candidate expression or parsed-factor list.";
candidateExternalVectors[parts_List] := SortBy[
  DeleteDuplicates @ Select[
    Flatten[Lookup[Select[parts, MatchQ[#, _Association] &], "VectorSymbols", {}]],
    Head[#] === Symbol && !generatedDummyVectorSymbolQ[#] &
  ],
  SymbolName
];
candidateExternalVectors[expr_] := candidateExternalVectors[factorMetadataSelector /@ candidateFactors[expr]];

candidateMetadata::usage = "candidateMetadata[expr] extracts selector metadata used for target-rank inference and runtime setup.";
candidateMetadata[1] := <|
  "Expression" -> 1,
  "Key" -> candidateCacheKey[1],
  "SpinorChiralities" -> <||>,
  "ExternalVectors" -> {}
|>;
candidateMetadata[expr_] := Module[{factors, parts},
  (* Metadata parsing is intentionally cheap: enough for rank/probe setup, no evaluator-only structures. *)
  factors = candidateFactors[expr];
  If[!AllTrue[factors, candidateFactorQ], Return[$Failed]];
  parts = factorMetadataSelector /@ factors;
  If[MemberQ[parts, $Failed], Return[$Failed]];
  <|
    "Expression" -> expr,
    "Key" -> candidateCacheKey[expr],
    "SpinorChiralities" -> candidateSpinorChiralities[parts],
    "ExternalVectors" -> candidateExternalVectors[parts]
  |>
];

parseCandidate::usage = "parseCandidate[expr] parses one selector candidate into reusable factor, spinor, and vector metadata.";
parseCandidate[1] := <|
  "Expression" -> 1,
  "Key" -> candidateCacheKey[1],
  "Factors" -> {},
  "FactorParts" -> {},
  "SpinorChiralities" -> <||>,
  "ExternalVectors" -> {}
|>;
parseCandidate[expr_] := Module[{factors, parts},
  (* Full parsing keeps evaluator-ready "FactorParts"; invalid explicit candidates fail here and upstream as badarg. *)
  factors = candidateFactors[expr];
  If[!AllTrue[factors, candidateFactorQ], Return[$Failed]];
  parts = factorPartsSelector /@ factors;
  If[MemberQ[parts, $Failed], Return[$Failed]];
  <|
    "Expression" -> expr,
    "Key" -> candidateCacheKey[expr],
    "Factors" -> factors,
    "FactorParts" -> parts,
    "SpinorChiralities" -> candidateSpinorChiralities[parts],
    "ExternalVectors" -> candidateExternalVectors[parts]
  |>
];

syntheticFactorFromParts::usage = "syntheticFactorFromParts[parts] rebuilds one parsed gamma or delta factor.";
syntheticFactorFromParts[parts_Association] /; Lookup[parts, "Kind", None] === "Gamma" := GammaAntisymmetricProductHold[
  Join[
    If[parts["CTag"] === None, {}, {parts["CTag"]}],
    parts["VectorLinks"],
    parts["TailLinks"]
  ],
  Sequence @@ parts["Spinors"]
];
syntheticFactorFromParts[parts_Association] /; Lookup[parts, "Kind", None] === "Delta" := flatSpaceMetricTensor @@ parts["VectorSymbols"];
syntheticFactorFromParts[_] := $Failed;


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
