(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`OPE`TypeII`FlatSpace`GammaProductGrammar`"];
Needs["StringCode`Symbols`TypeII`FlatSpace`"];


(* ::Section:: *)
(*Logic*)


Begin["Private`"];

gammaProductFactorQ::usage = "gammaProductFactorQ[expr] is True when expr is one GammaAntisymmetricProductHold factor.";
gammaProductFactorQ[expr_] := Head[expr] === GammaAntisymmetricProductHold;

candidateFactors::usage = "candidateFactors[expr] returns the multiplicative factor list for one candidate expression.";
candidateFactors[expr_] := If[Head[expr] === Times, List @@ expr, {expr}];

candidateCacheKey::usage = "candidateCacheKey[expr] builds a deterministic cache key for one candidate expression.";
candidateCacheKey[expr_] := ToString[InputForm[expr]];

gammaVectorLinkQ::usage = "gammaVectorLinkQ[link] is True when link is GammaUDHold or GammaDUHold.";
gammaVectorLinkQ[link_] := MatchQ[link, GammaUDHold[_] | GammaDUHold[_]];

gammaLinkIndexSelector::usage = "gammaLinkIndexSelector[link] extracts the vector payload from one GammaUDHold or GammaDUHold link.";
gammaLinkIndexSelector[GammaUDHold[idx_]] := idx;
gammaLinkIndexSelector[GammaDUHold[idx_]] := idx;
gammaLinkIndexSelector[_] := None;

gammaLinkVectorIndices::usage = "gammaLinkVectorIndices[link] extracts explicit vector indices from one gamma-chain link.";
gammaLinkVectorIndices[GammaUDHold[idx_]] := Flatten[{idx}];
gammaLinkVectorIndices[GammaDUHold[idx_]] := Flatten[{idx}];
gammaLinkVectorIndices[_] := {};

gammaProductSpinorChiralities::usage = "gammaProductSpinorChiralities[links] infers the endpoint chiralities carried by one GammaAntisymmetricProductHold link list.";
gammaProductSpinorChiralities[links_List] := Module[{reducedLinks, left, right},
  If[links =!= {} && First[links] === CUDHold, Return[{"chiral", "chiral"}]];
  If[links =!= {} && First[links] === CDUHold, Return[{"antichiral", "antichiral"}]];
  If[links =!= {} && AllTrue[links, # === Gamma11UUHold[] &], Return[{"chiral", "chiral"}]];
  If[links =!= {} && AllTrue[links, # === Gamma11DDHold[] &], Return[{"antichiral", "antichiral"}]];
  reducedLinks = DeleteCases[links, Gamma11UUHold[] | Gamma11DDHold[]];
  If[reducedLinks === {}, Return[{"chiral", "antichiral"}]];
  left = Which[
    Head[First[reducedLinks]] === GammaUDHold, "chiral",
    Head[First[reducedLinks]] === GammaDUHold, "antichiral",
    True, "chiral"
  ];
  right = left;
  Scan[
    Function[link, If[gammaVectorLinkQ[link], right = If[right === "chiral", "antichiral", "chiral"]]],
    reducedLinks
  ];
  {left, right}
];

gammaFactorPartsSelector::usage = "gammaFactorPartsSelector[factor] parses one GammaAntisymmetricProductHold factor into an association used by the selector.";
gammaFactorPartsSelector[factor_ /; gammaProductFactorQ[factor]] := Module[
  {links, cTag, coreLinks, vectorLinks},
  links = factor[[1]];
  cTag = If[links =!= {} && MatchQ[First[links], CUDHold | CDUHold], First[links], None];
  coreLinks = If[cTag === None, links, Rest[links]];
  vectorLinks = Select[coreLinks, gammaVectorLinkQ];
  <|
    "CTag" -> cTag,
    "VectorLinks" -> vectorLinks,
    "VectorSymbols" -> (gammaLinkIndexSelector /@ vectorLinks),
    "TailLinks" -> Select[coreLinks, !gammaVectorLinkQ[#] &],
    "Spinors" -> {factor[[2]], factor[[3]]},
    "SpinorChiralities" -> gammaProductSpinorChiralities[links]
  |>
];
gammaFactorPartsSelector[_] := $Failed;

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
candidateSpinorChiralities[expr_] := candidateSpinorChiralities[gammaFactorPartsSelector /@ candidateFactors[expr]];

generatedDummyVectorSymbolQ::usage = "generatedDummyVectorSymbolQ[sym] identifies TensorStructures dummy vector symbols built from \\[Nu]i names.";
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
candidateExternalVectors[expr_] := candidateExternalVectors[gammaFactorPartsSelector /@ candidateFactors[expr]];

parseCandidate::usage = "parseCandidate[expr] parses one selector candidate into reusable factor, spinor, and vector metadata.";
parseCandidate[expr_] := Module[{factors, parts},
  factors = candidateFactors[expr];
  If[!AllTrue[factors, gammaProductFactorQ], Return[$Failed]];
  parts = gammaFactorPartsSelector /@ factors;
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

syntheticFactorFromParts::usage = "syntheticFactorFromParts[parts] rebuilds one GammaAntisymmetricProductHold factor from parsed parts data.";
syntheticFactorFromParts[parts_Association] := GammaAntisymmetricProductHold[
  Join[
    If[parts["CTag"] === None, {}, {parts["CTag"]}],
    parts["VectorLinks"],
    parts["TailLinks"]
  ],
  Sequence @@ parts["Spinors"]
];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
