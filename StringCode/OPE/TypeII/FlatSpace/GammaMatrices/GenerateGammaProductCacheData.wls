scriptDir = DirectoryName[$InputFileName];

Needs["StringCode`"];
StringCode`InitStringCode[<|"theory" -> "TypeII", "CFT" -> "FlatSpace", "conventions" -> "TypeII-Ashoke", "bracket" -> "Flat", "signature" -> "Euclidean"|>];
Needs["StringCode`OPE`TypeII`FlatSpace`GammaMatrices`"];

families = {
  {None, 1},
  {None, 2},
  {CUDHold, 2},
  {CDUHold, 1}
};
gammaVectorDimension = 10;
gammaSpinorDimension = 16;

gammaProductCacheLinkHead[1] := GammaUDHold;
gammaProductCacheLinkHead[2] := GammaDUHold;

gammaProductCacheLinks[{cTag_, start_Integer}, inds_List] := Module[{dirs},
  dirs = Table[If[OddQ[pos], start, 3 - start], {pos, Length[inds]}];
  Join[
    If[cTag === None, {}, {cTag}],
    MapThread[#1[#2] &, {gammaProductCacheLinkHead /@ dirs, inds}]
  ]
];

gammaProductCacheLinkMatrix[CUDHold] := CUDSparse;
gammaProductCacheLinkMatrix[CDUHold] := CDUSparse;
gammaProductCacheLinkMatrix[GammaUDHold[mu_Integer]] /; 1 <= mu <= gammaVectorDimension := GammaUDSparse[mu];
gammaProductCacheLinkMatrix[GammaDUHold[mu_Integer]] /; 1 <= mu <= gammaVectorDimension := GammaDUSparse[mu];

gammaProductCacheAntisymmetrizedMatrixFromPattern[{}, {}] := SparseArray[Band[{1, 1}] -> 1, {gammaSpinorDimension, gammaSpinorDimension}];
gammaProductCacheAntisymmetrizedMatrixFromPattern[linkHeads_List, inds_List] /; Length[linkHeads] === Length[inds] :=
  gammaProductCacheAntisymmetrizedMatrixFromPattern[linkHeads, inds] = Module[
    {rank = Length[inds]},
    1/rank Sum[
      (-1)^(pos - 1) gammaProductCacheLinkMatrix[linkHeads[[1]][inds[[pos]]]] .
        gammaProductCacheAntisymmetrizedMatrixFromPattern[Rest[linkHeads], Delete[inds, pos]],
      {pos, 1, rank}
    ]
  ];

gammaProductCacheAntisymmetrizedMatrix[{}] := SparseArray[Band[{1, 1}] -> 1, {gammaSpinorDimension, gammaSpinorDimension}];
gammaProductCacheAntisymmetrizedMatrix[vectorLinks_List] := gammaProductCacheAntisymmetrizedMatrix[vectorLinks] = Module[
  {linkHeads, inds},
  linkHeads = Head /@ vectorLinks;
  inds = vectorLinks /. {GammaUDHold[mu_Integer] :> mu, GammaDUHold[mu_Integer] :> mu};
  If[!AllTrue[linkHeads, MemberQ[{GammaUDHold, GammaDUHold}, #] &] || !AllTrue[inds, IntegerQ], Return[$Failed]];
  gammaProductCacheAntisymmetrizedMatrixFromPattern[linkHeads, inds]
];

gammaProductCacheBuildMatrix[{None, start_Integer}, inds_List] :=
  gammaProductCacheAntisymmetrizedMatrix[gammaProductCacheLinks[{None, start}, inds]];
gammaProductCacheBuildMatrix[{cTag_, start_Integer}, inds_List] /; cTag =!= None :=
  gammaProductCacheLinkMatrix[cTag] . gammaProductCacheAntisymmetrizedMatrix[gammaProductCacheLinks[{None, start}, inds]];

gammaProductCacheData = Table[
  gammaProductCacheBuildMatrix[family, #] & /@ Subsets[Range[gammaVectorDimension], {rank}],
  {family, families},
  {rank, 0, gammaVectorDimension}
];

compressed = Compress[gammaProductCacheData];
cachePath = FileNameJoin[{scriptDir, "GammaProductCacheData.m"}];
Export[
  cachePath,
  StringJoin[
    "gammaProductCacheDataCompressed::usage =\n",
    "  \"gammaProductCacheDataCompressed is the compressed canonical alternating gamma-product cache data for TypeII flat-space spin contractions.\";\n",
    "gammaProductCacheDataCompressed = ",
    ToString[InputForm[compressed]],
    ";\n"
  ],
  "Text"
];

Print[cachePath];
Print[StringLength[compressed]];
