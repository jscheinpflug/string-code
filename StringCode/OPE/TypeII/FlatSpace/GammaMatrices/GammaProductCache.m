gammaProductCacheDataFileForSignature::usage =
  "gammaProductCacheDataFileForSignature[] returns the signature-specific gamma-product cache data file from the appropriate Euclidean or Lorentzian subdirectory.";
gammaProductCacheDataFileForSignature[] := Module[{dir, sigName},
  dir = DirectoryName[$InputFileName];
  sigName = If[currentSignature[] == "Lorentzian", "Lorentzian", "Euclidean"];
  FileNameJoin[{dir, sigName, "GammaProductCacheData.m"}]
];

Get[gammaProductCacheDataFileForSignature[]];


gammaProductCacheFamilies::usage =
  "gammaProductCacheFamilies is the ordered list of canonical alternating gamma-product families cached for TypeII flat-space spin contractions.";
gammaProductCacheFamilies = {
  {None, 1},
  {None, 2},
  {CUDHold, 2},
  {CDUHold, 1}
};


gammaProductCacheFamilySlots::usage =
  "gammaProductCacheFamilySlots maps each canonical gamma-product family key to its 1-based cache slot.";
gammaProductCacheFamilySlots = AssociationThread[gammaProductCacheFamilies -> Range[Length[gammaProductCacheFamilies]]];


gammaProductCacheCombinationCount::usage =
  "gammaProductCacheCombinationCount[rank] returns the number of sorted rank-index combinations cached for one family.";
gammaProductCacheCombinationCount[rank_Integer?NonNegative] /; rank <= gammaVectorDimension := Binomial[gammaVectorDimension, rank];


gammaProductCacheCombinationIndex::usage =
  "gammaProductCacheCombinationIndex[inds] returns the 1-based lexicographic slot of one sorted vector-index combination.";
gammaProductCacheCombinationIndex[inds_List] := Module[{rank = Length[inds], index = 1, start, stop},
  If[rank == 0, Return[1]];
  Do[
    start = If[pos == 1, 1, inds[[pos - 1]] + 1];
    stop = inds[[pos]] - 1;
    If[start <= stop, index += Sum[Binomial[gammaVectorDimension - value, rank - pos], {value, start, stop}]],
    {pos, 1, rank}
  ];
  index
];

gammaProductCacheCanonicalIndexQ::usage =
  "gammaProductCacheCanonicalIndexQ[idx] is True exactly for canonical 1..10 cache slots.";
gammaProductCacheCanonicalIndexQ[idx_Integer] := 1 <= idx <= gammaVectorDimension;
gammaProductCacheCanonicalIndexQ[_] := False;


gammaProductCacheZeroMatrix::usage =
  "gammaProductCacheZeroMatrix is the canonical zero sparse matrix returned for repeated antisymmetric vector indices.";
gammaProductCacheZeroMatrix = SparseArray[{}, {gammaSpinorDimension, gammaSpinorDimension}];


gammaProductCacheData::usage =
  "gammaProductCacheData is the uncompressed canonical alternating gamma-product sparse-matrix cache indexed by family slot, rank slot, and combination slot.";
gammaProductCacheData = Uncompress[gammaProductCacheDataCompressed];


gammaProductCacheLinks::usage =
  "gammaProductCacheLinks[family, inds] returns the canonical alternating link list for one cached family and one sorted vector-index tuple.";
gammaProductCacheLinks[{cTag_, start_Integer}, inds_List] := Module[{dirs},
  dirs = Table[If[OddQ[pos], start, 3 - start], {pos, Length[inds]}];
  Join[
    If[cTag === None, {}, {cTag}],
    MapThread[#1[#2] &, {Replace[dirs, {1 -> GammaUDHold, 2 -> GammaDUHold}, 1], inds}]
  ]
];


gammaCachedProductMatrix::usage =
  "gammaCachedProductMatrix[family, inds] returns one cached sparse gamma-product matrix for a canonical family and sorted vector-index tuple.";
gammaCachedProductMatrix[family : {_, _Integer}, inds_List] := Module[{rank = Length[inds], familySlot, comboSlot},
  If[rank > gammaVectorDimension || !AllTrue[inds, gammaProductCacheCanonicalIndexQ], Return[$Failed]];
  If[rank > 1 && !DuplicateFreeQ[inds], Return[gammaProductCacheZeroMatrix]];
  If[Sort[inds] =!= inds, Return[$Failed]];
  familySlot = If[KeyExistsQ[gammaProductCacheFamilySlots, family], gammaProductCacheFamilySlots[family], Missing["UnknownFamily"]];
  If[MissingQ[familySlot], Return[$Failed]];
  comboSlot = gammaProductCacheCombinationIndex[inds];
  gammaProductCacheData[[familySlot, rank + 1, comboSlot]]
];


gammaProductCacheNormalizeLinks::usage =
  "gammaProductCacheNormalizeLinks[links] returns {family, sortedCanonicalIndices, phase, canonicalIndexOrder} for one concrete cached gamma-link list, or $Failed if the list is outside the canonical alternating cache.";
gammaProductCacheNormalizeLinks[links_List] := Module[
  {cTag = None, vectorLinks = links, dirs, start, family, inds, canonicalInds, phase},
  If[links === {}, Return[$Failed]];
  If[MatchQ[First[links], CUDHold | CDUHold], cTag = First[links]; vectorLinks = Rest[links]];
  If[vectorLinks === {},
    Return @ Switch[cTag,
      CUDHold, {{CUDHold, 2}, {}, 1, {}},
      CDUHold, {{CDUHold, 1}, {}, 1, {}},
      _, $Failed
    ]
  ];
  If[!AllTrue[vectorLinks, MatchQ[#, GammaUDHold[_Integer] | GammaDUHold[_Integer]] &], Return[$Failed]];
  dirs = Replace[Head /@ vectorLinks, {GammaUDHold -> 1, GammaDUHold -> 2}, 1];
  start = First[dirs];
  If[dirs =!= Table[If[OddQ[pos], start, 3 - start], {pos, Length[dirs]}], Return[$Failed]];
  family = Switch[{cTag, start},
    {None, 1} | {None, 2} | {CUDHold, 2} | {CDUHold, 1}, {cTag, start},
    _, $Failed
  ];
  If[family === $Failed, Return[$Failed]];
  inds = vectorLinks /. {GammaUDHold[mu_Integer] :> mu, GammaDUHold[mu_Integer] :> mu};
  If[!AllTrue[inds, validGammaIndexQ], Return[$Failed]];
  canonicalInds = gammaCanonicalIndexFromExternal /@ inds;
  If[!AllTrue[canonicalInds, gammaProductCacheCanonicalIndexQ], Return[$Failed]];
  phase = Times @@ (gammaLorentzianPhase /@ inds);
  {family, Sort[canonicalInds], phase, canonicalInds}
];


gammaProductCacheLookupFromLinks::usage =
  "gammaProductCacheLookupFromLinks[links] returns the cached sparse matrix for one supported concrete gamma-link list, or $Failed if the list falls outside the canonical alternating cache.";
gammaProductCacheLookupFromLinks[links_List] := Module[{normalized, inds, sign, canonicalOrder},
  normalized = gammaProductCacheNormalizeLinks[links];
  If[normalized === $Failed, Return[$Failed]];
  inds = normalized[[2]];
  canonicalOrder = normalized[[4]];
  sign = If[Length[inds] > 1 && DuplicateFreeQ[canonicalOrder], Signature[Ordering[canonicalOrder]], 1];
  sign normalized[[3]] gammaCachedProductMatrix[normalized[[1]], inds]
];
