(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`OPE`TypeII`FlatSpace`IndependentTensorStructuresEvaluator`"];
Needs["StringCode`Symbols`TypeII`FlatSpace`"];
Needs["StringCode`OPE`TypeII`FlatSpace`GammaMatrices`"];
Needs["StringCode`OPE`TypeII`FlatSpace`GammaProductGrammar`"];


(* ::Section:: *)
(*Logic*)


Begin["Private`"];

allBasisSubsets::usage = "allBasisSubsets[rank] returns all increasing rank-subsets of Range[10], cached by rank.";
allBasisSubsets[0] := {{}};
allBasisSubsets[rank_Integer?Positive] := allBasisSubsets[rank] = Subsets[Range[10], {rank}];

associationLookup::usage = "associationLookup[assoc, key, default] looks up an association value while supporting non-atomic keys.";
associationLookup[assoc_Association, key_, default_] := If[KeyExistsQ[assoc, key], assoc[key], default];

orderedAssociationRules::usage = "orderedAssociationRules[assoc] returns deterministic rules sorted by key for exact cache keys.";
orderedAssociationRules[assoc_Association] := SortBy[Normal[assoc], First];

bitCount::usage = "bitCount[mask] returns the number of set bits in one nonnegative integer mask.";
bitCount[mask_Integer?NonNegative] := DigitCount[mask, 2, 1];

maskPositions::usage = "maskPositions[mask, length] returns the 1-based positions of set bits in mask.";
maskPositions[mask_Integer?NonNegative, length_Integer?NonNegative] := Select[Range[length], BitGet[mask, # - 1] == 1 &];

modularImaginaryUnit::usage = "modularImaginaryUnit[prime] returns a square root of -1 modulo prime.";
modularImaginaryUnit[prime_Integer] := PowerMod[-1, Quotient[prime - 1, 4], prime];

modularReduceExact::usage = "modularReduceExact[expr, prime, imag] reduces an exact matrix or scalar expression modulo prime.";
modularReduceExact[expr_, prime_Integer, imag_Integer] := Mod[expr /. Complex[a_, b_] :> (a + imag b) /. I -> imag, prime];

primeEvaluationData::usage = "primeEvaluationData[prime] precomputes the modular gamma data needed by the selector evaluator.";
primeEvaluationData[prime_Integer] := primeEvaluationData[prime] = Module[{imag = modularImaginaryUnit[prime]},
  (* All downstream arithmetic is modular; reduce matrices once per prime and reuse aggressively. *)
  <|
    "Prime" -> prime,
    "Identity" -> IdentityMatrix[16],
    "GammaUD" -> Table[modularReduceExact[GammaUD[mu], prime, imag], {mu, 1, 10}],
    "GammaDU" -> Table[modularReduceExact[GammaDU[mu], prime, imag], {mu, 1, 10}],
    "CUD" -> modularReduceExact[CUD, prime, imag],
    "CDU" -> modularReduceExact[CDU, prime, imag],
    "Gamma11UU" -> modularReduceExact[Gamma11UU, prime, imag],
    "Gamma11DD" -> modularReduceExact[Gamma11DD, prime, imag]
  |>
];

gammaLinkMatrix::usage = "gammaLinkMatrix[link, component, primeData] returns the modular matrix for one gamma-chain link.";
gammaLinkMatrix[link_, component_, primeData_Association] := Which[
  link === CUDHold, primeData["CUD"],
  link === CDUHold, primeData["CDU"],
  MatchQ[link, GammaUDHold[_]] && IntegerQ[component], primeData["GammaUD"][[component]],
  MatchQ[link, GammaDUHold[_]] && IntegerQ[component], primeData["GammaDU"][[component]],
  MatchQ[link, GammaUDHold[_]] && VectorQ[component, IntegerQ],
    Mod[Sum[component[[mu]] primeData["GammaUD"][[mu]], {mu, 1, Length[component]}], primeData["Prime"]],
  MatchQ[link, GammaDUHold[_]] && VectorQ[component, IntegerQ],
    Mod[Sum[component[[mu]] primeData["GammaDU"][[mu]], {mu, 1, Length[component]}], primeData["Prime"]],
  link === Gamma11UUHold[], primeData["Gamma11UU"],
  link === Gamma11DDHold[], primeData["Gamma11DD"],
  True, $Failed
];

gammaHeadBasisMatrix::usage = "gammaHeadBasisMatrix[head, basisIndex, primeData] returns one basis gamma matrix for GammaUDHold or GammaDUHold.";
gammaHeadBasisMatrix[GammaUDHold, basisIndex_Integer, primeData_Association] := primeData["GammaUD"][[basisIndex]];
gammaHeadBasisMatrix[GammaDUHold, basisIndex_Integer, primeData_Association] := primeData["GammaDU"][[basisIndex]];
gammaHeadBasisMatrix[_, _, _] := $Failed;

matrixProductMod::usage = "matrixProductMod[left, right, prime] multiplies two matrices modulo prime.";
matrixProductMod[left_List, right_List, prime_Integer] := Mod[left . right, prime];

antisymmetrizedVectorMatrixCache::usage = "antisymmetrizedVectorMatrixCache memoizes antisymmetrized basis gamma matrices.";
antisymmetrizedVectorMatrixCache = <||>;

antisymmetrizedVectorMatrixState::usage =
  "antisymmetrizedVectorMatrixState[headTypes, headMask, basisSubset, primeData] memoizes subset-DP states for antisymmetrized gamma products.";
antisymmetrizedVectorMatrixState[headTypes_List, 0, {}, primeData_Association] := primeData["Identity"];
antisymmetrizedVectorMatrixState[headTypes_List, headMask_Integer?NonNegative, basisSubset_List, primeData_Association] := Module[
  {key, cached, remainingHeads, rank, invRank, sumMatrix, pos, headPos, headMatrix, restMatrix},
  If[Length[basisSubset] =!= bitCount[headMask], Return[$Failed]];
  key = {primeData["Prime"], headTypes, headMask, basisSubset};
  cached = associationLookup[antisymmetrizedVectorMatrixCache, key, Missing["NotFound"]];
  If[cached =!= Missing["NotFound"], Return[cached]];
  remainingHeads = maskPositions[headMask, Length[headTypes]];
  rank = Length[remainingHeads];
  invRank = PowerMod[rank, -1, primeData["Prime"]];
  (* Dynamic programming over remaining-head masks avoids factorial re-expansion of antisymmetrization. *)
  sumMatrix = ConstantArray[0, {16, 16}];
  For[pos = 1, pos <= rank, pos++,
    headPos = remainingHeads[[pos]];
    headMatrix = gammaHeadBasisMatrix[headTypes[[headPos]], basisSubset[[pos]], primeData];
    restMatrix = antisymmetrizedVectorMatrixState[headTypes, BitClear[headMask, headPos - 1], Delete[basisSubset, pos], primeData];
    If[headMatrix === $Failed || restMatrix === $Failed, Return[$Failed]];
    sumMatrix = Mod[
      sumMatrix + (-1)^(pos - 1) matrixProductMod[headMatrix, restMatrix, primeData["Prime"]],
      primeData["Prime"]
    ];
  ];
  cached = Mod[invRank sumMatrix, primeData["Prime"]];
  AssociateTo[antisymmetrizedVectorMatrixCache, key -> cached];
  cached
];

antisymmetrizedVectorMatrix::usage = "antisymmetrizedVectorMatrix[vectorHeads, basisSubset, primeData] returns the antisymmetrized gamma matrix for one basis subset.";
antisymmetrizedVectorMatrix[vectorHeads_List, basisSubset_List, primeData_Association] := Module[
  {headTypes},
  headTypes = Head /@ vectorHeads;
  antisymmetrizedVectorMatrixState[headTypes, 2^Length[headTypes] - 1, basisSubset, primeData]
];

gammaFactorMatrixAssociationCache::usage = "gammaFactorMatrixAssociationCache memoizes basis-subset matrix associations for parsed gamma factors.";
gammaFactorMatrixAssociationCache = <||>;

gammaFactorMatrixAssociationKey::usage = "gammaFactorMatrixAssociationKey[parts, prime] builds the cache key for basis-subset gamma matrices.";
gammaFactorMatrixAssociationKey[parts_Association, prime_Integer] := {
  prime,
  parts["CTag"],
  Head /@ parts["VectorLinks"],
  Head /@ parts["TailLinks"]
};

gammaFactorMatrixAssociation::usage = "gammaFactorMatrixAssociation[parts, primeData] returns the basis-subset matrix table for one parsed gamma factor.";
gammaFactorMatrixAssociation[parts_Association, primeData_Association] := Module[
  {key, cached, cMatrix, tailMatrices, tailMatrix, vectorHeads, subsets, assoc},
  key = gammaFactorMatrixAssociationKey[parts, primeData["Prime"]];
  cached = associationLookup[gammaFactorMatrixAssociationCache, key, Missing["NotFound"]];
  If[cached =!= Missing["NotFound"], Return[cached]];
  cMatrix = If[parts["CTag"] === None, primeData["Identity"], gammaLinkMatrix[parts["CTag"], None, primeData]];
  If[cMatrix === $Failed, Return[$Failed]];
  tailMatrices = gammaLinkMatrix[#, None, primeData] & /@ parts["TailLinks"];
  If[AnyTrue[tailMatrices, # === $Failed &], Return[$Failed]];
  tailMatrix = Fold[
    matrixProductMod[#1, #2, primeData["Prime"]] &,
    primeData["Identity"],
    tailMatrices
  ];
  vectorHeads = parts["VectorLinks"];
  subsets = allBasisSubsets[Length[vectorHeads]];
  assoc = Association @ Table[
    With[
      {
        antiMatrix = antisymmetrizedVectorMatrix[vectorHeads, subset, primeData]
      },
      If[antiMatrix === $Failed, Return[$Failed]];
      subset -> matrixProductMod[cMatrix, matrixProductMod[antiMatrix, tailMatrix, primeData["Prime"]], primeData["Prime"]]
    ],
    {subset, subsets}
  ];
  AssociateTo[gammaFactorMatrixAssociationCache, key -> assoc];
  assoc
];

complementLowRankParts::usage = "complementLowRankParts[parts] returns the complementary low-rank gamma parts used when the vector rank exceeds 5.";
complementLowRankParts[parts_Association] := With[{q = 10 - Length[parts["VectorLinks"]]},
  Join[parts, <|"VectorLinks" -> Take[parts["VectorLinks"], q], "VectorSymbols" -> Take[parts["VectorSymbols"], q]|>]
];

matrixProportionalFactor::usage = "matrixProportionalFactor[high, low, prime] returns the modular scalar c with high == c low, or $Failed if none exists.";
matrixProportionalFactor[high_List, low_List, prime_Integer] := Module[{positions, pos, factor},
  positions = Position[low, x_ /; x =!= 0, {2}, Heads -> False];
  If[positions === {}, Return[If[high === ConstantArray[0, Dimensions[high]], 0, $Failed]]];
  pos = First[positions];
  factor = Mod[high[[Sequence @@ pos]] PowerMod[low[[Sequence @@ pos]], -1, prime], prime];
  If[Mod[high - factor low, prime] === ConstantArray[0, Dimensions[high]], factor, $Failed]
];

highRankComplementDataCache::usage = "highRankComplementDataCache memoizes complement-family data for high-rank gamma families.";
highRankComplementDataCache = <||>;

highRankComplementData::usage = "highRankComplementData[parts, primeData] returns the low-rank complement family and subset factors for one high-rank gamma factor.";
highRankComplementData[parts_Association, primeData_Association] := Module[
  {key, cached, lowParts, highAssoc, lowAssoc, factors},
  key = gammaFactorMatrixAssociationKey[parts, primeData["Prime"]];
  cached = associationLookup[highRankComplementDataCache, key, Missing["NotFound"]];
  If[cached =!= Missing["NotFound"], Return[cached]];
  lowParts = complementLowRankParts[parts];
  highAssoc = gammaFactorMatrixAssociation[parts, primeData];
  lowAssoc = gammaFactorMatrixAssociation[lowParts, primeData];
  If[highAssoc === $Failed || lowAssoc === $Failed, Return[$Failed]];
  factors = Association @ Table[
    With[{factor = matrixProportionalFactor[highAssoc[subset], lowAssoc[Complement[Range[10], subset]], primeData["Prime"]]},
      If[factor === $Failed, Return[$Failed]];
      subset -> factor
    ],
    {subset, Keys[highAssoc]}
  ];
  cached = <|"LowParts" -> lowParts, "Factors" -> factors|>;
  AssociateTo[highRankComplementDataCache, key -> cached];
  cached
];

gammaFactorCoefficientAssociationCache::usage = "gammaFactorCoefficientAssociationCache memoizes alternating-form coefficients for parsed gamma factors and probe spinors.";
gammaFactorCoefficientAssociationCache = <||>;

gammaFactorCoefficientAssociationKey::usage = "gammaFactorCoefficientAssociationKey[parts, spin1, spin2, prime] builds the cache key for one factor coefficient association.";
gammaFactorCoefficientAssociationKey[parts_Association, spin1_List, spin2_List, prime_Integer] := {gammaFactorMatrixAssociationKey[parts, prime], spin1, spin2};

gammaFactorMatrixCoefficientAssociation::usage = "gammaFactorMatrixCoefficientAssociation[matrixAssoc, spin1, spin2, prime] contracts one cached gamma-matrix association with a probe spinor pair.";
gammaFactorMatrixCoefficientAssociation[matrixAssoc_Association, spin1_List, spin2_List, prime_Integer] := Association @ Select[
  KeyValueMap[#1 -> Mod[spin1 . #2 . spin2, prime] &, matrixAssoc],
  Last[#] =!= 0 &
];

gammaFactorCoefficientAssociation::usage = "gammaFactorCoefficientAssociation[factorOrParts, probe, primeData] returns alternating-form coefficients for one gamma factor after spinor contraction.";
gammaFactorCoefficientAssociation[parts_Association, probe_Association, primeData_Association] := Module[
  {spin1, spin2, key, cached, complementData, lowCoeffs, matrixAssoc, prime = primeData["Prime"]},
  spin1 = Lookup[probe["SpinorComponents"], parts["Spinors"][[1]], Missing["Unassigned"]];
  spin2 = Lookup[probe["SpinorComponents"], parts["Spinors"][[2]], Missing["Unassigned"]];
  If[!VectorQ[spin1, IntegerQ] || !VectorQ[spin2, IntegerQ], Return[$Failed]];
  key = gammaFactorCoefficientAssociationKey[parts, spin1, spin2, prime];
  cached = associationLookup[gammaFactorCoefficientAssociationCache, key, Missing["NotFound"]];
  If[cached =!= Missing["NotFound"], Return[cached]];
  cached = If[
    (* Use Hodge-dual complement for rank>5 pure-vector factors to stay in low-rank matrix families. *)
    Length[parts["VectorLinks"]] > 5 && parts["TailLinks"] === {},
    complementData = highRankComplementData[parts, primeData];
    If[complementData === $Failed, Return[$Failed]];
    lowCoeffs = gammaFactorCoefficientAssociation[complementData["LowParts"], probe, primeData];
    If[lowCoeffs === $Failed, Return[$Failed]];
    Association @ Select[
      Table[
        subset -> Mod[complementData["Factors"][subset] associationLookup[lowCoeffs, Complement[Range[10], subset], 0], prime],
        {subset, Keys[complementData["Factors"]]}
      ],
      Last[#] =!= 0 &
    ],
    matrixAssoc = gammaFactorMatrixAssociation[parts, primeData];
    If[matrixAssoc === $Failed, Return[$Failed]];
    gammaFactorMatrixCoefficientAssociation[matrixAssoc, spin1, spin2, prime]
  ];
  If[parts["VectorLinks"] === {} && !KeyExistsQ[cached, {}], cached = Join[cached, <|{} -> 0|>]];
  AssociateTo[gammaFactorCoefficientAssociationCache, key -> cached];
  cached
];
gammaFactorCoefficientAssociation[factor_, probe_Association, primeData_Association] := Module[{parts},
  parts = gammaFactorPartsSelector[factor];
  If[parts === $Failed, $Failed, gammaFactorCoefficientAssociation[parts, probe, primeData]]
];

deltaFactorValue::usage = "deltaFactorValue[parts, probe, prime] evaluates one parsed \\[Delta] factor at a modular probe.";
deltaFactorValue[parts_Association, probe_Association, prime_Integer] := Module[{vec1, vec2},
  vec1 = Lookup[Lookup[probe, "VectorComponents", <||>], parts["VectorSymbols"][[1]], Missing["Unassigned"]];
  vec2 = Lookup[Lookup[probe, "VectorComponents", <||>], parts["VectorSymbols"][[2]], Missing["Unassigned"]];
  If[!VectorQ[vec1, IntegerQ] || !VectorQ[vec2, IntegerQ], Return[$Failed]];
  Mod[vec1 . vec2, prime]
];

formCoefficientValue::usage = "formCoefficientValue[coefficients, tuple, prime] evaluates one alternating-form coefficient table on an ordered basis tuple.";
formCoefficientValue[coefficients_Association, tuple_List, prime_Integer] := Module[{sorted},
  If[!DuplicateFreeQ[tuple], Return[0]];
  sorted = Sort[tuple];
  Mod[Signature[tuple] associationLookup[coefficients, sorted, 0], prime]
];

applyExternalVectorToCoefficients::usage = "applyExternalVectorToCoefficients[coefficients, rank, pos, vector, prime] plugs one concrete external vector into one alternating-form coefficient table.";
applyExternalVectorToCoefficients[coefficients_Association, rank_Integer?Positive, pos_Integer, vector_List, prime_Integer] := Association @ Select[
  Table[
    subset -> Mod[Sum[vector[[basisIndex]] formCoefficientValue[coefficients, Insert[subset, basisIndex, pos], prime], {basisIndex, 1, 10}], prime],
    {subset, allBasisSubsets[rank - 1]}
  ],
  Last[#] =!= 0 &
];

reduceFactorCoefficientsByExternalVectors::usage = "reduceFactorCoefficientsByExternalVectors[coefficients, vectorSymbols, probe, prime] plugs all external vectors into one factor coefficient table.";
reduceFactorCoefficientsByExternalVectors[coefficients_Association, vectorSymbols_List, probe_Association, prime_Integer] := Module[
  {positions, reduced = coefficients, remainingSymbols = vectorSymbols, pos, symbol},
  positions = Reverse @ Select[Range[Length[vectorSymbols]], KeyExistsQ[probe["VectorComponents"], vectorSymbols[[#]]] &];
  Do[
    pos = positions[[i]];
    symbol = remainingSymbols[[pos]];
    reduced = applyExternalVectorToCoefficients[reduced, Length[remainingSymbols], pos, probe["VectorComponents"][symbol], prime];
    remainingSymbols = Delete[remainingSymbols, pos],
    {i, Length[positions]}
  ];
  <|"Coefficients" -> reduced, "DummySymbols" -> remainingSymbols|>
];

disjointBlockBasisTuples::usage = "disjointBlockBasisTuples[blockSizes] returns canonical disjoint basis tuples for one block-tensor factorization.";
disjointBlockBasisTuples[{}] := {{}};
disjointBlockBasisTuples[blockSizes_List] := disjointBlockBasisTuples[blockSizes] = Module[{recurse},
  recurse[{}, _] := {{}};
  recurse[{size_, rest___}, remaining_List] := Flatten[
    Table[Prepend[#, subset] & /@ recurse[{rest}, Complement[remaining, subset]], {subset, Subsets[remaining, {size}]}],
    1
  ];
  recurse[blockSizes, Range[10]]
];

dummySymbolLocations::usage = "dummySymbolLocations[candidate, probe] returns the factor/position incidence list for every generated dummy symbol in one parsed candidate.";
dummySymbolLocations[candidate_Association, probe_Association] := Module[{rules},
  rules = Replace[
    Last @ Reap[
      Do[
        With[{part = candidate["FactorParts"][[i]]},
        Do[
          If[Head[part["VectorSymbols"][[j]]] === Symbol && !KeyExistsQ[probe["VectorComponents"], part["VectorSymbols"][[j]]],
            Sow[part["VectorSymbols"][[j]] -> {i, j}]
          ],
          {j, Length[part["VectorSymbols"]]}
        ]],
        {i, Length[candidate["FactorParts"]]}
      ]
    ],
    {{} -> {}, {items_List} :> items}
  ];
  rules = If[rules === {}, <||>, Merge[rules, Identity]];
  If[AllTrue[Values[rules], Length[#] == 2 &], rules, $Failed]
];

factorDummyBlocks::usage = "factorDummyBlocks[parts, factorIndex, dummyLocations, probe] partitions one factor's dummy symbols into partner blocks.";
factorDummyBlocks[parts_Association, factorIndex_Integer, dummyLocations_Association, probe_Association] := Module[
  {dummySymbols, currentPartner = None, currentBlock = {}, blocks = {}, locations, partners, partner},
  dummySymbols = Select[parts["VectorSymbols"], Head[#] === Symbol && !KeyExistsQ[probe["VectorComponents"], #] &];
  Do[
    locations = Lookup[dummyLocations, dummySymbols[[i]], {}];
    partners = DeleteCases[locations[[All, 1]], factorIndex];
    If[Length[partners] =!= 1, Return[$Failed]];
    partner = First[partners];
    If[currentPartner === None || partner === currentPartner,
      AppendTo[currentBlock, dummySymbols[[i]]],
      AppendTo[blocks, currentBlock];
      currentBlock = {dummySymbols[[i]]}
    ];
    currentPartner = partner,
    {i, Length[dummySymbols]}
  ];
  If[currentBlock =!= {}, AppendTo[blocks, currentBlock]];
  blocks
];

candidateExternalVectorSymbolSetKey::usage = "candidateExternalVectorSymbolSetKey[probe] returns a deterministic key for the set of external vectors assigned by one probe.";
candidateExternalVectorSymbolSetKey[probe_Association] := SortBy[Keys[Lookup[probe, "VectorComponents", <||>]], SymbolName];

candidateStructureCache::usage = "candidateStructureCache memoizes dummy-symbol incidence and per-factor dummy blocks by candidate and external-vector symbol set.";
candidateStructureCache = <||>;

candidateStructureCacheKey::usage = "candidateStructureCacheKey[candidate, probe] builds the cache key for candidate structure data.";
candidateStructureCacheKey[candidate_Association, probe_Association] := {candidate["Key"], candidateExternalVectorSymbolSetKey[probe]};

candidateStructureData::usage = "candidateStructureData[candidate, probe] returns cached dummy-symbol incidence and per-factor dummy blocks.";
candidateStructureData[candidate_Association, probe_Association] := Module[
  {key, cached, dummyLocations, factorBlocks},
  key = candidateStructureCacheKey[candidate, probe];
  cached = associationLookup[candidateStructureCache, key, Missing["NotFound"]];
  If[cached =!= Missing["NotFound"], Return[cached]];
  dummyLocations = dummySymbolLocations[candidate, probe];
  If[dummyLocations === $Failed, Return[$Failed]];
  factorBlocks = Table[
    factorDummyBlocks[candidate["FactorParts"][[i]], i, dummyLocations, probe],
    {i, Length[candidate["FactorParts"]]}
  ];
  (* Valid tensor networks require every dummy symbol to pair with exactly one partner factor. *)
  If[AnyTrue[factorBlocks, # === $Failed &], Return[$Failed]];
  cached = <|"DummyLocations" -> dummyLocations, "FactorBlocks" -> factorBlocks|>;
  AssociateTo[candidateStructureCache, key -> cached];
  cached
];

blockTensorFromReducedCoefficients::usage = "blockTensorFromReducedCoefficients[coefficients, blocks, prime] builds one sparse block tensor from reduced factor coefficients.";
blockTensorFromReducedCoefficients[coefficients_Association, blocks_List, prime_Integer] := If[
  blocks === {},
  <|"Blocks" -> {}, "Entries" -> <|{} -> associationLookup[coefficients, {}, 0]|>|>,
  <|
    "Blocks" -> blocks,
    "Entries" -> Association @ Select[
      Table[
        key -> formCoefficientValue[coefficients, Flatten[key], prime],
        {key, disjointBlockBasisTuples[Length /@ blocks]}
      ],
      Last[#] =!= 0 &
    ]
  |>
];

factorBlockTensorEntryCache::usage = "factorBlockTensorEntryCache memoizes block-tensor entries independent of dummy-symbol names.";
factorBlockTensorEntryCache = <||>;

factorBlockTensorProbeCache::usage = "factorBlockTensorProbeCache memoizes complete block tensors for one parsed factor under one probe and modulus.";
factorBlockTensorProbeCache = <||>;

coefficientAssociationKey::usage = "coefficientAssociationKey[coefficients] canonicalizes an alternating-form coefficient table for cache keys.";
coefficientAssociationKey[coefficients_Association] := orderedAssociationRules[coefficients];

probeCacheKey::usage = "probeCacheKey[probe] canonicalizes one selector probe for exact cache keys.";
probeCacheKey[probe_Association] := {
  orderedAssociationRules[Lookup[probe, "SpinorComponents", <||>]],
  orderedAssociationRules[Lookup[probe, "VectorComponents", <||>]]
};

factorBlockTensor::usage = "factorBlockTensor[candidate, factorIndex, factorBlocks, probe, primeData] builds one sparse block tensor for one parsed factor.";
factorBlockTensor[candidate_Association, factorIndex_Integer, factorBlocks_List, probe_Association, primeData_Association] := Module[
  {parts, coeffs, reduced, blocks, entryKey, entries, deltaValue},
  parts = candidate["FactorParts"][[factorIndex]];
  If[Lookup[parts, "Kind", "Gamma"] === "Delta",
    If[factorBlocks =!= {}, Return[$Failed]];
    deltaValue = deltaFactorValue[parts, probe, primeData["Prime"]];
    If[deltaValue === $Failed, Return[$Failed]];
    Return[<|"Blocks" -> {}, "Entries" -> <|{} -> deltaValue|>|>]
  ];
  coeffs = gammaFactorCoefficientAssociation[parts, probe, primeData];
  If[coeffs === $Failed, Return[$Failed]];
  reduced = reduceFactorCoefficientsByExternalVectors[coeffs, parts["VectorSymbols"], probe, primeData["Prime"]];
  blocks = factorBlocks;
  If[blocks === $Failed || Total[Length /@ blocks] =!= Length[reduced["DummySymbols"]], Return[$Failed]];
  (* Entry cache is keyed by block arities plus reduced alternating-form coefficients, not symbol identities. *)
  entryKey = {primeData["Prime"], Length /@ blocks, coefficientAssociationKey[reduced["Coefficients"]]};
  entries = associationLookup[factorBlockTensorEntryCache, entryKey, Missing["NotFound"]];
  If[entries === Missing["NotFound"],
    entries = blockTensorFromReducedCoefficients[reduced["Coefficients"], blocks, primeData["Prime"]]["Entries"];
    AssociateTo[factorBlockTensorEntryCache, entryKey -> entries];
  ];
  <|"Blocks" -> blocks, "Entries" -> entries|>
];

cachedFactorBlockTensor::usage = "cachedFactorBlockTensor[candidate, factorIndex, factorBlocks, probe, primeData] memoizes sparse block tensors across selector probes.";
cachedFactorBlockTensor[candidate_Association, factorIndex_Integer, factorBlocks_List, probe_Association, primeData_Association] := Module[
  {key, cached},
  key = {primeData["Prime"], probeCacheKey[probe], factorIndex, candidate["Key"]};
  cached = associationLookup[factorBlockTensorProbeCache, key, Missing["NotFound"]];
  If[cached =!= Missing["NotFound"], Return[cached]];
  cached = factorBlockTensor[candidate, factorIndex, factorBlocks, probe, primeData];
  AssociateTo[factorBlockTensorProbeCache, key -> cached];
  cached
];

scalarBlockTensorValue::usage = "scalarBlockTensorValue[tensor, prime] extracts the scalar value carried by a zero-block tensor.";
scalarBlockTensorValue[tensor_Association, prime_Integer] := Mod[associationLookup[tensor["Entries"], {}, 0], prime];

contractBlockTensors::usage = "contractBlockTensors[left, leftPos, right, rightPos, prime] contracts one shared block between two sparse block tensors.";
contractBlockTensors[left_Association, leftPos_Integer, right_Association, rightPos_Integer, prime_Integer] := Module[
  {indexedLeft, indexedRight, resultRules, resultEntries},
  indexedLeft = Map[({Delete[#[[1]], leftPos], #[[2]]} & /@ #) &, GroupBy[Normal[left["Entries"]], #[[1, leftPos]] &]];
  indexedRight = Map[({Delete[#[[1]], rightPos], #[[2]]} & /@ #) &, GroupBy[Normal[right["Entries"]], #[[1, rightPos]] &]];
  resultRules = Replace[
    Last @ Reap[
      Do[
        If[!KeyExistsQ[indexedRight, key], Continue[]];
        Do[Sow[Join[leftTerm[[1]], rightTerm[[1]]] -> Mod[leftTerm[[2]] rightTerm[[2]], prime]], {leftTerm, indexedLeft[key]}, {rightTerm, indexedRight[key]}],
        {key, Keys[indexedLeft]}
      ]
    ],
    {{} -> {}, {items_List} :> items}
  ];
  resultEntries = If[resultRules === {}, <||>, Select[Merge[resultRules, Mod[Total[#], prime] &], # =!= 0 &]];
  <|"Blocks" -> Join[Delete[left["Blocks"], leftPos], Delete[right["Blocks"], rightPos]], "Entries" -> resultEntries|>
];

sharedBlockPair::usage = "sharedBlockPair[tensors] returns the first pair of tensors and block positions that share the same dummy block.";
sharedBlockPair[tensors_List] := Module[{seen = <||>, i, p, block},
  For[i = 1, i <= Length[tensors], i++,
    For[p = 1, p <= Length[tensors[[i, "Blocks"]]], p++,
      block = tensors[[i, "Blocks", p]];
      If[KeyExistsQ[seen, block], Return[Join[seen[block], {i, p}]]];
      AssociateTo[seen, block -> {i, p}];
    ]
  ];
  Missing["NoSharedBlock"]
];

reduceBlockTensorNetwork::usage = "reduceBlockTensorNetwork[tensors, prime] contracts a sparse block-tensor network down to a modular scalar when possible.";
reduceBlockTensorNetwork[tensors_List, prime_Integer] := Module[{work = tensors, scalar = 1, pair, contracted, i},
  work = Select[work, # =!= $Failed &];
  If[AnyTrue[work, # === $Failed &], Return[$Failed]];
  While[True,
    (* Eagerly fold scalar factors to keep the working network small before choosing the next shared block. *)
    For[i = Length[work], i >= 1, i--,
      If[work[[i, "Blocks"]] === {}, scalar = Mod[scalar scalarBlockTensorValue[work[[i]], prime], prime]; work = Delete[work, i]];
    ];
    If[work === {}, Return[scalar]];
    If[Length[work] == 1, Return[If[work[[1, "Blocks"]] === {}, Mod[scalar scalarBlockTensorValue[work[[1]], prime], prime], $Failed]]];
    pair = sharedBlockPair[work];
    If[pair === Missing["NoSharedBlock"], Return[$Failed]];
    contracted = contractBlockTensors[work[[pair[[1]]]], pair[[2]], work[[pair[[3]]]], pair[[4]], prime];
    work = Append[Delete[work, {{pair[[3]]}, {pair[[1]]}}], contracted];
  ]
];

evaluateCandidateAtProbe::usage = "evaluateCandidateAtProbe[candidate, probe, primeData] evaluates one parsed or raw candidate expression at one modular probe.";
evaluateCandidateAtProbe[candidate_Association, probe_Association, primeData_Association] := Module[{structureData, tensors, factorBlocks},
  structureData = candidateStructureData[candidate, probe];
  If[structureData === $Failed, Return[$Failed]];
  factorBlocks = structureData["FactorBlocks"];
  tensors = Table[cachedFactorBlockTensor[candidate, i, factorBlocks[[i]], probe, primeData], {i, Length[candidate["Factors"]]}];
  If[AnyTrue[tensors, # === $Failed &], Return[$Failed]];
  reduceBlockTensorNetwork[tensors, primeData["Prime"]]
];
evaluateCandidateAtProbe[expr_, probe_Association, primeData_Association] := Module[{candidate = parseCandidate[expr]},
  If[candidate === $Failed, $Failed, evaluateCandidateAtProbe[candidate, probe, primeData]]
];
evaluateCandidateAtProbe[_, _, _] := $Failed;


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
