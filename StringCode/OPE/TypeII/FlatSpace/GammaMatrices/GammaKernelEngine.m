(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`OPE`TypeII`FlatSpace`GammaMatrices`GammaKernelEngine`"];
Needs["StringCode`Symbols`TypeII`FlatSpace`"];
Needs["StringCode`OPE`TypeII`FlatSpace`GammaMatrices`"];
Needs["StringCode`OPE`TypeII`FlatSpace`GammaMatrices`GammaProductGrammar`"];


(* ::Section:: *)
(*Logic*)


Begin["Private`"];

spinIterationValues::usage = "spinIterationValues[chirality] returns the explicit spin-vector basis used to randomize or sum over that chirality.";
spinIterationValues["antichiral"] := antichiralspins;
spinIterationValues[_] := chiralspins;

spinProjectionSpinBasisState::usage =
  "spinProjectionSpinBasisState[chirality] returns the ordered explicit spin basis used by the compiled exact gamma engine.";
spinProjectionSpinBasisState[chirality_String] := spinProjectionSpinBasisState[chirality] = spinIterationValues[chirality];

spinProjectionConcreteSpinBasisIndex::usage =
  "spinProjectionConcreteSpinBasisIndex[spin] returns the canonical 1-based spin-basis index for one concrete spin source, accepting either an index or an explicit chiral/antichiral basis vector.";
spinProjectionConcreteSpinBasisIndex[spin_Integer?Positive] := spin;
spinProjectionConcreteSpinBasisIndex[spin_List] := Module[{chiralIndex, antichiralIndex},
  chiralIndex = FirstPosition[spinProjectionSpinBasisState["chiral"], spin, Missing["NotFound"], {1}, Heads -> False];
  If[chiralIndex =!= Missing["NotFound"], Return[First[chiralIndex]]];
  antichiralIndex = FirstPosition[spinProjectionSpinBasisState["antichiral"], spin, Missing["NotFound"], {1}, Heads -> False];
  If[antichiralIndex =!= Missing["NotFound"], Return[First[antichiralIndex]]];
  $Failed
];
spinProjectionConcreteSpinBasisIndex[_] := $Failed;

spinProjectionGammaLinkMatrix::usage =
  "spinProjectionGammaLinkMatrix[link] returns the exact 16x16 matrix associated with one concrete gamma-chain link.";
spinProjectionGammaLinkMatrix[link_] := gammaProductLinkMatrix[link];

spinProjectionGammaVectorLinkHead::usage =
  "spinProjectionGammaVectorLinkHead[link] returns the GammaUDHold/GammaDUHold head for one concrete vector link.";
spinProjectionGammaVectorLinkHead[GammaUDHold[_Integer]] := GammaUDHold;
spinProjectionGammaVectorLinkHead[GammaDUHold[_Integer]] := GammaDUHold;
spinProjectionGammaVectorLinkHead[_] := $Failed;

spinProjectionGammaVectorLinkIndex::usage =
  "spinProjectionGammaVectorLinkIndex[link] returns the concrete vector index carried by one GammaUDHold/GammaDUHold link.";
spinProjectionGammaVectorLinkIndex[GammaUDHold[mu_Integer]] := mu;
spinProjectionGammaVectorLinkIndex[GammaDUHold[mu_Integer]] := mu;
spinProjectionGammaVectorLinkIndex[_] := $Failed;

spinProjectionAntisymmetrizedMatrixFromPattern::usage =
  "spinProjectionAntisymmetrizedMatrixFromPattern[linkHeads, inds] antisymmetrizes the vector labels while preserving the ordered U/D head pattern.";
spinProjectionAntisymmetrizedMatrixFromPattern[{}, {}] := gammaProductAntisymmetrizedMatrixFromPattern[{}, {}];
spinProjectionAntisymmetrizedMatrixFromPattern[linkHeads_List, inds_List] /; Length[linkHeads] === Length[inds] :=
  gammaProductAntisymmetrizedMatrixFromPattern[linkHeads, inds];

spinProjectionAntisymmetrizedMatrix::usage =
  "spinProjectionAntisymmetrizedMatrix[vectorLinks] returns the exact antisymmetrized gamma matrix for one concrete vector-link list.";
spinProjectionAntisymmetrizedMatrix[vectorLinks_List] := spinProjectionAntisymmetrizedMatrix[vectorLinks] =
  gammaProductAntisymmetrizedMatrix[vectorLinks];

spinProjectionFlipVectorLinkDirections::usage =
  "spinProjectionFlipVectorLinkDirections[links] swaps GammaUDHold and GammaDUHold on every explicit vector link.";
spinProjectionFlipVectorLinkDirections[links_List] := links /. {
  GammaUDHold[mu_Integer] :> GammaDUHold[mu],
  GammaDUHold[mu_Integer] :> GammaUDHold[mu]
};

spinProjectionOddMixedNoCTagLinksQ::usage =
  "spinProjectionOddMixedNoCTagLinksQ[links] is True exactly for odd-rank mixed chains with no leading C tag.";
spinProjectionOddMixedNoCTagLinksQ[links_List] := Module[{cTag, coreLinks, vectorLinks, chiralities},
  If[links === {}, Return[False]];
  cTag = If[MatchQ[First[links], CUDHold | CDUHold], First[links], None];
  If[cTag =!= None, Return[False]];
  coreLinks = links;
  vectorLinks = Select[coreLinks, gammaVectorLinkQ];
  If[vectorLinks === {} || EvenQ[Length[vectorLinks]], Return[False]];
  chiralities = gammaProductSpinorChiralities[links];
  chiralities[[1]] =!= chiralities[[2]]
];

spinProjectionGammaFactorMatrixRaw::usage =
  "spinProjectionGammaFactorMatrixRaw[links] returns the stored matrix represented by one concrete GammaAntisymmetricProductHold link list.";
spinProjectionGammaFactorMatrixRaw[links_List] := Module[{matrix = gammaProductFactorMatrixRaw[links]},
  If[links =!= {}, Return[matrix]];
  Switch[
    gammaProductSpinorChiralities[links],
    {"chiral", "antichiral"}, CUDSparse,
    {"antichiral", "chiral"}, CDUSparse,
    _, matrix
  ]
];

spinProjectionGammaFactorMatrix::usage =
  "spinProjectionGammaFactorMatrix[links] returns the exact matrix represented by one concrete GammaAntisymmetricProductHold link list.";
spinProjectionGammaFactorMatrix[links_List] := spinProjectionGammaFactorMatrix[links] =
  spinProjectionGammaFactorMatrixRaw[links];

spinProjectionDisjointBlockBasisTuples::usage =
  "spinProjectionDisjointBlockBasisTuples[blockSizes] returns ordered tuples of pairwise-disjoint increasing basis subsets with the requested ranks.";
spinProjectionDisjointBlockBasisTuples[{}] := {{}};
spinProjectionDisjointBlockBasisTuples[blockSizes_List] := spinProjectionDisjointBlockBasisTuples[blockSizes] = Module[{recurse},
  recurse[{}, _] := {{}};
  recurse[{size_, rest___}, remaining_List] := Flatten[
    Table[
      Prepend[#, subset] & /@ recurse[{rest}, Complement[remaining, subset]],
      {subset, Subsets[remaining, {size}]}
    ],
    1
  ];
  recurse[blockSizes, Range[10]]
];

spinProjectionAssociationLookup::usage =
  "spinProjectionAssociationLookup[assoc, key, default] looks up an association value while supporting list-valued keys.";
spinProjectionAssociationLookup[assoc_Association, key_, default_] := If[KeyExistsQ[assoc, key], assoc[key], default];

persistentCacheSourceFiles::usage =
  "persistentCacheSourceFiles[] returns the source files whose hashes version the persistent TypeII flat-space gamma-kernel cache.";
persistentCacheSourceFiles[] := persistentCacheSourceFiles[] = Module[{rootDir},
  rootDir = DirectoryName[DirectoryName[FindFile["StringCode`OPE`TypeII`FlatSpace`GammaMatrices`GammaKernelEngine`"]]];
  FileNameJoin[{rootDir, #}] & /@ {
    "GammaMatrices/GammaMatrices.m",
    "GammaMatrices/GammaKernelEngine.m",
    "GammaMatrices/SpinFieldConventionData.m",
    "TensorStructures/IndependentTensorStructures.m",
    "TensorStructures/IndependentTensorStructuresSelector.m",
    "SpinProjection/Compile.m"
  }
];

persistentCacheSourceHash::usage =
  "persistentCacheSourceHash[] returns the deterministic source hash used in the persistent gamma-kernel cache filename.";
persistentCacheSourceHash[] := persistentCacheSourceHash[] = IntegerString[
  Hash[FileHash[#, "SHA256"] & /@ persistentCacheSourceFiles[], "SHA256"],
  36
];

persistentGammaKernelCacheFile::usage =
  "persistentGammaKernelCacheFile[] returns the on-disk mx file used for the persistent TypeII flat-space gamma-kernel cache.";
persistentGammaKernelCacheFile[] := persistentGammaKernelCacheFile[] = FileNameJoin[
  {
    $UserBaseDirectory,
    "ApplicationData",
    "StringCode",
    "TypeIIFlatSpaceGammaKernelCache-" <> persistentCacheSourceHash[] <> ".mx"
  }
];

spinProjectionPersistentGammaKernelCacheLoaded::usage =
  "spinProjectionPersistentGammaKernelCacheLoaded tracks whether the persistent gamma-kernel cache has been loaded in this kernel session.";
spinProjectionPersistentGammaKernelCacheLoaded = False;

spinProjectionPersistentGammaKernelCacheDirty::usage =
  "spinProjectionPersistentGammaKernelCacheDirty is True exactly when the persistent gamma-kernel cache needs to be flushed to disk.";
spinProjectionPersistentGammaKernelCacheDirty = False;

spinProjectionPersistentGammaKernelCacheBoundaryDepth::usage =
  "spinProjectionPersistentGammaKernelCacheBoundaryDepth counts nested persistent-cache flush boundaries.";
spinProjectionPersistentGammaKernelCacheBoundaryDepth = 0;

loadPersistentGammaKernelCache0::usage =
  "loadPersistentGammaKernelCache0[] loads the persistent gamma-kernel cache once per kernel session if the current source hash matches.";
loadPersistentGammaKernelCache0[] := Module[{file},
  If[TrueQ[spinProjectionPersistentGammaKernelCacheLoaded], Return[Null]];
  spinProjectionPersistentGammaKernelCacheLoaded = True;
  file = persistentGammaKernelCacheFile[];
  If[FileExistsQ[file], Quiet[Check[Get[file], Null]]];
  Null
];

markPersistentGammaKernelCacheDirty0::usage =
  "markPersistentGammaKernelCacheDirty0[] marks the persistent gamma-kernel cache as dirty after a new persisted entry is created.";
markPersistentGammaKernelCacheDirty0[] := (spinProjectionPersistentGammaKernelCacheDirty = True);

flushPersistentCacheIfDirty::usage =
  "flushPersistentCacheIfDirty[] writes the persistent gamma-kernel cache to disk when new persisted entries were created.";
flushPersistentCacheIfDirty[] := Module[{file, dir, success = True},
  loadPersistentGammaKernelCache0[];
  If[!TrueQ[spinProjectionPersistentGammaKernelCacheDirty], Return[Null]];
  file = persistentGammaKernelCacheFile[];
  dir = DirectoryName[file];
  If[!DirectoryQ[dir],
    success = Quiet[Check[(CreateDirectory[dir, CreateIntermediateDirectories -> True]; True), False]];
    If[!TrueQ[success], Return[Null]];
  ];
  success = Quiet[Check[(DumpSave[file, {spinProjectionGammaKernelRegistry, spinProjectionGammaKernelPairMatrixCache}]; True), False]];
  If[TrueQ[success], spinProjectionPersistentGammaKernelCacheDirty = False];
  If[TrueQ[success], Null, $Failed]
];

withPersistentCacheBoundary::usage =
  "withPersistentCacheBoundary[expr] evaluates expr inside one nested persistent-cache flush boundary and flushes the cache only when the outermost boundary exits.";
withPersistentCacheBoundary[expr_] := Module[{},
  loadPersistentGammaKernelCache0[];
  Internal`WithLocalSettings[
    spinProjectionPersistentGammaKernelCacheBoundaryDepth++,
    expr,
    spinProjectionPersistentGammaKernelCacheBoundaryDepth = Max[0, spinProjectionPersistentGammaKernelCacheBoundaryDepth - 1];
    If[spinProjectionPersistentGammaKernelCacheBoundaryDepth === 0, flushPersistentCacheIfDirty[]]
  ]
];

flushPersistentGammaKernelCache0::usage =
  "flushPersistentGammaKernelCache0[] flushes the persistent gamma-kernel cache on demand.";
flushPersistentGammaKernelCache0[] := Module[{},
  loadPersistentGammaKernelCache0[];
  flushPersistentCacheIfDirty[]
];

spinProjectionNormalizeCompiledTermParts::usage =
  "spinProjectionNormalizeCompiledTermParts[parts] strips vector deltas into a scalar zero/nonzero factor, spin equalities, vector equalities, and normalized gamma factors for one compiled term.";
spinProjectionNormalizeCompiledTermParts[parts_List] := Module[
  {
    canonicalPair,
    deltaParts,
    spinEqualities,
    gammaParts,
    vectorSources,
    parents = <||>,
    find,
    join,
    roots,
    classes,
    members,
    concreteMembers,
    exposedMembers,
    representative,
    rules = <||>,
    vectorEqualities = {},
    normalizedGammaParts
  },
  canonicalPair[pair_List] := SortBy[pair, {First[#], Last[#]} &];
  deltaParts = Cases[parts, {0, _, _}];
  spinEqualities = DeleteDuplicates @ (canonicalPair /@ Cases[parts, {1, left_, right_} :> {left, right}]);
  gammaParts = Cases[parts, {2, _, _, _}];
  vectorSources = DeleteDuplicates @ Join[
    Flatten[Cases[deltaParts, {0, left_, right_} :> {left, right}], 1],
    Flatten[Cases[gammaParts, {2, _, _, desc_} :> desc[[3]], 1], 1]
  ];
  Scan[Function[src, parents[src] = src], vectorSources];
  find[src_] := parents[src] = If[parents[src] === src, src, find[parents[src]]];
  join[left_, right_] := Module[{leftRoot = find[left], rightRoot = find[right]},
    If[leftRoot =!= rightRoot, parents[rightRoot] = leftRoot]
  ];
  Scan[Function[factor, join[factor[[2]], factor[[3]]]], deltaParts];
  roots = DeleteDuplicates[find /@ vectorSources];
  classes = DeleteDuplicates @ Map[
    Function[root, DeleteDuplicates @ Select[vectorSources, find[#] === root &]],
    roots
  ];
  If[
    AnyTrue[
      classes,
      Function[currentMembers, Length[DeleteDuplicates[Last /@ Select[currentMembers, #[[1]] === 4 &]]] > 1]
    ],
    Return[<|"ScalarFactor" -> 0, "SpinEqualities" -> spinEqualities, "VectorEqualities" -> {}, "GammaParts" -> {}|>]
  ];
  Scan[
    Function[currentMembers,
      members = currentMembers;
      concreteMembers = DeleteDuplicates @ Select[members, #[[1]] === 4 &];
      exposedMembers = SortBy[DeleteDuplicates @ Select[members, MemberQ[{1, 2}, #[[1]]] &], {First[#], Last[#]} &];
      representative = Which[
        concreteMembers =!= {}, First[concreteMembers],
        exposedMembers =!= {}, First[exposedMembers],
        True, First[Select[members, #[[1]] === 3 &]]
      ];
      Scan[Function[src, rules[src] = representative], members];
      If[MatchQ[representative, {1 | 2 | 4, _Integer}],
        vectorEqualities = Join[
          vectorEqualities,
          canonicalPair /@ ({#, representative} & /@ DeleteCases[exposedMembers, representative])
        ]
      ]
    ],
    classes
  ];
  normalizedGammaParts = gammaParts /. {2, left_, right_, desc_} :>
    {
      2,
      left,
      right,
      {desc[[1]], desc[[2]], (If[KeyExistsQ[rules, #], rules[#], #] & /@ desc[[3]]), desc[[4]], None}
    };
  <|
    "ScalarFactor" -> 1,
    "SpinEqualities" -> spinEqualities,
    "VectorEqualities" -> DeleteDuplicates[vectorEqualities],
    "GammaParts" -> normalizedGammaParts
  |>
];

spinProjectionGammaKernelRegistry::usage =
  "spinProjectionGammaKernelRegistry memoizes structural metadata for normalized exact gamma kernels shared across selector and compiled RHS terms.";
spinProjectionGammaKernelRegistry = <||>;

spinProjectionGammaKernelSliceCache::usage =
  "spinProjectionGammaKernelSliceCache memoizes exact concrete vector slices of registered gamma kernels on first use.";
spinProjectionGammaKernelSliceCache = <||>;

spinProjectionGammaKernelComponents::usage =
  "spinProjectionGammaKernelComponents[gammaParts] partitions normalized gamma factors into independent dummy-sharing kernel components.";
spinProjectionGammaKernelComponents[gammaParts_List] := Module[
  {factorDummySources, sourceFactors = <||>, neighbors, remaining, start, queue, current, components = {}},
  If[gammaParts === {}, Return[{}]];
  factorDummySources = DeleteDuplicates @ Cases[#[[4, 3]], src_ /; First[src] === 3] & /@ gammaParts;
  Do[
    Scan[
      Function[src, sourceFactors[src] = Append[spinProjectionAssociationLookup[sourceFactors, src, {}], i]],
      factorDummySources[[i]]
    ],
    {i, Length[gammaParts]}
  ];
  neighbors = AssociationThread[Range[Length[gammaParts]] -> ConstantArray[{}, Length[gammaParts]]];
  Scan[
    Function[factors,
      If[Length[factors] > 1,
        Scan[
          Function[i, neighbors[i] = Union[neighbors[i], DeleteCases[factors, i]]],
          factors
        ]
      ]
    ],
    Values[sourceFactors]
  ];
  remaining = Range[Length[gammaParts]];
  While[remaining =!= {},
    start = First[remaining];
    queue = {start};
    current = {};
    While[queue =!= {},
      start = First[queue];
      queue = Rest[queue];
      If[!MemberQ[remaining, start], Continue[]];
      remaining = DeleteCases[remaining, start];
      AppendTo[current, gammaParts[[start]]];
      queue = Join[queue, Lookup[neighbors, start, {}]]
    ];
    AppendTo[components, current]
  ];
  components
];

spinProjectionKernelSourceSortKey::usage =
  "spinProjectionKernelSourceSortKey[src] returns the structural source tag used to order gamma factors independently of concrete boundary labels.";
spinProjectionKernelSourceSortKey[src_List] := Switch[src[[1]],
  4, {2, src[[2]]},
  3, {1},
  _, {0}
];

spinProjectionKernelFactorSortKey::usage =
  "spinProjectionKernelFactorSortKey[factor] returns the canonical structural sort key for one normalized gamma factor, ignoring concrete boundary-slot names.";
spinProjectionKernelFactorSortKey[factor_List] := Module[{desc = factor[[4]]},
  {
    Replace[desc[[1]], None -> 0],
    desc[[2]],
    spinProjectionKernelSourceSortKey /@ desc[[3]],
    desc[[4]]
  }
];

spinProjectionKernelDummySourceSignature::usage =
  "spinProjectionKernelDummySourceSignature[src, orderedComponent] returns the canonical occurrence signature used to order dummy sources inside one registered kernel component.";
spinProjectionKernelDummySourceSignature[src_, orderedComponent_List] := Cases[
  MapIndexed[
    Function[{factor, index},
      Cases[
        Position[factor[[4, 3]], src, {1}],
        {pos_Integer} :> {First[index], pos, factor[[4, 2, pos]]}
      ]
    ],
    orderedComponent
  ],
  {_Integer, _Integer, _Integer},
  Infinity
];

spinProjectionGammaKernelJoinPlan::usage =
  "spinProjectionGammaKernelJoinPlan[factors] precomputes how one kernel's factor rule lists are joined over shared spin slots.";
spinProjectionGammaKernelJoinPlan[factors_List] := Module[
  {currentPos = <||>},
  Map[
    Function[factor,
      Module[{slots = factor["SpinSlots"], commonSlots, extraSlots},
        commonSlots = Select[slots, KeyExistsQ[currentPos, #] &];
        extraSlots = Select[slots, !KeyExistsQ[currentPos, #] &];
        Scan[Function[slot, currentPos[slot] = 1 + Length[currentPos]], extraSlots];
        <|
          "CommonCurrentPos" -> Lookup[currentPos, commonSlots],
          "LocalCommonPos" -> Flatten[Position[slots, #] & /@ commonSlots],
          "ExtraSlots" -> extraSlots,
          "LocalExtraPos" -> Flatten[Position[slots, #] & /@ extraSlots]
        |>
      ]
    ],
    factors
  ]
];

spinProjectionRegisterGammaKernelComponent::usage =
  "spinProjectionRegisterGammaKernelComponent[component] registers one normalized gamma-kernel component and returns its runtime lookup reference.";
spinProjectionRegisterGammaKernelComponent[component_List] := Module[
  {
    orderedComponent,
    spinSlots = {},
    vectorSlots = {},
    spinPos = <||>,
    vectorPos = <||>,
    localSpin,
    localVector,
    dummyOrder,
    dummyOccurrences = <||>,
    blockMembers = <||>,
    blockMemberships,
    blocks,
    blockIds = <||>,
    blockOffsets = <||>,
    blockSizes,
    factors,
    storedFactors,
    key
  },
  orderedComponent = SortBy[
    component,
    spinProjectionKernelFactorSortKey
  ];
  localSpin[src_] := If[KeyExistsQ[spinPos, src], spinPos[src], AppendTo[spinSlots, src]; spinPos[src] = Length[spinSlots]];
  localVector[src_] := If[KeyExistsQ[vectorPos, src], vectorPos[src], AppendTo[vectorSlots, src]; vectorPos[src] = Length[vectorSlots]];
  dummyOrder = SortBy[
    DeleteDuplicates @ Flatten[Cases[orderedComponent, {2, _, _, desc_} :> Select[desc[[3]], First[#] === 3 &], 1], 1],
    spinProjectionKernelDummySourceSignature[#, orderedComponent] &
  ];
  Do[
    With[{sources = Select[orderedComponent[[factorIndex, 4, 3]], First[#] === 3 &]},
      If[Length[sources] =!= Length[DeleteDuplicates[sources]], Return[<|"ScalarFactor" -> 0, "KernelRef" -> None|>]];
      Scan[
        Function[src, dummyOccurrences[src] = Append[spinProjectionAssociationLookup[dummyOccurrences, src, {}], factorIndex]],
        DeleteDuplicates[sources]
      ]
    ],
    {factorIndex, Length[orderedComponent]}
  ];
  blockMemberships = DeleteDuplicates[spinProjectionAssociationLookup[dummyOccurrences, #, {}] & /@ dummyOrder];
  Scan[Function[membership, blockMembers[membership] = {}], blockMemberships];
  Scan[Function[src, blockMembers[dummyOccurrences[src]] = Append[blockMembers[dummyOccurrences[src]], src]], dummyOrder];
  blockMemberships = SortBy[blockMemberships, {Length[spinProjectionAssociationLookup[blockMembers, #, {}]], #} &];
  blocks = spinProjectionAssociationLookup[blockMembers, #, {}] & /@ blockMemberships;
  blockSizes = Length /@ blocks;
  If[AnyTrue[blockSizes, # > 10 &], Return[<|"ScalarFactor" -> 0, "KernelRef" -> None|>]];
  Scan[
    Function[index,
      Scan[
        Function[pos,
          blockIds[blocks[[index, pos]]] = index;
          blockOffsets[blocks[[index, pos]]] = pos
        ],
        Range[Length[blocks[[index]]]]
      ]
    ],
    Range[Length[blocks]]
  ];
  factors = Map[
    Function[factor,
      Module[{desc = factor[[4]], factorBlocks},
        factorBlocks = DeleteDuplicates[blockIds /@ Select[desc[[3]], First[#] === 3 &]];
        <|
          "SpinSlots" -> DeleteDuplicates[{localSpin[factor[[2]]], localSpin[factor[[3]]]}],
          "Blocks" -> factorBlocks,
          "BlockSizes" -> (blockSizes[[#]] & /@ factorBlocks),
          "Desc" -> {
            desc[[1]],
            desc[[2]],
            Map[
              Switch[#[[1]],
                4, {2, #[[2]]},
                3, {1, blockIds[#], blockOffsets[#]},
                _, {0, localVector[#]}
              ] &,
              desc[[3]]
            ],
            desc[[4]]
          },
          "KeyData" -> {
            localSpin[factor[[2]]],
            localSpin[factor[[3]]],
            {
              desc[[1]],
              desc[[2]],
              Map[
                Switch[#[[1]],
                  4, {2, #[[2]]},
                  3, {1, blockIds[#], blockOffsets[#]},
                  _, {0, localVector[#]}
                ] &,
                desc[[3]]
              ],
              desc[[4]]
            }
          }
        |>
      ]
    ],
    orderedComponent
  ];
  storedFactors = Map[KeyDrop[#, {"KeyData"}] &, factors];
  key = {blockSizes, factors[[All, "KeyData"]]};
  If[!KeyExistsQ[spinProjectionGammaKernelRegistry, key],
    spinProjectionGammaKernelRegistry[key] = <|
      "BlockSizes" -> blockSizes,
      "BlockTuples" -> spinProjectionDisjointBlockBasisTuples[blockSizes],
      "SpinSlotCount" -> Length[spinSlots],
      "Factors" -> storedFactors,
      "JoinPlan" -> spinProjectionGammaKernelJoinPlan[storedFactors]
    |>;
    markPersistentGammaKernelCacheDirty0[]
  ];
  <|"ScalarFactor" -> 1, "KernelRef" -> <|"Key" -> key, "SpinSlots" -> spinSlots, "VectorSlots" -> vectorSlots|>|>
];

spinProjectionGammaKernelData::usage =
  "spinProjectionGammaKernelData[gammaParts] registers the normalized gamma kernels needed by one compiled term and returns the runtime lookup references.";
spinProjectionGammaKernelData[gammaParts_List] := Module[{components, refs = {}, result},
  components = spinProjectionGammaKernelComponents[gammaParts];
  Do[
    result = spinProjectionRegisterGammaKernelComponent[component];
    If[result === $Failed, Return[$Failed]];
    If[result["ScalarFactor"] === 0, Return[<|"ScalarFactor" -> 0, "KernelRefs" -> {}|>]];
    If[result["KernelRef"] =!= None, AppendTo[refs, result["KernelRef"]]],
    {component, components}
  ];
  <|"ScalarFactor" -> 1, "KernelRefs" -> refs|>
];

spinProjectionVectorSourceValue::usage =
  "spinProjectionVectorSourceValue[src, freeVectors, stateVectors, dummy] resolves one compiled vector source to a concrete vector index.";
spinProjectionVectorSourceValue[src_, freeVectors_List, stateVectors_List, dummy_List] := Switch[src[[1]],
  1, freeVectors[[src[[2]]]],
  2, stateVectors[[src[[2]]]],
  3, dummy[[src[[2]]]],
  4, src[[2]],
  _, $Failed
];

spinProjectionSpinSourceValue::usage =
  "spinProjectionSpinSourceValue[src, freeSpins, stateSpins] resolves one compiled spin source to a concrete 1-based spin basis index.";
spinProjectionSpinSourceValue[src_, freeSpins_List, stateSpins_List] := Switch[src[[1]],
  1, freeSpins[[src[[2]]]],
  2, spinProjectionConcreteSpinBasisIndex[stateSpins[[src[[2]]]]],
  _, $Failed
];

spinProjectionConcreteGammaSparseMatrix::usage =
  "spinProjectionConcreteGammaSparseMatrix[desc, freeVectors, stateVectors, dummy] resolves one compiled exact gamma descriptor to a concrete sparse 16x16 matrix.";
spinProjectionConcreteGammaSparseMatrix[desc_, freeVectors_List, stateVectors_List, dummy_List] := Module[{values, matrix},
  If[desc[[5]] =!= None, Return[desc[[5]]]];
  values = spinProjectionVectorSourceValue[#, freeVectors, stateVectors, dummy] & /@ desc[[3]];
  If[!AllTrue[values, IntegerQ], Return[$Failed]];
  matrix = spinProjectionGammaFactorMatrix @ Join[
    If[desc[[1]] === None, {}, {desc[[1]]}],
    MapThread[If[#1 === 1, GammaUDHold[#2], GammaDUHold[#2]] &, {desc[[2]], values}],
    desc[[4]]
  ];
  matrix
];

spinProjectionConcreteGammaEntryRulesCache::usage =
  "spinProjectionConcreteGammaEntryRulesCache memoizes nonzero entry rules for concrete compiled gamma matrices.";
spinProjectionConcreteGammaEntryRulesCache = <||>;

spinProjectionConcreteGammaEntryRules::usage =
  "spinProjectionConcreteGammaEntryRules[desc, freeVectors, stateVectors, dummy] returns the nonzero {row,col}->value rules for one concrete compiled gamma matrix.";
spinProjectionConcreteGammaEntryRules[desc_, freeVectors_List, stateVectors_List, dummy_List] := Module[{values, key, matrix, rules},
  values = spinProjectionVectorSourceValue[#, freeVectors, stateVectors, dummy] & /@ desc[[3]];
  If[!AllTrue[values, IntegerQ], Return[$Failed]];
  key = {desc[[1]], desc[[2]], values, desc[[4]]};
  If[KeyExistsQ[spinProjectionConcreteGammaEntryRulesCache, key], Return[spinProjectionConcreteGammaEntryRulesCache[key]]];
  matrix = spinProjectionConcreteGammaSparseMatrix[desc, freeVectors, stateVectors, dummy];
  If[matrix === $Failed, Return[$Failed]];
  rules = Cases[Most[ArrayRules[SparseArray[matrix]]], Rule[{i_Integer, j_Integer}, value_] /; value =!= 0 :> {{i, j}, value}];
  AssociateTo[spinProjectionConcreteGammaEntryRulesCache, key -> rules];
  rules
];

spinProjectionConcreteGammaEntryValue::usage =
  "spinProjectionConcreteGammaEntryValue[desc, freeVectors, stateVectors, dummy, row, col] returns one exact concrete matrix entry for a compiled gamma descriptor.";
spinProjectionConcreteGammaEntryValue[desc_, freeVectors_List, stateVectors_List, dummy_List, row_Integer?Positive, col_Integer?Positive] := Module[{matrix},
  matrix = spinProjectionConcreteGammaSparseMatrix[desc, freeVectors, stateVectors, dummy];
  If[matrix === $Failed, Return[$Failed]];
  matrix[[row, col]]
];

spinProjectionGammaKernelVectorValue::usage =
  "spinProjectionGammaKernelVectorValue[spec, vectorTuple, blockTuple] resolves one localized kernel slot specification to a concrete vector index.";
spinProjectionGammaKernelVectorValue[spec_, vectorTuple_List, blockTuple_List] := Switch[spec[[1]],
  0, vectorTuple[[spec[[2]]]],
  1, blockTuple[[spec[[2]], spec[[3]]]],
  2, spec[[2]],
  _, $Failed
];

spinProjectionGammaKernelEntryRules::usage =
  "spinProjectionGammaKernelEntryRules[desc, vectorTuple, blockTuple] resolves one localized gamma descriptor to its exact nonzero matrix-entry rules.";
spinProjectionGammaKernelEntryRules[desc_, vectorTuple_List, blockTuple_List] := Module[{values},
  values = spinProjectionGammaKernelVectorValue[#, vectorTuple, blockTuple] & /@ desc[[3]];
  If[!AllTrue[values, IntegerQ], Return[$Failed]];
  spinProjectionConcreteGammaEntryRules[
    {desc[[1]], desc[[2]], ({4, #} & /@ values), desc[[4]], None},
    {},
    {},
    {}
  ]
];

spinProjectionGammaKernelFactorRules::usage =
  "spinProjectionGammaKernelFactorRules[factor, vectorTuple, blockTuple] returns the local sparse spin-tuple rule list for one concrete factor instance.";
spinProjectionGammaKernelFactorRules[factor_Association, vectorTuple_List, blockTuple_List] := Module[{rules},
  rules = spinProjectionGammaKernelEntryRules[factor["Desc"], vectorTuple, blockTuple];
  If[rules === $Failed, Return[$Failed]];
  If[
    Length[factor["SpinSlots"]] === 1,
    Cases[rules, {{i_Integer, j_Integer}, value_} /; i === j :> {{i}, value}],
    Cases[rules, {{i_Integer, j_Integer}, value_} :> {{i, j}, value}]
  ]
];

spinProjectionGammaKernelFactorEntryValue::usage =
  "spinProjectionGammaKernelFactorEntryValue[factor, vectorTuple, blockTuple, spinTuple] returns one exact factor contribution for the requested local spin tuple.";
spinProjectionGammaKernelFactorLocalEntryValue::usage =
  "spinProjectionGammaKernelFactorLocalEntryValue[factor, vectorTuple, blockTuple, localSpinTuple] returns one exact factor contribution for a local one- or two-spin assignment.";
spinProjectionGammaKernelFactorLocalEntryValue[factor_Association, vectorTuple_List, blockTuple_List, localSpinTuple_List] := Module[
  {values, desc, localSpins = localSpinTuple},
  desc = factor["Desc"];
  values = spinProjectionGammaKernelVectorValue[#, vectorTuple, blockTuple] & /@ desc[[3]];
  If[!AllTrue[values, IntegerQ], Return[$Failed]];
  If[Length[localSpins] === 1,
    spinProjectionConcreteGammaEntryValue[
      {desc[[1]], desc[[2]], ({4, #} & /@ values), desc[[4]], None},
      {},
      {},
      {},
      localSpins[[1]],
      localSpins[[1]]
    ],
    spinProjectionConcreteGammaEntryValue[
      {desc[[1]], desc[[2]], ({4, #} & /@ values), desc[[4]], None},
      {},
      {},
      {},
      localSpins[[1]],
      localSpins[[2]]
    ]
  ]
];

spinProjectionGammaKernelFactorEntryValue[factor_Association, vectorTuple_List, blockTuple_List, spinTuple_List] :=
  spinProjectionGammaKernelFactorLocalEntryValue[factor, vectorTuple, blockTuple, spinTuple[[factor["SpinSlots"]]]];

spinProjectionGammaKernelDecodeSpinKey::usage =
  "spinProjectionGammaKernelDecodeSpinKey[key, slotCount] decodes one packed base-16 spin key back to a 1-based spin tuple.";
spinProjectionGammaKernelDecodeSpinKey[key_Integer?Positive, slotCount_Integer?NonNegative] := Module[
  {tuple = ConstantArray[1, slotCount], q = key - 1},
  Do[
    tuple[[pos]] = Mod[q, 16] + 1;
    q = Quotient[q, 16],
    {pos, 1, slotCount}
  ];
  tuple
];

spinProjectionGammaKernelEncodeSpinTuple::usage =
  "spinProjectionGammaKernelEncodeSpinTuple[tuple] packs a 1-based local spin tuple into the base-16 key used during kernel compilation.";
spinProjectionGammaKernelEncodeSpinTuple[tuple_List] := If[
  tuple === {},
  1,
  1 + Total[(tuple - 1) 16^Range[0, Length[tuple] - 1]]
];

spinProjectionGammaKernelProjectSpinKey::usage =
  "spinProjectionGammaKernelProjectSpinKey[key, positions] projects one packed base-16 spin key onto a compact key over the requested slot positions.";
spinProjectionGammaKernelProjectSpinKey[key_Integer?Positive, positions_List] := Module[{q = key - 1},
  If[
    positions === {},
    1,
    1 + Sum[Mod[Quotient[q, 16^(positions[[idx]] - 1)], 16] 16^(idx - 1), {idx, Length[positions]}]
  ]
];

spinProjectionGammaKernelPreparedRules::usage =
  "spinProjectionGammaKernelPreparedRules[joinPlan, ruleLists, slotCount] prepares one block assignment's factor rules for the iterative spin-slot join.";
spinProjectionGammaKernelPreparedRules[joinPlan_List, ruleLists_List, slotCount_Integer?NonNegative] := Module[
  {weights = 16^Range[0, slotCount - 1]},
  MapThread[
    Function[{step, rules},
      GroupBy[
        Map[
          Function[entry,
            spinProjectionGammaKernelEncodeSpinTuple[entry[[1, step["LocalCommonPos"]]]] -> {
              Total[(entry[[1, step["LocalExtraPos"]]] - 1) weights[[step["ExtraSlots"]]]],
              entry[[2]]
            }
          ],
          rules
        ],
        First -> Last
      ]
    ],
    {joinPlan, ruleLists}
  ]
];

spinProjectionGammaKernelJoinBlockRules::usage =
  "spinProjectionGammaKernelJoinBlockRules[joinPlan, ruleLists, slotCount] joins one concrete block assignment's factor rule lists into sparse packed spin-key rules.";
spinProjectionGammaKernelJoinBlockRules[joinPlan_List, ruleLists_List, slotCount_Integer?NonNegative] := Module[
  {preparedRules, entries = {1 -> 1}, step, entryGroups, commonKeys, rules},
  preparedRules = spinProjectionGammaKernelPreparedRules[joinPlan, ruleLists, slotCount];
  Do[
    step = joinPlan[[idx]];
    If[step["CommonCurrentPos"] === {},
      rules = spinProjectionAssociationLookup[preparedRules[[idx]], 1, {}];
      entries = If[
        entries === {} || rules === {},
        {},
        Thread[
          Flatten[Outer[Plus, entries[[All, 1]], rules[[All, 1]]], 1] ->
            Flatten[Outer[Times, entries[[All, 2]], rules[[All, 2]]], 1]
        ]
      ];
      Continue[];
    ];
    entryGroups = If[
      entries === {},
      <||>,
      GroupBy[entries, spinProjectionGammaKernelProjectSpinKey[First[#], step["CommonCurrentPos"]] &]
    ];
    commonKeys = Intersection[Keys[entryGroups], Keys[preparedRules[[idx]]]];
    entries = Replace[
      Last @ Reap[
        Do[
          Do[
            Sow[(entry[[1]] + rule[[1]]) -> entry[[2]] rule[[2]]],
            {entry, entryGroups[commonKey]},
            {rule, preparedRules[[idx]][commonKey]}
          ],
          {commonKey, commonKeys}
        ]
      ],
      {{} -> {}, {items_List} :> items}
    ],
    {idx, Length[preparedRules]}
  ];
  entries
];

spinProjectionCompileGammaKernelSlice::usage =
  "spinProjectionCompileGammaKernelSlice[kernel, vectorTuple] compiles one exact concrete vector slice of a registered gamma kernel.";
spinProjectionCompileGammaKernelSlice[kernel_Association, vectorTuple_List] := Module[{items, ruleLists, blockEntries},
  If[kernel["Factors"] === {}, Return[<|{} -> 1|>]];
  items = Catch[
    Replace[
      Last @ Reap[
        Do[
          ruleLists = spinProjectionGammaKernelFactorRules[#, vectorTuple, blockTuple] & /@ kernel["Factors"];
          If[MemberQ[ruleLists, $Failed], Throw[$Failed, "KernelFailure"]];
          blockEntries = spinProjectionGammaKernelJoinBlockRules[kernel["JoinPlan"], ruleLists, kernel["SpinSlotCount"]];
          Scan[Sow, blockEntries],
          {blockTuple, kernel["BlockTuples"]}
        ]
      ],
      {{} -> {}, {values_List} :> values}
    ],
    "KernelFailure"
  ];
  If[items === $Failed, Return[$Failed]];
  Select[
    Association @ KeyValueMap[
      spinProjectionGammaKernelDecodeSpinKey[#1, kernel["SpinSlotCount"]] -> #2 &,
      If[items === {}, <||>, Select[Merge[items, Total], # =!= 0 &]]
    ],
    # =!= 0 &
  ]
];

spinProjectionGammaKernelSlice::usage =
  "spinProjectionGammaKernelSlice[key, vectorTuple] returns the exact cached slice for one registered gamma kernel, compiling it on first use.";
spinProjectionGammaKernelSlice[key_, vectorTuple_List] := Module[{kernel, cache, slice},
  If[!KeyExistsQ[spinProjectionGammaKernelRegistry, key], Return[$Failed]];
  cache = spinProjectionAssociationLookup[spinProjectionGammaKernelSliceCache, key, <||>];
  If[KeyExistsQ[cache, vectorTuple], Return[cache[vectorTuple]]];
  kernel = spinProjectionGammaKernelRegistry[key];
  slice = spinProjectionCompileGammaKernelSlice[kernel, vectorTuple];
  If[slice === $Failed, Return[$Failed]];
  AssociateTo[cache, vectorTuple -> slice];
  AssociateTo[spinProjectionGammaKernelSliceCache, key -> cache];
  slice
];

spinProjectionGammaKernelEntryCache::usage =
  "spinProjectionGammaKernelEntryCache memoizes exact kernel entry values by structural key, concrete vector tuple, and concrete spin tuple.";
spinProjectionGammaKernelEntryCache = <||>;

spinProjectionGammaKernelFactorValueVectorCache::usage =
  "spinProjectionGammaKernelFactorValueVectorCache memoizes factor block-tuple value vectors by kernel key, factor index, concrete vector tuple, and local spin tuple.";
spinProjectionGammaKernelFactorValueVectorCache = <||>;

spinProjectionGammaKernelFactorMatrixVectorCache::usage =
  "spinProjectionGammaKernelFactorMatrixVectorCache memoizes concrete factor-matrix vectors over every global block tuple for paired shared-kernel compilation.";
spinProjectionGammaKernelFactorMatrixVectorCache = <||>;

spinProjectionGammaKernelFactorLocalValueTableCache::usage =
  "spinProjectionGammaKernelFactorLocalValueTableCache memoizes concrete local factor block-value tables after local dummy-block renumbering.";
spinProjectionGammaKernelFactorLocalValueTableCache = <||>;

spinProjectionGammaKernelFactorLocalMatrixTableCache::usage =
  "spinProjectionGammaKernelFactorLocalMatrixTableCache memoizes concrete local factor matrices over local dummy-block tuples.";
spinProjectionGammaKernelFactorLocalMatrixTableCache = <||>;

spinProjectionGammaKernelCanonicalFamilyRowOperatorCache::usage =
  "spinProjectionGammaKernelCanonicalFamilyRowOperatorCache memoizes canonical sparse row operators built directly from cached alternating gamma-product families.";
spinProjectionGammaKernelCanonicalFamilyRowOperatorCache = <||>;

spinProjectionGammaKernelLocalizedFactorRowOperatorCache::usage =
  "spinProjectionGammaKernelLocalizedFactorRowOperatorCache memoizes localized sparse row operators for concrete two-spinor gamma factors.";
spinProjectionGammaKernelLocalizedFactorRowOperatorCache = <||>;

spinProjectionGammaKernelFactorLocalizedKey::usage =
  "spinProjectionGammaKernelFactorLocalizedKey[factor, vectorTuple] returns a concrete local factor descriptor key independent of the surrounding kernel's global block numbering.";
spinProjectionGammaKernelFactorLocalizedKey[factor_Association, vectorTuple_List] := Module[
  {desc = factor["Desc"], blockMap, localizedSpecs},
  blockMap = AssociationThread[factor["Blocks"] -> Range[Length[factor["Blocks"]]]];
  localizedSpecs = Map[
    Switch[#[[1]],
      0, {2, vectorTuple[[#[[2]]]]},
      1, {1, blockMap[#[[2]]], #[[3]]},
      2, #,
      _, $Failed
    ] &,
    desc[[3]]
  ];
  If[MemberQ[localizedSpecs, $Failed], Return[$Failed]];
  {desc[[1]], desc[[2]], localizedSpecs, desc[[4]], factor["BlockSizes"]}
];

spinProjectionGammaKernelFactorLocalValueTable::usage =
  "spinProjectionGammaKernelFactorLocalValueTable[factor, vectorTuple, localSpinTuple] returns the cached factor values over local block tuples only.";
spinProjectionGammaKernelFactorLocalValueTable[factor_Association, vectorTuple_List, localSpinTuple_List] := Module[
  {factorKey, cache, spinCache, desc, localTuples, values},
  factorKey = spinProjectionGammaKernelFactorLocalizedKey[factor, vectorTuple];
  If[factorKey === $Failed, Return[$Failed]];
  cache = spinProjectionAssociationLookup[spinProjectionGammaKernelFactorLocalValueTableCache, factorKey, <||>];
  If[KeyExistsQ[cache, localSpinTuple], Return[cache[localSpinTuple]]];
  desc = factorKey[[;; 4]];
  localTuples = spinProjectionDisjointBlockBasisTuples[factor["BlockSizes"]];
  values = spinProjectionGammaKernelFactorLocalEntryValue[
      <|"Desc" -> desc, "SpinSlots" -> Range[Length[localSpinTuple]], "Blocks" -> Range[Length[factor["BlockSizes"]]], "BlockSizes" -> factor["BlockSizes"]|>,
      {},
      #,
      localSpinTuple
    ] & /@ localTuples;
  If[MemberQ[values, $Failed], Return[$Failed]];
  AssociateTo[cache, localSpinTuple -> values];
  AssociateTo[spinProjectionGammaKernelFactorLocalValueTableCache, factorKey -> cache];
  values
];

spinProjectionGammaKernelFactorValueVector::usage =
  "spinProjectionGammaKernelFactorValueVector[key, factorIndex, vectorTuple, localSpinTuple] returns the cached factor values over every global block tuple for one local spin assignment.";
spinProjectionGammaKernelFactorValueVector[key_, factorIndex_Integer?Positive, vectorTuple_List, localSpinTuple_List] := Module[
  {cache, vectorCache, spinCache, kernel, factor, localTable, localTuples, localIndex},
  cache = spinProjectionAssociationLookup[spinProjectionGammaKernelFactorValueVectorCache, key, <||>];
  vectorCache = spinProjectionAssociationLookup[cache, factorIndex, <||>];
  spinCache = spinProjectionAssociationLookup[vectorCache, vectorTuple, <||>];
  If[KeyExistsQ[spinCache, localSpinTuple], Return[spinCache[localSpinTuple]]];
  kernel = spinProjectionGammaKernelRegistry[key];
  factor = kernel["Factors"][[factorIndex]];
  localTable = spinProjectionGammaKernelFactorLocalValueTable[factor, vectorTuple, localSpinTuple];
  If[localTable === $Failed, Return[$Failed]];
  localTuples = spinProjectionDisjointBlockBasisTuples[factor["BlockSizes"]];
  localIndex = AssociationThread[localTuples -> Range[Length[localTuples]]];
  AssociateTo[
    spinCache,
    localSpinTuple -> localTable[[Lookup[localIndex, kernel["BlockTuples"][[All, factor["Blocks"]]]]]]
  ];
  AssociateTo[vectorCache, vectorTuple -> spinCache];
  AssociateTo[cache, factorIndex -> vectorCache];
  AssociateTo[spinProjectionGammaKernelFactorValueVectorCache, key -> cache];
  spinCache[localSpinTuple]
];

spinProjectionGammaKernelFactorLocalizedMatrix::usage =
  "spinProjectionGammaKernelFactorLocalizedMatrix[factorKey, localBlockTuple] returns the concrete sparse matrix for one localized factor on one local dummy-block tuple.";
spinProjectionGammaKernelFactorLocalizedMatrix[factorKey_List, localBlockTuple_List] := Module[
  {desc = factorKey[[;; 4]], values, links},
  values = spinProjectionGammaKernelVectorValue[#, {}, localBlockTuple] & /@ desc[[3]];
  If[!AllTrue[values, IntegerQ], Return[$Failed]];
  links = Join[
    If[desc[[1]] === None, {}, {desc[[1]]}],
    MapThread[
      If[#1 === 1, GammaUDHold[#2], GammaDUHold[#2]] &,
      {desc[[2]], values}
    ],
    desc[[4]]
  ];
  spinProjectionGammaFactorMatrix[links]
];

spinProjectionGammaKernelFactorLocalMatrixTable::usage =
  "spinProjectionGammaKernelFactorLocalMatrixTable[factor, vectorTuple] returns the cached concrete local factor matrices over local block tuples only.";
spinProjectionGammaKernelFactorLocalMatrixTable[factor_Association, vectorTuple_List] := Module[
  {factorKey, cache, localTuples, matrices},
  factorKey = spinProjectionGammaKernelFactorLocalizedKey[factor, vectorTuple];
  If[factorKey === $Failed, Return[$Failed]];
  cache = spinProjectionAssociationLookup[spinProjectionGammaKernelFactorLocalMatrixTableCache, factorKey, Missing["NotFound"]];
  If[cache =!= Missing["NotFound"], Return[cache]];
  localTuples = spinProjectionDisjointBlockBasisTuples[factor["BlockSizes"]];
  matrices = spinProjectionGammaKernelFactorLocalizedMatrix[factorKey, #] & /@ localTuples;
  If[MemberQ[matrices, $Failed], Return[$Failed]];
  AssociateTo[spinProjectionGammaKernelFactorLocalMatrixTableCache, factorKey -> matrices];
  matrices
];

spinProjectionGammaKernelStackSparseRows0::usage =
  "spinProjectionGammaKernelStackSparseRows0[rowVectors] stacks sparse row vectors of equal length into one sparse matrix without densifying them.";
spinProjectionGammaKernelStackSparseRows0[rowVectors_List] := Module[{rules, rowLength},
  If[rowVectors === {}, Return[SparseArray[{}, {0, 0}]]];
  rowLength = First[Dimensions[SparseArray[First[rowVectors]]]];
  rules = Flatten[
    MapIndexed[
      Function[{rowVector, idx},
        ({idx[[1]], #[[1, 1]]} -> #[[2]]) & /@ Most[ArrayRules[SparseArray[rowVector]]]
      ],
      rowVectors
    ],
    1
  ];
  SparseArray[rules, {Length[rowVectors], rowLength}]
];

spinProjectionGammaKernelFactorMatrixVector::usage =
  "spinProjectionGammaKernelFactorMatrixVector[key, factorIndex, vectorTuple] returns the cached factor matrices over every global block tuple for paired shared-kernel compilation.";
spinProjectionGammaKernelFactorMatrixVector[key_, factorIndex_Integer?Positive, vectorTuple_List] := Module[
  {cache, vectorCache, kernel, factor, localTable, localTuples, localIndex},
  cache = spinProjectionAssociationLookup[spinProjectionGammaKernelFactorMatrixVectorCache, key, <||>];
  vectorCache = spinProjectionAssociationLookup[cache, factorIndex, <||>];
  If[KeyExistsQ[vectorCache, vectorTuple], Return[vectorCache[vectorTuple]]];
  kernel = spinProjectionGammaKernelRegistry[key];
  factor = kernel["Factors"][[factorIndex]];
  localTable = spinProjectionGammaKernelFactorLocalMatrixTable[factor, vectorTuple];
  If[localTable === $Failed, Return[$Failed]];
  localTuples = spinProjectionDisjointBlockBasisTuples[factor["BlockSizes"]];
  localIndex = AssociationThread[localTuples -> Range[Length[localTuples]]];
  AssociateTo[
    vectorCache,
    vectorTuple -> localTable[[Lookup[localIndex, kernel["BlockTuples"][[All, factor["Blocks"]]]]]]
  ];
  AssociateTo[cache, factorIndex -> vectorCache];
  AssociateTo[spinProjectionGammaKernelFactorMatrixVectorCache, key -> cache];
  vectorCache[vectorTuple]
];

spinProjectionGammaKernelMatrixEntrySparseRow::usage =
  "spinProjectionGammaKernelMatrixEntrySparseRow[matrix] encodes one sparse factor matrix into the column-major boundary-entry basis without calling Normal.";
spinProjectionGammaKernelMatrixEntrySparseRow[matrix_] := Module[{rules, dim = gammaSpinorDimension},
  rules = Most[ArrayRules[SparseArray[matrix]]];
  SparseArray[
    ({#[[1, 1]] + dim (#[[1, 2]] - 1)} -> #[[2]]) & /@ rules,
    {dim^2}
  ]
];

spinProjectionGammaKernelCanonicalFamilyRankFromFactorKey0::usage =
  "spinProjectionGammaKernelCanonicalFamilyRankFromFactorKey0[factorKey] returns {family, rank, sign} when one localized factor key is a canonical single-block alternating gamma family, and $Failed otherwise.";
spinProjectionGammaKernelCanonicalFamilyRankFromFactorKey0[factorKey_List] := Module[
  {cTag, dirs, localizedSpecs, tailLinks, blockSizes, rank, positions, start, family},
  {cTag, dirs, localizedSpecs, tailLinks, blockSizes} = factorKey;
  rank = Length[dirs];
  If[tailLinks =!= {} || Length[blockSizes] =!= 1 || blockSizes[[1]] =!= rank, Return[$Failed]];
  If[!AllTrue[localizedSpecs, MatchQ[#, {1, 1, _Integer}] &], Return[$Failed]];
  positions = localizedSpecs[[All, 3]];
  If[Sort[positions] =!= Range[rank], Return[$Failed]];
  If[rank === 0, Return[$Failed]];
  start = First[dirs];
  If[dirs =!= Table[If[OddQ[pos], start, 3 - start], {pos, rank}], Return[$Failed]];
  family = {cTag, start};
  If[!MemberQ[gammaProductCacheFamilies, family], Return[$Failed]];
  {family, rank, If[rank > 1, Signature[positions], 1]}
];

spinProjectionGammaKernelCanonicalFamilyRowOperator0::usage =
  "spinProjectionGammaKernelCanonicalFamilyRowOperator0[family, rank] builds one sparse row operator directly from the cached canonical gamma-product family.";
spinProjectionGammaKernelCanonicalFamilyRowOperator0[family : {_, _Integer}, rank_Integer?NonNegative] := Module[
  {cacheKey = {family, rank}, cache, rows},
  cache = spinProjectionAssociationLookup[
    spinProjectionGammaKernelCanonicalFamilyRowOperatorCache,
    cacheKey,
    Missing["NotFound"]
  ];
  If[cache =!= Missing["NotFound"], Return[cache]];
  rows = spinProjectionGammaKernelMatrixEntrySparseRow[gammaCachedProductMatrix[family, #]] & /@
    Subsets[Range[gammaVectorDimension], {rank}];
  cache = spinProjectionGammaKernelStackSparseRows0[rows];
  spinProjectionGammaKernelCanonicalFamilyRowOperatorCache[cacheKey] = cache;
  cache
];

spinProjectionGammaKernelLocalizedFactorRowOperator0::usage =
  "spinProjectionGammaKernelLocalizedFactorRowOperator0[factorKey] returns the sparse local row operator for one localized two-spinor factor key.";
spinProjectionGammaKernelLocalizedFactorRowOperator0[factorKey_List] := Module[
  {cache, canonicalData, localTuples, rows},
  cache = spinProjectionAssociationLookup[
    spinProjectionGammaKernelLocalizedFactorRowOperatorCache,
    factorKey,
    Missing["NotFound"]
  ];
  If[cache =!= Missing["NotFound"], Return[cache]];
  canonicalData = spinProjectionGammaKernelCanonicalFamilyRankFromFactorKey0[factorKey];
  If[canonicalData =!= $Failed,
    cache = canonicalData[[3]] spinProjectionGammaKernelCanonicalFamilyRowOperator0[canonicalData[[1]], canonicalData[[2]]];
    spinProjectionGammaKernelLocalizedFactorRowOperatorCache[factorKey] = cache;
    Return[cache];
  ];
  localTuples = spinProjectionDisjointBlockBasisTuples[factorKey[[5]]];
  rows = spinProjectionGammaKernelMatrixEntrySparseRow[
      spinProjectionGammaKernelFactorLocalizedMatrix[factorKey, #]
    ] & /@ localTuples;
  If[MemberQ[rows, $Failed], Return[$Failed]];
  cache = spinProjectionGammaKernelStackSparseRows0[rows];
  spinProjectionGammaKernelLocalizedFactorRowOperatorCache[factorKey] = cache;
  cache
];

spinProjectionGammaKernelFactorRowOperator0::usage =
  "spinProjectionGammaKernelFactorRowOperator0[key, factorIndex, vectorTuple] returns the sparse row operator over global block tuples for one two-spinor factor.";
spinProjectionGammaKernelFactorRowOperator0[key_, factorIndex_Integer?Positive, vectorTuple_List] := Module[
  {kernel, factor, factorKey, localRows, localTuples, localIndex},
  If[!KeyExistsQ[spinProjectionGammaKernelRegistry, key], Return[$Failed]];
  kernel = spinProjectionGammaKernelRegistry[key];
  factor = kernel["Factors"][[factorIndex]];
  If[Length[factor["SpinSlots"]] =!= 2, Return[$Failed]];
  factorKey = spinProjectionGammaKernelFactorLocalizedKey[factor, vectorTuple];
  If[factorKey === $Failed, Return[$Failed]];
  localRows = spinProjectionGammaKernelLocalizedFactorRowOperator0[factorKey];
  If[localRows === $Failed, Return[$Failed]];
  localTuples = spinProjectionDisjointBlockBasisTuples[factor["BlockSizes"]];
  localIndex = AssociationThread[localTuples -> Range[Length[localTuples]]];
  localRows[[Lookup[localIndex, kernel["BlockTuples"][[All, factor["Blocks"]]]]]]
];

spinProjectionCompileGammaKernelEntry::usage =
  "spinProjectionCompileGammaKernelEntry[kernel, vectorTuple, spinTuple] computes one exact kernel entry directly without materializing the full external-spin slice.";
spinProjectionCompileGammaKernelEntry[key_, kernel_Association, vectorTuple_List, spinTuple_List] := Module[
  {factorVectors},
  If[kernel["Factors"] === {}, Return[If[spinTuple === {}, 1, 0]]];
  factorVectors = Table[
    spinProjectionGammaKernelFactorValueVector[key, factorIndex, vectorTuple, spinTuple[[kernel["Factors"][[factorIndex, "SpinSlots"]]]]],
    {factorIndex, Length[kernel["Factors"]]}
  ];
  If[MemberQ[factorVectors, $Failed], Return[$Failed]];
  Total[Times @@ factorVectors]
];

spinProjectionGammaKernelEntryValue::usage =
  "spinProjectionGammaKernelEntryValue[key, vectorTuple, spinTuple] returns the exact cached kernel entry for one registered gamma kernel.";
spinProjectionGammaKernelEntryValue[key_, vectorTuple_List, spinTuple_List] := Module[{kernelCache, spinCache, value, kernel, pairMatrix},
  If[!KeyExistsQ[spinProjectionGammaKernelRegistry, key], Return[$Failed]];
  kernelCache = spinProjectionAssociationLookup[spinProjectionGammaKernelEntryCache, key, <||>];
  spinCache = spinProjectionAssociationLookup[kernelCache, vectorTuple, <||>];
  If[KeyExistsQ[spinCache, spinTuple], Return[spinCache[spinTuple]]];
  kernel = spinProjectionGammaKernelRegistry[key];
  pairMatrix = spinProjectionGammaKernelPairMatrix[key, vectorTuple];
  value = If[
    pairMatrix === $Failed,
    spinProjectionCompileGammaKernelEntry[key, kernel, vectorTuple, spinTuple],
    pairMatrix[[
      spinProjectionGammaKernelEncodeSpinTuple[spinTuple[[kernel["Factors"][[1, "SpinSlots"]]]]],
      spinProjectionGammaKernelEncodeSpinTuple[spinTuple[[kernel["Factors"][[2, "SpinSlots"]]]]]
    ]]
  ];
  If[value === $Failed, Return[$Failed]];
  AssociateTo[spinCache, spinTuple -> value];
  AssociateTo[kernelCache, vectorTuple -> spinCache];
  AssociateTo[spinProjectionGammaKernelEntryCache, key -> kernelCache];
  value
];

spinProjectionGammaKernelLocalSpinTuples::usage =
  "spinProjectionGammaKernelLocalSpinTuples[arity] returns the ordered local spin tuples used to contract selector probes against one shared gamma kernel factor.";
spinProjectionGammaKernelLocalSpinTuples[0] := {{}};
spinProjectionGammaKernelLocalSpinTuples[arity_Integer?Positive] := spinProjectionGammaKernelLocalSpinTuples[arity] = Tuples[Range[16], arity];

spinProjectionGammaKernelFactorProbeVectorCache::usage =
  "spinProjectionGammaKernelFactorProbeVectorCache memoizes selector probe contractions of shared factor value vectors.";
spinProjectionGammaKernelFactorProbeVectorCache = <||>;

spinProjectionGammaKernelFactorProbeVector::usage =
  "spinProjectionGammaKernelFactorProbeVector[key, factorIndex, vectorTuple, localSpinVectors] contracts one shared factor against dense selector spin vectors and returns its value vector over global block tuples.";
spinProjectionGammaKernelFactorProbeVector[key_, factorIndex_Integer?Positive, vectorTuple_List, localSpinVectors_List] := Module[
  {cache, factorCache, vectorCache, kernel, factor, rowOperator, boundaryVector, tuples, result, tuple, weight, valueVector},
  cache = spinProjectionAssociationLookup[spinProjectionGammaKernelFactorProbeVectorCache, key, <||>];
  factorCache = spinProjectionAssociationLookup[cache, factorIndex, <||>];
  vectorCache = spinProjectionAssociationLookup[factorCache, vectorTuple, <||>];
  If[KeyExistsQ[vectorCache, localSpinVectors], Return[vectorCache[localSpinVectors]]];
  kernel = spinProjectionGammaKernelRegistry[key];
  factor = kernel["Factors"][[factorIndex]];
  If[Length[localSpinVectors] === 2,
    rowOperator = spinProjectionGammaKernelFactorRowOperator0[key, factorIndex, vectorTuple];
    If[rowOperator =!= $Failed,
      boundaryVector = spinProjectionGammaKernelBoundaryVector[localSpinVectors];
      If[!VectorQ[boundaryVector, spinProjectionSelectorExactScalarQ], Return[$Failed]];
      result = Normal[rowOperator . SparseArray[boundaryVector]];
      vectorCache[localSpinVectors] = result;
      factorCache[vectorTuple] = vectorCache;
      cache[factorIndex] = factorCache;
      spinProjectionGammaKernelFactorProbeVectorCache[key] = cache;
      Return[result];
    ];
  ];
  tuples = spinProjectionGammaKernelLocalSpinTuples[Length[localSpinVectors]];
  result = ConstantArray[0, Length[kernel["BlockTuples"]]];
  Do[
    weight = Times @@ Table[localSpinVectors[[pos, tuple[[pos]]]], {pos, Length[localSpinVectors]}];
    If[weight === 0, Continue[]];
    valueVector = spinProjectionGammaKernelFactorValueVector[key, factorIndex, vectorTuple, tuple];
    If[valueVector === $Failed, Return[$Failed]];
    result += weight valueVector,
    {tuple, tuples}
  ];
  vectorCache[localSpinVectors] = result;
  factorCache[vectorTuple] = vectorCache;
  cache[factorIndex] = factorCache;
  spinProjectionGammaKernelFactorProbeVectorCache[key] = cache;
  result
];

spinProjectionGammaKernelProbeCache::usage =
  "spinProjectionGammaKernelProbeCache memoizes dense selector probe contractions of shared gamma kernels by concrete exposed-vector tuple.";
spinProjectionGammaKernelProbeCache = <||>;

spinProjectionGammaKernelPairMatrixQ::usage =
  "spinProjectionGammaKernelPairMatrixQ[kernel] is True when one registered gamma kernel has the paired two-factor topology that should be cached as a shared K-matrix.";
spinProjectionGammaKernelPairMatrixQ[kernel_Association] := Module[{factors = kernel["Factors"]},
  Length[factors] == 2 &&
  AllTrue[factors, Length[#["SpinSlots"]] == 2 &] &&
  factors[[1, "Blocks"]] === factors[[2, "Blocks"]] &&
  DuplicateFreeQ[Join[factors[[1, "SpinSlots"]], factors[[2, "SpinSlots"]]]]
];

spinProjectionGammaKernelPairMatrixCache::usage =
  "spinProjectionGammaKernelPairMatrixCache memoizes shared paired-kernel matrices by structural key and concrete exposed-vector tuple.";
spinProjectionGammaKernelPairMatrixCache = <||>;

spinProjectionGammaKernelMatrixEntryVector::usage =
  "spinProjectionGammaKernelMatrixEntryVector[matrix] flattens a concrete factor matrix in the same {row,col} entry order used by spinProjectionGammaKernelEncodeSpinTuple[{row,col}].";
spinProjectionGammaKernelMatrixEntryVector[matrix_] := Normal[spinProjectionGammaKernelMatrixEntrySparseRow[matrix]];

spinProjectionCompileGammaKernelPairMatrixReferenceDense0::usage =
  "spinProjectionCompileGammaKernelPairMatrixReferenceDense0[key, kernel, vectorTuple] is the frozen dense reference implementation for paired gamma-kernel matrix compilation.";
spinProjectionCompileGammaKernelPairMatrixReferenceDense0[key_, kernel_Association, vectorTuple_List] := Module[
  {leftMatrices, rightMatrices},
  leftMatrices = spinProjectionGammaKernelFactorMatrixVector[key, 1, vectorTuple];
  rightMatrices = spinProjectionGammaKernelFactorMatrixVector[key, 2, vectorTuple];
  If[leftMatrices === $Failed || rightMatrices === $Failed, Return[$Failed]];
  Total @ MapThread[
    Outer[
      Times,
      spinProjectionGammaKernelMatrixEntryVector[#1],
      spinProjectionGammaKernelMatrixEntryVector[#2]
    ] &,
    {leftMatrices, rightMatrices}
  ]
];

spinProjectionCompileGammaKernelPairMatrixSparseOuter::usage =
  "spinProjectionCompileGammaKernelPairMatrixSparseOuter[left, right] builds one sparse outer-product contribution in the paired K-matrix entry basis.";
spinProjectionCompileGammaKernelPairMatrixSparseOuter[left_, right_] := Module[{leftRules, rightRules},
  leftRules = Most[ArrayRules[SparseArray[left]]];
  rightRules = Most[ArrayRules[SparseArray[right]]];
  SparseArray[
    Flatten[
      Table[
        {
          spinProjectionGammaKernelEncodeSpinTuple[leftEntry[[1]]],
          spinProjectionGammaKernelEncodeSpinTuple[rightEntry[[1]]]
        } -> leftEntry[[2]] rightEntry[[2]],
        {leftEntry, leftRules},
        {rightEntry, rightRules}
      ],
      1
    ],
    {256, 256}
  ]
];

spinProjectionCompileGammaKernelPairMatrix::usage =
  "spinProjectionCompileGammaKernelPairMatrix[key, kernel, vectorTuple] builds one shared paired K-matrix by summing sparse outer products of cached factor matrices over the antisymmetric dummy-index sum.";
spinProjectionCompileGammaKernelPairMatrix[key_, kernel_Association, vectorTuple_List] := Module[
  {leftRows, rightRows},
  leftRows = spinProjectionGammaKernelFactorRowOperator0[key, 1, vectorTuple];
  rightRows = spinProjectionGammaKernelFactorRowOperator0[key, 2, vectorTuple];
  If[leftRows === $Failed || rightRows === $Failed, Return[$Failed]];
  Normal[Transpose[leftRows] . rightRows]
];

spinProjectionGammaKernelPairMatrix::usage =
  "spinProjectionGammaKernelPairMatrix[key, vectorTuple] returns the cached paired K-matrix for one registered gamma kernel when that topology applies.";
spinProjectionGammaKernelPairMatrix[key_, vectorTuple_List] := Module[
  {kernelCache, kernel, matrix},
  If[!KeyExistsQ[spinProjectionGammaKernelRegistry, key], Return[$Failed]];
  kernelCache = spinProjectionAssociationLookup[spinProjectionGammaKernelPairMatrixCache, key, <||>];
  If[KeyExistsQ[kernelCache, vectorTuple], Return[kernelCache[vectorTuple]]];
  kernel = spinProjectionGammaKernelRegistry[key];
  If[!spinProjectionGammaKernelPairMatrixQ[kernel], Return[$Failed]];
  matrix = spinProjectionCompileGammaKernelPairMatrix[key, kernel, vectorTuple];
  If[matrix === $Failed, Return[$Failed]];
  kernelCache[vectorTuple] = matrix;
  spinProjectionGammaKernelPairMatrixCache[key] = kernelCache;
  markPersistentGammaKernelCacheDirty0[];
  matrix
];

spinProjectionGammaKernelBoundaryVector::usage =
  "spinProjectionGammaKernelBoundaryVector[spinVectors] flattens one ordered list of boundary spin vectors into the dense entry-order basis used by paired K-matrix contractions.";
spinProjectionGammaKernelBoundaryVector[{vec_}] := vec;
spinProjectionGammaKernelBoundaryVector[{left_, right_}] := Flatten[Transpose[Outer[Times, left, right]]];
spinProjectionGammaKernelBoundaryVector[spinVectors_List] := Flatten[KroneckerProduct @@ spinVectors];

spinProjectionGammaKernelSelectorPairValues0::usage =
  "spinProjectionGammaKernelSelectorPairValues0[key, vectorTuple, leftBoundaryRows, rightBoundaryRows] evaluates one selector batch directly against the cached paired K-matrix without probe-cache bookkeeping.";
spinProjectionGammaKernelSelectorPairValues0[key_, vectorTuple_List, leftBoundaryRows_List, rightBoundaryRows_List] := Module[{pairMatrix},
  If[leftBoundaryRows === {} || rightBoundaryRows === {}, Return[{}]];
  pairMatrix = spinProjectionGammaKernelPairMatrix[key, vectorTuple];
  If[pairMatrix === $Failed, Return[$Failed]];
  Diagonal[SparseArray[leftBoundaryRows] . pairMatrix . Transpose[SparseArray[rightBoundaryRows]]]
];

spinProjectionGammaKernelSelectorSingleFactorValues0::usage =
  "spinProjectionGammaKernelSelectorSingleFactorValues0[key, vectorTuple, boundaryRows] evaluates one selector batch directly against the cached two-spinor factor row operator without probe-cache bookkeeping.";
spinProjectionGammaKernelSelectorSingleFactorValues0[key_, vectorTuple_List, boundaryRows_List] := Module[{rowOperator, values},
  If[boundaryRows === {}, Return[{}]];
  rowOperator = spinProjectionGammaKernelFactorRowOperator0[key, 1, vectorTuple];
  If[rowOperator === $Failed, Return[$Failed]];
  values = Total[rowOperator . Transpose[SparseArray[boundaryRows]], {1}];
  If[Head[values] === SparseArray, Normal[values], values]
];

spinProjectionGammaKernelProbeValuesBatch0::usage =
  "spinProjectionGammaKernelProbeValuesBatch0[key, vectorTuple, spinVectorsBatch] contracts one shared gamma kernel against a batch of dense selector spin-vector assignments, caching the scalar results entrywise.";
spinProjectionGammaKernelProbeValuesBatch0[key_, vectorTuple_List, spinVectorsBatch_List] := Module[
  {
    kernelCache,
    spinCache,
    kernel,
    values,
    missingPositions,
    missingBatch,
    pairMatrix,
    leftBoundaryVectors,
    rightBoundaryVectors,
    batchValues,
    idx
  },
  If[spinVectorsBatch === {}, Return[{}]];
  If[!KeyExistsQ[spinProjectionGammaKernelRegistry, key], Return[$Failed]];
  kernelCache = spinProjectionAssociationLookup[spinProjectionGammaKernelProbeCache, key, <||>];
  spinCache = spinProjectionAssociationLookup[kernelCache, vectorTuple, <||>];
  values = Table[
    If[KeyExistsQ[spinCache, spinVectorsBatch[[i]]], spinCache[spinVectorsBatch[[i]]], Missing["NotCached"]],
    {i, Length[spinVectorsBatch]}
  ];
  missingPositions = Flatten[Position[values, Missing["NotCached"], {1}, Heads -> False]];
  If[missingPositions === {}, Return[values]];
  kernel = spinProjectionGammaKernelRegistry[key];
  missingBatch = spinVectorsBatch[[missingPositions]];
  If[
    !AllTrue[missingBatch, ListQ] ||
    !AllTrue[missingBatch, Length[#] == kernel["SpinSlotCount"] &],
    Return[$Failed]
  ];
  pairMatrix = spinProjectionGammaKernelPairMatrix[key, vectorTuple];
  If[pairMatrix === $Failed || Length[kernel["Factors"]] =!= 2,
    Do[
      values[[idx]] = spinProjectionGammaKernelProbeValue[key, vectorTuple, spinVectorsBatch[[idx]]];
      If[values[[idx]] === $Failed, Return[$Failed]],
      {idx, missingPositions}
    ];
    Return[values];
  ];
  leftBoundaryVectors = spinProjectionGammaKernelBoundaryVector /@ Map[
    Part[#, kernel["Factors"][[1, "SpinSlots"]]] &,
    missingBatch
  ];
  rightBoundaryVectors = spinProjectionGammaKernelBoundaryVector /@ Map[
    Part[#, kernel["Factors"][[2, "SpinSlots"]]] &,
    missingBatch
  ];
  If[
    !AllTrue[leftBoundaryVectors, VectorQ[#, spinProjectionSelectorExactScalarQ] &] ||
    !AllTrue[rightBoundaryVectors, VectorQ[#, spinProjectionSelectorExactScalarQ] &],
    Return[$Failed]
  ];
  batchValues = Diagonal[SparseArray[leftBoundaryVectors] . pairMatrix . Transpose[SparseArray[rightBoundaryVectors]]];
  Do[
    values[[missingPositions[[j]]]] = batchValues[[j]];
    spinCache[spinVectorsBatch[[missingPositions[[j]]]]] = batchValues[[j]],
    {j, Length[missingPositions]}
  ];
  kernelCache[vectorTuple] = spinCache;
  spinProjectionGammaKernelProbeCache[key] = kernelCache;
  values
];

spinProjectionGammaKernelProbeValue::usage =
  "spinProjectionGammaKernelProbeValue[key, vectorTuple, spinVectors] contracts one shared gamma kernel against dense selector spin vectors.";
spinProjectionGammaKernelProbeValue[key_, vectorTuple_List, spinVectors_List] := Module[
  {kernelCache, spinCache, kernel, factorVectors, value, pairMatrix},
  If[!KeyExistsQ[spinProjectionGammaKernelRegistry, key], Return[$Failed]];
  kernelCache = spinProjectionAssociationLookup[spinProjectionGammaKernelProbeCache, key, <||>];
  spinCache = spinProjectionAssociationLookup[kernelCache, vectorTuple, <||>];
  If[KeyExistsQ[spinCache, spinVectors], Return[spinCache[spinVectors]]];
  kernel = spinProjectionGammaKernelRegistry[key];
  If[Length[spinVectors] =!= kernel["SpinSlotCount"], Return[$Failed]];
  If[kernel["Factors"] === {}, Return[1]];
  pairMatrix = spinProjectionGammaKernelPairMatrix[key, vectorTuple];
  value = If[
    pairMatrix === $Failed,
    factorVectors = Table[
      spinProjectionGammaKernelFactorProbeVector[
        key,
        factorIndex,
        vectorTuple,
        spinVectors[[kernel["Factors"][[factorIndex, "SpinSlots"]]]]
      ],
      {factorIndex, Length[kernel["Factors"]]}
    ];
    If[MemberQ[factorVectors, $Failed], Return[$Failed]];
    Total[Times @@ factorVectors],
    spinProjectionGammaKernelBoundaryVector[spinVectors[[kernel["Factors"][[1, "SpinSlots"]]]]] .
      pairMatrix .
      spinProjectionGammaKernelBoundaryVector[spinVectors[[kernel["Factors"][[2, "SpinSlots"]]]]]
  ];
  spinCache[spinVectors] = value;
  kernelCache[vectorTuple] = spinCache;
  spinProjectionGammaKernelProbeCache[key] = kernelCache;
  value
];

spinProjectionAllBasisSubsets::usage =
  "spinProjectionAllBasisSubsets[rank] returns all increasing basis subsets of Range[10] with the requested rank.";
spinProjectionAllBasisSubsets[0] := {{}};
spinProjectionAllBasisSubsets[rank_Integer?Positive] := spinProjectionAllBasisSubsets[rank] = Subsets[Range[10], {rank}];

spinProjectionOrderedAssociationRules::usage =
  "spinProjectionOrderedAssociationRules[assoc] returns deterministic association rules sorted by key.";
spinProjectionOrderedAssociationRules[assoc_Association] := SortBy[Normal[assoc], First];

spinProjectionSelectorProbeKey::usage =
  "spinProjectionSelectorProbeKey[probe] builds the deterministic cache key for one exact selector probe.";
spinProjectionSelectorProbeKey[probe_Association] := {
  spinProjectionOrderedAssociationRules[Lookup[probe, "SpinorComponents", <||>]],
  spinProjectionOrderedAssociationRules[Lookup[probe, "VectorComponents", <||>]]
};

spinProjectionSelectorGammaFactorMatrixAssociationCache::usage =
  "spinProjectionSelectorGammaFactorMatrixAssociationCache memoizes exact basis-subset matrix associations for parsed selector gamma factors.";
spinProjectionSelectorGammaFactorMatrixAssociationCache = <||>;

spinProjectionSelectorGammaFactorMatrixAssociationKey::usage =
  "spinProjectionSelectorGammaFactorMatrixAssociationKey[parts] returns the structural key for one parsed selector gamma factor.";
spinProjectionSelectorGammaFactorMatrixAssociationKey[parts_Association] := {
  parts["CTag"],
  Head /@ parts["VectorLinks"],
  parts["TailLinks"]
};

spinProjectionSelectorGammaFactorLinks::usage =
  "spinProjectionSelectorGammaFactorLinks[parts, subset] instantiates one parsed selector gamma factor on a concrete increasing basis subset.";
spinProjectionSelectorGammaFactorLinks[parts_Association, subset_List] := Join[
  If[parts["CTag"] === None, {}, {parts["CTag"]}],
  MapThread[
    If[Head[#1] === GammaUDHold, GammaUDHold[#2], GammaDUHold[#2]] &,
    {parts["VectorLinks"], subset}
  ],
  parts["TailLinks"]
];

spinProjectionSelectorGammaFactorMatrixAssociation::usage =
  "spinProjectionSelectorGammaFactorMatrixAssociation[parts] returns the exact basis-subset matrix table for one parsed selector gamma factor.";
spinProjectionSelectorGammaFactorMatrixAssociation[parts_Association] := Module[{key, cached, subsets, assoc},
  key = spinProjectionSelectorGammaFactorMatrixAssociationKey[parts];
  cached = spinProjectionAssociationLookup[spinProjectionSelectorGammaFactorMatrixAssociationCache, key, Missing["NotFound"]];
  If[cached =!= Missing["NotFound"], Return[cached]];
  subsets = spinProjectionAllBasisSubsets[Length[parts["VectorLinks"]]];
  assoc = Association @ Table[
    subset -> spinProjectionGammaFactorMatrix[spinProjectionSelectorGammaFactorLinks[parts, subset]],
    {subset, subsets}
  ];
  If[MemberQ[Values[assoc], $Failed], Return[$Failed]];
  AssociateTo[spinProjectionSelectorGammaFactorMatrixAssociationCache, key -> assoc];
  assoc
];

spinProjectionSelectorGammaFactorCoefficientAssociationCache::usage =
  "spinProjectionSelectorGammaFactorCoefficientAssociationCache memoizes exact alternating-form coefficients for parsed selector gamma factors.";
spinProjectionSelectorGammaFactorCoefficientAssociationCache = <||>;

spinProjectionSelectorExactScalarQ::usage =
  "spinProjectionSelectorExactScalarQ[value] is True for exact numeric selector-probe components, including Gaussian integers.";
spinProjectionSelectorExactScalarQ[value_] := NumericQ[value] && FreeQ[Unevaluated[value], _Real];

spinProjectionSelectorGammaFactorCoefficientAssociationKey::usage =
  "spinProjectionSelectorGammaFactorCoefficientAssociationKey[parts, spin1, spin2] builds the cache key for one parsed selector gamma factor and probe spinor pair.";
spinProjectionSelectorGammaFactorCoefficientAssociationKey[parts_Association, spin1_List, spin2_List] := {
  spinProjectionSelectorGammaFactorMatrixAssociationKey[parts],
  spin1,
  spin2
};

spinProjectionSelectorGammaFactorMatrixCoefficientAssociation::usage =
  "spinProjectionSelectorGammaFactorMatrixCoefficientAssociation[matrixAssoc, spin1, spin2] contracts one exact basis-subset gamma-matrix table with a dense probe spinor pair.";
spinProjectionSelectorGammaFactorMatrixCoefficientAssociation[matrixAssoc_Association, spin1_List, spin2_List] := Association @ Select[
  KeyValueMap[#1 -> (spin1 . #2 . spin2) &, matrixAssoc],
  Last[#] =!= 0 &
];

spinProjectionSelectorGammaFactorCoefficientAssociation::usage =
  "spinProjectionSelectorGammaFactorCoefficientAssociation[parts, probe] returns exact alternating-form coefficients for one parsed selector gamma factor under a dense probe.";
spinProjectionSelectorGammaFactorCoefficientAssociation[parts_Association, probe_Association] := Module[
  {spin1, spin2, key, cached, matrixAssoc},
  spin1 = Lookup[Lookup[probe, "SpinorComponents", <||>], parts["Spinors"][[1]], Missing["Unassigned"]];
  spin2 = Lookup[Lookup[probe, "SpinorComponents", <||>], parts["Spinors"][[2]], Missing["Unassigned"]];
  If[!VectorQ[spin1, spinProjectionSelectorExactScalarQ] || !VectorQ[spin2, spinProjectionSelectorExactScalarQ], Return[$Failed]];
  key = spinProjectionSelectorGammaFactorCoefficientAssociationKey[parts, spin1, spin2];
  cached = spinProjectionAssociationLookup[spinProjectionSelectorGammaFactorCoefficientAssociationCache, key, Missing["NotFound"]];
  If[cached =!= Missing["NotFound"], Return[cached]];
  matrixAssoc = spinProjectionSelectorGammaFactorMatrixAssociation[parts];
  If[matrixAssoc === $Failed, Return[$Failed]];
  cached = spinProjectionSelectorGammaFactorMatrixCoefficientAssociation[matrixAssoc, spin1, spin2];
  AssociateTo[spinProjectionSelectorGammaFactorCoefficientAssociationCache, key -> cached];
  cached
];

spinProjectionSelectorDeltaFactorValue::usage =
  "spinProjectionSelectorDeltaFactorValue[parts, probe] evaluates one parsed selector delta factor at an exact dense probe.";
spinProjectionSelectorDeltaFactorValue[parts_Association, probe_Association] := Module[{vec1, vec2},
  vec1 = Lookup[Lookup[probe, "VectorComponents", <||>], parts["VectorSymbols"][[1]], Missing["Unassigned"]];
  vec2 = Lookup[Lookup[probe, "VectorComponents", <||>], parts["VectorSymbols"][[2]], Missing["Unassigned"]];
  If[!VectorQ[vec1, spinProjectionSelectorExactScalarQ] || !VectorQ[vec2, spinProjectionSelectorExactScalarQ], Return[$Failed]];
  vec1 . vec2
];

spinProjectionSelectorFormCoefficientValue::usage =
  "spinProjectionSelectorFormCoefficientValue[coefficients, tuple] evaluates one exact alternating-form coefficient table on an ordered basis tuple.";
spinProjectionSelectorFormCoefficientValue[coefficients_Association, tuple_List] := Module[{sorted},
  If[!DuplicateFreeQ[tuple], Return[0]];
  sorted = Sort[tuple];
  Signature[tuple] spinProjectionAssociationLookup[coefficients, sorted, 0]
];

spinProjectionSelectorApplyExternalVectorToCoefficients::usage =
  "spinProjectionSelectorApplyExternalVectorToCoefficients[coefficients, rank, pos, vector] plugs one exact external vector into an alternating-form coefficient table.";
spinProjectionSelectorApplyExternalVectorToCoefficients[coefficients_Association, rank_Integer?Positive, pos_Integer?Positive, vector_List] := Association @ Select[
  Table[
    subset -> Sum[
      vector[[basisIndex]] spinProjectionSelectorFormCoefficientValue[coefficients, Insert[subset, basisIndex, pos]],
      {basisIndex, 1, 10}
    ],
    {subset, spinProjectionAllBasisSubsets[rank - 1]}
  ],
  Last[#] =!= 0 &
];

spinProjectionSelectorReduceFactorCoefficientsByExternalVectors::usage =
  "spinProjectionSelectorReduceFactorCoefficientsByExternalVectors[coefficients, vectorSymbols, probe] plugs all exact external vectors into one alternating-form coefficient table.";
spinProjectionSelectorReduceFactorCoefficientsByExternalVectors[coefficients_Association, vectorSymbols_List, probe_Association] := Module[
  {positions, reduced = coefficients, remainingSymbols = vectorSymbols, pos, symbol},
  positions = Reverse @ Select[
    Range[Length[vectorSymbols]],
    KeyExistsQ[Lookup[probe, "VectorComponents", <||>], vectorSymbols[[#]]] &
  ];
  Do[
    pos = positions[[i]];
    symbol = remainingSymbols[[pos]];
    reduced = spinProjectionSelectorApplyExternalVectorToCoefficients[
      reduced,
      Length[remainingSymbols],
      pos,
      probe["VectorComponents"][symbol]
    ];
    remainingSymbols = Delete[remainingSymbols, pos],
    {i, Length[positions]}
  ];
  <|"Coefficients" -> reduced, "DummySymbols" -> remainingSymbols|>
];

spinProjectionSelectorDummyVectorSymbolQ::usage =
  "spinProjectionSelectorDummyVectorSymbolQ[sym] is True when sym is either a generated dummy vector symbol from tensor generation or a canonical selector dummy placeholder.";
spinProjectionSelectorDummyVectorSymbolQ[sym_Symbol] := generatedDummyVectorSymbolQ[sym] || StringStartsQ[SymbolName[Unevaluated[sym]], "selectorDummy"];
spinProjectionSelectorDummyVectorSymbolQ[_] := False;

spinProjectionSelectorFamilyCompileCache::usage =
  "spinProjectionSelectorFamilyCompileCache memoizes canonical selector families compiled onto the shared gamma-kernel registry.";
spinProjectionSelectorFamilyCompileCache = <||>;

spinProjectionSelectorVectorSource::usage =
  "spinProjectionSelectorVectorSource[sym, externalSlots, dummySlots] maps one selector vector symbol to a shared gamma-kernel source descriptor.";
spinProjectionSelectorVectorSource[sym_Integer, _Association, _Association] := {4, sym};
spinProjectionSelectorVectorSource[sym_Symbol, externalSlots_Association, dummySlots_Association] := Which[
  KeyExistsQ[externalSlots, sym], {1, externalSlots[sym]},
  KeyExistsQ[dummySlots, sym], {3, dummySlots[sym]},
  True, $Failed
];
spinProjectionSelectorVectorSource[_, _Association, _Association] := $Failed;

spinProjectionSelectorMatrixDesc::usage =
  "spinProjectionSelectorMatrixDesc[parts, externalSlots, dummySlots] converts one parsed selector gamma factor into the shared exact gamma descriptor used by both selector families and compiled RHS terms.";
spinProjectionSelectorMatrixDesc[parts_Association, externalSlots_Association, dummySlots_Association] := Module[
  {sources, links},
  sources = spinProjectionSelectorVectorSource[#, externalSlots, dummySlots] & /@ parts["VectorSymbols"];
  If[MemberQ[sources, $Failed], Return[$Failed]];
  If[AllTrue[sources, First[#] === 4 &],
    links = Join[
      If[parts["CTag"] === None, {}, {parts["CTag"]}],
      MapThread[If[Head[#1] === GammaUDHold, GammaUDHold[#2[[2]]], GammaDUHold[#2[[2]]]] &, {parts["VectorLinks"], sources}],
      parts["TailLinks"]
    ];
    Return[
      {
        parts["CTag"],
        Replace[Head /@ parts["VectorLinks"], {GammaUDHold -> 1, GammaDUHold -> 2}, 1],
        sources,
        parts["TailLinks"],
        spinProjectionGammaFactorMatrix[links]
      }
    ]
  ];
  {
    parts["CTag"],
    Replace[Head /@ parts["VectorLinks"], {GammaUDHold -> 1, GammaDUHold -> 2}, 1],
    sources,
    parts["TailLinks"],
    None
  }
];

spinProjectionSelectorCompiledFamilyData::usage =
  "spinProjectionSelectorCompiledFamilyData[candidate] compiles one canonical parsed selector family onto the shared gamma-kernel registry.";
spinProjectionSelectorCompiledFamilyData[candidate_Association] := Module[
  {
    cached,
    spinSymbols,
    vectorSymbols,
    dummySymbols,
    spinSlots,
    externalSlots,
    dummySlots,
    gammaParts = {},
    deltaFactors = {},
    part,
    sources,
    matrix,
    kernelData
  },
  cached = spinProjectionAssociationLookup[spinProjectionSelectorFamilyCompileCache, candidate["Key"], Missing["NotFound"]];
  If[cached =!= Missing["NotFound"], Return[cached]];
  spinSymbols = SortBy[Keys[candidate["SpinorChiralities"]], SymbolName];
  vectorSymbols = SortBy[Lookup[candidate, "ExternalVectors", {}], SymbolName];
  dummySymbols = SortBy[
    DeleteDuplicates @ Select[
      Flatten[Lookup[candidate["FactorParts"], "VectorSymbols", {}], 1],
      spinProjectionSelectorDummyVectorSymbolQ
    ],
    SymbolName
  ];
  spinSlots = AssociationThread[spinSymbols -> Range[Length[spinSymbols]]];
  externalSlots = AssociationThread[vectorSymbols -> Range[Length[vectorSymbols]]];
  dummySlots = AssociationThread[dummySymbols -> Range[Length[dummySymbols]]];
  Do[
    part = candidate["FactorParts"][[i]];
    Switch[part["Kind"],
      "Delta",
      sources = spinProjectionSelectorVectorSource[#, externalSlots, dummySlots] & /@ part["VectorSymbols"];
      If[MemberQ[sources, $Failed] || AnyTrue[sources, First[#] === 3 &], Return[$Failed]];
      AppendTo[deltaFactors, sources],
      "Gamma",
      matrix = spinProjectionSelectorMatrixDesc[part, externalSlots, dummySlots];
      If[matrix === $Failed, Return[$Failed]];
      AppendTo[
        gammaParts,
        {
          2,
          {1, spinSlots[part["Spinors"][[1]]]},
          {1, spinSlots[part["Spinors"][[2]]]},
          matrix
        }
      ],
      _,
      Return[$Failed]
    ],
    {i, Length[candidate["FactorParts"]]}
  ];
  kernelData = spinProjectionGammaKernelData[gammaParts];
  If[kernelData === $Failed, Return[$Failed]];
  cached = <|
    "Parsed" -> candidate,
    "SpinSymbols" -> spinSymbols,
    "VectorSymbols" -> vectorSymbols,
    "DeltaFactors" -> deltaFactors,
    "GammaKernelRefs" -> kernelData["KernelRefs"],
    "ScalarFactor" -> kernelData["ScalarFactor"],
    "Mode" -> If[
      vectorSymbols === {} &&
      AllTrue[
        kernelData["KernelRefs"],
        Function[ref,
          Module[{kernel = spinProjectionGammaKernelRegistry[ref["Key"]]},
            spinProjectionGammaKernelPairMatrixQ[kernel] || Length[kernel["Factors"]] <= 1
          ]
        ]
      ],
      "sharedKernel",
      "blockTensor"
    ]
  |>;
  AssociateTo[spinProjectionSelectorFamilyCompileCache, candidate["Key"] -> cached];
  cached
];

StringCode`FlushKernelCache[] := flushPersistentGammaKernelCache0[];
loadPersistentGammaKernelCache0[];

spinProjectionSelectorFamilyVectorSourceValue::usage =
  "spinProjectionSelectorFamilyVectorSourceValue[src, vectorTuple] resolves one canonical selector family vector source under a concrete exposed-vector assignment.";
spinProjectionSelectorFamilyVectorSourceValue[src_, vectorTuple_List] := Switch[src[[1]],
  1, vectorTuple[[src[[2]]]],
  4, src[[2]],
  _, $Failed
];

spinProjectionSelectorProbeSpinVectors::usage =
  "spinProjectionSelectorProbeSpinVectors[spinSources, spinSymbols, probe] returns the dense selector spin vectors aligned to one shared kernel ref.";
spinProjectionSelectorProbeSpinVectors[spinSources_List, spinSymbols_List, probe_Association] := Module[{vectors},
  vectors = Map[
    Function[src,
      Switch[src[[1]],
        1, Lookup[Lookup[probe, "SpinorComponents", <||>], spinSymbols[[src[[2]]]], Missing["Unassigned"]],
        _, Missing["Unsupported"]
      ]
    ],
    spinSources
  ];
  If[
    AnyTrue[vectors, MatchQ[#, Missing[__]] &] || !AllTrue[vectors, VectorQ[#, spinProjectionSelectorExactScalarQ] &],
    $Failed,
    vectors
  ]
];

spinProjectionSelectorExternalVectorAssignments::usage =
  "spinProjectionSelectorExternalVectorAssignments[vectorCount] returns the concrete exposed-vector assignments summed over in canonical selector family evaluation.";
spinProjectionSelectorExternalVectorAssignments[0] := {{}};
spinProjectionSelectorExternalVectorAssignments[vectorCount_Integer?Positive] := Tuples[Range[10], vectorCount];

spinProjectionSelectorExternalVectorWeight::usage =
  "spinProjectionSelectorExternalVectorWeight[compiled, vectorTuple, probe] returns the exact dense selector weight for one concrete exposed-vector assignment, including delta constraints.";
spinProjectionSelectorExternalVectorWeight[compiled_Association, vectorTuple_List, probe_Association] := Module[
  {vectorComponents, weight, left, right},
  vectorComponents = Lookup[Lookup[probe, "VectorComponents", <||>], compiled["VectorSymbols"], Missing["Unassigned"]];
  If[AnyTrue[vectorComponents, # === Missing["Unassigned"] &] || !AllTrue[vectorComponents, VectorQ[#, spinProjectionSelectorExactScalarQ] &], Return[$Failed]];
  weight = If[vectorTuple === {}, 1, Times @@ MapThread[#1[[#2]] &, {vectorComponents, vectorTuple}]];
  Do[
    left = spinProjectionSelectorFamilyVectorSourceValue[delta[[1]], vectorTuple];
    right = spinProjectionSelectorFamilyVectorSourceValue[delta[[2]], vectorTuple];
    If[!IntegerQ[left] || !IntegerQ[right], Return[$Failed]];
    If[left =!= right, Return[0]],
    {delta, compiled["DeltaFactors"]}
  ];
  weight
];

spinProjectionSelectorCompiledFamilyValue::usage =
  "spinProjectionSelectorCompiledFamilyValue[compiled, probe] evaluates one canonical selector family by contracting dense probes against the shared gamma-kernel cache.";
spinProjectionSelectorCompiledFamilyValue[compiled_Association, probe_Association] := Module[
  {spinVectors, vectorAssignments, total = 0, weight, kernelValue, localTuple},
  If[compiled["ScalarFactor"] === 0, Return[0]];
  If[compiled["Mode"] === "blockTensor", Return[compiled["ScalarFactor"] spinProjectionSelectorBlockTensorCandidateValue[compiled["Parsed"], probe]]];
  spinVectors = spinProjectionSelectorProbeSpinVectors[#, compiled["SpinSymbols"], probe] & /@ compiled["GammaKernelRefs"][[All, "SpinSlots"]];
  If[MemberQ[spinVectors, $Failed], Return[$Failed]];
  vectorAssignments = spinProjectionSelectorExternalVectorAssignments[Length[compiled["VectorSymbols"]]];
  Do[
    weight = spinProjectionSelectorExternalVectorWeight[compiled, vectorTuple, probe];
    If[weight === $Failed, Return[$Failed]];
    If[weight === 0, Continue[]];
    kernelValue = Times @@ Table[
      localTuple = spinProjectionSelectorFamilyVectorSourceValue[#, vectorTuple] & /@ compiled["GammaKernelRefs"][[idx, "VectorSlots"]];
      If[!AllTrue[localTuple, IntegerQ], Return[$Failed]];
      spinProjectionGammaKernelProbeValue[compiled["GammaKernelRefs"][[idx, "Key"]], localTuple, spinVectors[[idx]]],
      {idx, Length[compiled["GammaKernelRefs"]]}
    ];
    If[kernelValue === $Failed, Return[$Failed]];
    total += weight kernelValue,
    {vectorTuple, vectorAssignments}
  ];
  compiled["ScalarFactor"] total
];

spinProjectionSelectorDummySymbolLocations::usage =
  "spinProjectionSelectorDummySymbolLocations[candidate] returns the factor/position incidence list for every generated dummy vector symbol in one parsed selector candidate.";
spinProjectionSelectorDummySymbolLocations[candidate_Association] := Module[{rules},
  rules = Replace[
    Last @ Reap[
      Do[
        With[{part = candidate["FactorParts"][[i]]},
          Do[
            If[
              spinProjectionSelectorDummyVectorSymbolQ[part["VectorSymbols"][[j]]],
              Sow[part["VectorSymbols"][[j]] -> {i, j}]
            ],
            {j, Length[part["VectorSymbols"]]}
          ]
        ],
        {i, Length[candidate["FactorParts"]]}
      ]
    ],
    {{} -> {}, {items_List} :> items}
  ];
  rules = If[rules === {}, <||>, Merge[rules, Identity]];
  If[AllTrue[Values[rules], Length[#] == 2 &], rules, $Failed]
];

spinProjectionSelectorFactorDummyBlocks::usage =
  "spinProjectionSelectorFactorDummyBlocks[parts, factorIndex, dummyLocations] partitions one parsed selector factor's dummy vector symbols into shared partner blocks.";
spinProjectionSelectorFactorDummyBlocks[parts_Association, factorIndex_Integer?Positive, dummyLocations_Association] := Module[
  {dummySymbols, currentPartner = None, currentBlock = {}, blocks = {}, locations, partners, partner},
  dummySymbols = Select[parts["VectorSymbols"], spinProjectionSelectorDummyVectorSymbolQ];
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

spinProjectionSelectorCandidateStructureCache::usage =
  "spinProjectionSelectorCandidateStructureCache memoizes dummy-symbol incidence and factor dummy blocks for parsed selector candidates.";
spinProjectionSelectorCandidateStructureCache = <||>;

spinProjectionSelectorCandidateStructureData::usage =
  "spinProjectionSelectorCandidateStructureData[candidate] returns cached dummy-symbol incidence and per-factor dummy blocks for one parsed selector candidate.";
spinProjectionSelectorCandidateStructureData[candidate_Association] := Module[
  {cached, dummyLocations, factorBlocks},
  cached = spinProjectionAssociationLookup[spinProjectionSelectorCandidateStructureCache, candidate["Key"], Missing["NotFound"]];
  If[cached =!= Missing["NotFound"], Return[cached]];
  dummyLocations = spinProjectionSelectorDummySymbolLocations[candidate];
  If[dummyLocations === $Failed, Return[$Failed]];
  factorBlocks = Table[
    spinProjectionSelectorFactorDummyBlocks[candidate["FactorParts"][[i]], i, dummyLocations],
    {i, Length[candidate["FactorParts"]]}
  ];
  If[AnyTrue[factorBlocks, # === $Failed &], Return[$Failed]];
  cached = <|"DummyLocations" -> dummyLocations, "FactorBlocks" -> factorBlocks|>;
  AssociateTo[spinProjectionSelectorCandidateStructureCache, candidate["Key"] -> cached];
  cached
];

spinProjectionSelectorCoefficientAssociationKey::usage =
  "spinProjectionSelectorCoefficientAssociationKey[coefficients] canonicalizes one exact alternating-form coefficient table for cache keys.";
spinProjectionSelectorCoefficientAssociationKey[coefficients_Association] := spinProjectionOrderedAssociationRules[coefficients];

spinProjectionSelectorBlockTensorFromReducedCoefficients::usage =
  "spinProjectionSelectorBlockTensorFromReducedCoefficients[coefficients, blocks] builds one sparse exact block tensor from reduced alternating-form coefficients.";
spinProjectionSelectorBlockTensorFromReducedCoefficients[coefficients_Association, blocks_List] := If[
  blocks === {},
  <|"Blocks" -> {}, "Entries" -> <|{} -> spinProjectionAssociationLookup[coefficients, {}, 0]|>|>,
  <|
    "Blocks" -> blocks,
    "Entries" -> Association @ Select[
      Table[
        key -> spinProjectionSelectorFormCoefficientValue[coefficients, Flatten[key]],
        {key, spinProjectionDisjointBlockBasisTuples[Length /@ blocks]}
      ],
      Last[#] =!= 0 &
    ]
  |>
];

spinProjectionSelectorFactorBlockTensorEntryCache::usage =
  "spinProjectionSelectorFactorBlockTensorEntryCache memoizes sparse exact block-tensor entries by block arities and reduced alternating-form coefficients.";
spinProjectionSelectorFactorBlockTensorEntryCache = <||>;

spinProjectionSelectorFactorBlockTensorCache::usage =
  "spinProjectionSelectorFactorBlockTensorCache memoizes complete exact block tensors for parsed selector factors under dense probes.";
spinProjectionSelectorFactorBlockTensorCache = <||>;

spinProjectionSelectorFactorBlockTensor::usage =
  "spinProjectionSelectorFactorBlockTensor[candidate, factorIndex, factorBlocks, probe] builds one sparse exact block tensor for one parsed selector factor.";
spinProjectionSelectorFactorBlockTensor[candidate_Association, factorIndex_Integer?Positive, factorBlocks_List, probe_Association] := Module[
  {parts, coefficients, reduced, blocks, entryKey, entries, deltaValue},
  parts = candidate["FactorParts"][[factorIndex]];
  If[Lookup[parts, "Kind", "Gamma"] === "Delta",
    If[factorBlocks =!= {}, Return[$Failed]];
    deltaValue = spinProjectionSelectorDeltaFactorValue[parts, probe];
    If[deltaValue === $Failed, Return[$Failed]];
    Return[<|"Blocks" -> {}, "Entries" -> <|{} -> deltaValue|>|>]
  ];
  coefficients = spinProjectionSelectorGammaFactorCoefficientAssociation[parts, probe];
  If[coefficients === $Failed, Return[$Failed]];
  reduced = spinProjectionSelectorReduceFactorCoefficientsByExternalVectors[coefficients, parts["VectorSymbols"], probe];
  blocks = factorBlocks;
  If[blocks === $Failed || Total[Length /@ blocks] =!= Length[reduced["DummySymbols"]], Return[$Failed]];
  entryKey = {Length /@ blocks, spinProjectionSelectorCoefficientAssociationKey[reduced["Coefficients"]]};
  entries = spinProjectionAssociationLookup[spinProjectionSelectorFactorBlockTensorEntryCache, entryKey, Missing["NotFound"]];
  If[entries === Missing["NotFound"],
    entries = spinProjectionSelectorBlockTensorFromReducedCoefficients[reduced["Coefficients"], blocks]["Entries"];
    AssociateTo[spinProjectionSelectorFactorBlockTensorEntryCache, entryKey -> entries];
  ];
  <|"Blocks" -> blocks, "Entries" -> entries|>
];

spinProjectionSelectorCachedFactorBlockTensor::usage =
  "spinProjectionSelectorCachedFactorBlockTensor[candidate, factorIndex, factorBlocks, probe] memoizes sparse exact block tensors across selector probes.";
spinProjectionSelectorCachedFactorBlockTensor[candidate_Association, factorIndex_Integer?Positive, factorBlocks_List, probe_Association] := Module[
  {probeKey, cached},
  probeKey = {candidate["Key"], factorIndex, spinProjectionSelectorProbeKey[probe]};
  cached = spinProjectionAssociationLookup[spinProjectionSelectorFactorBlockTensorCache, probeKey, Missing["NotFound"]];
  If[cached =!= Missing["NotFound"], Return[cached]];
  cached = spinProjectionSelectorFactorBlockTensor[candidate, factorIndex, factorBlocks, probe];
  If[cached === $Failed, Return[$Failed]];
  AssociateTo[spinProjectionSelectorFactorBlockTensorCache, probeKey -> cached];
  cached
];

spinProjectionSelectorScalarBlockTensorValue::usage =
  "spinProjectionSelectorScalarBlockTensorValue[tensor] extracts the scalar carried by a zero-block exact tensor.";
spinProjectionSelectorScalarBlockTensorValue[tensor_Association] := spinProjectionAssociationLookup[tensor["Entries"], {}, 0];

spinProjectionSelectorContractBlockTensors::usage =
  "spinProjectionSelectorContractBlockTensors[left, leftPos, right, rightPos] contracts one shared dummy block between two sparse exact block tensors.";
spinProjectionSelectorContractBlockTensors[left_Association, leftPos_Integer?Positive, right_Association, rightPos_Integer?Positive] := Module[
  {indexedLeft, indexedRight, resultRules, resultEntries},
  indexedLeft = Map[({Delete[#[[1]], leftPos], #[[2]]} & /@ #) &, GroupBy[Normal[left["Entries"]], #[[1, leftPos]] &]];
  indexedRight = Map[({Delete[#[[1]], rightPos], #[[2]]} & /@ #) &, GroupBy[Normal[right["Entries"]], #[[1, rightPos]] &]];
  resultRules = Replace[
    Last @ Reap[
      Do[
        If[!KeyExistsQ[indexedRight, key], Continue[]];
        Do[
          Sow[Join[leftTerm[[1]], rightTerm[[1]]] -> leftTerm[[2]] rightTerm[[2]]],
          {leftTerm, indexedLeft[key]},
          {rightTerm, indexedRight[key]}
        ],
        {key, Keys[indexedLeft]}
      ]
    ],
    {{} -> {}, {items_List} :> items}
  ];
  resultEntries = If[resultRules === {}, <||>, Select[Merge[resultRules, Total], # =!= 0 &]];
  <|"Blocks" -> Join[Delete[left["Blocks"], leftPos], Delete[right["Blocks"], rightPos]], "Entries" -> resultEntries|>
];

spinProjectionSelectorSelfContractBlockTensor::usage =
  "spinProjectionSelectorSelfContractBlockTensor[tensor, leftPos, rightPos] contracts one repeated dummy block inside a single sparse exact block tensor.";
spinProjectionSelectorSelfContractBlockTensor[tensor_Association, leftPos_Integer?Positive, rightPos_Integer?Positive] := Module[
  {deletePositions, resultRules, resultEntries},
  If[leftPos === rightPos, Return[$Failed]];
  If[tensor["Blocks"][[leftPos]] =!= tensor["Blocks"][[rightPos]], Return[$Failed]];
  deletePositions = List /@ Sort[{leftPos, rightPos}];
  resultRules = Cases[
    Normal[tensor["Entries"]],
    (key_ -> value_) /; key[[leftPos]] === key[[rightPos]] :> (Delete[key, deletePositions] -> value)
  ];
  resultEntries = If[resultRules === {}, <||>, Select[Merge[resultRules, Total], # =!= 0 &]];
  <|"Blocks" -> Delete[tensor["Blocks"], deletePositions], "Entries" -> resultEntries|>
];

spinProjectionSelectorSharedBlockPair::usage =
  "spinProjectionSelectorSharedBlockPair[tensors] returns the first pair of tensors and block positions that share the same dummy block.";
spinProjectionSelectorSharedBlockPair[tensors_List] := Module[{seen = <||>, i, p, block},
  For[i = 1, i <= Length[tensors], i++,
    For[p = 1, p <= Length[tensors[[i, "Blocks"]]], p++,
      block = tensors[[i, "Blocks", p]];
      If[KeyExistsQ[seen, block], Return[Join[seen[block], {i, p}]]];
      AssociateTo[seen, block -> {i, p}];
    ]
  ];
  Missing["NoSharedBlock"]
];

spinProjectionSelectorReduceBlockTensorNetwork::usage =
  "spinProjectionSelectorReduceBlockTensorNetwork[tensors] contracts a sparse exact block-tensor network down to a scalar when possible.";
spinProjectionSelectorReduceBlockTensorNetwork[tensors_List] := Module[{work = tensors, scalar = 1, pair, contracted, i},
  If[AnyTrue[work, # === $Failed &], Return[$Failed]];
  While[True,
    For[i = Length[work], i >= 1, i--,
      If[work[[i, "Blocks"]] === {},
        scalar *= spinProjectionSelectorScalarBlockTensorValue[work[[i]]];
        work = Delete[work, i]
      ];
    ];
    If[work === {}, Return[scalar]];
    pair = spinProjectionSelectorSharedBlockPair[work];
    If[pair === Missing["NoSharedBlock"], Return[$Failed]];
    contracted = If[
      pair[[1]] === pair[[3]],
      spinProjectionSelectorSelfContractBlockTensor[work[[pair[[1]]]], pair[[2]], pair[[4]]],
      spinProjectionSelectorContractBlockTensors[work[[pair[[1]]]], pair[[2]], work[[pair[[3]]]], pair[[4]]]
    ];
    If[contracted === $Failed, Return[$Failed]];
    work = If[
      pair[[1]] === pair[[3]],
      ReplacePart[work, pair[[1]] -> contracted],
      Append[Delete[work, List /@ Sort[{pair[[1]], pair[[3]]}, Greater]], contracted]
    ];
  ]
];

spinProjectionSelectorBlockTensorCandidateValue::usage =
  "spinProjectionSelectorBlockTensorCandidateValue[candidate, probe] evaluates one parsed selector candidate at one exact dense probe through sparse block-tensor contraction.";
spinProjectionSelectorBlockTensorCandidateValue[candidate_Association, probe_Association] := Module[
  {structureData, factorBlocks, tensors},
  structureData = spinProjectionSelectorCandidateStructureData[candidate];
  If[structureData === $Failed, Return[$Failed]];
  factorBlocks = structureData["FactorBlocks"];
  tensors = Table[
    spinProjectionSelectorCachedFactorBlockTensor[candidate, i, factorBlocks[[i]], probe],
    {i, Length[candidate["FactorParts"]]}
  ];
  If[AnyTrue[tensors, # === $Failed &], Return[$Failed]];
  spinProjectionSelectorReduceBlockTensorNetwork[tensors]
];

spinProjectionEqualitiesHoldQ::usage =
  "spinProjectionEqualitiesHoldQ[equalities, valueFn] returns True when every equality pair resolves to the same concrete value.";
spinProjectionEqualitiesHoldQ[equalities_List, valueFn_] := AllTrue[
  equalities,
  With[{left = valueFn[#[[1]]], right = valueFn[#[[2]]]}, IntegerQ[left] && IntegerQ[right] && left === right] &
];

spinProjectionTermValue::usage =
  "spinProjectionTermValue[term, freeSpins, freeVectors, stateSpins, stateVectors] evaluates one compiled tensor term through normalized equalities and the lazy gamma-kernel entry cache.";
spinProjectionTermValue[term_Association, freeSpins_List, freeVectors_List, stateSpins_List, stateVectors_List] := Module[
  {kernelValue = 1, vectorTuple, spinTuple, value},
  If[term["ScalarFactor"] === 0, Return[0]];
  If[!spinProjectionEqualitiesHoldQ[term["SpinEqualities"], spinProjectionSpinSourceValue[#, freeSpins, stateSpins] &], Return[0]];
  If[!spinProjectionEqualitiesHoldQ[term["VectorEqualities"], spinProjectionVectorSourceValue[#, freeVectors, stateVectors, {}] &], Return[0]];
  Do[
    vectorTuple = spinProjectionVectorSourceValue[#, freeVectors, stateVectors, {}] & /@ ref["VectorSlots"];
    If[!AllTrue[vectorTuple, IntegerQ], Return[$Failed]];
    spinTuple = spinProjectionSpinSourceValue[#, freeSpins, stateSpins] & /@ ref["SpinSlots"];
    If[!AllTrue[spinTuple, IntegerQ], Return[$Failed]];
    value = spinProjectionGammaKernelEntryValue[ref["Key"], vectorTuple, spinTuple];
    If[value === $Failed, Return[$Failed]];
    kernelValue *= value;
    If[kernelValue === 0, Return[0]],
    {ref, term["GammaKernelRefs"]}
  ];
  If[kernelValue === $Failed, Return[$Failed]];
  term["ScalarFactor"] kernelValue
];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
