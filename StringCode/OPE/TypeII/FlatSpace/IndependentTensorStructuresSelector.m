(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`OPE`TypeII`FlatSpace`IndependentTensorStructuresSelector`"];
Needs["StringCode`OPE`TypeII`FlatSpace`CountSinglet`"];
Needs["StringCode`OPE`TypeII`FlatSpace`GammaProductGrammar`"];
Needs["StringCode`OPE`TypeII`FlatSpace`IndependentTensorStructuresEvaluator`"];


(* ::Section:: *)
(*Logic*)


Begin["Private`"];

selectorCandidates::usage = "selectorCandidates[candidates] parses one explicit candidate list into reusable selector data.";
selectorCandidates[candidates_List] := Module[{parsed},
  If[candidates === {} || AllTrue[candidates, MatchQ[#, _Association] &], Return[candidates]];
  parsed = parseCandidate /@ candidates;
  If[MemberQ[parsed, $Failed], $Failed, parsed]
];

probeModulus::usage = "probeModulus[primes] returns a shared sampling modulus whose residues are uniform modulo every selection prime.";
probeModulus[primes_List] := LCM @@ primes;

probeAssignment::usage = "probeAssignment[spinorSymbols, externalVectors, modulus, baseSeed, probeIndex] builds one deterministic component probe.";
probeAssignment[spinorSymbols_List, externalVectors_List, modulus_Integer?Positive, baseSeed_, probeIndex_Integer] := BlockRandom[
  If[baseSeed === Automatic,
    SeedRandom[Hash[{DateList[], probeIndex, Length[spinorSymbols], Length[externalVectors]}]],
    SeedRandom[Hash[{baseSeed, probeIndex}]]
  ];
  <|
    "SpinorComponents" -> AssociationThread[spinorSymbols -> Table[RandomInteger[{0, modulus - 1}, 16], {Length[spinorSymbols]}]],
    "VectorComponents" -> AssociationThread[externalVectors -> Table[RandomInteger[{0, modulus - 1}, 10], {Length[externalVectors]}]]
  |>
];

buildProbeBank::usage = "buildProbeBank[spinorSymbols, externalVectors, modulus, count, seed] builds a deterministic list of component probes.";
buildProbeBank[spinorSymbols_List, externalVectors_List, modulus_Integer?Positive, count_Integer?NonNegative, seed_] := Table[
  probeAssignment[spinorSymbols, externalVectors, modulus, seed, i],
  {i, 1, count}
];

initialPivotState::usage = "initialPivotState[prime] constructs an empty incremental modular pivot state for one modulus.";
initialPivotState[prime_Integer] := <|"Prime" -> prime, "Rows" -> {}, "PivotColumns" -> {}|>;

incrementalPivotInsert::usage = "incrementalPivotInsert[state, row] inserts one modular signature row into an incremental row-echelon state.";
incrementalPivotInsert[state_Association, row_List] := Module[
  {reducedRow, rows, pivots, pivotPos, pivotValue, insertPos, newRows, newPivots, i},
  reducedRow = Mod[row, state["Prime"]];
  rows = state["Rows"];
  pivots = state["PivotColumns"];
  For[i = 1, i <= Length[rows], i++,
    If[reducedRow[[pivots[[i]]]] =!= 0, reducedRow = Mod[reducedRow - reducedRow[[pivots[[i]]]] rows[[i]], state["Prime"]]];
  ];
  pivotPos = FirstCase[Range[Length[reducedRow]], j_ /; reducedRow[[j]] =!= 0 :> j, Missing["NoPivot"]];
  If[pivotPos === Missing["NoPivot"], Return[<|"State" -> state, "RankIncreased" -> False|>]];
  pivotValue = reducedRow[[pivotPos]];
  reducedRow = Mod[PowerMod[pivotValue, -1, state["Prime"]] reducedRow, state["Prime"]];
  newRows = rows;
  For[i = 1, i <= Length[newRows], i++,
    If[newRows[[i, pivotPos]] =!= 0, newRows[[i]] = Mod[newRows[[i]] - newRows[[i, pivotPos]] reducedRow, state["Prime"]]];
  ];
  insertPos = Count[pivots, _?(# < pivotPos &)] + 1;
  newRows = Insert[newRows, reducedRow, insertPos];
  newPivots = Insert[pivots, pivotPos, insertPos];
  <|"State" -> <|"Prime" -> state["Prime"], "Rows" -> newRows, "PivotColumns" -> newPivots|>, "RankIncreased" -> True|>
];

selectionRuntime::usage = "selectionRuntime[parsedCandidates, optsAssoc, targetRank] initializes shared runtime state for one selector run.";
selectionRuntime[parsedCandidates_List, optsAssoc_Association, targetRank_Integer?NonNegative] := Module[
  {probeCount, seed, primes, spinorMap, externalVectors, modulus},
  probeCount = Max[Lookup[optsAssoc, "ProbeCount", 5], targetRank];
  seed = Lookup[optsAssoc, "RandomSeed", Automatic];
  primes = Lookup[optsAssoc, "ModulusPrimes", {32009, 32057, 32089}];
  modulus = probeModulus[primes];
  spinorMap = If[parsedCandidates === {}, <||>, Merge[parsedCandidates[[All, "SpinorChiralities"]], First]];
  externalVectors = If[parsedCandidates === {}, {}, SortBy[DeleteDuplicates[Flatten[parsedCandidates[[All, "ExternalVectors"]], 1]], SymbolName]];
  <|
    "Primes" -> primes,
    "PrimeData" -> AssociationThread[primes -> (primeEvaluationData /@ primes)],
    "Probes" -> buildProbeBank[Keys[spinorMap], externalVectors, modulus, probeCount, seed],
    "ProbeModulus" -> modulus,
    "BaseSeed" -> seed,
    "SpinorSymbols" -> Keys[spinorMap],
    "ExternalVectors" -> externalVectors,
    "SignatureCache" -> <||>,
    "DeferredQueue" -> {},
    "AcceptedCandidates" -> {},
    "PrimeStates" -> AssociationThread[primes -> (initialPivotState /@ primes)]
  |>
];

listSelectionRuntime::usage = "listSelectionRuntime[candidates, optsAssoc, targetRank] initializes selector runtime for candidate-list input.";
listSelectionRuntime[candidates_List, optsAssoc_Association, targetRank_Integer?NonNegative] := Module[{parsed = selectorCandidates[candidates]},
  If[parsed === $Failed, $Failed, selectionRuntime[parsed, optsAssoc, targetRank]]
];

ensureCandidatePrimeSignature::usage = "ensureCandidatePrimeSignature[candidate, runtime, prime] ensures that runtime holds the full active-probe signature for one candidate under one modulus.";
ensureCandidatePrimeSignature[candidate_Association, runtime_Association, prime_Integer] := Module[
  {candidateAssoc, existing, start, extended, nextRuntime},
  candidateAssoc = Lookup[runtime["SignatureCache"], candidate["Key"], <||>];
  existing = Lookup[candidateAssoc, prime, {}];
  If[Length[existing] >= Length[runtime["Probes"]], Return[runtime]];
  start = Length[existing] + 1;
  extended = Join[
    existing,
    Table[evaluateCandidateAtProbe[candidate, runtime["Probes"][[i]], runtime["PrimeData"][prime]], {i, start, Length[runtime["Probes"]]}]
  ];
  candidateAssoc = Join[candidateAssoc, <|prime -> extended|>];
  nextRuntime = runtime;
  AssociateTo[nextRuntime, "SignatureCache" -> Join[nextRuntime["SignatureCache"], <|candidate["Key"] -> candidateAssoc|>]];
  nextRuntime
];

candidateSignature::usage = "candidateSignature[candidate, runtime, prime] returns the modular signature list for one candidate under one prime.";
candidateSignature[candidate_Association, runtime_Association, prime_Integer] := Lookup[Lookup[runtime["SignatureCache"], candidate["Key"], <||>], prime, {}];

queueDeferredCandidate::usage = "queueDeferredCandidate[candidate, runtime] appends one candidate to the deferred queue if it is not already present.";
queueDeferredCandidate[candidate_Association, runtime_Association] := Module[{nextRuntime},
  If[MemberQ[runtime["DeferredQueue"][[All, "Key"]], candidate["Key"]], Return[runtime]];
  nextRuntime = runtime;
  AssociateTo[nextRuntime, "DeferredQueue" -> Append[nextRuntime["DeferredQueue"], candidate]];
  nextRuntime
];

tryAcceptCandidate::usage = "tryAcceptCandidate[candidate, runtime] tests one candidate against the current modular pivot states.";
tryAcceptCandidate[candidate_Association, runtime_Association] := Module[
  {nextRuntime, primaryPrime, primaryInsertion, insertions = <||>, allAccepted = True, signature, primes, prime},
  nextRuntime = runtime;
  primes = nextRuntime["Primes"];
  primaryPrime = First[primes];
  nextRuntime = ensureCandidatePrimeSignature[candidate, nextRuntime, primaryPrime];
  signature = candidateSignature[candidate, nextRuntime, primaryPrime];
  If[AnyTrue[signature, # === $Failed &], Return[<|"Runtime" -> nextRuntime, "Status" -> "Invalid"|>]];
  primaryInsertion = incrementalPivotInsert[nextRuntime["PrimeStates"][primaryPrime], signature];
  If[!TrueQ[primaryInsertion["RankIncreased"]], Return[<|"Runtime" -> nextRuntime, "Status" -> "Rejected"|>]];
  AssociateTo[insertions, primaryPrime -> primaryInsertion];
  Do[
    nextRuntime = ensureCandidatePrimeSignature[candidate, nextRuntime, prime];
    signature = candidateSignature[candidate, nextRuntime, prime];
    If[AnyTrue[signature, # === $Failed &], Return[<|"Runtime" -> nextRuntime, "Status" -> "Invalid"|>]];
    AssociateTo[insertions, prime -> incrementalPivotInsert[nextRuntime["PrimeStates"][prime], signature]];
    allAccepted = allAccepted && TrueQ[insertions[prime]["RankIncreased"]],
    {prime, Rest[primes]}
  ];
  If[allAccepted,
    AssociateTo[
      nextRuntime,
      <|
        "PrimeStates" -> Association@Table[prime -> insertions[prime]["State"], {prime, primes}],
        "AcceptedCandidates" -> Append[nextRuntime["AcceptedCandidates"], candidate]
      |>
    ];
    Return[<|"Runtime" -> nextRuntime, "Status" -> "Accepted"|>]
  ];
  <|"Runtime" -> queueDeferredCandidate[candidate, nextRuntime], "Status" -> "Deferred"|>
];

appendVerificationProbes::usage = "appendVerificationProbes[runtime, optsAssoc] appends fresh verification probes to the runtime probe bank.";
appendVerificationProbes[runtime_Association, optsAssoc_Association] := Module[{extraCount, startIndex, nextRuntime},
  extraCount = Lookup[optsAssoc, "VerificationProbeCount", 3];
  If[extraCount <= 0, Return[runtime]];
  startIndex = Length[runtime["Probes"]] + 1;
  nextRuntime = runtime;
  AssociateTo[
    nextRuntime,
    "Probes" -> Join[
      nextRuntime["Probes"],
      Table[
        probeAssignment[nextRuntime["SpinorSymbols"], nextRuntime["ExternalVectors"], nextRuntime["ProbeModulus"], nextRuntime["BaseSeed"], startIndex + i - 1],
        {i, 1, extraCount}
      ]
    ]
  ];
  nextRuntime
];

rebuildAcceptedBasis::usage = "rebuildAcceptedBasis[runtime] rebuilds the accepted-basis prime states on the current probe bank and drops unstable candidates.";
rebuildAcceptedBasis[runtime_Association] := Module[
  {freshStates, nextRuntime, kept = {}, insertions, statuses, primes},
  freshStates = AssociationThread[runtime["Primes"] -> (initialPivotState /@ runtime["Primes"])];
  nextRuntime = runtime;
  primes = runtime["Primes"];
  Do[
    Do[nextRuntime = ensureCandidatePrimeSignature[candidate, nextRuntime, prime], {prime, primes}];
    insertions = Association@Table[
      prime -> incrementalPivotInsert[freshStates[prime], candidateSignature[candidate, nextRuntime, prime]],
      {prime, primes}
    ];
    statuses = Table[insertions[prime]["RankIncreased"], {prime, primes}];
    If[And @@ statuses,
      freshStates = Association@Table[prime -> insertions[prime]["State"], {prime, primes}];
      AppendTo[kept, candidate];
    ],
    {candidate, runtime["AcceptedCandidates"]}
  ];
  AssociateTo[nextRuntime, <|"AcceptedCandidates" -> kept, "PrimeStates" -> freshStates|>];
  nextRuntime
];

retryDeferredQueue::usage = "retryDeferredQueue[runtime] retries deferred candidates under the current probe bank.";
retryDeferredQueue[runtime_Association] := Module[{nextRuntime, result},
  nextRuntime = runtime;
  AssociateTo[nextRuntime, "DeferredQueue" -> {}];
  Do[
    result = tryAcceptCandidate[candidate, nextRuntime];
    nextRuntime = result["Runtime"],
    {candidate, runtime["DeferredQueue"]}
  ];
  nextRuntime
];

verifySelectionRuntime::usage = "verifySelectionRuntime[runtime, optsAssoc] appends verification probes, rebuilds the basis, and retries deferred candidates.";
verifySelectionRuntime[runtime_Association, optsAssoc_Association] := retryDeferredQueue @ rebuildAcceptedBasis @ appendVerificationProbes[runtime, optsAssoc];

automaticCandidateTargetRank::usage = "automaticCandidateTargetRank[candidates] infers an exact singlet-count upper bound from candidate spinor chiralities and external vectors.";
automaticCandidateTargetRank[candidates_List] := Module[{parsed, chiralityMap, nVectors, counts, flipped},
  parsed = selectorCandidates[candidates];
  If[parsed === $Failed || parsed === {}, Return[0]];
  chiralityMap = Merge[parsed[[All, "SpinorChiralities"]], First];
  nVectors = Length[DeleteDuplicates[Flatten[parsed[[All, "ExternalVectors"]], 1]]];
  counts = {
    countSinglets[Count[Values[chiralityMap], "chiral"], Count[Values[chiralityMap], "antichiral"], nVectors]
  };
  (* For explicit candidate lists the outgoing spinor is unknown, so flip each endpoint once and keep the tightest positive bound. *)
  counts = Join[
    counts,
    Table[
      flipped = Join[chiralityMap, <|sym -> If[chiralityMap[sym] === "chiral", "antichiral", "chiral"]|>];
      countSinglets[Count[Values[flipped], "chiral"], Count[Values[flipped], "antichiral"], nVectors],
      {sym, Keys[chiralityMap]}
    ]
  ];
  counts = Select[counts, Positive];
  If[counts === {}, 0, Min[counts]]
];

scanCandidateList::usage = "scanCandidateList[candidates, targetRank, optsAssoc] scans an explicit candidate list in order and returns the verified basis and visit count.";
scanCandidateList[candidates_List, targetRank_, optsAssoc_Association] := Module[
  {parsed, effectiveTarget, runtime, visited = 0, result, cursor = 1, count},
  parsed = selectorCandidates[candidates];
  If[parsed === $Failed, Return[$Failed]];
  effectiveTarget = If[targetRank === Automatic, automaticCandidateTargetRank[parsed], targetRank];
  If[effectiveTarget <= 0,
    Return[<|"Basis" -> {}, "TargetRank" -> 0, "VisitedCandidates" -> 0|>]
  ];
  runtime = listSelectionRuntime[parsed, optsAssoc, effectiveTarget];
  If[runtime === $Failed, Return[$Failed]];
  count = Length[parsed];
  While[True,
    While[cursor <= count && Length[runtime["AcceptedCandidates"]] < effectiveTarget,
      visited++;
      result = tryAcceptCandidate[parsed[[cursor]], runtime];
      runtime = result["Runtime"];
      cursor++;
    ];
    runtime = verifySelectionRuntime[runtime, optsAssoc];
    If[Length[runtime["AcceptedCandidates"]] >= effectiveTarget || cursor > count, Break[]];
  ];
  If[targetRank === Automatic, effectiveTarget = Length[runtime["AcceptedCandidates"]]];
  <|
    "Basis" -> runtime["AcceptedCandidates"][[All, "Expression"]],
    "TargetRank" -> effectiveTarget,
    "VisitedCandidates" -> visited
  |>
];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
