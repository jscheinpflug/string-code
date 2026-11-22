(* Run with WolframKernel -noprompt -script <this file>.
   STRINGCODE_BASIS_LEVEL optionally selects one of levels 1, 2, 3.
   STRINGCODE_BASIS_BASELINE_DIR optionally supplies pre-fix key snapshots. *)
$HistoryLength = 0;
$Path = Prepend[$Path, Nest[DirectoryName, $InputFileName, 5]];
Needs["StringCode`"];
InitStringCode[<|"theory" -> "TypeII", "CFT" -> "FlatSpace",
  "conventions" -> "TypeII-Ashoke", "bracket" -> "Flat"|>];

dedupResults = {};
dedupCheck::usage = "Records a basis-deduplication regression assertion.";
dedupCheck[name_String, condition_] := Module[{passed = TrueQ[condition]},
  AppendTo[dedupResults, <|"Check" -> name, "Passed" -> passed|>];
  Print[name, " ", passed];
  If[!passed, Quit[1]]
];

dedupIndexKey::usage =
  "Independently renames NS matter slots to fixed symbols and removes an overall coefficient for comparison.";
dedupIndexKey[word_] := Module[{slots, renamed, firstTerm, operator},
  slots = DeleteDuplicates[Cases[word,
    (dX | dXt | \[Psi] | \[Psi]t)[index_Symbol, _, _] :> index, Infinity]];
  renamed = Expand[word /. Thread[slots -> Table[
    Symbol["Global`comparisonSlot" <> ToString[index]], {index, Length[slots]}]]];
  firstTerm = If[Head[renamed] === Plus, First[renamed], renamed];
  operator = FirstCase[firstTerm, _R, 1, {0, 1}];
  Expand[renamed/(firstTerm/operator)]
];

dedupOriginalCollector::usage =
  "Exact copy of the native collector used while observing its input words.";
DownValues[dedupOriginalCollector] = DownValues[Private`independentROperatorsFromExpressions] /.
  Private`independentROperatorsFromExpressions -> dedupOriginalCollector;

dedupObservedBasis::usage =
  "Runs native generateBasis once and returns its output together with the words entering duplicate removal.";
dedupObservedBasis[level_Integer, ghost_Integer] := Module[{rawWords = {}, operators},
  operators = Internal`InheritedBlock[{Private`independentROperatorsFromExpressions},
    Private`independentROperatorsFromExpressions[expressions_List] := (
      rawWords = Join[rawWords,
        Flatten[Private`independentROperatorsFromExpression /@ expressions, 1]];
      dedupOriginalCollector[expressions]
    );
    generateBasis[2 level, ghost, {-1, -1}]
  ];
  {operators, rawWords}
];

dedupClosedStates::usage =
  "Runs the user's c0-plus extension and native b0-minus filter on generated basis lists.";
dedupClosedStates[raw_List, lowerGhost_List] := DeleteCases[
  Select[
    Join[raw, R[c[1, 0] + ct[1, 0], #] & /@ lowerGhost],
    Expand[Private`basisApplyB0Minus[#]] === 0 &
  ],
  0
];

key = Private`basisOperatorComparisonKey;
wordA = R[ct[0, 0], d\[Phi]t[0, 0], exp\[Phi]f[-1, 0],
  \[Eta]t[0, 0], \[Psi][dedupMuA, 0, 0]];
wordB = wordA /. dedupMuA -> dedupMuB;
dedupCheck["Renamed copies have equal comparison keys", key[wordA] === key[wordB]];
dedupCheck["Comparison leaves input indices untouched", !FreeQ[wordA, dedupMuA]];
dedupCheck["Collector keeps one original representative",
  Private`independentROperatorsFromExpressions[{wordA, wordB}] === {wordA}];
dedupCheck["A repeated Lorentz slot remains distinct from two slots",
  key[R[dX[dedupMuA, 0, 0], \[Psi][dedupMuA, 0, 0]]] =!=
  key[R[dX[dedupMuA, 0, 0], \[Psi][dedupMuB, 0, 0]]]];
dedupCheck["Holomorphic and antiholomorphic words remain distinct",
  key[R[\[Psi][dedupMuA, 0, 0]]] =!= key[R[\[Psi]t[dedupMuA, 0, 0]]]];
dedupCheck["Derivative orders remain distinct",
  key[wordA] =!= key[wordA /. \[Psi][index_, 0, 0] :> \[Psi][index, 1, 0]]];


dedupCheck["Fixed numerical vector components remain distinct",
  key[R[\[Psi][0, 0, 0]]] =!= key[R[\[Psi][1, 0, 0]]]];
spinWord = R[S[{dedupAlphaA, "chiral"}, -1/2, {}, 0, 0]];
dedupCheck["Renamed spinor slots have equal comparison keys",
  key[spinWord] === key[spinWord /. dedupAlphaA -> dedupAlphaB]];
dedupCheck["Spinor chirality remains distinct",
  key[spinWord] =!= key[spinWord /. "chiral" -> "antichiral"]];
dedupCheck["Spinor worldsheet chirality remains distinct",
  key[spinWord] =!= key[spinWord /. S -> St]];

excitedSpinWord = R[S[{dedupAlphaA, "chiral"}, -3/2, {{dedupMuA, -1}}, 0, 0]];
dedupCheck["Renamed excited-spinor slots have equal comparison keys",
  key[excitedSpinWord] === key[excitedSpinWord /. {dedupAlphaA -> dedupAlphaB, dedupMuA -> dedupMuB}]];
dedupCheck["Excited-spinor keys retain their spin field",
  MatchQ[key[excitedSpinWord], HoldPattern[R[_S]]]];
dedupCheck["Excited-spinor mode numbers remain distinct",
  key[excitedSpinWord] =!= key[excitedSpinWord /. -1 -> -2]];
dedupCheck["A spin excitation remains distinct from a bosonic oscillator",
  key[excitedSpinWord] =!= key[R[dX[dedupMuA, 0, 0], S[{dedupAlphaA, "chiral"}, -3/2, {}, 0, 0]]]];

selectedLevel = Environment["STRINGCODE_BASIS_LEVEL"];
levels = If[StringQ[selectedLevel], {ToExpression[selectedLevel]}, {1, 2, 3}];
dedupCheck["Requested levels are supported", AllTrue[levels, MemberQ[{1, 2, 3}, #] &]];
baselineDirectory = Environment["STRINGCODE_BASIS_BASELINE_DIR"];
dedupCounts = {};
Do[
  basisByGhost = <||>;
  Do[
    Print["START n=", level, " ghost=", ghost];
    {seconds, {operators, rawWords}} = AbsoluteTiming[dedupObservedBasis[level, ghost]];
    referenceKeys = Sort[DeleteDuplicates[dedupIndexKey /@ rawWords]];
    Clear[rawWords];
    computedKeys = dedupIndexKey /@ operators;
    name = "n=" <> ToString[level] <> " ghost=" <> ToString[ghost];
    dedupCheck[name <> " is nonempty", operators =!= {}];
    dedupCheck[name <> " has no duplicate index structures", DuplicateFreeQ[computedKeys]];
    dedupCheck[name <> " contains ordinary R words", AllTrue[operators, MatchQ[#, _R] &]];
    dedupCheck[name <> " has no comparison slots in output", FreeQ[operators, _Private`basisIndexSlot]];
    If[StringQ[baselineDirectory],
      Get[FileNameJoin[{baselineDirectory,
        "before-n" <> ToString[level] <> "-g" <> ToString[ghost] <> ".mx"}]];
      dedupCheck[name <> " collected span matches the independent pre-fix run", referenceKeys === keys]
    ];
    dedupCheck[name <> " preserves the complete collected span", Sort[computedKeys] === referenceKeys];
    AssociateTo[basisByGhost, ghost -> operators];
    AppendTo[dedupCounts, <|"Level" -> level, "GhostNumber" -> ghost,
      "Count" -> Length[operators], "Seconds" -> seconds|>];
    Print[InputForm[Last[dedupCounts]]];
  , {ghost, {0, 1, 2}}];
  Do[
    closed = dedupClosedStates[basisByGhost[ghost], basisByGhost[ghost - 1]];
    closedKeys = dedupIndexKey /@ closed;
    name = "n=" <> ToString[level] <> " ghost=" <> ToString[ghost] <> " b0-minus kernel";
    dedupCheck[name <> " has no duplicate structures", DuplicateFreeQ[closedKeys]];
    dedupCheck[name <> " obeys the native constraint",
      AllTrue[closed, Expand[Private`basisApplyB0Minus[#]] === 0 &]];
    Print["CLOSED_COUNT n=", level, " ghost=", ghost, " count=", Length[closed]];
    If[level === 1,
      dedupCheck[name <> " has the verified level-one count", Length[closed] === If[ghost === 1, 143, 180]]
    ];
  , {ghost, {1, 2}}];
, {level, levels}];

(* Preserve the explicit index-output option while comparing slots canonically. *)
uncanonicalized = generateBasis[2, 2, {-1, -1}, "CanonicalizeIndices" -> False];
dedupCheck["CanonicalizeIndices False also removes duplicate structures",
  Length[uncanonicalized] === 323 && DuplicateFreeQ[dedupIndexKey /@ uncanonicalized]];
dedupCheck["CanonicalizeIndices False preserves the original symbol naming",
  AnyTrue[Cases[uncanonicalized, index_Symbol /; StringStartsQ[SymbolName[index], "mu"], Infinity],
    StringContainsQ[SymbolName[#], "$"] &]];

reportFile = Environment["STRINGCODE_BASIS_REPORT"];
If[!StringQ[reportFile],
  reportFile = FileNameJoin[{$TemporaryDirectory, "StringCodeBasisIndexDeduplicationChecks.json"}]
];
Export[reportFile, <|"AllPassed" -> And @@ Lookup[dedupResults, "Passed"],
  "Counts" -> dedupCounts, "Checks" -> dedupResults|>, "RawJSON"];
Print["ALL_PASSED ", And @@ Lookup[dedupResults, "Passed"]];
Quit[If[And @@ Lookup[dedupResults, "Passed"], 0, 1]];
