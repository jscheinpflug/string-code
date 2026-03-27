scriptArgs = If[Length[$CommandLine] > 4, Drop[$CommandLine, 4], {}];
convention = If[scriptArgs === {}, "TypeII-Xi", First[scriptArgs]];

Needs["StringCode`"];
StringCode`InitStringCode[<|"theory" -> "TypeII", "CFT" -> "FlatSpace", "conventions" -> convention, "bracket" -> "Flat"|>];
Needs["StringCode`OPE`TypeII`FlatSpace`"];

getOutgoing = ToExpression["Private`getOutgoingOperatorsTensors"];
compileModel = ToExpression["Private`compileSpinProjectionSectorModel"];
assignmentIterator = ToExpression["Private`spinProjectionAssignmentIterator"];
candidateRows = ToExpression["Private`spinProjectionCandidateRows"];
termValue = ToExpression["Private`spinProjectionTermValue"];
familyOutputSpinDomain = ToExpression["Private`spinProjectionFamilyOutputSpinDomain"];
familyStateIterator = ToExpression["Private`spinProjectionFamilyStateIterator"];
exactBasisInsertRow = ToExpression["Private`spinProjectionExactBasisInsertRow"];
operatorAssociation = ToExpression["Private`spinProjectionOperatorAssociation"];
spinBasisState = ToExpression["Private`spinProjectionSpinBasisState"];
spinTypedIndices = ToExpression["Private`spinTypedIndices"];
evaluateTensorScalars = ToExpression["Private`spinProjectionEvaluateTensorScalars"];

ops = ToExpression["{R[S[{a1, \"chiral\"}, -1/2, {}, 0, z1]], R[S[{a2, \"chiral\"}, -1/2, {}, 0, z2]], R[S[{a3, \"chiral\"}, -1/2, {}, 0, z3]], R[S[{a4, \"chiral\"}, -1/2, {}, 0, z4]], R[S[{a5, \"chiral\"}, -1/2, {}, 0, z5]]}"];
outgoing = getOutgoing[ops, 0, 0, 1234];
model = compileModel["Holo", outgoing["holoOps"], 0, outgoing["holoData"]];
family = First[model["Families"]];
flatTerms = Flatten[Map[Function[pair, Map[<|"Output" -> pair[[1]], "Tensor" -> #|> &, pair[[2]]]], outgoing["holoData"]], 1];

exactMatchQ::usage =
  "exactMatchQ[left, right] returns True when two exact values agree up to simplification.";
exactMatchQ[left_, right_] := TrueQ[left === right || Simplify[left == right]];

rowMatchQ::usage =
  "rowMatchQ[left, right] checks exact equality of two coefficient rows.";
rowMatchQ[left_List, right_List] := Length[left] == Length[right] && AllTrue[MapThread[exactMatchQ, {left, right}], TrueQ];

randomAllSpinCandidate::usage =
  "randomAllSpinCandidate[model] returns one random free-spin assignment over the full spin-basis domain.";
randomAllSpinCandidate[model_Association] := {
  Developer`ToPackedArray[RandomInteger[{1, 16}, Length[model["FreeSpinSymbols"]]]],
  Developer`ToPackedArray[ConstantArray[1, Length[model["FreeVectorGroups"]]]]
};

tensorDummySymbols::usage =
  "tensorDummySymbols[tensor, model, family] returns the sorted dummy-vector symbols of one original tensor term.";
tensorDummySymbols[tensor_, model_Association, family_Association] := SortBy[
  Complement[
    DeleteDuplicates @ Cases[spinTypedIndices[tensor], {sym_Symbol, "v"} :> sym],
    Flatten[model["FreeVectorGroups"]],
    family["VectorSymbols"]
  ],
  SymbolName
];

tensorRules::usage =
  "tensorRules[tensor, model, family, candidate, stateSpins, stateVectors, dummy] builds the concrete substitutions used by the direct symbolic row comparator.";
tensorRules[tensor_, model_Association, family_Association, candidate : {freeSpins_List, freeVectors_List}, stateSpins_List, stateVectors_List, dummy_List] := Join[
  Thread[
    model["FreeSpinSymbols"] ->
      MapThread[spinBasisState[#1][[#2]] &, {model["FreeSpinChiralities"], freeSpins}]
  ],
  Thread[
    family["SpinSymbols"] ->
      MapThread[spinBasisState[#1][[#2]] &, {family["SpinChiralities"], stateSpins}]
  ],
  Flatten @ MapThread[Thread[#1 -> #2] &, {model["FreeVectorGroups"], freeVectors}],
  Thread[family["VectorSymbols"] -> stateVectors],
  Thread[tensorDummySymbols[tensor, model, family] -> dummy]
];

dummyTuples::usage =
  "dummyTuples[k] returns the ordered dummy-vector tuples used by the direct symbolic row comparator.";
dummyTuples[k_Integer?NonNegative] := If[k == 0, {{}}, Tuples[Range[10], k]];

symbolicTermValue::usage =
  "symbolicTermValue[column, candidate, stateSpins, stateVectors] evaluates one original tensor term by an explicit ordered dummy sum.";
symbolicTermValue[column_Integer?Positive, candidate_, stateSpins_List, stateVectors_List] := Module[
  {term = family["Terms"][[column]], tensor = flatTerms[[column, "Tensor"]]},
  Total[
    evaluateTensorScalars[tensor /. tensorRules[tensor, model, family, candidate, stateSpins, stateVectors, #]] & /@ dummyTuples[term[[4]]]
  ]
];

compiledStateRow::usage =
  "compiledStateRow[candidate, stateSpins, stateVectors, activeTerms] builds the compiled coefficient row for one concrete output state.";
compiledStateRow[candidate : {freeSpins_List, freeVectors_List}, stateSpins_List, stateVectors_List, activeTerms_List] := Module[
  {row = ConstantArray[0, model["VarCount"]], value},
  Scan[
    Function[term,
      value = termValue[term, freeSpins, freeVectors, stateSpins, stateVectors];
      If[value =!= 0, row[[term[[1]]]] += value]
    ],
    activeTerms
  ];
  row
];

symbolicStateRow::usage =
  "symbolicStateRow[candidate, stateSpins, stateVectors] builds the direct symbolic coefficient row for one concrete output state.";
symbolicStateRow[candidate_, stateSpins_List, stateVectors_List] := Module[{row = ConstantArray[0, model["VarCount"]], value},
  Do[
    value = symbolicTermValue[column, candidate, stateSpins, stateVectors];
    If[value =!= 0, row[[column]] += value],
    {column, model["VarCount"]}
  ];
  row
];

directOutputAssociation::usage =
  "directOutputAssociation[family, tuple] bosonizes one concrete output state directly, without using the precomputed output-association cache.";
directOutputAssociation[family_Association, tuple_List] := Module[{spinCount = Length[family["SpinSymbols"]]},
  operatorAssociation @ Bosonize[
    family["Template"] /. Join[
      Thread[family["VectorSymbols"] -> Drop[tuple, spinCount]],
      MapThread[#1 -> spinBasisState[#2][[#3]] &, {family["SpinSymbols"], family["SpinChiralities"], Take[tuple, spinCount]}]
    ]
  ]
];

accumulateRows::usage =
  "accumulateRows[rows, assoc, row] returns the updated operator-row association after adding one operator-weighted coefficient row.";
accumulateRows[rows_Association, assoc_Association, row_List] := Fold[
  Function[{acc, pair},
    Join[acc, <|pair[[1]] -> Lookup[acc, pair[[1]], ConstantArray[0, model["VarCount"]]] + pair[[2]] row|>]
  ],
  rows,
  Normal[assoc]
];

basisFromFamilyRows::usage =
  "basisFromFamilyRows[rows] inserts one exact family-row association into the same reduced basis logic used by candidateRows.";
basisFromFamilyRows[rows_Association] := Module[{state = <|"Rows" -> {}, "Pivots" -> {}|>, keptRows = {}, keptKeys = {}, insert},
  Scan[
    Function[pair,
      insert = exactBasisInsertRow[state, pair[[2]]];
      If[insert[[2]],
        state = insert[[1]];
        AppendTo[keptRows, pair[[2]]];
        AppendTo[keptKeys, pair[[1]]]
      ]
    ],
    SortBy[Normal[rows], First]
  ];
  <|"Basis" -> state, "Rows" -> keptRows, "Keys" -> keptKeys|>
];

firstRowMismatch::usage =
  "firstRowMismatch[leftRows, rightRows] returns Missing when two operator-row associations agree, otherwise the first differing key and rows.";
firstRowMismatch[leftRows_Association, rightRows_Association] := Module[{keys = Sort @ DeleteDuplicates @ Join[Keys[leftRows], Keys[rightRows]], left, right},
  FirstCase[
    keys,
    key_ /; Module[{},
      left = Lookup[leftRows, key, ConstantArray[0, model["VarCount"]]];
      right = Lookup[rightRows, key, ConstantArray[0, model["VarCount"]]];
      !rowMatchQ[left, right]
    ] :> <|"Key" -> key, "Compiled" -> left, "Symbolic" -> right, "DifferingColumns" -> Flatten @ Position[MapThread[Not @* exactMatchQ, {left, right}], True]|>,
    Missing["NoMismatch"]
  ]
];

runRawSearch::usage =
  "runRawSearch[nextCandidate, limit] returns the accepted candidate list of the raw compiled row builder without the pivot-basis solve workaround.";
runRawSearch[nextCandidate_, limit_Integer?Positive] := Module[
  {state = <|"Rows" -> {}, "Pivots" -> {}|>, acceptedCandidates = {}, visited = 0, candidate, result},
  While[visited < limit,
    candidate = nextCandidate[];
    If[candidate === EndOfFile, Break[]];
    visited++;
    result = candidateRows[model, candidate, state, 1234];
    If[result["Rows"] === {}, Continue[]];
    state = result["Basis"];
    AppendTo[acceptedCandidates, candidate];
    If[Length[state["Pivots"]] >= model["VarCount"], Break[]]
  ];
  acceptedCandidates
];

modeAudit::usage =
  "modeAudit[candidate, mode] compares compiled and direct symbolic rows for one accepted candidate under one state-scan mode.";
modeAudit[candidate_, mode_String] := Module[
  {spinDomain, termBuckets, nextState, tuple, stateSpins, stateVectors, compiledFamilyRows = <||>, symbolicFamilyRows = <||>, stateMismatch = Missing["NoMismatch"], compiledRow, symbolicRow, compiledAssoc, symbolicAssoc, compiledAccepted, symbolicAccepted},
  {spinDomain, termBuckets} = Switch[mode,
    "Current", familyOutputSpinDomain[family, candidate, 1234, True],
    "NoBuckets", {familyOutputSpinDomain[family, candidate, 1234], <||>},
    "FullState", {Range[16], <||>}
  ];
  nextState = familyStateIterator[family, 1234, spinDomain];
  While[True,
    tuple = nextState[];
    If[tuple === EndOfFile, Break[]];
    tuple = Reverse[tuple];
    stateSpins = Developer`ToPackedArray[Take[tuple, Length[family["SpinSymbols"]]]];
    stateVectors = Developer`ToPackedArray[Drop[tuple, Length[family["SpinSymbols"]]]];
    compiledRow = compiledStateRow[
      candidate,
      stateSpins,
      stateVectors,
      If[mode === "Current", Join[Lookup[termBuckets, 0, {}], Lookup[termBuckets, stateSpins[[1]], {}]], family["Terms"]]
    ];
    symbolicRow = symbolicStateRow[candidate, stateSpins, stateVectors];
    If[MissingQ[stateMismatch] && !rowMatchQ[compiledRow, symbolicRow],
      stateMismatch = <|
        "StateTuple" -> tuple,
        "Compiled" -> compiledRow,
        "Symbolic" -> symbolicRow,
        "DifferingColumns" -> Flatten @ Position[MapThread[Not @* exactMatchQ, {compiledRow, symbolicRow}], True]
      |>
    ];
    compiledAssoc = If[KeyExistsQ[family["OutputAssociations"], tuple], family["OutputAssociations"][tuple], <||>];
    symbolicAssoc = directOutputAssociation[family, tuple];
    compiledFamilyRows = accumulateRows[compiledFamilyRows, compiledAssoc, compiledRow];
    symbolicFamilyRows = accumulateRows[symbolicFamilyRows, symbolicAssoc, symbolicRow]
  ];
  compiledAccepted = If[mode === "Current", candidateRows[model, candidate, <|"Rows" -> {}, "Pivots" -> {}|>, 1234], basisFromFamilyRows[compiledFamilyRows]];
  symbolicAccepted = basisFromFamilyRows[symbolicFamilyRows];
  <|
    "Mode" -> mode,
    "StateRowMismatch" -> stateMismatch,
    "AggregatedMismatch" -> firstRowMismatch[compiledFamilyRows, symbolicFamilyRows],
    "AcceptedRowMismatch" -> <|
      "RowsMatchQ" -> (compiledAccepted["Rows"] === symbolicAccepted["Rows"]),
      "KeysMatchQ" -> (compiledAccepted["Keys"] === symbolicAccepted["Keys"]),
      "PivotsMatchQ" -> (compiledAccepted["Basis"]["Pivots"] === symbolicAccepted["Basis"]["Pivots"])
    |>
  |>
];

deterministicAccepted::usage =
  "deterministicAccepted[] returns the first accepted support-driven candidate from the raw compiled search.";
deterministicAccepted[] := First[runRawSearch[assignmentIterator[model, 1234], 16]];

randomAccepted::usage =
  "randomAccepted[] returns the first accepted uniformly random free-spin candidate from the raw compiled search.";
randomAccepted[] := Module[{accepted},
  SeedRandom[123456];
  accepted = runRawSearch[Function[{}, randomAllSpinCandidate[model]], 64];
  If[accepted === {}, $Failed, First[accepted]]
];

Print @ InputForm @ <|
  "Convention" -> convention,
  "DeterministicCandidate" -> With[{candidate = deterministicAccepted[]},
    <|
      "Candidate" -> candidate,
      "Audits" -> (modeAudit[candidate, #] & /@ {"Current", "NoBuckets", "FullState"})
    |>
  ],
  "RandomAcceptedCandidate" -> With[{candidate = randomAccepted[]},
    If[candidate === $Failed,
      <|"Candidate" -> $Failed|>,
      <|
        "Candidate" -> candidate,
        "Audits" -> (modeAudit[candidate, #] & /@ {"Current", "NoBuckets", "FullState"})
      |>
    ]
  ]
|>;

Exit[];
