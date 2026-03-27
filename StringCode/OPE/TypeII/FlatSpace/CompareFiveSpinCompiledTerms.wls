scriptArgs = If[Length[$CommandLine] > 4, Drop[$CommandLine, 4], {}];
convention = If[scriptArgs === {}, "TypeII-Xi", First[scriptArgs]];

Needs["StringCode`"];
StringCode`InitStringCode[<|"theory" -> "TypeII", "CFT" -> "FlatSpace", "conventions" -> convention, "bracket" -> "Flat"|>];
Needs["StringCode`OPE`TypeII`FlatSpace`"];

getOutgoing = ToExpression["Private`getOutgoingOperatorsTensors"];
compileModel = ToExpression["Private`compileSpinProjectionSectorModel"];
witnessAssignment = ToExpression["Private`spinProjectionWitnessAssignment"];
factorSupport = ToExpression["Private`spinProjectionFactorOutputSpinSupport"];
scalarFactorValue = ToExpression["Private`spinProjectionScalarFactorValue"];
termValue = ToExpression["Private`spinProjectionTermValue"];
spinBasisState = ToExpression["Private`spinProjectionSpinBasisState"];
spinTypedIndices = ToExpression["Private`spinTypedIndices"];
evaluateTensorScalars = ToExpression["Private`spinProjectionEvaluateTensorScalars"];

ops = ToExpression["{R[S[{a1, \"chiral\"}, -1/2, {}, 0, z1]], R[S[{a2, \"chiral\"}, -1/2, {}, 0, z2]], R[S[{a3, \"chiral\"}, -1/2, {}, 0, z3]], R[S[{a4, \"chiral\"}, -1/2, {}, 0, z4]], R[S[{a5, \"chiral\"}, -1/2, {}, 0, z5]]}"];
outgoing = getOutgoing[ops, 0, 0, 1234];
model = compileModel["Holo", outgoing["holoOps"], 0, outgoing["holoData"]];
family = First[model["Families"]];
flatTerms = Flatten[Map[Function[pair, Map[<|"Output" -> pair[[1]], "Tensor" -> #|> &, pair[[2]]]], outgoing["holoData"]], 1];

exactMatchQ::usage =
  "exactMatchQ[left, right] returns True when two exact scalar values agree up to simplification.";
exactMatchQ[left_, right_] := TrueQ[left === right || Simplify[left == right]];

randomAllSpinCandidate::usage =
  "randomAllSpinCandidate[model] returns one random free-spin assignment over the full spin-basis domain.";
randomAllSpinCandidate[model_Association] := {
  Developer`ToPackedArray[RandomInteger[{1, 16}, Length[model["FreeSpinSymbols"]]]],
  Developer`ToPackedArray[ConstantArray[1, Length[model["FreeVectorGroups"]]]]
};

termSupport::usage =
  "termSupport[term, candidate] returns the allowed output-spin basis states for one compiled five-spin term under one candidate.";
termSupport[term_List, candidate : {freeSpins_List, freeVectors_List}] := Module[{supports},
  supports = Select[factorSupport[#, 1, freeSpins, freeVectors] & /@ term[[3]], ListQ];
  If[supports === {}, Range[16], Intersection @@ supports]
];

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
  "tensorRules[tensor, model, family, candidate, stateSpins, stateVectors, dummy] builds the concrete substitution rules used by the direct symbolic comparator.";
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

compiledTupleValue::usage =
  "compiledTupleValue[term, freeSpins, freeVectors, stateSpins, stateVectors, dummy] multiplies the compiled scalar factors for one fixed dummy tuple without performing the compiled dummy sum.";
compiledTupleValue[term_List, freeSpins_List, freeVectors_List, stateSpins_List, stateVectors_List, dummy_List] := Module[
  {values},
  values = scalarFactorValue[#, freeSpins, freeVectors, stateSpins, stateVectors, dummy] & /@ term[[3]];
  If[MemberQ[values, $Failed], Return[$Failed]];
  If[MemberQ[values, 0], 0, term[[2]] Times @@ values]
];

symbolicTupleValue::usage =
  "symbolicTupleValue[tensor, model, family, candidate, stateSpins, stateVectors, dummy] evaluates one original tensor term directly at one fixed dummy tuple.";
symbolicTupleValue[tensor_, model_Association, family_Association, candidate_, stateSpins_List, stateVectors_List, dummy_List] :=
  evaluateTensorScalars[tensor /. tensorRules[tensor, model, family, candidate, stateSpins, stateVectors, dummy]];

dummyTuples::usage =
  "dummyTuples[k] returns the ordered dummy-vector tuples used by the direct symbolic comparator.";
dummyTuples[k_Integer?NonNegative] := If[k == 0, {{}}, Tuples[Range[10], k]];

symbolicTermValue::usage =
  "symbolicTermValue[tensor, term, model, family, candidate, stateSpins, stateVectors] evaluates the original tensor by an explicit ordered dummy sum.";
symbolicTermValue[tensor_, term_List, model_Association, family_Association, candidate_, stateSpins_List, stateVectors_List] := Total[
  symbolicTupleValue[tensor, model, family, candidate, stateSpins, stateVectors, #] & /@ dummyTuples[term[[4]]]
];

supportingRandomCandidate::usage =
  "supportingRandomCandidate[model, term, seed] returns the first seeded random free-spin candidate whose term support is nonempty.";
supportingRandomCandidate[model_Association, term_List, seed_] := Module[{candidate},
  BlockRandom[
    SeedRandom[seed];
    Do[
      candidate = randomAllSpinCandidate[model];
      If[termSupport[term, candidate] =!= {}, Return[candidate]],
      {4096}
    ]
  ];
  $Failed
];

auditCase::usage =
  "auditCase[column, candidateKind, candidate] compares compiled and direct symbolic tuple/summed values for one term column.";
auditCase[column_Integer?Positive, candidateKind_String, candidate_] := Module[
  {term = family["Terms"][[column]], tensor = flatTerms[[column, "Tensor"]], support, state, tuples, tuple, compiledTuple, symbolicTuple, compiledTerm, symbolicTerm},
  If[candidate === $Failed, Return[<|"Column" -> column, "CandidateKind" -> candidateKind, "Candidate" -> $Failed, "SupportedQ" -> False|>]];
  support = termSupport[term, candidate];
  If[support === {}, Return[<|"Column" -> column, "CandidateKind" -> candidateKind, "Candidate" -> candidate, "SupportedQ" -> False|>]];
  state = {First[support]};
  tuples = dummyTuples[term[[4]]];
  tuple = FirstCase[
    tuples,
    dummy_ /; Module[{left, right},
      left = compiledTupleValue[term, candidate[[1]], candidate[[2]], state, {}, dummy];
      right = symbolicTupleValue[tensor, model, family, candidate, state, {}, dummy];
      !(exactMatchQ[left, 0] && exactMatchQ[right, 0])
    ],
    First[tuples]
  ];
  compiledTuple = compiledTupleValue[term, candidate[[1]], candidate[[2]], state, {}, tuple];
  symbolicTuple = symbolicTupleValue[tensor, model, family, candidate, state, {}, tuple];
  compiledTerm = termValue[term, candidate[[1]], candidate[[2]], state, {}];
  symbolicTerm = symbolicTermValue[tensor, term, model, family, candidate, state, {}];
  <|
    "Column" -> column,
    "CandidateKind" -> candidateKind,
    "Candidate" -> candidate,
    "SupportedQ" -> True,
    "State" -> state,
    "DummyTuple" -> tuple,
    "CompiledTupleValue" -> compiledTuple,
    "SymbolicTupleValue" -> symbolicTuple,
    "TupleMatchQ" -> exactMatchQ[compiledTuple, symbolicTuple],
    "CompiledTermValue" -> compiledTerm,
    "SymbolicTermValue" -> symbolicTerm,
    "TermMatchQ" -> exactMatchQ[compiledTerm, symbolicTerm]
  |>
];

representativeColumns = First /@ Partition[Cases[family["Terms"], term_ /; term[[4]] == 1 :> term[[1]]], 3];
heavyColumn = FirstCase[family["Terms"], term_ /; term[[4]] == 3 :> term[[1]]];
columns = Join[representativeColumns, {heavyColumn}];

Print @ InputForm @ <|
  "Convention" -> convention,
  "Columns" -> columns,
  "Cases" -> Flatten @ Table[
    With[
      {
        term = family["Terms"][[column]],
        iteratorCandidate = witnessAssignment[model, family, family["Terms"][[column]], 1234, 1],
        randomCandidate = supportingRandomCandidate[model, family["Terms"][[column]], 9000 + column]
      },
      {
        auditCase[column, "Witness", iteratorCandidate],
        auditCase[column, "RandomAllSpin", randomCandidate]
      }
    ],
    {column, columns}
  ]
|>;

Exit[];
