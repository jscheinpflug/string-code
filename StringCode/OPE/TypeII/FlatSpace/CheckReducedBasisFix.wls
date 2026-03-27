scriptArgs = If[Length[$CommandLine] > 4, Drop[$CommandLine, 4], {}];
convention = If[scriptArgs === {}, "TypeII-Xi", First[scriptArgs]];

Needs["StringCode`"];
StringCode`InitStringCode[<|"theory" -> "TypeII", "CFT" -> "FlatSpace", "conventions" -> convention, "bracket" -> "Flat"|>];
Needs["StringCode`OPE`TypeII`FlatSpace`"];

getOutgoing = ToExpression["Private`getOutgoingOperatorsTensors"];
compileModel = ToExpression["Private`compileSpinProjectionSectorModel"];
assignmentIterator = ToExpression["Private`spinProjectionAssignmentIterator"];
candidateRows = ToExpression["Private`spinProjectionCandidateRows"];
concreteInputs = ToExpression["Private`spinProjectionConcreteInputs"];
projectInputs = ToExpression["Private`spinProjectionProjectInputs"];
operatorAssociation = ToExpression["Private`spinProjectionOperatorAssociation"];
exprWeight = ToExpression["Private`spinProjectionExpressionWeight"];

ops = ToExpression["{R[S[{a1, \"chiral\"}, -1/2, {}, 0, z1]], R[S[{a2, \"chiral\"}, -1/2, {}, 0, z2]], R[S[{a3, \"chiral\"}, -1/2, {}, 0, z3]], R[S[{a4, \"chiral\"}, -1/2, {}, 0, z4]], R[S[{a5, \"chiral\"}, -1/2, {}, 0, z5]]}"];
outgoing = getOutgoing[ops, 0, 0, 1234];
model = compileModel["Holo", outgoing["holoOps"], 0, outgoing["holoData"]];

exactMatchQ::usage =
  "exactMatchQ[left, right] returns True when two exact values agree up to simplification.";
exactMatchQ[left_, right_] := TrueQ[left === right || Simplify[left == right]];

randomAllSpinCandidate::usage =
  "randomAllSpinCandidate[model] returns one random free-spin assignment over the full spin-basis domain.";
randomAllSpinCandidate[model_Association] := {
  Developer`ToPackedArray[RandomInteger[{1, 16}, Length[model["FreeSpinSymbols"]]]],
  Developer`ToPackedArray[ConstantArray[1, Length[model["FreeVectorGroups"]]]]
};

targetWeight::usage =
  "targetWeight stores the compiled projected target weight used for held-out validation.";
targetWeight = Lookup[model, "TargetWeight", model["Weight"]];
If[targetWeight === None,
  targetWeight = model["Weight"] - Total[
    exprWeight[#, model["Sector"]] & /@
      concreteInputs[
        model,
        {
          Developer`ToPackedArray[ConstantArray[1, Length[model["FreeSpinSymbols"]]]],
          Developer`ToPackedArray[ConstantArray[1, Length[model["FreeVectorGroups"]]]]
        }
      ]
  ]
];

runRawSearch::usage =
  "runRawSearch[nextCandidate, limit] returns the accepted compiled rows gathered before the pivot-basis solve workaround.";
runRawSearch[nextCandidate_, limit_Integer?Positive] := Module[
  {state = <|"Rows" -> {}, "Pivots" -> {}|>, acceptedCandidates = {}, acceptedRows = {}, acceptedKeys = {}, visited = 0, candidate, accepted},
  While[visited < limit,
    candidate = nextCandidate[];
    If[candidate === EndOfFile, Break[]];
    visited++;
    accepted = candidateRows[model, candidate, state, 1234];
    If[accepted["Rows"] === {}, Continue[]];
    state = accepted["Basis"];
    AppendTo[acceptedCandidates, candidate];
    acceptedRows = Join[acceptedRows, accepted["Rows"]];
    acceptedKeys = Join[acceptedKeys, accepted["Keys"]];
    If[Length[state["Pivots"]] >= model["VarCount"], Break[]]
  ];
  <|
    "VisitedCandidates" -> visited,
    "AcceptedCandidates" -> acceptedCandidates,
    "AcceptedRows" -> acceptedRows,
    "AcceptedKeys" -> acceptedKeys,
    "Basis" -> state,
    "PivotColumns" -> state["Pivots"],
    "MissingColumns" -> Complement[Range[model["VarCount"]], state["Pivots"]]
  |>
];

raw::usage =
  "raw stores the raw accepted compiled rows gathered before the pivot-basis solve workaround.";
raw = runRawSearch[assignmentIterator[model, 1234], 128];
pivots = raw["PivotColumns"];
dropped = raw["MissingColumns"];
basisRows = raw["Basis"]["Rows"];
relations = AssociationThread[dropped, basisRows[[All, #]] & /@ dropped];

trainingSystem::usage =
  "trainingSystem rebuilds the accepted compiled equations used to test reduced-basis reconstruction.";
trainingSystem[] := Module[
  {next = assignmentIterator[model, 1234], exactBasis = <|"Rows" -> {}, "Pivots" -> {}|>, rows = {}, rhs = {}, visited = 0, candidate, accepted, lhsAssoc},
  While[visited < 128,
    candidate = next[];
    If[candidate === EndOfFile, Break[]];
    visited++;
    accepted = candidateRows[model, candidate, exactBasis, 1234];
    If[accepted["Rows"] === {}, Continue[]];
    lhsAssoc = operatorAssociation @ projectInputs[model["Sector"], model["Weight"], targetWeight, concreteInputs[model, candidate]];
    exactBasis = accepted["Basis"];
    rows = Join[rows, accepted["Rows"]];
    rhs = Join[rhs, Lookup[lhsAssoc, #, 0] & /@ accepted["Keys"]];
  ];
  <|"Rows" -> rows, "Rhs" -> rhs, "Basis" -> exactBasis|>
];

system = trainingSystem[];
pivotCoeffs = LinearSolve[system["Rows"][[All, pivots]], system["Rhs"]];
zeroDroppedCoeffs = ConstantArray[0, model["VarCount"]];
zeroDroppedCoeffs[[pivots]] = pivotCoeffs;
fullCoeffs = ConstantArray[0, model["VarCount"]];
fullCoeffs[[pivots]] = pivotCoeffs;
Scan[(fullCoeffs[[#]] = basisRows[[All, #]].pivotCoeffs) &, dropped];

rowRelationQ::usage =
  "rowRelationQ[row] checks whether one coefficient row obeys the derived nonpivot-column relations.";
rowRelationQ[row_List] := AllTrue[dropped, exactMatchQ[row[[#]], row[[pivots]].relations[#]] &];

candidateCheck::usage =
  "candidateCheck[candidate] tests the reduced-basis reconstruction on one held-out concrete candidate.";
candidateCheck[candidate_] := Module[{accepted, lhsAssoc, observed, zeroDroppedPredicted, reconstructedPredicted},
  accepted = candidateRows[model, candidate, <|"Rows" -> {}, "Pivots" -> {}|>, 1234];
  If[accepted["Rows"] === {}, Return[Missing["NoRows"]]];
  lhsAssoc = operatorAssociation @ projectInputs[model["Sector"], model["Weight"], targetWeight, concreteInputs[model, candidate]];
  observed = Lookup[lhsAssoc, #, 0] & /@ accepted["Keys"];
  zeroDroppedPredicted = accepted["Rows"].zeroDroppedCoeffs;
  reconstructedPredicted = accepted["Rows"].fullCoeffs;
  <|
    "Candidate" -> candidate,
    "RowCount" -> Length[accepted["Rows"]],
    "RelationOK" -> AllTrue[accepted["Rows"], rowRelationQ],
    "ZeroDroppedPredictionOK" -> (Length[zeroDroppedPredicted] == Length[observed] && AllTrue[MapThread[exactMatchQ, {zeroDroppedPredicted, observed}], TrueQ]),
    "ReconstructedPredictionOK" -> (Length[reconstructedPredicted] == Length[observed] && AllTrue[MapThread[exactMatchQ, {reconstructedPredicted, observed}], TrueQ]),
    "FirstMismatch" -> FirstCase[
      Transpose[{accepted["Keys"], zeroDroppedPredicted, reconstructedPredicted, observed}],
      {key_, zeroPred_, reconPred_, obs_} /; !exactMatchQ[zeroPred, obs] || !exactMatchQ[reconPred, obs] :> <|"Key" -> key, "ZeroDroppedPredicted" -> zeroPred, "ReconstructedPredicted" -> reconPred, "Observed" -> obs|>,
      Missing["NoMismatch"]
    ]
  |>
];

collectChecks::usage =
  "collectChecks[nextCandidate, want] gathers the first held-out candidates that produce nonempty compiled equations.";
collectChecks[nextCandidate_, want_Integer?Positive] := Module[{checks = {}, tries = 0, candidate, check},
  While[Length[checks] < want && tries < 512,
    candidate = nextCandidate[];
    If[candidate === EndOfFile, Break[]];
    tries++;
    check = candidateCheck[candidate];
    If[AssociationQ[check], AppendTo[checks, check]];
  ];
  <|"Checks" -> checks, "Tried" -> tries|>
];

supportChecks = collectChecks[assignmentIterator[model, 4321], 8];
SeedRandom[24680];
randomChecks = collectChecks[Function[{}, randomAllSpinCandidate[model]], 8];

Print @ InputForm @ <|
  "Convention" -> convention,
  "RawRank" -> <|
    "AcceptedRows" -> Length[system["Rows"]],
    "PivotColumns" -> pivots,
    "MissingColumns" -> dropped
  |>,
  "ColumnRelations" -> AssociationMap[relations[#] &, dropped],
  "SolvedCoefficients" -> AssociationThread[Range[model["VarCount"]], fullCoeffs],
  "ZeroDroppedRepresentative" -> AssociationThread[Range[model["VarCount"]], zeroDroppedCoeffs],
  "TrainingRowsAllSatisfyRelationsQ" -> AllTrue[system["Rows"], rowRelationQ],
  "HeldOutSupportDriven" -> <|
    "Tried" -> supportChecks["Tried"],
    "Count" -> Length[supportChecks["Checks"]],
    "AllRelationOKQ" -> AllTrue[Lookup[supportChecks["Checks"], "RelationOK", {}], TrueQ],
    "AllZeroDroppedPredictionOKQ" -> AllTrue[Lookup[supportChecks["Checks"], "ZeroDroppedPredictionOK", {}], TrueQ],
    "AllReconstructedPredictionOKQ" -> AllTrue[Lookup[supportChecks["Checks"], "ReconstructedPredictionOK", {}], TrueQ],
    "Checks" -> supportChecks["Checks"]
  |>,
  "HeldOutRandomAllSpin" -> <|
    "Tried" -> randomChecks["Tried"],
    "Count" -> Length[randomChecks["Checks"]],
    "AllRelationOKQ" -> AllTrue[Lookup[randomChecks["Checks"], "RelationOK", {}], TrueQ],
    "AllZeroDroppedPredictionOKQ" -> AllTrue[Lookup[randomChecks["Checks"], "ZeroDroppedPredictionOK", {}], TrueQ],
    "AllReconstructedPredictionOKQ" -> AllTrue[Lookup[randomChecks["Checks"], "ReconstructedPredictionOK", {}], TrueQ],
    "Checks" -> randomChecks["Checks"]
  |>
|>;

Exit[];
