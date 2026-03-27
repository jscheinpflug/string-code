scriptArgs = If[Length[$CommandLine] > 4, Drop[$CommandLine, 4], {}];

If[scriptArgs === {},
  Print @ InputForm @ AssociationMap[
    ToExpression[
      StringTrim @ RunProcess[{First[$CommandLine], "-noprompt", "-script", $InputFileName, #}, "StandardOutput"],
      InputForm
    ] &,
    {"TypeII-Xi", "TypeII-Ashoke"}
  ];
  Exit[];
];

Needs["StringCode`"];
StringCode`InitStringCode[<|"theory" -> "TypeII", "CFT" -> "FlatSpace", "conventions" -> First[scriptArgs], "bracket" -> "Flat"|>];
Needs["StringCode`OPE`TypeII`FlatSpace`"];

getOutgoing = ToExpression["Private`getOutgoingOperatorsTensors"];
compileModel = ToExpression["Private`compileSpinProjectionSectorModel"];
assignmentIterator = ToExpression["Private`spinProjectionAssignmentIterator"];
candidateRows = ToExpression["Private`spinProjectionCandidateRows"];
solveSector = ToExpression["Private`solveCompiledSpinProjectionSector"];

ops = ToExpression["{R[S[{a1, \"chiral\"}, -1/2, {}, 0, z1]], R[S[{a2, \"chiral\"}, -1/2, {}, 0, z2]], R[S[{a3, \"chiral\"}, -1/2, {}, 0, z3]], R[S[{a4, \"chiral\"}, -1/2, {}, 0, z4]], R[S[{a5, \"chiral\"}, -1/2, {}, 0, z5]]}"];
outgoing = getOutgoing[ops, 0, 0, 1234];
model = compileModel["Holo", outgoing["holoOps"], 0, outgoing["holoData"]];

randomAllSpinCandidate::usage =
  "randomAllSpinCandidate[model] returns one random free-spin assignment over the full spin-basis domain.";
randomAllSpinCandidate[model_Association] := {
  Developer`ToPackedArray[RandomInteger[{1, 16}, Length[model["FreeSpinSymbols"]]]],
  Developer`ToPackedArray[ConstantArray[1, Length[model["FreeVectorGroups"]]]]
};

searchDigest::usage =
  "searchDigest[result] keeps only the stable raw-rank fields from one compiled search audit.";
searchDigest[result_Association] := KeyTake[
  result,
  {
    "VisitedCandidates",
    "AcceptedCandidateCount",
    "AcceptedIndices",
    "PivotColumns",
    "MissingColumns",
    "RankTrace",
    "FullRankQ"
  }
];

runRawSearch::usage =
  "runRawSearch[nextCandidate, limit] runs the raw compiled row builder without the pivot-basis solve workaround.";
runRawSearch[nextCandidate_, limit_Integer?Positive] := Module[
  {state = <|"Rows" -> {}, "Pivots" -> {}|>, accepted = 0, acceptedIndices = {}, rankTrace = {}, visited = 0, candidate, result},
  While[visited < limit,
    candidate = nextCandidate[];
    If[candidate === EndOfFile, Break[]];
    visited++;
    result = candidateRows[model, candidate, state, 1234];
    If[result["Rows"] === {}, Continue[]];
    state = result["Basis"];
    accepted++;
    AppendTo[acceptedIndices, visited];
    AppendTo[rankTrace, Length[state["Pivots"]]];
    If[Length[state["Pivots"]] >= model["VarCount"], Break[]]
  ];
  <|
    "VisitedCandidates" -> visited,
    "AcceptedCandidateCount" -> accepted,
    "AcceptedIndices" -> acceptedIndices,
    "PivotColumns" -> state["Pivots"],
    "MissingColumns" -> Complement[Range[model["VarCount"]], state["Pivots"]],
    "RankTrace" -> rankTrace,
    "FullRankQ" -> (Length[state["Pivots"]] >= model["VarCount"])
  |>
];

limit = 128;
deterministic = searchDigest @ runRawSearch[assignmentIterator[model, 1234], limit];
SeedRandom[123456];
randomAllSpin = searchDigest @ runRawSearch[Function[{}, randomAllSpinCandidate[model]], limit];
solved = solveSector[model, 1234];

Print @ InputForm @ <|
  "Convention" -> First[scriptArgs],
  "Limit" -> limit,
  "VarCount" -> model["VarCount"],
  "TermDummyCounts" -> Counts[First[model["Families"]]["Terms"][[All, 4]]],
  "Deterministic" -> deterministic,
  "RandomAllSpin" -> randomAllSpin,
  "Solver" -> <|
    "ReturnedQ" -> (solved =!= $Failed),
    "Attempts" -> If[AssociationQ[solved], solved["Attempts"], Missing["Failed"]],
    "PivotBasisOnlyQ" -> (AssociationQ[solved] && !deterministic["FullRankQ"])
  |>
|>;

Exit[];
