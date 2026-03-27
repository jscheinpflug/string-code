Needs["StringCode`"];
StringCode`InitStringCode[<|"theory" -> "TypeII", "CFT" -> "FlatSpace", "conventions" -> "TypeII-Ashoke", "bracket" -> "Flat"|>];
Needs["StringCode`OPE`TypeII`FlatSpace`"];

getOutgoing = ToExpression["Private`getOutgoingOperatorsTensors"];
compileModel = ToExpression["Private`compileSpinProjectionSectorModel"];
assignmentIterator = ToExpression["Private`spinProjectionAssignmentIterator"];
factorSupport = ToExpression["Private`spinProjectionFactorOutputSpinSupport"];
termValue = ToExpression["Private`spinProjectionTermValue"];

ops = ToExpression["{R[S[{a1, \"chiral\"}, -1/2, {}, 0, z1]], R[S[{a2, \"chiral\"}, -1/2, {}, 0, z2]], R[S[{a3, \"chiral\"}, -1/2, {}, 0, z3]], R[S[{a4, \"chiral\"}, -1/2, {}, 0, z4]], R[S[{a5, \"chiral\"}, -1/2, {}, 0, z5]]}"];
outgoing = getOutgoing[ops, 0, 0, 1234];
model = compileModel["Holo", outgoing["holoOps"], 0, outgoing["holoData"]];
family = First[model["Families"]];
candidate = assignmentIterator[model, 1234][];
terms = family["Terms"];
heavyTerm = FirstCase[terms, term_ /; term[[4]] == 3];
heavySupport = With[
  {lists = Select[factorSupport[#, 1, candidate[[1]], candidate[[2]]] & /@ heavyTerm[[3]], ListQ]},
  If[lists === {}, Range[16], Intersection @@ lists]
];
probeState = {First[heavySupport]};

termTimings = Table[
  First @ AbsoluteTiming[termValue[terms[[k]], candidate[[1]], candidate[[2]], probeState, {}]],
  {k, Length[terms]}
];
heavyTermTiming = First @ AbsoluteTiming[
  heavyTermValue = termValue[heavyTerm, candidate[[1]], candidate[[2]], probeState, {}]
];

Print @ InputForm @ <|
  "termDummyCounts" -> Counts[terms[[All, 4]]],
  "termTimings" -> termTimings,
  "heavyTerm" -> heavyTerm,
  "heavySupport" -> heavySupport,
  "heavyTermTiming" -> heavyTermTiming,
  "heavyTermValueZeroQ" -> (heavyTermValue === 0)
|>;

Exit[];
