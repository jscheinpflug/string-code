(* Loaded by Solve.m inside the shared Private` context. *)

spinProjectionLastSolveResult::usage =
  "spinProjectionLastSolveResult holds the latest public solve, including rejection diagnostics.";
spinProjectionLastSolveResult = Missing["NoSolveYet"];

spinProjectionValidationPolicy0::usage =
  "spinProjectionValidationPolicy0[] specifies mandatory bounded validation, not exhaustive certification.";
spinProjectionValidationPolicy0[] := <|
  "Version" -> 1, "ProbeSeconds" -> 20, "PhaseSeconds" -> 120,
  "FailFastSupport" -> 8, "RoutineSupport" -> 16, "RoutineUniform" -> 24, "RelabelProbes" -> 8
|>;

spinProjectionValidationBadExpressionQ0::usage =
  "spinProjectionValidationBadExpressionQ0[expr] rejects computation failures and unevaluated OPE/bosonization calls before cancellation.";
spinProjectionValidationBadExpressionQ0[expr_] := !FreeQ[expr, $Failed | $Aborted | _Failure | _Missing] ||
  !FreeQ[expr, x_ /; With[{h = Head[x]}, Head[h] === Symbol &&
    MemberQ[{"OPE", "OPEProjected", "OPEProjectedHolo", "OPEProjectedAntiHolo", "Bosonize"}, SymbolName[h]]]];

spinProjectionValidationPrediction0::usage =
  "spinProjectionValidationPrediction0[artifact, coefficients, candidate] reconstructs all output components without pivot-row or output-support pruning.";
spinProjectionValidationPrediction0[artifact_Association, coefficients_List, candidate_List] := Module[{data},
  data = spinProjectionArtifactExhaustiveFamilyRows0[artifact, #, candidate] & /@ artifact["Families"];
  If[!FreeQ[data, $Failed | $Aborted | _Failure | _Missing], Return[$Failed]];
  Expand[Total[Flatten[(First[#] (Last[#].coefficients) & /@ #["FamilyRows"]) & /@ data]]]
];

spinProjectionValidationProbe0::usage =
  "spinProjectionValidationProbe0[artifact, coefficients, candidate, seconds] checks the complete reference-minus-prediction output exactly and fails closed on timeouts or unresolved residuals.";
spinProjectionValidationProbe0[artifact_Association, coefficients_List, candidate_List, seconds_] := Module[{answer},
  answer = TimeConstrained[Quiet[Check[Module[{inputs, reference, prediction, residual},
    inputs = spinProjectionConcreteInputs[artifact, candidate];
    reference = spinProjectionSectorEvaluation[artifact["Sector"], artifact["Weight"], inputs];
    prediction = spinProjectionValidationPrediction0[artifact, coefficients, candidate];
    If[spinProjectionValidationBadExpressionQ0[{reference, prediction}],
      Return[<|"PassedQ" -> False, "Status" -> "EvaluationFailure", "Candidate" -> candidate|>]];
    residual = Factor[reference - prediction];
    <|"PassedQ" -> TrueQ[residual === 0], "Status" -> If[TrueQ[residual === 0], "Passed", "ResidualNotZero"],
      "Candidate" -> candidate, "ReferenceZeroQ" -> TrueQ[reference === 0], "Residual" -> residual|>
  ], $Failed]], seconds, $Aborted];
  If[AssociationQ[answer], answer,
    <|"PassedQ" -> False, "Status" -> If[answer === $Aborted, "Timeout", "EvaluationFailure"], "Candidate" -> candidate|>]
];

spinProjectionValidationSupport0::usage =
  "spinProjectionValidationSupport0[artifact, seed, count] obtains deterministic support-directed probes, including degenerate zero inputs.";
spinProjectionValidationSupport0[artifact_Association, seed_, count_Integer] := Module[{next, result = {}, candidate, failed = False},
  next = spinProjectionAssignmentIterator[artifact, seed];
  If[next === $Failed, Return[$Failed]];
  Do[candidate = next[]; If[candidate === EndOfFile, Break[]];
    If[!MatchQ[candidate, {_List, _List}], failed = True; Break[]];
    AppendTo[result, candidate], {count}];
  If[failed, $Failed, DeleteDuplicates[result]]
];

spinProjectionValidationUniform0::usage =
  "spinProjectionValidationUniform0[artifact, seed, count] generates uniform probes without modifying the caller's random stream.";
spinProjectionValidationUniform0[artifact_Association, seed_, count_Integer] := BlockRandom[
  SeedRandom[seed];
  DeleteDuplicates[Table[{
    (RandomInteger[{1, Length[spinProjectionSpinBasisState[#]]}] & /@ artifact["FreeSpinChiralities"]),
    RandomInteger[{1, Length[vectors]}, Length[artifact["FreeVectorGroups"]]]
  }, {count}]]
];

spinProjectionValidationRepeated0::usage =
  "spinProjectionValidationRepeated0[candidates] generates up to 28 repeated-index probes, testing rather than assuming vanishing coincident fermion products.";
spinProjectionValidationRepeated0[candidates_List] := DeleteDuplicates[Flatten[
  Function[candidate, Module[{spins = candidate[[1]], vv = candidate[[2]], pairs},
    If[Length[vv] < 2, {},
      pairs = Take[Subsets[Range[Length[vv]], {2}], UpTo[6]];
      Join[{{spins, ConstantArray[First[vv], Length[vv]]}},
        ({spins, ReplacePart[vv, #[[2]] -> vv[[#[[1]]]]]} & /@ pairs)]
    ]
  ]] /@ Take[candidates, UpTo[4]], 1]];

spinProjectionValidationBatch0::usage =
  "spinProjectionValidationBatch0[artifact, coefficients, candidates, seconds] stops at the first failed component and retains the candidate and residual.";
spinProjectionValidationBatch0[artifact_Association, coefficients_List, candidates_List, seconds_] := Module[{checks = {}, check, failure = None},
  If[candidates === {}, Return[<|"PassedQ" -> False, "Status" -> "NoValidationCandidates", "CheckedCount" -> 0|>]];
  Do[
    check = spinProjectionValidationProbe0[artifact, coefficients, candidate, seconds];
    AppendTo[checks, check];
    If[!TrueQ[check["PassedQ"]], failure = <|"PassedQ" -> False, "Status" -> check["Status"],
      "CheckedCount" -> Length[checks], "Failure" -> check, "Checks" -> checks|>; Break[]],
    {candidate, candidates}];
  If[AssociationQ[failure], failure,
    <|"PassedQ" -> True, "Status" -> "Passed", "CheckedCount" -> Length[checks], "Checks" -> checks|>]
];

spinProjectionValidationRelabel0::usage =
  "spinProjectionValidationRelabel0[artifact, fit, candidates, seed] refits with reversed index-name ordering and compares explicit components including normal-ordering signs; the auxiliary fit is never an accepted public solution.";
spinProjectionValidationRelabel0[artifact_Association, fit_Association, candidates_List, seed_] := Module[
  {ss, vs, rules, inverse, associations, ops, factor, renamed, other, spins, vv, mapped,
    originalPrediction, renamedPrediction, residual, count = 0, failure = None},
  ss = artifact["FreeSpinSymbols"]; vs = DeleteDuplicates[Flatten[artifact["FreeVectorGroups"]]];
  rules = Join[
    Thread[ss -> Table[Symbol["Private`validationSpin" <> ToString[Length[ss] - i + 1]], {i, Length[ss]}]],
    Thread[vs -> Table[Symbol["Private`validationVector" <> ToString[Length[vs] - i + 1]], {i, Length[vs]}]]
  ];
  inverse = Reverse /@ rules;
  associations = spinProjectionOperatorAssociation /@ (artifact["Ops"] /. rules);
  If[!AllTrue[associations, AssociationQ[#] && Length[#] == 1 && RTest[First[Keys[#]]] &],
    Return[<|"PassedQ" -> False, "Status" -> "RelabelInputFailure"|>]];
  ops = First[Keys[#]] & /@ associations;
  factor = Times @@ (First[Values[#]] & /@ associations);
  renamed = buildSectorArtifact[artifact["Sector"], ops, artifact["Weight"], seed];
  If[!AssociationQ[renamed] || renamed["Mode"] =!= "SpinProjection",
    Return[<|"PassedQ" -> False, "Status" -> "RelabelArtifactFailure"|>]];
  other = spinProjectionFitSectorArtifact0[renamed, seed];
  If[!TrueQ[other["CompleteQ"]], Return[<|"PassedQ" -> False, "Status" -> "RelabelFitIncomplete"|>]];
  Do[
    spins = AssociationThread[ss -> candidate[[1]]];
    vv = Association[Flatten[MapThread[Thread[#1 -> #2] &, {artifact["FreeVectorGroups"], candidate[[2]]}]]];
    mapped = {Lookup[spins, renamed["FreeSpinSymbols"] /. inverse],
      Lookup[vv, First /@ renamed["FreeVectorGroups"] /. inverse]};
    residual = TimeConstrained[
      originalPrediction = spinProjectionValidationPrediction0[artifact, fit["CoeffVector"], candidate];
      renamedPrediction = factor spinProjectionValidationPrediction0[renamed, other["CoeffVector"], mapped];
      If[spinProjectionValidationBadExpressionQ0[{originalPrediction, renamedPrediction}],
        $Failed, Factor[originalPrediction - renamedPrediction]],
      spinProjectionValidationPolicy0[]["ProbeSeconds"], $Aborted];
    If[MemberQ[{$Failed, $Aborted}, residual],
      failure = <|"PassedQ" -> False, "Status" -> If[residual === $Aborted, "Timeout", "RelabelEvaluationFailure"], "Candidate" -> candidate|>; Break[]];
    count++;
    If[residual =!= 0, failure = <|"PassedQ" -> False, "Status" -> "RelabelMismatch",
      "CheckedCount" -> count, "Candidate" -> candidate, "Residual" -> residual|>; Break[]],
    {candidate, candidates}];
  If[AssociationQ[failure], failure,
    <|"PassedQ" -> (count > 0), "Status" -> If[count > 0, "Passed", "NoValidationCandidates"], "CheckedCount" -> count|>]
];

spinProjectionValidateSolution0::usage =
  "spinProjectionValidateSolution0[artifact, fit, seed] requires fail-fast, routine component and relabel-refit validation to pass. Phase deadlines and evaluator failures never count as success.";
spinProjectionValidateSolution0[artifact_Association, fit_Association, seed_] := Module[
  {policy = spinProjectionValidationPolicy0[], fast, routine, support, samples, repeats,
    fastCandidates, routineCandidates, relabel, summary, validationSeed},
  If[artifact["Mode"] === "ClosedForm", Return[<|"PassedQ" -> True, "Status" -> "NotApplicableClosedForm",
    "FailFast" -> <|"PassedQ" -> True, "Status" -> "NotApplicable"|>,
    "RoutineRegression" -> <|"PassedQ" -> True, "Status" -> "NotApplicable"|>|>]];
  If[artifact["Mode"] =!= "SpinProjection", Return[<|"PassedQ" -> False, "Status" -> "InvalidArtifact",
    "FailFast" -> <|"PassedQ" -> False, "Status" -> "NotRun"|>,
    "RoutineRegression" -> <|"PassedQ" -> False, "Status" -> "NotRun"|>|>]];
  validationSeed = Hash[{"SpinValidation-v1", seed}, "CRC32"];
  fast = TimeConstrained[Quiet[Check[
    support = spinProjectionValidationSupport0[artifact, validationSeed, policy["FailFastSupport"]];
    If[support === $Failed, <|"PassedQ" -> False, "Status" -> "CandidateGenerationFailure"|>,
      repeats = spinProjectionValidationRepeated0[Join[fit["WitnessAssignments"], support]];
      fastCandidates = DeleteDuplicates[Join[Take[fit["WitnessAssignments"], UpTo[8]], repeats, support]];
      spinProjectionValidationBatch0[artifact, fit["CoeffVector"], fastCandidates, policy["ProbeSeconds"]]
    ], $Failed]], policy["PhaseSeconds"], $Aborted];
  If[!AssociationQ[fast], fast = <|"PassedQ" -> False, "Status" -> If[fast === $Aborted, "Timeout", "EvaluationFailure"]|>];
  If[!TrueQ[fast["PassedQ"]], Return[<|"PassedQ" -> False, "Status" -> "FailFastRejected", "Policy" -> policy,
    "FailFast" -> fast, "RoutineRegression" -> <|"PassedQ" -> False, "Status" -> "NotRun"|>|>]];
  routine = TimeConstrained[Quiet[Check[
    support = spinProjectionValidationSupport0[artifact, validationSeed + 1, policy["RoutineSupport"]];
    samples = spinProjectionValidationUniform0[artifact, validationSeed + 2, policy["RoutineUniform"]];
    If[support === $Failed, <|"PassedQ" -> False, "Status" -> "CandidateGenerationFailure"|>,
      routineCandidates = DeleteDuplicates[Join[support, samples]];
      summary = spinProjectionValidationBatch0[artifact, fit["CoeffVector"], routineCandidates, policy["ProbeSeconds"]];
      If[!TrueQ[summary["PassedQ"]], summary,
        relabel = spinProjectionValidationRelabel0[artifact, fit, Take[routineCandidates, UpTo[policy["RelabelProbes"]]], seed];
        Join[summary, <|"PassedQ" -> TrueQ[relabel["PassedQ"]], "Status" -> If[TrueQ[relabel["PassedQ"]], "Passed", "RelabelRejected"], "Relabel" -> relabel|>]
      ]
    ], $Failed]], policy["PhaseSeconds"], $Aborted];
  If[!AssociationQ[routine], routine = <|"PassedQ" -> False, "Status" -> If[routine === $Aborted, "Timeout", "EvaluationFailure"]|>];
  <|"PassedQ" -> TrueQ[routine["PassedQ"]], "Status" -> If[TrueQ[routine["PassedQ"]], "PassedSampledValidation", "RoutineRegressionRejected"],
    "Policy" -> policy, "FailFast" -> fast, "RoutineRegression" -> routine|>
];

