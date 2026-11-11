$Path = Prepend[$Path, Nest[DirectoryName, $InputFileName, 4]];
Needs["StringCode`"];
InitStringCode[<|"theory" -> "TypeII", "CFT" -> "FlatSpace", "conventions" -> "TypeII-Ashoke", "bracket" -> "Flat"|>];

(* Freeze the original implementation as an independent expansion oracle. *)
validationLegacy::usage = "validationLegacy is the unmodified expansion-based projection validator used as the regression oracle.";
validationLegacy[expr_] := Module[{terms, factorsOf, dollarTally},
  terms = If[Head[#] === Plus, List @@ #, {#}] & @ Expand[expr];
  factorsOf[term_] := Flatten[Replace[
    If[Head[term] === Times, List @@ term, {term}],
    p_^n_Integer?Positive :> ConstantArray[p, n], {1}]];
  dollarTally[term_] := Tally[Flatten[
    Cases[#, s_Symbol /; (StringContainsQ[SymbolName[s], "$"] &&
      !Private`projectionStrandProtectedQ[SymbolName[s]]),
      {0, Infinity}, Heads -> True] & /@ factorsOf[term]]];
  Cases[Map[{#, Select[dollarTally[#], Last[#] != 2 &]} &, terms],
    {_, v_ /; v =!= {}}]];
validationLegacyAssert::usage = "validationLegacyAssert freezes the old projection guard including inherited-index exemptions.";
validationLegacyAssert[expr_, inputExpr_] := Module[{viol, inputDummies},
  If[!TrueQ[Private`$StringCodeProjectionGuard], Return[expr]];
  viol = validationLegacy[expr];
  If[viol === {}, Return[expr]];
  inputDummies = DeleteDuplicates[Cases[inputExpr,
    s_Symbol /; StringContainsQ[SymbolName[s], "$"],
    {0, Infinity}, Heads -> True]];
  viol = Map[{#[[1]], Select[#[[2]], !MemberQ[inputDummies, First[#]] &]} &, viol];
  viol = Select[viol, #[[2]] =!= {} &];
  If[viol === {}, expr, $Failed]];

validationResults = {};
validationCheck::usage = "validationCheck records a substantive projection-validator regression check.";
validationCheck[label_, condition_] := Module[{ok = TrueQ[condition]},
  AppendTo[validationResults, <|"Check" -> label, "Passed" -> ok|>];
  Print[label, ": ", ok]];
validationNormalize::usage = "validationNormalize ignores diagnostic pair ordering when comparing equivalent violation lists.";
validationNormalize[v_List] := Sort[({#[[1]], Sort[#[[2]]]} & /@ v)];

validationExpressions = {
  0, 1, (x + y)^7,
  f[mu$71] g[mu$71], f[mu$71], f[mu$71]^2, f[mu$71]^3,
  (f[mu$71] + g[mu$71])^2,
  (f[mu$71] + g[nu$71])^2,
  (f[mu$71] g[mu$71] + f[nu$71] g[nu$71]) (x + y)^6,
  (f[mu$71] + g[mu$71]) (h[mu$71] + k[mu$71]),
  (f[mu$71] + g[nu$71]) (h[mu$71] + k[nu$71]),
  f[mu$71] (x + y) - x f[mu$71] - y f[mu$71],
  f[mu$71] (x + y)^2 - f[mu$71] (x^2 + 2 x y + y^2),
  f[mu$71] g[mu$71] (x + y) + f[nu$71] (x + y)^2,
  f[mu$71]/(1 + x + y), 1/f[mu$71]^2,
  f[mu$71 + nu$71]^2, ff$71[x] gg$71[x], ff$71[x]^2,
  f[t$71] g[tbar$71] h[mu$71] k[mu$71],
  (f[mu$71] g[mu$71] + f[nu$71] g[nu$71])^2,
  f[mu$71] (g[mu$71] + h[nu$71] k[nu$71]),
  f[mu$71] g[mu$71]/(1 + f[nu$71]),
  Sin[f[mu$71] + g[nu$71]]^2
};
Do[
  validationOld = validationNormalize[validationLegacy[validationExpressions[[i]]]];
  validationNew = validationNormalize[Private`projectionStrandViolations[validationExpressions[[i]]]];
  validationCheck["Legacy equivalence example " <> ToString[i], SameQ[validationOld, validationNew]],
  {i, Length[validationExpressions]}];

SeedRandom[261020];
validationAtoms = {x, y, f[mu$71], g[mu$71], f[nu$71], g[nu$71], f[mu$71] g[mu$71]};
validationRandomExpressions = Table[
  (Total[RandomChoice[validationAtoms, 3]])^RandomInteger[{1, 3}] *
    Total[RandomChoice[validationAtoms, 2]] -
    RandomChoice[validationAtoms] (x + y), {120}];
validationCheck["120 deterministic randomized factored polynomials agree with legacy",
  And @@ (SameQ[validationNormalize[validationLegacy[#]],
    validationNormalize[Private`projectionStrandViolations[#]]] & /@ validationRandomExpressions)];

validationCheck["Input-inherited index is exempt while a new paired index is checked",
  SameQ[Private`assertProjectionContracted[f[inherited$71] g[mu$71] h[mu$71], input[inherited$71]],
    f[inherited$71] g[mu$71] h[mu$71]]];
validationCheck["Input exemption does not hide a new unpaired index",
  SameQ[Quiet[Private`assertProjectionContracted[f[inherited$71] g[new$71], input[inherited$71]],
    Private`BracketProjection::strand], $Failed]];
validationCheck["Guard remains enabled", TrueQ[Private`$StringCodeProjectionGuard]];
validationCheck["Failure and acceptance decisions match the original guard",
  And @@ (SameQ[Quiet[validationLegacyAssert[#, input[inherited$71]], Private`BracketProjection::strand],
    Quiet[Private`assertProjectionContracted[#, input[inherited$71]], Private`BracketProjection::strand]] & /@
    validationExpressions)];

validationHuge = (1 + x1 + x2 + x3 + x4 + x5 + x6)^1000000 *
  (f[mu$71] g[mu$71] + f[nu$71] g[nu$71]);
validationTime = AbsoluteTiming[validationHugeResult = TimeConstrained[
  Private`projectionStrandViolations[validationHuge], 3, $TimedOut];][[1]];
validationCheck["Factored polynomial with astronomical monomial count validates without expansion",
  SameQ[validationHugeResult, {}]];
validationCheck["Factored validation completes within three seconds", validationTime < 3];

validationInheritedHuge = (1 + x1 + x2 + x3 + x4 + x5)^1000000 f[inherited$71];
validationCheck["Inherited dummies are removed before any expansion",
  SameQ[TimeConstrained[Private`assertProjectionContracted[validationInheritedHuge, input[inherited$71]],
    3, $TimedOut], validationInheritedHuge]];

(* Exercise the replacement through a real StringCode projected two-bracket. *)
validationSmoke = TimeConstrained[EffectiveBracket[
  R[c[0, 0], ct[0, 0], exp\[Phi]f[-1, 0], \[Psi][aa, 0, 0],
    exp\[Phi]tf[-1, 0], \[Psi]t[bb, 0, 0]],
  R[c[0, 0], ct[0, 0], exp\[Phi]f[-1, 0], \[Psi][cc, 0, 0],
    exp\[Phi]tf[-1, 0], \[Psi]t[dd, 0, 0]], 1, 1], 45, $TimedOut];
validationCheck["StringCode projected-bracket smoke test completes with guard enabled",
  FreeQ[validationSmoke, $Failed | $TimedOut | _Private`assertProjectionContracted | _Private`projectionStrandViolations]];

Export[FileNameJoin[{$TemporaryDirectory, "StringCodeProjectionGuardChecks.json"}],
  <|"AllPassed" -> And @@ Lookup[validationResults, "Passed"],
    "HugeFactoredValidationSeconds" -> validationTime,
    "Checks" -> validationResults|>, "RawJSON"];
Print["ALL ", And @@ Lookup[validationResults, "Passed"]];
Quit[If[And @@ Lookup[validationResults, "Passed"], 0, 1]];
