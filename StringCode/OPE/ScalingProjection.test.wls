Needs["StringCode`"];
InitStringCode[<|
  "theory" -> "TypeII",
  "CFT" -> "FlatSpace",
  "conventions" -> "TypeII-Ashoke",
  "bracket" -> "Flat"
|>];

scalingProjectionResults = {};
scalingProjectionCheck::usage =
  "scalingProjectionCheck[label, condition] records one scaling-projection regression assertion.";
scalingProjectionCheck[label_, condition_] := Module[{passed = TrueQ[condition]},
  AppendTo[scalingProjectionResults, {label, passed}];
  Print[label, ": ", passed]
];

Clear[scale, insertion, modulus];

normalizedFixed = Private`normalizeScalingParameter[
  scale - modulus scale,
  scale
];
scalingProjectionCheck[
  "OPE normalizer extracts scale from a unit-position difference",
  TrueQ[Simplify[normalizedFixed - scale (1 - modulus)] === 0]
];

normalizedModeFixed = Private`normalizeScalingParameterForModeProjection[
  scale - modulus scale,
  scale
];
scalingProjectionCheck[
  "mode normalizer extracts scale from a unit-position difference",
  TrueQ[Simplify[normalizedModeFixed - scale (1 - modulus)] === 0]
];

genericProjection = Private`projectHolo[
  1/(insertion scale - modulus scale),
  -1,
  scale
] /. insertion -> 1;
fixedProjection = Private`projectHolo[
  1/(scale - modulus scale),
  -1,
  scale
];
scalingProjectionCheck[
  "specializing an insertion to one commutes with scalar OPE projection",
  TrueQ[Simplify[genericProjection - fixedProjection] === 0] &&
    TrueQ[Simplify[fixedProjection - 1/(1 - modulus)] === 0]
];

Print["ALL=", And @@ scalingProjectionResults[[All, 2]]];
Quit[If[And @@ scalingProjectionResults[[All, 2]], 0, 1]];
