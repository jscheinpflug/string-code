$Path = Prepend[$Path, FileNameJoin[{Directory[], "prototype-string-code"}]];
Needs["StringCode`"];
StringCode`InitStringCode[
  <|"theory" -> "TypeII", "CFT" -> "FlatSpace",
    "conventions" -> "TypeII-Ashoke", "bracket" -> "Flat"|>
];

parseArgs[raw_] := Module[
  {opts = <|"case" -> All, "family" -> All, "samples" -> 3,
      "emit-json" -> "/tmp/string-code-mathematica-ope.json",
      "verify-zig-json" -> None|>,
   i = 1},
  While[i <= Length[raw],
    Switch[raw[[i]],
      "--case", i++; opts["case"] = raw[[i]],
      "--family", i++; opts["family"] = raw[[i]],
      "--samples", i++; opts["samples"] = ToExpression[raw[[i]], InputForm],
      "--emit-json", i++; opts["emit-json"] = raw[[i]],
      "--verify-zig-json", i++; opts["verify-zig-json"] = raw[[i]],
      _, Print["unknown argument: ", raw[[i]]]; Quit[2]
    ];
    i++;
  ];
  opts
];

termsCount[expr_] := Module[{expanded = Expand[expr]},
  If[expanded === 0, 0, If[Head[expanded] === Plus, Length[List @@ expanded], 1]]
];

canonicalHash[expr_] := IntegerString[
  Hash[ToString[InputForm[Expand[expr]]], "SHA256"],
  16,
  64
];

rowValue[row_, key_] := Lookup[If[AssociationQ[row], row, Association[row]], key, Missing[key]];

numericOverallFactor[actual_, candidate_] := Module[
  {expandedActual = Expand[actual], expandedCandidate = Expand[candidate],
   ratio},
  Which[
    expandedActual === 0 && expandedCandidate === 0, 1,
    expandedActual === 0 || expandedCandidate === 0, Missing["not-proportional"],
    True,
      ratio = Quiet[FullSimplify[expandedActual/expandedCandidate]];
      If[TrueQ[NumericQ[N[ratio]]] &&
         TrueQ[FullSimplify[Expand[expandedActual - ratio expandedCandidate] === 0]],
        ratio,
        Missing["not-proportional"]
      ]
  ]
];

zigVerificationFields[row_, expr_, zigByCase_] := Module[
  {zigRow, zigExpressionString, zigExpression, exact, factor},
  zigRow = Lookup[zigByCase, row["case"], Missing["zig-case"]];
  If[MissingQ[zigRow], Return[<|"zig_expression_present" -> False|>]];
  zigExpressionString = rowValue[zigRow, "zig_expression"];
  If[MissingQ[zigExpressionString], Return[<|"zig_expression_present" -> False|>]];
  zigExpression = ToExpression[zigExpressionString, InputForm];
  exact = TrueQ[FullSimplify[Expand[expr - zigExpression] === 0]];
  factor = numericOverallFactor[expr, zigExpression];
  <|
    "zig_expression_present" -> True,
    "zig_expression_equal" -> exact,
    "zig_expression_proportional" -> ! MissingQ[factor],
    "zig_expression_factor" -> If[MissingQ[factor], "not-proportional", ToString[InputForm[factor]]]
  |>
];

timedOPEProjectedSeconds[code_, samples_Integer] := Module[{times},
  times = Table[First@AbsoluteTiming[ToExpression[code, InputForm]], {samples}];
  Median[times]
];

caseRows = {
  <|"case" -> "bc-1-pair-w0", "family" -> "bc",
    "code" -> "OPEProjected[0,0][R[b[0,z1]],R[c[0,z2]]]"|>,
  <|"case" -> "bc-derivative-pair-w0", "family" -> "bc",
    "code" -> "OPEProjected[0,0][R[b[1,z1]],R[c[2,z2]]]"|>,
  <|"case" -> "bc-2-pairs-w0", "family" -> "bc",
    "code" -> "OPEProjected[0,0][R[b[0,z1],b[1,z1]],R[c[0,z2],c[1,z2]]]"|>,
  <|"case" -> "bc-6-pairs-w0", "family" -> "bc",
    "code" -> "OPEProjected[0,0][R[b[0,z1],b[1,z1],b[2,z1],b[3,z1],b[4,z1],b[5,z1]],R[c[0,z2],c[1,z2],c[2,z2],c[3,z2],c[4,z2],c[5,z2]]]"|>,
  <|"case" -> "fermion-1-pair-w0", "family" -> "fermion",
    "code" -> "OPEProjected[0,0][R[\[Psi][mu1,0,z1]],R[\[Psi][mu1,1,z2]]]"|>,
  <|"case" -> "fermion-2-pairs-w0", "family" -> "fermion",
    "code" -> "OPEProjected[0,0][R[\[Psi][mu1,0,z1],\[Psi][mu2,1,z1]],R[\[Psi][mu1,2,z2],\[Psi][mu2,3,z2]]]"|>,
  <|"case" -> "fermion-6-pairs-w0", "family" -> "fermion",
    "code" -> "OPEProjected[0,0][R[\[Psi][mu1,0,z1],\[Psi][mu2,0,z1],\[Psi][mu3,0,z1],\[Psi][mu4,0,z1],\[Psi][mu5,0,z1],\[Psi][mu6,0,z1]],R[\[Psi][mu1,0,z2],\[Psi][mu2,0,z2],\[Psi][mu3,0,z2],\[Psi][mu4,0,z2],\[Psi][mu5,0,z2],\[Psi][mu6,0,z2]]]"|>,
  <|"case" -> "boson-dx-pair-w0", "family" -> "boson",
    "code" -> "OPEProjected[0,0][R[dX[mu,1,z1]],R[dX[nu,3,z2]]]"|>,
  <|"case" -> "boson-dx-6-pairs-w0", "family" -> "boson",
    "code" -> "OPEProjected[0,0][R[dX[mu1,0,z1],dX[mu2,0,z1],dX[mu3,0,z1],dX[mu4,0,z1],dX[mu5,0,z1],dX[mu6,0,z1]],R[dX[mu1,0,z2],dX[mu2,0,z2],dX[mu3,0,z2],dX[mu4,0,z2],dX[mu5,0,z2],dX[mu6,0,z2]]]"|>,
  <|"case" -> "boson-exp-pair-w0", "family" -> "boson",
    "code" -> "OPEProjected[0,0][R[expX[k,z1,z1b]],R[expX[p,z2,z2b]]]"|>
};

allArgs = Join[$CommandLine, $ScriptCommandLine];
firstFlag = FirstPosition[
  allArgs,
  "--case" | "--family" | "--samples" | "--emit-json" | "--verify-zig-json",
  Missing["NotFound"]
];
rawArgs = If[MissingQ[firstFlag], {}, allArgs[[firstFlag[[1]] ;;]]];
opts = parseArgs[rawArgs];
selected = Select[caseRows,
   (opts["case"] === All || #["case"] === opts["case"]) &&
     (opts["family"] === All || #["family"] === opts["family"]) &];
zigRows = If[opts["verify-zig-json"] === None, {}, Import[opts["verify-zig-json"], "JSON"]];
zigByCase = Association[
  Table[rowValue[row, "case"] -> row, {row, zigRows}]
];

results = Table[
   Module[{expr, seconds},
    (* Timing intentionally covers only OPEProjected evaluation.  Expansion,
       hashing, import of Zig output, and proportional equality checks are
       oracle work and are computed after this value is fixed. *)
    seconds = timedOPEProjectedSeconds[row["code"], opts["samples"]];
    expr = ToExpression[row["code"], InputForm];
    Join[
    <|
      "case" -> row["case"],
      "family" -> row["family"],
      "mathematica_term_count" -> termsCount[expr],
      "mathematica_hash" -> canonicalHash[expr],
      "mathematica_median_s" -> seconds,
      "mathematica_timed_operation" -> "OPEProjected only",
      "comparison_timed_in_mathematica_median" -> False,
      "samples" -> opts["samples"],
      "mathematica_version" -> $Version,
      "prototype_path" -> FileNameJoin[{Directory[], "prototype-string-code"}]
    |>,
    If[opts["verify-zig-json"] === None, <||>, zigVerificationFields[row, expr, zigByCase]]
    ]
   ],
   {row, selected}
];

Export[opts["emit-json"], results, "JSON"];
Print["wrote ", opts["emit-json"], " cases=", Length[results]];
Quit[0];
