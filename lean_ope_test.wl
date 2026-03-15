root = DirectoryName[$InputFileName];
SetDirectory[root];

build = RunProcess[{"lake", "build", "lean-ope-cli"}];
If[build["ExitCode"] =!= 0,
  Print[build["StandardOutput"]];
  Print[build["StandardError"]];
  Exit[1];
];

bin = FileNameJoin[{root, ".lake", "build", "bin", "lean-ope-cli"}];
cases = {"bc", "cbc", "bbcc"};

runCase[c_String] := Module[{proc},
  proc = RunProcess[{bin, c}];
  <|
    "case" -> c,
    "exit" -> proc["ExitCode"],
    "stdout" -> StringTrim[proc["StandardOutput"]],
    "stderr" -> StringTrim[proc["StandardError"]]
  |>
];

results = runCase /@ cases;

Scan[
  (
    Print["--- ", #["case"], " ---"];
    Print[#["stdout"]];
    If[#["stderr"] =!= "", Print["stderr: ", #["stderr"]]];
    Print[""]
  ) &,
  results
];

results
