repo = DirectoryName[$InputFileName];
root = FileNameJoin[{repo, "StringCode"}];

$Path = DeleteDuplicates@Join[{repo}, $Path];

Get[FileNameJoin[{root, "OPE", "OPE.m"}]];
Get[FileNameJoin[{root, "Brackets", "Brackets.m"}]];

Print["Context[OPEProjected]: ", Context[StringCode`OPE`OPEProjected]];
Print["SubValues[OPEProjected] count: ", Length[SubValues[StringCode`OPE`OPEProjected]]];
Print["Context[BracketFromOPE]: ", Context[StringCode`Brackets`Private`BracketFromOPE]];
Print["Context[ope`OPEProjected]: ", Context[ope`OPEProjected]];
Print["Alias mapping for ope`: ", Lookup[$ContextAliases, "ope`", Missing["NotFound"]]];
Print["DownValues[BracketFromOPE]: ", InputForm[DownValues[StringCode`Brackets`Private`BracketFromOPE]]];

Print["DownValues[BracketFromOPE] count: ", Length[DownValues[StringCode`Brackets`Private`BracketFromOPE]]];

Print["BracketFromOPE call: ", StringCode`Brackets`Private`BracketFromOPE[1, 2, a]];

Exit[];
