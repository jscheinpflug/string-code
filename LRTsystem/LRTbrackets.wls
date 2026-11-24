(* Background kernel for LRTRunBrackets: evaluates one bracket part of fullLevel_n on the backgrounds d = 5, 4, 3.
   usage: wolframscript -file LRTbrackets.wls n sector part [cache data helpers]   (or WolframKernel -script ...)      (sector = grav | aux | dil) *)
Needs["StringCode`"];
InitStringCode[<|"theory" -> "TypeII", "CFT" -> "FlatSpace", "conventions" -> "TypeII-Ashoke", "bracket" -> "Flat"|>];
$HistoryLength = 0; $IterationLimit = Infinity; $RecursionLimit = 16000;
(* optional arguments 5-7: cache, data and helpers folders (as set in the calling notebook) *)
(* arguments: from wolframscript ($ScriptCommandLine) or from WolframKernel -script ($CommandLine) *)
args = If[Length[$ScriptCommandLine] > 1, Rest[$ScriptCommandLine],
   With[{i = FirstPosition[$CommandLine, "-script"]}, If[MissingQ[i], {}, Drop[$CommandLine, First[i] + 1]]]];
If[Length[args] >= 6, LRT$Cache = args[[4]]; LRT$Data = args[[5]]; LRT$Helpers = args[[6]]];
Get[FileNameJoin[{DirectoryName[$InputFileName], "LRTsystem.wl"}]];
LRTInit[];
LRTBracketPart[ToExpression[args[[1]]], args[[2]], ToExpression[args[[3]]]];
