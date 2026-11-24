(* The half-lambda0 diffeo brackets bracketDiffHalf / bDiff (n = 1) and n2OPE / n2Raised (n = 2), with the pipeline's conventions:
   seed profile Kon -> U1 (n = 1) and M -> U2 (n = 2), both Orderless, and twoBracketReplRule applied.
   usage: wolframscript -file Diffeohalves.wls 1|2 cacheDir    (or WolframKernel -script ...)
   output: cacheDir/D1_bDiff.mx   (bracketDiffHalf, bDiff)
           cacheDir/D2_n2OPE.mx   (n2OPE, n2Raised)     n2Raised = holomorphic, then antiholomorphic PCO acting on n2OPE *)
PrependTo[$Path, ParentDirectory[DirectoryName[$InputFileName]]];   (* the repo root, where StringCode/ lives *)
Needs["StringCode`"];
InitStringCode[<|"theory" -> "TypeII", "CFT" -> "FlatSpace", "conventions" -> "TypeII-Ashoke", "bracket" -> "Flat"|>];
$HistoryLength = 0; $IterationLimit = Infinity; $RecursionLimit = 16000;
Private`$OPEProjChiralCacheOn = True;
(* arguments: from wolframscript ($ScriptCommandLine) or from WolframKernel -script ($CommandLine) *)
args = If[Length[$ScriptCommandLine] > 1, Rest[$ScriptCommandLine],
   With[{i = FirstPosition[$CommandLine, "-script"]}, If[MissingQ[i], {}, Drop[$CommandLine, First[i] + 1]]]];
which = ToExpression[args[[1]]];
cache = args[[2]];
log = OpenWrite[FileNameJoin[{cache, "D" <> ToString[which] <> "_halves.log"}]];
say[s__] := (WriteString[log, StringJoin[ToString /@ {s}], "\n"]; Flush[log]);

(* vertex constructors and helpers *)
twoBracketReplRule = {Private`z[2, 1][{}] :> z, Private`z[2, 2][{}] :> -z, Private`q[2, 1][{}] :> Private`r0, Private`q[2, 2][{}] :> Private`r0,
   Private`zbar[2, 1][{}] :> z, Private`zbar[2, 2][{}] :> -z, Private`qbar[2, 1][{}] :> Private`r0, Private`qbar[2, 2][{}] :> Private`r0};
mass1dX[F_, \[Mu]1_, \[Nu]1_, \[Mu]2_, \[Nu]2_, z_, zbar_] := R[ProfileX[F[\[Mu]1, \[Nu]1, \[Mu]2, \[Nu]2], {}, z, zbar],
   c[0, z], ct[0, zbar], exp\[Phi]f[-1, z], \[Psi][\[Mu]1, 0, z], dX[\[Nu]1, 0, z], exp\[Phi]tf[-1, zbar], \[Psi]t[\[Mu]2, 0, zbar], dXt[\[Nu]2, 0, zbar]];
mass2dX[F_, \[Mu]1_, \[Nu]1_, \[Rho]1_, \[Mu]2_, \[Nu]2_, \[Rho]2_, z_, zbar_] := R[ProfileX[F[\[Mu]1, \[Nu]1, \[Rho]1, \[Mu]2, \[Nu]2, \[Rho]2], {}, z, zbar],
   c[0, z], ct[0, zbar], exp\[Phi]f[-1, z], \[Psi][\[Mu]1, 0, z], dX[\[Nu]1, 0, z], dX[\[Rho]1, 0, z], exp\[Phi]tf[-1, zbar], \[Psi]t[\[Mu]2, 0, zbar],
   dXt[\[Nu]2, 0, zbar], dXt[\[Rho]2, 0, zbar]];
bottomUpTimes[reducer_][expr_?AtomQ] := expr;
bottomUpTimes[reducer_][expr_] := Module[{mapped}, mapped = bottomUpTimes[reducer] /@ expr; If[Head[mapped] === Times, reducer[mapped], mapped]];
derAppendDeep[expr_] := bottomUpTimes[derAppend][expr];
SetAttributes[{U1, U2}, Orderless];
lambda0Half = R[ProfileX[V[\[Mu]], {}, 0, 0], c[0, 0], ct[0, 0], exp\[Phi]f[-1, 0], \[Psi][\[Mu], 0, 0], exp\[Phi]tb[-2, 0], \[Xi]t[1, 0]];

If[which == 1,
  say["n = 1: EffectiveBracket[lambda0 half, mass1dX[Kon, p1, p2, p3, p4, 0, 0], 1, 1]"];
  {t, bracketDiffHalf} = AbsoluteTiming[EffectiveBracket[lambda0Half, mass1dX[Kon, p1, p2, p3, p4, 0, 0], 1, 1]];
  say["bracket done in ", Round[t], " s, leaves ", LeafCount[bracketDiffHalf]];
  bracketDiffHalf = bracketDiffHalf /. Kon[a__] :> U1[a];
  bDiff = derAppendDeep[bracketDiffHalf //. twoBracketReplRule];
  say["bDiff: leaves ", LeafCount[bDiff], ", Kon left: ", !FreeQ[bDiff, Kon]];
  DumpSave[FileNameJoin[{cache, "D1_bDiff.mx"}], {bracketDiffHalf, bDiff}];
  say["saved D1_bDiff.mx"]];

If[which == 2,
  say["n = 2: OPEProjected[2, 2][lambda0 half, mass2dX[M, p1, ..., p6, z0, z0bar]]"];
  {t, n2OPE} = AbsoluteTiming[ContractDelta[derAppendDeep[OPEProjected[2, 2][lambda0Half, mass2dX[M, p1, p2, p3, p4, p5, p6, z0, z0bar]] //. {dot[a_, b_] :> 0}]]];
  n2OPE = (n2OPE //. twoBracketReplRule) /. M[a__] :> U2[a];
  say["n2OPE done in ", Round[t], " s, leaves ", LeafCount[n2OPE], ", M left: ", !FreeQ[n2OPE, M]];
  DumpSave[FileNameJoin[{cache, "D2_n2OPE.mx"}], {n2OPE}];
  say["saved D2_n2OPE.mx (n2OPE only); raising the PCOs"];
  pcoTerms[expr_] := With[{e = Expand[expr]}, If[Head[e] === Plus, List @@ e, {e}]];
  {t, holoTerms} = AbsoluteTiming[Flatten[pcoTerms /@ Private`actPCOHoloAtPos /@ pcoTerms[n2OPE], 1]];
  say["holomorphic PCO: ", Length[holoTerms], " terms in ", Round[t], " s"];
  {t, n2Raised} = AbsoluteTiming[Total[Private`actPCOAntiHoloAtPos /@ holoTerms]];
  say["antiholomorphic PCO in ", Round[t], " s, leaves ", LeafCount[n2Raised]];
  DumpSave[FileNameJoin[{cache, "D2_n2OPE.mx"}], {n2OPE, n2Raised}];
  say["saved D2_n2OPE.mx (n2OPE, n2Raised)"]];
Close[log];
