(* Background kernel for DFRunBracket: the bracket [lambda0 (x) V_n[T0]] of App. app:Diffeo, saved raw.
   usage: wolframscript -file Diffeobrackets.wls n cacheDir    (or WolframKernel -script ...)
   The seed is polarized (all slots = p, i.e. T0 = u^s with e^{ik.X} carried by the profile DFT<n>), which is
   what the pipeline substitutes anyway and keeps the bracket small. *)
Needs["StringCode`"];
InitStringCode[<|"theory" -> "TypeII", "CFT" -> "FlatSpace", "conventions" -> "TypeII-Ashoke", "bracket" -> "Flat"|>];
$HistoryLength = 0; $IterationLimit = Infinity; $RecursionLimit = 16000;
(* arguments: from wolframscript ($ScriptCommandLine) or from WolframKernel -script ($CommandLine) *)
args = If[Length[$ScriptCommandLine] > 1, Rest[$ScriptCommandLine],
   With[{i = FirstPosition[$CommandLine, "-script"]}, If[MissingQ[i], {}, Drop[$CommandLine, First[i] + 1]]]];
n = ToExpression[args[[1]]];
cache = args[[2]];
log = OpenWrite[FileNameJoin[{cache, "D" <> ToString[n] <> "_bracket.log"}]];
say[s__] := (WriteString[log, StringJoin[ToString /@ {s}], "\n"]; Flush[log]);
seedHead = {DFT1, DFT2, DFT3}[[n]];
(* V_n[T0] in the draft's order: c e^{-phi} dX..dX psi cbar e^{-phibar} dXbar..dXbar psibar *)
seed = R @@ Join[{ProfileX[seedHead, {}, 0, 0], c[0, 0], exp\[Phi]f[-1, 0]}, ConstantArray[dX[p, 0, 0], n], {\[Psi][p, 0, 0], ct[0, 0], exp\[Phi]tf[-1, 0]},
    ConstantArray[dXt[p, 0, 0], n], {\[Psi]t[p, 0, 0]}];
(* lambda0 = V_mu c cbar (e^{-phi} psi^mu e^{-2phibar} dbar xibar + e^{-2phi} d xi e^{-phibar} psibar^mu) *)
lambda0 = R[ProfileX[Vp[\[Mu]], {}, 0, 0], c[0, 0], ct[0, 0], exp\[Phi]f[-1, 0], \[Psi][\[Mu], 0, 0], exp\[Phi]tb[-2, 0], \[Xi]t[1, 0]] +
   R[ProfileX[Vp[\[Mu]], {}, 0, 0], c[0, 0], ct[0, 0], exp\[Phi]b[-2, 0], \[Xi][1, 0], exp\[Phi]tf[-1, 0], \[Psi]t[\[Mu], 0, 0]];
say["n = ", n, ": computing EffectiveBracket[lambda0, V_n[T0], n, n]"];
{t, DFbracketRaw} = AbsoluteTiming[EffectiveBracket[lambda0, seed, n, n]];
say["bracket done in ", Round[t], " s, leaves ", LeafCount[DFbracketRaw]];
DumpSave[FileNameJoin[{cache, "D" <> ToString[n] <> "_bracket.mx"}], DFbracketRaw];
say["saved"];
Close[log];
