(* ::Package:: *)

(* ::Title:: *)
(*LRTsystem.wl \[LongDash] the C_n coefficient system of main-6.tex from the recorded fullLevel1 / fullLevel2*)


(* ::Text:: *)
(*Usage from a notebook, after Needs["StringCode`"] and InitStringCode[<|"theory" -> "TypeII", "CFT" -> "FlatSpace", "conventions" -> "TypeII-Ashoke", "bracket" -> "Flat"|>]:*)
(**)
(*  Get["/path/to/this/folder/LRTsystem.wl"];   (* paths below are relative to this folder; see README.md *)*)
(*  LRTInit[];                              (* audit helper definitions; does not re-initialise StringCode *)*)
(**)
(*  (* STEP 1 \[LongDash] split fullLevel_n into its oscillator components *)*)
(*  LRTSplit[n];                            (* separate Q C_n, kinetic and bracket pieces of data/fullLevel_n (fast, inert load) *)*)
(*  (or LRTSplit[n, fullLevel1] for an expression computed in the notebook) *)
(*  LRTRunBrackets[n];                      (* evaluate the bracket pieces on the backgrounds in background kernels *)*)
(*  LRTBracketStatus[n]                     (* progress; continue when every part reports "saved" *)*)
(*  comps = LRTComponents[n, d];            (* all oscillator components of the EOM, d = 5, 4, 3 *)*)
(**)
(*  (* STEP 2 \[LongDash] print the equations and compare with the draft *)*)
(*  LRTPrintSystem[comps];*)
(*  LRTCompareWithDraft[comps];*)
(**)
(*  (* STEP 3 \[LongDash] solve for the coefficients and M_n *)*)
(*  sol = LRTSolve[comps];*)
(**)
(*  (* STEP 4 \[LongDash] print the solution and compare with the draft *)*)
(*  LRTPrintSolution[comps, sol];*)
(**)
(*Conventions: alpha' = 1, E = 2 Sqrt[n]; the overall N_n e^{-iEt} is stripped; z = X^1 + i X^2 (zz), t = X^0 (tt).*)
(*Unknowns: acoef[l], bcoef[l] (l = 1..5), ccoef[l] (l = 1..26) as in App. app:Cn; at n = 1 also aT, bT for B v Tbar; and M (= M_n).*)
(*The draft's free parameter delta_n is called del.*)


(* ::Section:: *)
(*Paths and settings*)


(* all paths are relative to the folder of this file; each can be set before Get to point elsewhere *)
If[!ValueQ[LRT$Dir], LRT$Dir = If[StringQ[$InputFileName] && FileExistsQ[$InputFileName], DirectoryName[$InputFileName], Directory[]]];
If[!ValueQ[LRT$Cache], LRT$Cache = FileNameJoin[{LRT$Dir, "cache"}]];        (* intermediate and final results *)
If[!ValueQ[LRT$Data], LRT$Data = FileNameJoin[{LRT$Dir, "data"}]];           (* fullLevel1.m, fullLevel2.mx, basis<n>Projected.m *)
If[!ValueQ[LRT$Helpers], LRT$Helpers = FileNameJoin[{LRT$Dir, "helpers"}]];  (* vertex and draft-formula helpers *)
If[!ValueQ[LRT$Kernel], LRT$Kernel = First[$CommandLine]];                   (* the kernel used for background runs *)

LRTFullFile[1] = "fullLevel1.m";   LRTFullFile[2] = "fullLevel2.mx";
LRTSeedHead[1] = U1;               LRTSeedHead[2] = U2;
LRTCoefHead[1] = C1;               LRTCoefHead[2] = C2;
LRTKeep[1] = {25, 34, 36, 45, 115, 117, 125, 126, 147, 223, 224, 286, 287, 365, 366, 376, 377, 448, 449, 455, 456};
LRTKeep[2] = {635, 666, 899, 930, 2222, 2223, 2224, 2227, 2266, 2268, 2271, 2310, 2311, 2312, 2315, 2442, 2443, 2444, 2447, 3995, 4001,
   4956, 4962, 6910, 6911, 6912, 6915, 7174, 7175, 7176, 7179, 8424, 8430, 8455, 8461, 8486, 8492, 8579, 8585};
LRTParts[1] = <|"dil" -> 1, "grav" -> 1, "aux" -> 1|>;
LRTParts[2] = <|"dil" -> 1, "grav" -> 3, "aux" -> 4|>;
LRTDims = {5, 4, 3};

(* the StringCode heads that make re-evaluation expensive; holding them inert makes loading and splitting instant *)
SetAttributes[LRTInert, HoldAll];
LRTInert[body_] := Block[{R, ProfileX, der, dot, \[Delta]}, body];

LRTInit[] := (
  Needs["StringCode`"];
  SetAttributes[{U1, U2, U3, U1p, U2p, U3p}, Orderless];
  Scan[Get[FileNameJoin[{LRT$Helpers, #}]] &, {"vertices.wl", "free_comparison.wl", "draft_checks.wl", "source_evaluation.wl"}];
  If[!DirectoryQ[LRT$Cache], CreateDirectory[LRT$Cache]];
  Print["LRTsystem loaded. Cache: ", LRT$Cache]);


(* ::Section:: *)
(*Kinematics, backgrounds and the draft ansatz*)


LRTEnergy[n_] := 2 Sqrt[n];
LRTNorm[n_] := 2^(n + 2)/n!;
(* slot indices of the seed U_n[...] in fullLevel_n: read from the data by LRTSplit (any names work); m1, m2, ... if not split yet *)
LRTSlotFile[n_] := FileNameJoin[{LRT$Cache, "L" <> ToString[n] <> "_slots.mx"}];
LRTSlots[n_] := If[FileExistsQ[LRTSlotFile[n]], Block[{LRTslotNames}, Get[LRTSlotFile[n]]; LRTslotNames], Take[{m1, m2, m3, m4, m5, m6, m7, m8}, 2 n + 2]];
(* T0 = u^(2n+2) e^{ik.X} substituted into the seed profile U_n[x1, ..., x_s] (e^{ik.X} stripped, each derivative gives ik):
   a repeated slot is a trace of u^s, i.e. u.u = 0; a slot that is not one of the canonical slot names (a dummy left by
   ContractDelta) becomes delta[x, u]; the canonical names are renamed to u afterwards (Thread[slots -> p]) *)
LRTSeedRule[seed_, slots_, EE_] := {
   ProfileX[seed[a__], _List, _, _] /; !DuplicateFreeQ[{a}] :> 0,
   ProfileX[seed[a__], ds_List, _, _] :> (Times @@ (\[Delta][#, p] & /@ Complement[{a}, slots])) Times @@ ((-EE \[Delta][#, 0]) & /@ ds)};
(* the puncture placeholders of a raw two-bracket, in case twoBracketReplRule was not applied in the notebook *)
LRTPlaceholder = (Private`z | Private`zbar | Private`q | Private`qbar)[2, _][{}];
LRTz = x[1] + I x[2];   (* z = u.X in the audit coordinates; x[0] = t *)
LRTlrt[n_] := R[auditC0, auditLRTBody[n, p]];   (* c0+ B_n Bbar_n *)

(* background of the draft in Euclidean components (x_E^0 = I t): {h^(2) (with the SFT-parameter terms), phi^(2), A^(2)};
   tau = Log[r0], bLog = Log[2 z0]; StringCode's graviton profile is 4 h. d = 3 is AdS3 x S3 x S3 x S1 with sphere share sp = p_+^2. *)
LRTxE = Join[{I x[0]}, Table[x[j], {j, 1, 9}]];
LRTBackground[5] := Module[{xa = Take[LRTxE, 5], xi = Drop[LRTxE, 5], kap = tau + bLog/4},
  {ArrayFlatten[{{-Outer[Times, xa, xa], 0}, {0, Outer[Times, xi, xi]}}] + 4 kap DiagonalMatrix[Join[ConstantArray[1, 5], ConstantArray[-1, 5]]],
   -xa.xa + xi.xi, Join[20 xa, -20 xi]}];
LRTBackground[4] := Module[{xa = Take[LRTxE, 4], xi = Drop[LRTxE, 4], jx},
  jx = Flatten[({#[[2]], -#[[1]]} &) /@ Partition[xi, 2]];
  {ArrayFlatten[{{-Outer[Times, xa, xa], 0}, {0, (Outer[Times, xi, xi] - Outer[Times, jx, jx])/4}}] +
     DiagonalMatrix[Join[ConstantArray[3 tau + bLog, 4], ConstantArray[-2 tau, 6]]], -xa.xa + 4 bLog, Join[16 xa, -8 xi]}];
LRTBackground[3] := Module[{xa = Take[LRTxE, 3], xi = LRTxE[[4 ;; 6]], xr = LRTxE[[7 ;; 9]], k3 = 2 tau + bLog, sm = 1 - sp},
  {DiagonalMatrix[Join[ConstantArray[k3, 3], ConstantArray[-sp k3, 3], ConstantArray[-sm k3, 3], {0}]] +
     ArrayFlatten[{{-Outer[Times, xa, xa], 0, 0, 0}, {0, sp Outer[Times, xi, xi], 0, 0}, {0, 0, sm Outer[Times, xr, xr], 0}, {0, 0, 0, {{0}}}}],
   -xa.xa + sp xi.xi + sm xr.xr, Join[12 xa, -12 sp xi, -12 sm xr, {0}]}];

LRTSetBackground[d_] := Module[{},
  {LRT$bgMetric, LRT$bgPhi, LRT$bgA} = LRTBackground[d];
  Clear[auditSourceJet];
  auditSourceJet[dd_, key_, indices_List, derivatives_List] := auditSourceJet[dd, key, indices, derivatives] =
    Module[{vec, tensor}, vec[i_Integer] := UnitVector[10, i + 1]; vec[p] := {0, 1, I, 0, 0, 0, 0, 0, 0, 0}; vec[m] := {0, 1, -I, 0, 0, 0, 0, 0, 0, 0};
      tensor = Switch[key, "metric", vec[indices[[1]]].LRT$bgMetric.vec[indices[[2]]], "A", vec[First[indices]].LRT$bgA, "phi", LRT$bgPhi];
      auditProfileDerivative[tensor, derivatives, 0]]];

(* operators of the draft at level n, with the audit's normalizations (P_n = c c[2,0] ..., B^0 = i c e^{-phi} psi_E^0 ...) *)
LRTOp[n_, id_] := Switch[id,
  "T", R @@ Join[{c[0, 0], exp\[Phi]f[-1, 0], d\[Phi][0, 0], \[Psi][p, 0, 0]}, ConstantArray[dX[p, 0, 0], n - 1]],
  "Q", R @@ Join[{c[0, 0], exp\[Phi]f[1, 0], \[Eta][0, 0], \[Eta][1, 0], \[Psi][p, 0, 0]}, ConstantArray[dX[p, 0, 0], n - 1]],
  _, auditExtraCore[n, id, p]];
LRTOpNames[1] = {"B", "B0", "U0", "F", "G", "P", "A", "T", "Q", "D", "L", "S", "R"};
LRTOpNames[2] = {"B", "B0", "U0", "F", "Y", "Z", "G", "P", "A", "H", "K", "T", "Q", "D", "L", "S", "R"};

(* draft ansatz (Cngeneralform, App. app:Cn) with symbolic coefficients; n = 1 adds z (aT + t bT) B v Tbar *)
LRTAnsatz[n_] := Expand[auditCompanion[n, 5, 0, True]/LRTNorm[n] +
    If[n == 1, LRTz (aT + x[0] bT) (R[LRTOp[n, "B"], auditBar[LRTOp[n, "T"]]] + R[LRTOp[n, "T"], auditBar[LRTOp[n, "B"]]]), 0]];
LRTReadable = {fitA[l_] :> acoef[l], fitB[l_] :> bcoef[l], fitC[l_] :> ccoef[l]};


(* ::Section:: *)
(*Step 1a \[LongDash] split fullLevel_n into its pieces*)


LRT$ChunkLeaves = 2*10^6;   (* LRTSplit; the bracket kernels re-split to LRT$WorkerChunkLeaves *)
LRT$WorkerChunkLeaves = 2*10^5;
LRTSplitTerm[t_, max_: LRT$ChunkLeaves] := If[LeafCount[t] < max, {t},
   Which[Head[t] === Plus, Flatten[LRTSplitTerm[#, max] & /@ (List @@ t)],
    Head[t] === Times, Module[{fs = List @@ t, pos, f, rest},
      pos = Flatten[Position[fs, _Plus, {1}, Heads -> False]];
      If[pos === {}, {t}, f = fs[[First[MaximalBy[pos, LeafCount[fs[[#]]] &]]]]; rest = Times @@ DeleteCases[fs, f, {1}, 1];
       Flatten[LRTSplitTerm[rest #, max] & /@ (List @@ f)]]], True, {t}]];

(* LRTSplit[n] reads data/fullLevel<n>; LRTSplit[n, expr] splits an expression already in the notebook (e.g. fullLevel1) *)
SetAttributes[LRTSplit, HoldRest];   (* the expression is read only inside the inert block, so StringCode never re-evaluates it *)
LRTSplit[n_] := LRTSplit[n, Automatic];
LRTSplit[n_, given_] := LRTInert[Module[{full, groups, cls, coef = LRTCoefHead[n], seed = LRTSeedHead[n], t0 = AbsoluteTime[]},
   Which[given =!= Automatic, full = given,
    n == 1, full = Get[FileNameJoin[{LRT$Data, LRTFullFile[1]}]],
    True, Get[FileNameJoin[{LRT$Data, LRTFullFile[2]}]]; full = fullLevel2; Clear[fullLevel2]];
   If[Head[full] =!= Plus, Print["fullLevel", n, " is not a sum of terms (head ", Head[full], "): nothing to split"]; Abort[]];
   (* the seed's slot names, read from the data: the most frequent slot list is the canonical one. Any other list means
      ContractDelta was applied before derAppend had merged every derivative factor: it then renames indices in a
      der[..] factor and not in its profile (seed and background alike), and the EOM comes out wrong. Stop. *)
   Module[{tal = ReverseSortBy[Tally[Cases[full, seed[a__] :> {a}, {0, Infinity}]], Last], canon},
     canon = tal[[1, 1]];
     If[Length[canon] != 2 n + 2 || !DuplicateFreeQ[canon], Print["unexpected seed slot list ", seed @@ canon]; Abort[]];
     If[Length[tal] > 1, Print["fullLevel", n, ": ", Total[Rest[tal][[All, 2]]], " seed occurrences with contracted slots. ",
        "Build the BRST and bracket terms without ContractDelta (e.g. derAppend[EffectiveBracket[...]]); the pipeline contracts them itself."]; Abort[]];
     Block[{LRTslotNames = canon}, DumpSave[LRTSlotFile[n], LRTslotNames]];
     Print["seed slots: ", seed @@ canon, " (", tal[[1, 2]], " occurrences)"]];
   cls[t_] := Which[!FreeQ[t, coef], "QC", !FreeQ[t, H[_, _]], "grav", !FreeQ[t, A[_]], "aux", !FreeQ[t, Dil], "dil", !FreeQ[t, seed], "kin", True, "other"];
   groups = GroupBy[List @@ full, cls]; Clear[full];
   Print["fullLevel", n, ": ", Map[Length, groups], " top-level terms (", Round[AbsoluteTime[] - t0], " s)"];
   If[KeyExistsQ[groups, "other"], Print["unclassified terms: ", Length[groups["other"]]]];
   LRTpiece = groups["QC"]; DumpSave[FileNameJoin[{LRT$Cache, "L" <> ToString[n] <> "_QC.mx"}], LRTpiece];
   LRTpiece = groups["kin"]; DumpSave[FileNameJoin[{LRT$Cache, "L" <> ToString[n] <> "_kin.mx"}], LRTpiece];
   Clear[LRTpiece];
   KeyValueMap[Function[{sector, k}, Module[{chunks = Flatten[LRTSplitTerm /@ groups[sector]], sizes, cum, tot},
       sizes = LeafCount /@ chunks; cum = Accumulate[sizes]; tot = Last[cum];
       Do[LRTchunk = chunks[[Flatten[Position[cum, s_ /; (j - 1) tot/k < s <= j tot/k]]]];
         DumpSave[FileNameJoin[{LRT$Cache, "L" <> ToString[n] <> "_" <> sector <> "_" <> ToString[j] <> ".mx"}], LRTchunk], {j, k}];
       Clear[LRTchunk];
       Print["  ", sector, ": ", Length[chunks], " chunks, ", tot, " leaves, in ", k, " part(s)"]]], LRTParts[n]];
   ]];


(* ::Section:: *)
(*Step 1b \[LongDash] evaluate the bracket pieces on the backgrounds (one background kernel per part)*)


(* start a worker script in a detached background kernel (macOS / Linux shell) *)
LRTLaunch[script_String, args_List, out_String] := Run["nohup " <> StringRiffle[("'" <> ToString[#] <> "'") & /@ Join[{LRT$Kernel, "-script", script}, args], " "] <>
    " > '" <> out <> "' 2>&1 &"];

LRTRunBrackets[n_] := Module[{logs = {}},
  KeyValueMap[Function[{sector, k}, Do[
      Module[{log = FileNameJoin[{LRT$Cache, "L" <> ToString[n] <> "_" <> sector <> "_" <> ToString[j] <> ".log"}]},
       LRTLaunch[FileNameJoin[{LRT$Dir, "LRTbrackets.wls"}], {n, sector, j, LRT$Cache, LRT$Data, LRT$Helpers}, log <> ".out"];
       AppendTo[logs, log]], {j, k}]], LRTParts[n]];
  Print["started ", Length[logs], " bracket kernels for n = ", n, "; follow them with LRTBracketStatus[", n, "]"]; logs];

LRTBracketStatus[n_] := Module[{rows},
  rows = Flatten[KeyValueMap[Function[{sector, k}, Table[Module[{tag = "L" <> ToString[n] <> "_" <> sector <> "_" <> ToString[j], log, last},
        log = FileNameJoin[{LRT$Cache, tag <> ".log"}];
        last = If[FileExistsQ[log], Last[ReadList[log, String], "starting"], "not started"];
        {tag, last}], {j, k}]], LRTParts[n]], 1];
  Grid[Prepend[rows, {"part", "last log line"}], Alignment -> Left, Frame -> All]];

(* the work done by each background kernel: chart, seed, exact pruning, contraction, Cartesian evaluation, heat factor *)
LRTSumOverComponents[term_, d_] := Module[{profile, indices, jets, free, op, support, key, isSum},
  isSum[i_] := Head[i] === Symbol && !MemberQ[{p, m}, i];
  profile = First[Cases[term, _ProfileX, Infinity]];
  key = Which[Head[profile[[1]]] === h, "metric", Head[profile[[1]]] === av, "A", profile[[1]] === ph, "phi"];
  indices = If[AtomQ[profile[[1]]], {}, List @@ profile[[1]]];
  jets = profile[[2]]; op = term /. profile -> 1;
  free = DeleteDuplicates[Select[Join[indices, jets], isSum]];
  support = Map[Function[args, With[{r = Thread[free -> args]}, With[{value = auditSourceJet[d, key, indices /. r, jets /. r]},
       If[value === 0, Nothing, {r, value}]]]], Tuples[Range[0, 9], Length[free]]];
  Total[Function[entry, Module[{v = op /. entry[[1]], remaining},
      remaining = DeleteDuplicates[Select[auditWordSlots[v], isSum]];
      entry[[2]] Total[Function[args, v /. Thread[remaining -> args]] /@ Tuples[Range[0, 9], Length[remaining]]]]] /@ support]];

LRTBracketPart[n_, sector_String, part_Integer] := Module[
  {tag = "L" <> ToString[n] <> "_" <> sector <> "_" <> ToString[part], log, say, EE = LRTEnergy[n], slots = LRTSlots[n], seed = LRTSeedHead[n],
   chart, bgRule, bgPat, maxOrd, ord, trunc, data, tot, survivors, acc = 0, t0 = AbsoluteTime[], src, canon, lap, heat},
  log = OpenWrite[FileNameJoin[{LRT$Cache, tag <> ".log"}]];
  say[s__] := (WriteString[log, StringJoin[ToString /@ {s}], "\n"]; Flush[log]);
  chart = {z -> 1/2, HoldPattern[dot[__]] -> 0, \[Alpha]p -> 1, Private`r0 -> rr,          (* z = 1/2: the (2z)^(k.p) chart kernel is 1 *)
    (* the same if twoBracketReplRule was not applied in the notebook. StringCode evaluates the raw placeholders
       z[2,1][{}] -> -z0, z[2,2][{}] -> z0 and q[2,_][{}] -> r0 on reading, so map the symbol z0 (a rule for -z0 would be a
       product pattern and would stop the chart from reaching inside the terms it matches) *)
    z0 -> -1/2, Private`zbar[2, 1][{}] -> 1/2, Private`zbar[2, 2][{}] -> -1/2, Private`q[2, _][{}] -> rr, Private`qbar[2, _][{}] -> rr,
    Sequence @@ LRTSeedRule[seed, slots, EE],                                            (* seed T0 = u^(2n+2) e^{-iEt} *)
    With[{sd = seed}, HoldPattern[der[sd[__]][j_]]] :> -EE \[Delta][j, 0]};   (* With: HoldPattern must still see U1 / U2 *)
  bgRule = {ProfileX[H[a_, b_], ds_List, s_, t_] :> 4 ProfileX[h[a, b], ds, s, t], ProfileX[A[a_], ds_List, s_, t_] :> ProfileX[av[a], ds, s, t],
    ProfileX[Dil, ds_List, s_, t_] :> ProfileX[ph, ds, s, t]};
  bgPat = Switch[sector, "grav", H[_, _], "aux", A[_], "dil", Dil]; maxOrd = Switch[sector, "aux", 1, _, 2];
  ord[t_] := Count[t, der[bgPat][_], Infinity] + Total[Cases[t, Power[der[bgPat][_], k_Integer] :> k - 1, Infinity]] +
     Total[Cases[t, ProfileX[bgPat, ds_List, _, _] :> Length[ds], Infinity]];
  LRTInert[Get[FileNameJoin[{LRT$Cache, tag <> ".mx"}]]; data = Flatten[LRTSplitTerm[#, LRT$WorkerChunkLeaves] & /@ LRTchunk]; Clear[LRTchunk]; tot = Length[data]];
  say[tag, ": ", tot, " chunks"];
  (* phase 1, inside ONE inert block (entering the block per chunk costs ~1 s because R carries many definitions):
     substitute, expand, and drop monomials with more background derivatives than the polynomial background allows *)
  (* truncated expansion: multiply out factor by factor and drop every partial product above maxOrd at once
     (same monomials as Expand followed by the cut, ~20x faster on the dense chunks) *)
  trunc[e_] := Which[
    Head[e] === Plus, Join @@ (trunc /@ List @@ e),
    Head[e] === Times, Fold[Function[{acc, f}, Select[Flatten[Outer[Times, acc, trunc[f]]], ord[#] <= maxOrd &]], {1}, List @@ e],
    MatchQ[e, Power[_Plus, _Integer?Positive]], trunc[Times @@ ConstantArray[e[[1]], e[[2]]]],
    True, If[ord[e] <= maxOrd, {e}, {}]];
  survivors = LRTInert[Module[{out = {}},
      Do[Module[{mons, ch = (data[[i]] /. chart) /. Thread[slots -> p]},
         If[!FreeQ[ch, LRTPlaceholder | z0 | seed], say["chunk ", i, ": a puncture placeholder or the seed ", seed, " survived the chart; stopping"]; Abort[]];
         mons = trunc[ch /. auditNullRules]; data[[i]] = 0;
         If[mons =!= {}, AppendTo[out, With[{r = Total[mons]}, Hold[r]]]];
         If[Mod[i, Max[1, Floor[tot/40]]] == 0, say["  phase 1: ", i, "/", tot, " at ", Round[AbsoluteTime[] - t0], " s, surviving pieces ", Length[out]]]], {i, tot}];
      out]];
  say["phase 1 done: ", Length[survivors], " surviving pieces at ", Round[AbsoluteTime[] - t0], " s"];
  (* intermediate 1: the expanded, pruned bracket terms of this part (chart and seed applied; held unevaluated) *)
  Block[{LRTexpanded = survivors}, DumpSave[FileNameJoin[{LRT$Cache, "L" <> ToString[n] <> "X_" <> sector <> "_" <> ToString[part] <> ".mx"}], LRTexpanded]];
  (* phase 2: StringCode evaluation of the survivors only *)
  Do[Module[{e = Expand[ReleaseHold[survivors[[i]]] /. auditNullRules]},
     If[e =!= 0, e = derAppend[e] /. bgRule; acc += Expand[Contract[ContractDelta[Expand[e]]] /. auditNullRules]];
     If[Mod[i, Max[1, Floor[Length[survivors]/20]]] == 0, say["  phase 2: ", i, "/", Length[survivors], " at ", Round[AbsoluteTime[] - t0], " s"]]], {i, Length[survivors]}];
  src = auditProjectionCleanup[acc];
  say["uniform r0 power (dropped): ", Union[Exponent[#, rr] & /@ auditTerms[src]]];
  canon = Expand[canonicalizeDummies[src /. rr -> 1]];
  (* intermediate 2: the evaluated, contracted source of this part, before any background is chosen *)
  Block[{LRTsource = canon}, DumpSave[FileNameJoin[{LRT$Cache, "L" <> ToString[n] <> "C_" <> sector <> "_" <> ToString[part] <> ".mx"}], LRTsource]];
  say["intermediates saved: L", n, "X_", sector, "_", part, ".mx (expanded, pruned), L", n, "C_", sector, "_", part, ".mx (contracted source)"];
  lap[f_] := -D[f, {x[0], 2}] + Sum[D[f, {x[j], 2}], {j, 1, 9}];
  heat[f_, co_] := Expand[f + co lap[f] + co^2 lap[lap[f]]/2 + co^3 lap[lap[lap[f]]]/6];
  Do[Module[{base},
     LRTSetBackground[d];
     base = auditProjectionCleanup[auditNumericWord[Total[Expand[Total[LRTSumOverComponents[#, d] & /@ #]] & /@ Partition[auditTerms[canon], UpTo[200]]]]];
     LRTshat = heat[base, bLog/2];   (* S-hat = e^{(b/2) Box} S; bLog must cancel *)
     say["d = ", d, ": ", Length[auditTerms[LRTshat]], " monomials, bLog left: ", !FreeQ[LRTshat, bLog]];
     DumpSave[FileNameJoin[{LRT$Cache, "L" <> ToString[n] <> "S_" <> sector <> "_" <> ToString[part] <> "_d" <> ToString[d] <> ".mx"}], LRTshat]], {d, LRTDims}];
  say["saved (", Round[AbsoluteTime[] - t0], " s)"]; Close[log];];


(* ::Section:: *)
(*Step 1c \[LongDash] all oscillator components of the EOM*)


(* evaluate one recorded term carrying one profile, '$' dummies summed over 0..9. The slot indices are set either
   by rules (C_n basis elements, whose slots sit in the word) or by a list of labels for the profile's own arguments
   (the seed, whose slot names vary from term to term; a repeated argument is a trace of u^s and gives 0) *)
LRTEvalProfile[t_, prof_, rules : {___Rule}, f_, EE_] := LRTEvalCore[t /. rules, prof, f, EE];
LRTEvalProfile[t_, prof_, labels : {Except[_Rule] ..}, f_, EE_] := Module[{args = First[Cases[t, ProfileX[hh_ /; MatchQ[hh, prof], __] :> List @@ hh, Infinity]]},
  If[!DuplicateFreeQ[args], 0, LRTEvalCore[t /. Thread[args -> labels], prof, f, EE]]];
LRTEvalCore[t1_, prof_, f_, EE_] := Module[{ds, ids},
  ds = First[Cases[t1, ProfileX[hh_ /; MatchQ[hh, prof], jet_List, _, _] :> jet, Infinity]];
  ids = DeleteDuplicates[Cases[t1, q_Symbol /; StringContainsQ[SymbolName[q], "$"], Infinity]];
  Total[Table[Module[{r = Thread[ids -> vals], value}, value = auditProfileDerivative[f, ds /. r, EE];
      If[value === 0, 0, (t1 /. r /. ProfileX[hh_ /; MatchQ[hh, prof], _, _, _] -> 1) value /. auditNullRules]], {vals, Tuples[Range[0, 9], Length[ids]]}]]];

(* Q C_n from the recorded Q C_n terms: the draft ansatz is written on the kept generic basis elements and substituted *)
LRTQC[n_] := Module[{EE = LRTEnergy[n], coef = LRTCoefHead[n], basis, slotsOf, elem, cands, elems, allW, ansatz = LRTAnsatz[n], mat, rhs, gsol, nz, terms},
  Get[FileNameJoin[{LRT$Cache, "L" <> ToString[n] <> "_QC.mx"}]];
  basis = Get[FileNameJoin[{LRT$Data, "basis" <> ToString[n] <> "Projected.m"}]];
  slotsOf[e_] := DeleteDuplicates[Cases[e, s_Symbol /; Context[s] === "Global`" && StringStartsQ[SymbolName[s], "mu"], {0, Infinity}, Heads -> True]];
  elem[k_, as_] := Expand[basis[[k]] /. Thread[slotsOf[basis[[k]]] -> as] /. ProfileX[coef[_], {}, 0, 0] -> 1 /. auditNullRules];
  cands = Select[Flatten[Table[{k, as}, {k, LRTKeep[n]}, {as, Tuples[{p, 0}, Length[slotsOf[basis[[k]]]]]}], 1], elem @@ # =!= 0 &];
  elems = elem @@@ cands;
  allW = Union[Cases[ansatz, _R, {0, Infinity}], Flatten[Cases[#, _R, {0, Infinity}] & /@ elems]];
  mat = SparseArray[Table[Coefficient[elems[[j]], allW[[i]]], {i, Length[allW]}, {j, Length[cands]}]];
  rhs = Coefficient[ansatz, #] & /@ allW;
  gsol = LinearSolve[mat, rhs];
  If[Union[Expand[mat.gsol - rhs]] =!= {0}, Print["ansatz decomposition failed"]; Abort[]];
  nz = Select[Transpose[{cands, gsol}], Expand[#[[2]]] =!= 0 &];
  terms = Flatten[auditTerms[Expand[#]] & /@ (derAppend /@ LRTpiece)]; Clear[LRTpiece];
  auditProjectionCleanup[auditNumericWord[Total[Function[t, Module[{k = FirstCase[t, ProfileX[coef[kk_], _, 0, 0] :> kk, $Failed, Infinity]},
        Total[Function[st, LRTEvalProfile[t, coef[k], Thread[slotsOf[basis[[k]]] -> st[[1, 2]]], st[[2]], EE]] /@ Select[nz, #[[1, 1]] == k &]]]] /@ terms]]]];

(* Q V_n[F_H(T0)] from the recorded kinetic terms *)
LRTQV[n_, d_] := Module[{EE = LRTEnergy[n], slots = LRTSlots[n], ss = 2 n + 2, seed = LRTSeedHead[n], hSol, vecX, structs, kin},
  hSol = LRTBackground[d][[1]] /. {tau -> 0, bLog -> 0};
  vecX = Join[{I x[0]}, Table[x[j], {j, 1, d - 1}], ConstantArray[0, 10 - d]];        (* X_a along AdS only *)
  (* F_H(T0) as {coefficient, labels of the s slots}; every family is summed over the slot positions, so the labels can be put
     on whatever slot list a term carries (see LRTEvalProfile) *)
  structs = Join[{{Tr[hSol]/2 + I n EE x[0], ConstantArray[p, ss]}},                      (* (-(X^2 - rho_I)/2 + i n E t) u^s *)
    Flatten[Table[If[vecX[[i + 1]] === 0, Nothing, {LRTz/2 vecX[[i + 1]], ReplacePart[ConstantArray[p, ss], j -> i]}], {j, ss}, {i, 0, 9}], 1],
    Table[{I n (3 n + 7)/(4 ss) LRTz I EE, ReplacePart[ConstantArray[p, ss], j -> 0]}, {j, ss}]];   (* i n(3n+7)/4 z k_(a u...) *)
  Get[FileNameJoin[{LRT$Cache, "L" <> ToString[n] <> "_kin.mx"}]];
  kin = Flatten[auditTerms[Expand[#]] & /@ (derAppend /@ LRTpiece)]; Clear[LRTpiece];
  auditProjectionCleanup[auditNumericWord[Total[Flatten[Table[LRTEvalProfile[t, _seed, s[[2]], s[[1]], EE], {t, kin}, {s, structs}]]]]]];

(* S^NS-hat: sum of the evaluated bracket parts *)
LRTSNS[n_, d_] := Module[{files = Flatten[KeyValueMap[Table["L" <> ToString[n] <> "S_" <> #1 <> "_" <> ToString[j] <> "_d" <> ToString[d] <> ".mx", {j, #2}] &, LRTParts[n]]], missing},
  missing = Select[files, !FileExistsQ[FileNameJoin[{LRT$Cache, #}]] &];
  If[missing =!= {}, Print["bracket parts not ready: ", missing, " \[LongDash] see LRTBracketStatus[", n, "]"]; Abort[]];
  auditProjectionCleanup[Total[(Get[FileNameJoin[{LRT$Cache, #}]]; LRTshat) & /@ files]]];

(* operator dictionary: StringCode word -> {holo operator, antiholo operator, c0+?, coefficient} *)
LRTDictionary[n_] := Module[{dict = <||>},
  Do[Module[{e = Expand[If[c0, R[auditC0, R[LRTOp[n, a], auditBar[LRTOp[n, b]]]], R[LRTOp[n, a], auditBar[LRTOp[n, b]]]]]},
      Do[dict[w] = {a, b, c0, Coefficient[e, w]}, {w, DeleteDuplicates[Cases[e, _R, {0, Infinity}]]}]],
    {a, LRTOpNames[n]}, {b, LRTOpNames[n]}, {c0, {False, True}}];
  dict];
LRTLabel[{a_, b_, c0_}] := If[c0, "c0+ ", ""] <> StringReplace[a, {"B0" -> "B^0", "U0" -> "U^0"}] <> " " <> StringReplace[b, {"B0" -> "B^0", "U0" -> "U^0"}] <> "bar";
LRTtoZT[ex_] := Expand[ex /. {x[1] -> (zz + zb)/2, x[2] -> (zz - zb)/(2 I), x[0] -> tt}];

(* group a total EOM expression by oscillator component; each component is a polynomial in zz, tt *)
LRTByComponent[total_, n_] := Module[{dict = LRTDictionary[n], comps = <||>, unknown = {}},
  Do[If[KeyExistsQ[dict, w],
     Module[{key = Most[dict[w]], val = LRTtoZT[Coefficient[total, w]/Last[dict[w]]]},
      If[KeyExistsQ[comps, key] && Expand[comps[key] - val] =!= 0, Print["inconsistent c0+ halves for ", LRTLabel[key]]];
      comps[key] = val], AppendTo[unknown, w]], {w, DeleteDuplicates[Cases[total, _R, {0, Infinity}]]}];
  If[unknown =!= {}, Print["words outside the draft's operator list: ", unknown]];
  If[!FreeQ[Values[comps], zb], Print["warning: a component depends on zbar"]];
  KeySortBy[comps, {#[[3]], #[[1]], #[[2]]} &]];

LRTComponents[n_, d_] := Module[{t0 = AbsoluteTime[], qc, qv, sns, sR, j, total},
  Print["Step 1: oscillator components of the level-", n, " EOM on the d = ", d, " background"];
  qc = LRTQC[n];      Print["  Q C_", n, " from the recorded terms: ", Length[auditTerms[qc]], " monomials"];
  qv = LRTQV[n, d];   Print["  Q V_", n, "[F_H(T0)] from the recorded kinetic terms: ", Length[auditTerms[qv]], " monomials"];
  sns = LRTSNS[n, d]; Print["  S^NS-hat from the recorded brackets: ", Length[auditTerms[sns]], " monomials"];
  sR = -2 (d - 1) n tau LRTlrt[n];                       (* draft (RRsourceterm) *)
  j = Expand[auditJGeom[n, d, M]/LRTNorm[n]];            (* draft (EOMterms2nd) *)
  total = auditProjectionCleanup[Expand[qv + qc + sns + sR - j]];
  Print["  total: ", Length[DeleteDuplicates[Cases[total, _R, {0, Infinity}]]], " oscillator components (", Round[AbsoluteTime[] - t0], " s)"];
  <|"n" -> n, "d" -> d, "QC" -> qc, "QV" -> qv, "SNS" -> sns, "SR" -> sR, "J" -> j, "total" -> total,
    "components" -> (LRTByComponent[total, n] /. LRTReadable)|>];


(* ::Section:: *)
(*Step 2 \[LongDash] the equations, and comparison with the draft*)


LRTEquations[comps_] := Module[{seen = <||>, eqs = {}},
  KeyValueMap[Function[{key, val}, Module[{skey = {Sort[key[[1 ;; 2]]], key[[3]]}},
      If[!KeyExistsQ[seen, skey], seen[skey] = True;   (* the vee / wedge partner gives the same equations *)
       Do[AppendTo[eqs, {LRTLabel[key], r[[1]], r[[2]] == 0}], {r, CoefficientRules[val, {zz, tt}]}]]]], comps["components"]];
  eqs];

LRTPrintSystem[comps_] := (
  Print["\n===== EOM of level ", comps["n"], ", d = ", comps["d"], ":  Q V[F_H] + Q C + S^NS + S^R - J, per oscillator component (z = zz, t = tt) ====="];
  KeyValueMap[Print["  [", LRTLabel[#1], "]   ", ToString[Collect[#2, {zz, tt}, Factor], InputForm]] &, comps["components"]];
  Print["\n===== the system: coefficient of z^i t^j in each component = 0 ====="];
  Scan[Print["  [", #[[1]], "]  z^", #[[2, 1]], " t^", #[[2, 2]], ":   ", ToString[#[[3]], InputForm]] &, LRTEquations[comps]];
  Print["(", Length[LRTEquations[comps]], " distinct equations)"]);

(* the draft's Appendix formula for Q C_n, R[c0+, P^(1)_QC] + P^(2)_QC (does not contain the n = 1 B v Tbar term) *)
LRTDraftQC[n_] := Module[{z = LRTz, t = x[0], E0 = LRTEnergy[n], iE, op, pr, v, w, a1, a2, a3, a4, a5, b1, b2, b3, b4, b5, cc, P1, P2},
  iE = I E0; {a1, a2, a3, a4, a5} = Array[fitA, 5]; {b1, b2, b3, b4, b5} = Array[fitB, 5]; cc = Array[fitC, 26];
  (* Y_n, Z_n, H_n exist only for n >= 2: at n = 1 their operators and the coefficients that multiply them are dropped *)
  op[id_] := If[n == 1 && MemberQ[{"Y", "Z", "H"}, id], 0, LRTOp[n, id]];
  pr[a_, b_] := With[{o1 = op[a], o2 = op[b]}, If[o1 === 0 || o2 === 0, 0, R[o1, auditBar[o2]]]];
  v[a_, b_] := pr[a, b] + pr[b, a]; w[a_, b_] := pr[a, b] - pr[b, a];
  P1 = (-a4 + 2 a5 + t (-b4 + 2 b5)) pr["B", "B"] - iE cc[[17]] z^2 pr["B0", "B0"] + 2 iE cc[[20]] z^2 pr["U0", "U0"] + z^2 (-n cc[[21]] + 2 cc[[22]]) pr["F", "F"] +
    2 (n - 1) cc[[24]] z^2 pr["Y", "Y"] + z/2 (b4 - iE (a4 + t b4) - 2 cc[[17]] + 4 cc[[18]]) v["B", "B0"] + z (iE (a5 + t b5) - b5 - cc[[19]] + 2 cc[[20]]) v["B", "U0"] +
    z (-iE b1 - n/2 (a4 + t b4) + a5 + t b5 - cc[[21]] + 2 cc[[22]]) v["B", "F"] + z (-iE b2 + (n - 1) (a5 + t b5) - cc[[23]] + 2 cc[[24]]) v["B", "Y"] +
    z (-iE b3 - cc[[25]] + 2 cc[[26]]) v["B", "Z"] - z/2 (n (a4 + t b4) + 2 (a5 + t b5)) v["B", "T"] + iE z^2/2 (2 cc[[18]] - cc[[19]]) v["B0", "U0"] -
    z^2/2 (iE cc[[21]] + n cc[[17]] - 2 cc[[18]]) v["B0", "F"] + z^2/2 (-iE cc[[23]] + 2 (n - 1) cc[[18]]) v["B0", "Y"] - iE cc[[25]] z^2/2 v["B0", "Z"] -
    z^2/2 (n cc[[17]] + 2 cc[[18]]) v["B0", "T"] - z^2/2 (-2 iE cc[[22]] + n cc[[19]] - 2 cc[[20]]) v["U0", "F"] + z^2 (iE cc[[24]] + (n - 1) cc[[20]]) v["U0", "Y"] +
    iE cc[[26]] z^2 v["U0", "Z"] - z^2/2 (n cc[[19]] + 2 cc[[20]]) v["U0", "T"] + z^2/2 (2 (n - 1) cc[[22]] - n cc[[23]] + 2 cc[[24]]) v["F", "Y"] -
    z^2/2 (n cc[[25]] - 2 cc[[26]]) v["F", "Z"] - z^2/2 (n cc[[21]] + 2 cc[[22]]) v["F", "T"] + (n - 1) cc[[26]] z^2 v["Y", "Z"] - z^2/2 (n cc[[23]] + 2 cc[[24]]) v["Y", "T"] -
    z^2/2 (n cc[[25]] + 2 cc[[26]]) v["Z", "T"] - I z^2/4 (E0 cc[[17]] - 2 I cc[[21]]) w["G", "D"] - I z^2/4 (E0 cc[[18]] - 2 I cc[[22]]) w["G", "L"] +
    I z^2/4 (E0 cc[[19]] - 2 I cc[[21]] - 4 I cc[[23]]) w["P", "D"] + I z^2/4 (E0 cc[[20]] - 2 I cc[[22]] - 4 I cc[[24]]) w["P", "L"] - z^2/2 (n cc[[17]] - cc[[19]] + cc[[25]]) w["A", "D"] -
    z^2/2 (n cc[[18]] - cc[[20]] + cc[[26]]) w["A", "L"] - z^2/4 (-iE cc[[25]] + 2 (n - 1) cc[[21]] - 4 cc[[23]]) w["H", "D"] - z^2/4 (-iE cc[[26]] + 2 (n - 1) cc[[22]] - 4 cc[[24]]) w["H", "L"];
  P2 = z/4 (2 a1 - a4 + t (2 b1 - b4) - 4 cc[[13]] + 8 cc[[14]]) w["G", "B"] + z^2/4 (-2 iE cc[[13]] + 2 cc[[1]] - cc[[17]]) w["G", "B0"] +
    z^2/4 (4 iE cc[[14]] - cc[[19]] + 2 cc[[4]]) w["G", "U0"] + I z^2/4 (E0 cc[[1]] + 2 I n cc[[13]] - 4 I cc[[14]] + I cc[[21]] - 2 I cc[[7]]) w["G", "F"] +
    I z^2/4 (E0 cc[[2]] - 4 I (n - 1) cc[[14]] + I cc[[23]] - 2 I cc[[8]]) w["G", "Y"] + I z^2/4 (E0 cc[[3]] + I cc[[25]] - 2 I cc[[9]]) w["G", "Z"] -
    z^2/2 (n cc[[13]] + 2 cc[[14]]) w["G", "T"] - z/2 (a1 + 2 a2 + a5 + t (b1 + 2 b2 + b5) + 2 cc[[15]] - 4 cc[[16]]) w["P", "B"] -
    z^2/2 (iE cc[[15]] + cc[[1]] + cc[[18]] + 2 cc[[2]]) w["P", "B0"] - z^2/2 (-2 iE cc[[16]] + cc[[20]] + cc[[4]] + 2 cc[[5]]) w["P", "U0"] -
    I z^2/4 (E0 cc[[4]] - 2 I n cc[[15]] + 4 I cc[[16]] - 2 I cc[[22]] - 2 I cc[[7]] - 4 I cc[[8]]) w["P", "F"] -
    I z^2/4 (E0 cc[[5]] - 4 I cc[[10]] + 4 I (n - 1) cc[[16]] - 2 I cc[[24]] - 2 I cc[[8]]) w["P", "Y"] - I z^2/4 (E0 cc[[6]] - 4 I cc[[11]] - 2 I cc[[26]] - 2 I cc[[9]]) w["P", "Z"] -
    z^2/2 (n cc[[15]] + 2 cc[[16]]) w["P", "T"] + z/2 (a3 + t b3) w["A", "B"] + cc[[3]] z^2/2 w["A", "B0"] + cc[[6]] z^2/2 w["A", "U0"] +
    z^2/2 (n cc[[1]] - cc[[4]] + cc[[9]]) w["A", "F"] + z^2/2 (n cc[[2]] - cc[[5]] + cc[[11]]) w["A", "Y"] + z^2/2 (n cc[[3]] - cc[[6]] + cc[[12]]) w["A", "Z"] +
    z/4 (-iE (a3 + t b3) + 2 (n - 1) (a1 + t b1) - 4 (a2 + t b2) + b3) w["H", "B"] + z^2/4 (-iE cc[[3]] + 2 (n - 1) cc[[1]] - 4 cc[[2]]) w["H", "B0"] +
    z^2/4 (-iE cc[[6]] + 2 (n - 1) cc[[4]] - 4 cc[[5]]) w["H", "U0"] + z^2/4 (-iE cc[[9]] + 2 (n - 1) cc[[7]] - 4 cc[[8]]) w["H", "F"] +
    z^2/4 (-iE cc[[11]] - 4 cc[[10]] + 2 (n - 1) cc[[8]]) w["H", "Y"] + z^2/4 (-iE cc[[12]] - 4 cc[[11]] + 2 (n - 1) cc[[9]]) w["H", "Z"] +
    z^2/2 (n cc[[13]] + cc[[15]]) w["Q", "D"] + z^2/2 (n cc[[14]] + cc[[16]]) w["Q", "L"];
  auditProjectionCleanup[Expand[R[auditC0, P1] + P2 /. If[n == 1, Thread[Join[{fitA[2], fitA[3], fitB[2], fitB[3]}, fitC /@ {2, 3, 5, 6, 8, 9, 10, 11, 12, 23, 24, 25, 26}] -> 0], {}]]]];

(* the draft's EOM: Appendix Q C_n + (EOMterms1st) + (NSsourceterm) + (RRsourceterm) - (EOMterms2nd) *)
LRTDraftTotal[n_, d_] := Module[{lrt = LRTlrt[n], N0 = LRTNorm[n]},
  auditProjectionCleanup[Expand[
    LRTDraftQC[n] +
     auditQFHPrinted[n, d]/N0 - 2 (d - 4) (d - 5) lrt + If[n >= 2, n (n - 1) LRTz^2/24 auditWedge[n, "K", p], 0] +      (* main-6 terms missing from the audit transcription *)
     auditNSPrinted[n, d]/N0 + 2 (d - 4) (d - 5) lrt + 2 (d - 1) n tau lrt -
     2 (d - 1) n tau lrt - auditJGeom[n, d, M]/N0]]];

LRTCompareWithDraft[comps_] := Module[{n = comps["n"], d = comps["d"], draftTotal, draftComps, keys, diff, lrt, N0, eqR, eqD},
  lrt = LRTlrt[n]; N0 = LRTNorm[n];
  Print["\n===== Step 2: comparison with the draft (n = ", n, ", d = ", d, ") ====="];
  Print["  Q V[F_H] vs (EOMterms1st): ", Length[auditTerms[auditProjectionCleanup[Expand[comps["QV"] - (auditQFHPrinted[n, d]/N0 - 2 (d - 4) (d - 5) lrt +
          If[n >= 2, n (n - 1) LRTz^2/24 auditWedge[n, "K", p], 0])]]]], " monomials differ"];
  Print["  S^NS vs (NSsourceterm):    ", Length[auditTerms[auditProjectionCleanup[Expand[comps["SNS"] - (auditNSPrinted[n, d]/N0 + 2 (d - 4) (d - 5) lrt + 2 (d - 1) n tau lrt)]]]], " monomials differ"];
  Print["  Q C vs Appendix formula:   ", Length[auditTerms[auditProjectionCleanup[Expand[(comps["QC"] /. {aT -> 0, bT -> 0}) - LRTDraftQC[n]]]]], " monomials differ",
    If[n == 1, "   (the B v Tbar columns aT, bT are not in the draft's formula and are compared separately below)", ""]];
  draftComps = LRTByComponent[LRTDraftTotal[n, d], n] /. LRTReadable;
  keys = Union[Keys[comps["components"]], Keys[draftComps]];
  diff = Select[keys, Expand[(Lookup[comps["components"], Key[#], 0] /. {aT -> 0, bT -> 0}) - Lookup[draftComps, Key[#], 0]] =!= 0 &];
  Print["  oscillator components: ", Length[keys], " in total, ", Length[keys] - Length[diff], " identical to the draft's system", If[diff === {}, "", ", differing: " <> StringRiffle[LRTLabel /@ diff, ", "]]];
  eqR = Union[Last /@ LRTEquations[<|"components" -> (comps["components"] /. {aT -> 0, bT -> 0})|>]];
  eqD = Union[Last /@ LRTEquations[<|"components" -> draftComps|>]];
  Print["  equation lists (with aT = bT = 0): recorded ", Length[eqR], ", draft ", Length[eqD], ", identical: ", Sort[eqR] === Sort[eqD]];
  If[n == 1, Print["  n = 1 B v Tbar columns: ", Length[Select[keys, !FreeQ[comps["components"][#], aT | bT] &]], " components involve aT, bT (from the recorded Q C_1 only)"]];
  ];


(* ::Section:: *)
(*Steps 3 and 4 \[LongDash] solve, print, compare*)


LRTUnknowns[eqs_] := Select[Join[Array[acoef, 5], Array[bcoef, 5], Array[ccoef, 26], {aT, bT, M}], !FreeQ[eqs, #] &];

LRTSolve[comps_] := Module[{eqs = Last /@ LRTEquations[comps], unk, sol},
  unk = LRTUnknowns[eqs];
  Print["\n===== Step 3: Solve[", Length[eqs], " equations, ", Length[unk], " unknowns (", Length[unk] - 1, " coefficients and M)] ====="];
  sol = Quiet[Solve[eqs, unk], Solve::svars];
  If[sol === {}, Print["  no solution"]; Return[{}]];
  Print["  free parameters: ", Complement[unk, Keys[First[sol]]]];
  First[sol]];

LRTDraftSolution[n_, d_] := Module[{e = LRTEnergy[n]},
  Join[Thread[Array[acoef, 5] -> {del (n + 1)/(2 n) + n (n + 2) (3 n - 1)/(4 n + 4) + If[n == 1, 1/4, 0], del (n^2 - 1)/(4 n) + n (3 n^3 + 3 n^2 - 5 n + 3)/(8 n + 8),
      I e n/4, (d + n + 3)/4, -n (d + n + 3)/8}],
   Thread[Array[bcoef, 5] -> {0, 0, 0, -I e/2, I e n/4}],
   Thread[Array[ccoef, 26] -> {I del/e, I del (n - 1)/(2 e), 0, I e del/4, I e del (n - 1)/8, 0, del, del (n - 1)/2, 0, del (n - 1)^2/4, 0, 0, del/(4 n) + 1/16,
      -del/8 - n/32, -del/4 - n/16, del n/8 + n^2/32, -I e/8, I e n/16, -I e n/8, I e n^2/16, -n/4, n^2/8, -n (n - 1)/8, n^2 (n - 1)/16, 0, 0}],
   {aT -> -1/4, bT -> 0, M -> 2 (n - 1) (3 n + 1)}]];

LRTPrintSolution[comps_, sol_] := Module[{n = comps["n"], d = comps["d"], draft, eqs = Last /@ LRTEquations[comps], unk, show, m1, m2, rows, res},
  draft = LRTDraftSolution[n, d]; unk = LRTUnknowns[eqs];
  show[ex_] := ToString[Simplify[ex], InputForm];
  m1 = {"B v Fbar", "B v Ybar", "B v Zbar", "c0+ B ^ Dbar", "c0+ B ^ Lbar"};
  m2 = {"B0 v Fbar", "B0 v Ybar", "B0 v Zbar", "U0 v Fbar", "U0 v Ybar", "U0 v Zbar", "F Fbar", "F v Ybar", "F v Zbar", "Y Ybar", "Y v Zbar", "Z Zbar",
    "G ^ Dbar", "G ^ Lbar", "P ^ Dbar", "P ^ Lbar", "c0+ B0 ^ Dbar", "c0+ B0 ^ Lbar", "c0+ U0 ^ Dbar", "c0+ U0 ^ Lbar", "c0+ F ^ Dbar", "c0+ F ^ Lbar",
    "c0+ Y ^ Dbar", "c0+ Y ^ Lbar", "c0+ Z ^ Dbar", "c0+ Z ^ Lbar"};
  rows = Join[
    Flatten[Table[If[MemberQ[unk, acoef[l]] || MemberQ[unk, bcoef[l]],
       {{"a_" <> ToString[l] <> "   z " <> m1[[l]], show[acoef[l] /. sol], show[acoef[l] /. draft]}, {"b_" <> ToString[l] <> "   z t " <> m1[[l]], show[bcoef[l] /. sol], show[bcoef[l] /. draft]}}, Nothing], {l, 5}], 1],
    If[n == 1, {{"aT   z B v Tbar", show[aT /. sol], show[aT /. draft]}, {"bT   z t B v Tbar", show[bT /. sol], show[bT /. draft]}}, {}],
    Table[If[MemberQ[unk, ccoef[l]], {"c_" <> ToString[l] <> "   z^2 " <> m2[[l]], show[ccoef[l] /. sol], show[ccoef[l] /. draft]}, Nothing], {l, 26}],
    {{"M_" <> ToString[n], show[M /. sol], show[M /. draft]}}];
  Print["\n===== Step 4: solution (n = ", n, ", d = ", d, "); draft with free parameter del ====="];
  Print[Grid[Prepend[rows, {"coefficient", "Solve", "draft"}], Alignment -> Left, Frame -> All]];
  res = DeleteCases[Union[Simplify[eqs /. draft]], True | 0];
  Print["  the draft's coefficients and M_", n, " = ", M /. draft, " ", If[res === {}, "solve all " <> ToString[Length[eqs]] <> " equations", "leave residuals " <> ToString[res, InputForm]]];
  res === {}];
