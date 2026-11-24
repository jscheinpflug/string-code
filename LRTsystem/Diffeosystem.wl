(* ::Package:: *)

(* ::Title:: *)
(*Diffeosystem.wl \[LongDash] F_H from the V_n component of eq. (diffeoDemand), App. app:Diffeo of main-6.tex*)


(* ::Text:: *)
(*Usage from a notebook (after Needs["StringCode`"] and InitStringCode[...]):*)
(**)
(*  Get["/path/to/this/folder/Diffeosystem.wl"];   (* paths below are relative to this folder; see README.md *)*)
(**)
(*  (* STEP 1 \[LongDash] assemble the V_n component of (diffeoDemand) *)*)
(*  DFRunBracket[n];  DFBracketStatus[n]     (* [lambda0 (x) V_n[T0]] in a background kernel *)*)
(*  comps = DFComponents[n];                  (* bracket + Q lambda_n - V_n[L_{V/8} T0] - V_n[F_{dV H}(T0)] *)*)
(*  (DFComponents[n, "draft"] uses the draft's bracket formula; DFComponents[n, expr, factor] a notebook bracket such as*)
(*   bDiff or n2Raised from Get[DFCacheFile["D1_bDiff.mx"]] / Get[DFCacheFile["D2_n2OPE.mx"]], times factor) *)
(**)
(*  (* STEP 2 \[LongDash] print the system and compare with the draft *)*)
(*  DFPrintSystem[comps];*)
(*  DFCompareWithDraft[comps];*)
(**)
(*  (* STEP 3 \[LongDash] solve for the F_H coefficients and the compensator profile coefficients *)*)
(*  sol = DFSolve[comps];               (* particular solution + the free F_H directions *)*)
(**)
(*  (* STEP 4 \[LongDash] print F_H and compare with the draft *)*)
(*  DFPrintSolution[comps, sol];*)
(**)
(*Method. Every term is linear in V and in T0 = e^{ik.X} u^{(x)s}, s = 2n+2; e^{ik.X} and N_n are stripped.*)
(*V is a general cubic, so its jets dV[a, {d1,...}] = d_{d1}...d V_a (at most three derivatives) are independent.*)
(*The V_n component is projected onto its totally symmetric part by contracting the s word indices with a generic vector w.*)
(*Index labels: p = u, kk = k, w = w, tr = a traced pair.  u.u = u.k = 0, k.k = -4n, and w enters through*)
(*wu = w.u, kw = k.w, ww = w.w.  No sqrt(n) appears, so all arithmetic is exact over Q(i).*)
(*Each scalar equation is the coefficient of one monomial (V jet) x wu^a kw^b ww^c.*)
(*Unknowns: fH[i] (F_H, general, linear in H, at most two derivatives counting k's) and lam[l, j] (profile of the*)
(*compensator basis element l of Qlambda<n>paper.m, general tensor linear in V, of degree s in u).*)


(* ::Section:: *)
(*Paths and settings (each can be set before Get)*)


If[!ValueQ[DF$Dir], DF$Dir = If[StringQ[$InputFileName] && FileExistsQ[$InputFileName], DirectoryName[$InputFileName], Directory[]]];
If[!ValueQ[DF$Cache], DF$Cache = FileNameJoin[{DF$Dir, "cache"}]];
If[!ValueQ[DF$Data], DF$Data = FileNameJoin[{DF$Dir, "data"}]];           (* Qlambda<n>paper.m: BRST actions of the compensator basis *)
If[!ValueQ[DF$Kernel], DF$Kernel = First[$CommandLine]];                  (* the kernel used for background runs *)
If[!ValueQ[DF$KMax], DF$KMax = 3];                       (* max number of k's in a compensator profile *)
If[!ValueQ[DF$PunctureSign], DF$PunctureSign = 1];       (* +1: z[2,1] = +1/2, z[2,2] = -1/2, z0 = -1/2 (the LRT chart) *)
If[!DirectoryQ[DF$Cache], CreateDirectory[DF$Cache]];

DFQlambdaFile[n_] := FileNameJoin[{DF$Data, "Qlambda" <> ToString[n] <> "paper.m"}];
DFBracketFile[n_] := FileNameJoin[{DF$Cache, "D" <> ToString[n] <> "_bracket.mx"}];
DFBracketLog[n_] := FileNameJoin[{DF$Cache, "D" <> ToString[n] <> "_bracket.log"}];
DFCacheFile[name_String] := FileNameJoin[{DF$Cache, name}];

SetAttributes[DFInert, HoldAll];
DFInert[body_] := Block[{R, ProfileX, der, dot, \[Delta]}, body];
DFTerms[e_] := Which[e === 0, {}, Head[e] === Plus, List @@ e, True, {e}];


(* ::Section:: *)
(*Kinematics*)


DFRank[n_] := 2 n + 2;
DFLabels = {p, kk, w};
DFLabelQ[x_] := MemberQ[DFLabels, x];
DFdot[a_, b_, n_] := Switch[Sort[{a, b}], {kk, kk}, -4 n, {kk, p}, 0, {p, p}, 0, {kk, w}, kw, {p, w}, wu, {w, w}, ww, _, $Failed];
DFSeedHead[n_] := {DFT1, DFT2, DFT3}[[n]];

(* jets of V: dV[a, sorted ds], traces labelled tr; V cubic *)
DFjet[a_, ds_List] := Module[{all = Prepend[ds, a], dums, cnt},
   If[Length[ds] > 3, Return[0]];
   dums = Select[DeleteDuplicates[all], !DFLabelQ[#] && # =!= tr &];
   cnt = Count[all, #] & /@ dums;
   If[AnyTrue[cnt, # =!= 2 &], Return[$Failed]];
   dV[a /. Thread[dums -> tr], Sort[ds /. Thread[dums -> tr]]]];
DFd[lab_][e_] := Expand[e /. dV[a_, ds_] :> If[Length[ds] >= 3, 0, dV[a, Sort[Append[ds, lab]]]]];


(* ::Section:: *)
(*Reduction of StringCode terms to the w-contracted V_n component*)


DFVnQ[word_R, n_] := Module[{f = DeleteCases[List @@ word, _ProfileX]},
   Sort[Head /@ f] === Sort[Join[{c, ct, exp\[Phi]f, exp\[Phi]tf, \[Psi], \[Psi]t}, ConstantArray[dX, n], ConstantArray[dXt, n]]] &&
    AllTrue[Cases[f, (c | ct)[k_, _] :> k], # == 0 &] && AllTrue[Cases[f, (\[Psi] | \[Psi]t | dX | dXt)[_, k_, _] :> k], # == 0 &] &&
    AllTrue[Cases[f, (exp\[Phi]f | exp\[Phi]tf)[q_, _] :> q], # == -1 &]];

(* V_n[U] in the draft's order: c e^{-phi} dX..dX psi cbar e^{-phibar} dXbar..dXbar psibar; the sign of its canonical R form *)
DFVnWord[n_, idx_List] := R @@ Join[{c[0, 0], exp\[Phi]f[-1, 0]}, Table[dX[idx[[i]], 0, 0], {i, n}], {\[Psi][idx[[n + 1]], 0, 0], ct[0, 0], exp\[Phi]tf[-1, 0]},
    Table[dXt[idx[[i]], 0, 0], {i, n + 2, 2 n + 1}], {\[Psi]t[idx[[2 n + 2]], 0, 0]}];
DFVnSign[n_] := DFVnSign[n] = Module[{e = Expand[DFVnWord[n, ConstantArray[w, DFRank[n]]]]}, Coefficient[e, First[Cases[{e}, _R, {0, Infinity}]]]];

(* contract the deltas of ONE monomial (no R left) and turn V profiles into jets *)
DFcontract[mono_, n_] := Module[{t = mono /. \[Delta] -> dd, d},
   While[(d = FirstCase[{t}, dd[a_, b_] /; !DFLabelQ[a] || !DFLabelQ[b], None, {0, Infinity}]) =!= None,
    Which[d[[1]] === d[[2]], t = t /. d -> 10,
     !DFLabelQ[d[[1]]], t = (t /. d -> 1) /. d[[1]] -> d[[2]],
     True, t = (t /. d -> 1) /. d[[2]] -> d[[1]]]];
   t = t /. dd[a_, b_] :> DFdot[a, b, n];
   t = t /. ProfileX[Vp[a_], ds_List, _, _] :> DFjet[a, ds];
   If[!FreeQ[t, $Failed | _ProfileX | _R | _dd], Print["DFcontract: cannot reduce ", InputForm[mono]]; Abort[]];
   t];

(* one expanded StringCode monomial -> its w-contracted V_n coefficient, relative to V_n[w^s] in the draft's order.
   profSub is applied to the profiles once they are out of the word (used for the compensator ansatz) *)
DFreduce[mono_, n_, profSub_: {}] := Module[{word, idx, t},
   word = FirstCase[{mono}, _R, None, {0, Infinity}];
   If[word === None || !DFVnQ[word, n], Return[0]];
   idx = Cases[List @@ word, (\[Psi] | \[Psi]t | dX | dXt)[i_, _, _] :> i];
   t = Expand[(mono /. word -> (Times @@ Cases[List @@ word, _ProfileX])) /. profSub];
   Do[Which[
      DFLabelQ[ti[[1]]], t = t DFdot[ti[[1]], w, n]^ti[[2]],
      ti[[2]] == 2, t = t ww,                                   (* pair traced inside the word: eta -> w.w *)
      True, t = t /. ti[[1]] -> w], {ti, Tally[idx]}];
   Expand[Total[DFcontract[#, n] & /@ DFTerms[Expand[t]]]/DFVnSign[n]]];


(* ::Section:: *)
(*Step 1a \[LongDash] the bracket [lambda0 (x) V_n[T0]]*)


(* start a worker script in a detached background kernel (macOS / Linux shell) *)
DFLaunch[script_String, args_List, out_String] := Run["nohup " <> StringRiffle[("'" <> ToString[#] <> "'") & /@ Join[{DF$Kernel, "-script", script}, args], " "] <>
    " > '" <> out <> "' 2>&1 &"];
DFRunBracket[n_] := (DFLaunch[FileNameJoin[{DF$Dir, "Diffeobrackets.wls"}], {n, DF$Cache}, FileNameJoin[{DF$Cache, "D" <> ToString[n] <> "_bracket.out"}]];
   Print["bracket kernel started for n = ", n, ". Follow it with DFBracketStatus[", n, "]; result in ", DFBracketFile[n]]);
DFBracketStatus[n_] := If[FileExistsQ[DFBracketLog[n]], Column[ReadList[DFBracketLog[n], String]], "not started"];

(* chart: punctures at +-1/2 (the (2z)^{k.p} kernel -> 1), momentum exponents dropped, r0 kept as rr to check that its
   power is uniform, alpha' = 1; the seed profile e^{ik.X} is stripped, so each derivative on it gives i k *)
DFChart[n_] := With[{sd = DFSeedHead[n], z1 = DF$PunctureSign/2}, {
    (* StringCode evaluates z[2,1][{}] -> -z0 and z[2,2][{}] -> z0, so the holomorphic punctures enter through z0 *)
    Private`zbar[2, 1][{}] -> z1, Private`zbar[2, 2][{}] -> -z1,
    Private`q[2, _][{}] -> rr, Private`qbar[2, _][{}] -> rr, Private`r0 -> rr, z0 -> -z1, \[Alpha]p -> 1,
    ProfileX[sd, ds_List, _, _] :> Times @@ ((I \[Delta][#, kk]) & /@ ds),
    HoldPattern[der[sd][j_]] :> I \[Delta][j, kk]}];

DFBracketVn[n_] := Module[{br, e, pw},
   If[!FileExistsQ[DFBracketFile[n]], Print["no bracket yet for n = ", n, ": run DFRunBracket[", n, "]"]; Abort[]];
   br = DFInert[Get[DFBracketFile[n]]; DFbracketRaw];
   (* momentum-dependent exponents -> 0; a dot[] anywhere else would be a genuine momentum factor *)
   e = br /. Power[b_, ex_] /; !FreeQ[ex, dot] :> Power[b, ex /. HoldPattern[dot[__]] -> 0];
   If[!FreeQ[e, dot], Print["dot[] outside an exponent: the dot -> 0 chart is not valid here"]; Abort[]];
   e = Expand[e /. DFChart[n]];
   If[!FreeQ[e, DFSeedHead[n] | z0 | (Private`z | Private`zbar | Private`q | Private`qbar)[2, _][{}]], Print["bracket chart left placeholders"]; Abort[]];
   pw = Union[Exponent[#, rr] & /@ DFTerms[e]];
   Print["  bracket: uniform power of r0 (dropped) ", pw];
   e = Expand[derAppend[Expand[e /. rr -> 1]]];
   If[!FreeQ[e, HoldPattern[der[_][_]]], Print["unattached der after derAppend"]; Abort[]];
   Expand[Total[DFreduce[#, n] & /@ DFTerms[e]]]];


(* the same from a bracket expression computed in the notebook (e.g. bDiff, n2Raised, bracketDiffn2):
   seed profile U1/U2/U3[slots] (slots -> u), gauge profile V[mu]; raw placeholders or twoBracketReplRule form (punctures at +-z, z -> 1/2 here);
   uniform powers of r0 and of the OPE position z0, z0bar are reported and dropped *)
DFBracketVnFrom[expr_, n_] := Module[{sd = {U1, U2, U3}[[n]], e, slots, pw, chart},
   e = expr /. Power[b_, ex_] /; !FreeQ[ex, dot] :> Power[b, ex /. HoldPattern[dot[__]] -> 0];
   If[!FreeQ[e, dot], Print["dot[] outside an exponent: the dot -> 0 chart is not valid here"]; Abort[]];
   (* raw placeholders (if twoBracketReplRule was not applied in the notebook) -> the twoBracketReplRule form *)
   (* StringCode evaluates z[2,1][{}] -> -z0, z[2,2][{}] -> z0 and q[2,_][{}] -> r0 on reading. In an OPE-route expression
      (seed inserted at z0, z0bar, as in n2OPE / n2Raised) z0 is the insertion point and is left alone *)
   e = e /. Join[If[FreeQ[e, z0bar], {z0 -> -z}, {}],
      {Private`zbar[2, 1][{}] -> z, Private`zbar[2, 2][{}] -> -z, Private`q[2, _][{}] -> Private`r0, Private`qbar[2, _][{}] -> Private`r0}];
   (* T0 = u^s: a seed with a repeated slot (a trace left by ContractDelta) is u.u = 0; every other slot, including dummies, is u *)
   e = e /. With[{s = sd}, ProfileX[s[a__], _List, _, _] /; !DuplicateFreeQ[{a}] :> 0];
   slots = DeleteDuplicates[Flatten[Cases[e, sd[a__] :> {a}, {0, Infinity}]]];
   e = e /. {ProfileX[V[a_], r__] :> ProfileX[Vp[a], r], HoldPattern[der[V[a_]]] :> der[Vp[a]]};
   chart = With[{s = sd}, {z -> DF$PunctureSign/2, Private`r0 -> rr, r0 -> rr, \[Alpha]p -> 1,     (* With: HoldPattern must see U1 / U2 *)
     ProfileX[s[__], ds_List, _, _] :> Times @@ ((I \[Delta][#, kk]) & /@ ds), HoldPattern[der[s[__]][j_]] :> I \[Delta][j, kk]}];
   e = Expand[(e /. chart) /. Thread[slots -> p]];
   If[!FreeQ[e, sd | (Private`z | Private`zbar | Private`q | Private`qbar)[2, _][{}]],
    Print["bracket chart left: ", Take[DeleteDuplicates[Cases[e, x : (_sd | (Private`z | Private`zbar | Private`q | Private`qbar)[2, _][{}]), {0, Infinity}]], UpTo[5]]]; Abort[]];
   pw = Union[{Exponent[#, rr], Exponent[#, z0], Exponent[#, z0bar]} & /@ DFTerms[e]];
   Print["  supplied bracket: powers {r0, z0, z0bar} ", pw, If[Length[pw] == 1, " (uniform, dropped)", "  NOT UNIFORM"]];
   If[Length[pw] == 1, e = Expand[e /. {rr -> 1, z0 -> 1, z0bar -> 1}]];
   e = Expand[derAppend[e]];
   If[!FreeQ[e, HoldPattern[der[_][_]]], Print["unattached der after derAppend"]; Abort[]];
   Expand[Total[DFreduce[#, n] & /@ DFTerms[e]]]];


(* ::Section:: *)
(*Step 1b \[LongDash] Q lambda_n: exported compensator actions with a general profile ansatz*)


DFFreeIndices[e_] := Sort[DeleteDuplicates[Cases[e, s_Symbol /; StringMatchQ[SymbolName[s], "mu" ~~ DigitCharacter ..], {0, Infinity}]]];
DFMatchings[l_List] := If[Length[l] < 2, {{}}, With[{f = First[l]},
    Join[DFMatchings[Rest[l]], Flatten[Table[Prepend[#, {f, x}] & /@ DFMatchings[DeleteCases[Rest[l], x]], {x, Rest[l]}], 1]]]];

(* every tensor structure of a rank-r profile, linear in V, of degree s in u, at most DF$KMax k's, V cubic.
   A free index is u, k, the index of V, a derivative index of V, or paired with another free index (eta);
   the V slots left over carry u, k or traces. e^{ik.X} is stripped. *)
DFProfileStructures[free_List, n_] := Module[{r = Length[free], s = DFRank[n], out = {}},
   Do[Module[{rest = Complement[Range[r], Flatten[m]], etas},
      etas = Times @@ (\[Delta][free[[#[[1]]]], free[[#[[2]]]]] & /@ m);
      Do[Module[{nu = Count[rv, "u"], nk = Count[rv, "k"], vI = Pick[free[[rest]], rv, "V"], dI = Pick[free[[rest]], rv, "d"], base},
         If[Length[vI] <= 1 && Length[dI] <= 3,
          base = etas Times @@ MapThread[Switch[#2, "u", \[Delta][#1, p], "k", \[Delta][#1, kk], _, 1] &, {free[[rest]], rv}];
          Do[Module[{fill = If[vI === {}, Prepend[ex, a0], ex], nt, k = 0, rho, slots, a, ds},
             nt = Count[fill, tr];
             If[nu + Count[fill, p] == s && nk + Count[fill, kk] <= DF$KMax && EvenQ[nt],
              rho = {\[Rho]1, \[Rho]2};
              slots = fill /. tr :> rho[[Quotient[k++, 2] + 1]];
              {a, ds} = If[vI === {}, {First[slots], Join[dI, Rest[slots]]}, {First[vI], Join[dI, slots]}];
              AppendTo[out, base ProfileX[Vp[a], ds, 0, 0]]]],
           {a0, If[vI === {}, {p, kk, tr}, {Null}]},
           {ex, Join @@ Table[Sort /@ Union[Sort /@ Tuples[{p, kk, tr}, j]], {j, 0, 3 - Length[dI]}]}]]],
        {rv, Tuples[{"u", "k", "V", "d"}, Length[rest]]}]], {m, DFMatchings[Range[r]]}];
   DeleteDuplicates[out]];

(* derivatives of e^{ik.X} S (e^{ik.X} stripped) *)
DFProfileDerivative[S_, {}] := S;
DFProfileDerivative[S_, ds_List] := DFProfileDerivative[
   I \[Delta][First[ds], kk] S + (S /. ProfileX[Vp[a_], js_List, 0, 0] :> ProfileX[Vp[a], Append[js, First[ds]], 0, 0]), Rest[ds]];

(* the V_n component of Q lambda_n with the general ansatz; returns <|"image" -> expr, "unknowns" -> {...}, "structures" -> <|..|>|> *)
DFQlambdaVn[n_] := Module[{ql, out = 0, unk = {}, structs = <||>, t0 = AbsoluteTime[]},
   ql = Get[DFQlambdaFile[n]];
   Do[Module[{e = Expand[derAppend[Expand[ql[[i]] /. \[Alpha]p -> 1]]], prof, label, free, S, sub, img},   (* der[lambda][mu] factors -> profile derivatives *)
      If[!FreeQ[e, HoldPattern[der[_][_]]], Print["unattached der in Q lambda entry ", i]; Abort[]];
      prof = First[Cases[e, ProfileX[h_, _, _, _] :> h, {0, Infinity}]]; label = First[prof];
      free = DFFreeIndices[e];
      S = DFProfileStructures[free, n];
      structs[label] = <|"free" -> free, "structures" -> S|>;
      sub = {ProfileX[prof, ds_List, _, _] :> Sum[lam[label, j] DFProfileDerivative[S[[j]], ds], {j, Length[S]}]};
      img = Expand[Total[DFreduce[#, n, sub] & /@ DFTerms[Expand[e]]]];
      Print["  Q lambda: element ", label, " (rank ", Length[free], "): ", Length[S], " profile structures, V_n image of ",
       Length[DFTerms[img]], " monomials (", Round[AbsoluteTime[] - t0], " s)"];
      out += img; unk = Join[unk, Array[lam[label, #] &, Length[S]]]], {i, Length[ql]}];
   <|"image" -> out, "unknowns" -> unk, "structures" -> structs|>];


(* ::Section:: *)
(*Step 1c \[LongDash] the right-hand side: V_n[L_{V/8} T0] + V_n[F_{dV H}(T0)]*)


(* Lie derivative of the covariant T0 along V/8, contracted with w^s *)
DFLie[n_] := With[{s = DFRank[n]}, Expand[(I dV[kk, {}] wu^s + s wu^(s - 1) dV[p, {w}])/8]];

(* F_H ansatz: monomials wu^a kw^b ww^c dH[{x, y}, {ds}], linear in H with |ds| + (number of k's) <= 2,
   degree s in u and in w; traced pairs carry the labels t1, t2 *)
DFHcanon[dH[xy_List, ds_List]] := First[Sort[{dH[Sort[xy], Sort[ds]], dH[Sort[xy /. {t1 -> t2, t2 -> t1}], Sort[ds /. {t1 -> t2, t2 -> t1}]]}]];
DFHStructures[n_] := Module[{s = DFRank[n], out = {}},
   Do[Module[{slots = Join[xy, ds], np, nw, nk, a, b, c},
      If[Count[slots, t1] == 2 && Count[slots, t2] == 2 || Count[slots, t1] == 2 && Count[slots, t2] == 0 || Count[slots, t1] == 0 && Count[slots, t2] == 0,
       np = Count[slots, p]; nw = Count[slots, w]; nk = Count[slots, kk];
       a = s - np;
       Do[c = (np - nw - b)/2;
        If[a >= 0 && IntegerQ[c] && c >= 0 && Length[ds] + nk + b <= 2,
         AppendTo[out, wu^a kw^b ww^c DFHcanon[dH[xy, ds]]]], {b, 0, 2}]]],
    {m, 0, 2}, {xy, Tuples[{p, kk, w, t1, t2}, 2]}, {ds, Tuples[{p, kk, w, t1, t2}, m]}];
   DeleteDuplicates[out]];

(* F_{dV H}: H_{xy} -> (d_x V_y + d_y V_x)/8 *)
DFHtoV[e_] := Expand[e /. dH[{x_, y_}, ds_List] :> (DFjet[y, Append[ds, x]] + DFjet[x, Append[ds, y]])/8];

DFFAnsatz[n_] := Module[{S = DFHStructures[n]}, <|"structures" -> S, "unknowns" -> Array[fH, Length[S]], "F" -> S . Array[fH, Length[S]]|>];


(* ::Section:: *)
(*Step 1 \[LongDash] all components*)


(* src: "recorded" (the StringCode bracket in DFBracketFile[n]), "draft" (the draft's R0/R1/R2 formula), or a bracket expression
   from the notebook (e.g. bDiff, n2Raised), multiplied by factor (e.g. 2 if it is one half of lambda0 and the halves contribute equally) *)
DFComponents[n_, src_: "recorded", factor_: 1] := Module[{br, ql, fa, lie, total, vars, rules, t0 = AbsoluteTime[],
    bracketSource = Which[src === "recorded" || src === "draft", src, True, "supplied"]},
   Print["Step 1: V_", n, " component of (diffeoDemand), contracted with w^", DFRank[n], "  [bracket: ", bracketSource,
    If[factor =!= 1, " x " <> ToString[factor, InputForm], ""], "]"];
   br = factor Which[src === "draft", DFDraftBracket[n], src === "recorded", DFBracketVn[n], True, DFBracketVnFrom[src, n]];
   Print["  bracket [lambda0 (x) V_n[T0]]: ", Length[DFTerms[br]], " monomials"];
   ql = DFQlambdaVn[n];
   fa = DFFAnsatz[n];     Print["  F_H ansatz: ", Length[fa["structures"]], " structures"];
   lie = DFLie[n];
   total = Expand[br + ql["image"] - lie - DFHtoV[fa["F"]]];
   If[!FreeQ[total, $Failed], Print["reduction failure"]; Abort[]];
   vars = Join[DeleteDuplicates[Cases[total, _dV, {0, Infinity}]], {wu, kw, ww}];
   rules = CoefficientRules[total, vars];
   Print["  ", Length[rules], " scalar equations (", Round[AbsoluteTime[] - t0], " s)"];
   <|"n" -> n, "bracket" -> br, "Qlambda" -> ql, "F" -> fa, "Lie" -> lie, "total" -> total, "vars" -> vars,
    "equations" -> (Times @@ (vars^#[[1]]) -> #[[2]] &) /@ rules, "bracketSource" -> bracketSource|>];


(* ::Section:: *)
(*Readable printing*)


DFlab[x_] := Switch[x, p, "u", kk, "k", w, "w", tr, "\[Rho]", t1, "\[Rho]", t2, "\[Sigma]", _, ToString[x]];
DFVString[dV[a_, ds_]] := StringJoin[("\[PartialD]" <> DFlab[#]) & /@ ds] <> "V" <> DFlab[a];
DFHString[dH[{x_, y_}, ds_]] := StringJoin[("\[PartialD]" <> DFlab[#]) & /@ ds] <> "H" <> DFlab[x] <> DFlab[y];
DFMonoString[m_] := StringRiffle[Join[
    Table[With[{k = Exponent[m, v[[1]]]}, If[k > 0, v[[2]] <> If[k > 1, "^" <> ToString[k], ""], Nothing]], {v, {{wu, "(u.w)"}, {kw, "(k.w)"}, {ww, "(w.w)"}}}],
    DFVString /@ Cases[{m}, _dV, {0, Infinity}], DFHString /@ Cases[{m}, _dH, {0, Infinity}]], " "];
(* the structural part of a term: powers of wu, kw, ww and the V or H jet *)
DFStruct[t_] := wu^Exponent[t, wu] kw^Exponent[t, kw] ww^Exponent[t, ww] (Times @@ Cases[{t}, _dV | _dH, {0, Infinity}]);
DFGroup[e_] := GroupBy[DFTerms[Expand[e]], DFStruct -> (#/DFStruct[#] &), Total];
DFCoefString[c_] := With[{cs = Simplify[c]}, If[Head[cs] === Plus, "(" <> ToString[cs, InputForm] <> ")", ToString[cs, InputForm]]];
DFReadable[e_, ___] := If[Expand[e] === 0, "0", StringRiffle[KeyValueMap[DFCoefString[#2] <> " " <> DFMonoString[#1] &, DFGroup[e]], "\n    + "]];
(* coefficient vectors of several expressions on a common list of structures *)
DFMatrix[es_List] := Module[{gs = DFGroup /@ es, keys}, keys = Union @@ (Keys /@ gs); {Table[Lookup[g, keys, 0], {g, gs}], keys}];

(* split one equation into the part without compensator unknowns and the number of compensator unknowns it involves *)
DFPrintSystem[comps_] := Module[{eqs = comps["equations"]},
   Print["\n===== V_", comps["n"], " component: bracket + Q lambda - L_{V/8}T0 - F_{dV H}(T0) = 0, one equation per (V jet) x (u.w)^a (k.w)^b (w.w)^c ====="];
   Do[Module[{c = Last[eq], lamPart, rest},
      lamPart = Select[DFTerms[Expand[c]], !FreeQ[#, _lam] &];
      rest = Expand[c - Total[lamPart]];
      Print["  [", DFMonoString[First[eq]], "]   ", ToString[Collect[rest, _fH], InputForm],
       If[lamPart === {}, "", "  + (compensators: " <> ToString[Length[DeleteDuplicates[Cases[lamPart, _lam, {0, Infinity}]]]] <> " lam's)"], "  == 0"]], {eq, eqs}];
   Print["(", Length[eqs], " equations)"]];


(* ::Section:: *)
(*The draft's formulas (App. app:Diffeo), contracted with w*)


(* operators on V jets: D_w = d_w - i k.w,  D+_w = d_w + i k.w,  (u.d) *)
DFDw[x_] := DFd[w][x] - I kw x;  DFDpw[x_] := DFd[w][x] + I kw x;  DFud[x_] := DFd[p][x];
DFpow[op_, k_, x_] := Nest[op, x, k];

DFDraftBracket[n_] := Module[{s = DFRank[n], R0, R1, R2, rho, V},
   V = dV[rho, {}];
   R0[x_] := wu^s x + n/2 wu^(s - 1) DFDw[DFud[x]] + n (3 n - 1)/32 wu^(s - 2) DFpow[DFDw, 2, DFpow[DFud, 2, x]] +
     n (n - 1) (5 n - 1)/576 wu^(s - 3) DFpow[DFDw, 3, DFpow[DFud, 3, x]];
   R1[x_] := wu^(s - 1) x + 3 n/8 wu^(s - 2) DFDw[DFud[x]] + n (5 n - 2)/96 wu^(s - 3) DFpow[DFDw, 2, DFpow[DFud, 2, x]] +
     5 n (n - 1) (7 n - 2)/9216 wu^(s - 4) DFpow[DFDw, 3, DFpow[DFud, 3, x]];
   R2[x_] := wu^(s - 2) x + (3 n - 1)/8 wu^(s - 3) DFDw[DFud[x]] + (n - 1) (5 n - 1)/96 wu^(s - 4) DFpow[DFDw, 2, DFpow[DFud, 2, x]];
   With[{rho2 = rho}, Module[{ct},
     ct[x_, how_] := Expand[x /. dV[rho2, ds_] :> Switch[how, "div", If[Length[ds] >= 3, 0, dV[tr, Sort[Append[ds, tr]]]],
          "ik", I dV[kk, ds], "u", dV[p, ds], "w", dV[w, ds]]];
     Expand[(ct[R0[V], "div"] + ct[R0[V], "ik"])/8 + (n + 1)/16 (ct[DFDw[R1[V]], "u"] - 2 ct[DFud[R1[V]], "w"]) + n/32 ww ct[DFud[R2[V]], "u"]]]]];

DFDraftF[n_] := With[{s = DFRank[n]}, Expand[
    1/2 dH[{t1, t1}, {}] wu^s - (n + 1) dH[{p, w}, {}] wu^(s - 1) +
     I n/2 (dH[{kk, w}, {p}] + dH[{kk, p}, {w}] - dH[{p, w}, {kk}]) wu^(s - 1) - I n/2 dH[{t1, t1}, {p}] kw wu^(s - 1) +
     3 I n (n + 1)/4 kw (dH[{p, w}, {p}] - dH[{p, p}, {w}]) wu^(s - 2)] /. h_dH :> DFHcanon[h]];

DFDraftQlambda[n_] := Module[{s = DFRank[n], at, a1, a2, a3, rt, r1, r2},
   at = (n + 1)/16 dV[p, {}] + I n/16 dV[kk, {p}] - n/16 dV[tr, {p, tr}];
   a1 = -3 I n (n + 1)/128 kw dV[p, {p}] + n (3 n - 1)/256 kw dV[kk, {p, p}] - 3 n (n + 1)/128 dV[p, {p, w}] + 3 n (n + 1)/64 dV[w, {p, p}] -
     I n (3 n - 1)/256 kw dV[tr, {p, p, tr}] + 3 I n (3 n - 1)/256 dV[kk, {p, p, w}];
   a2 = -n (n + 1) (5 n - 2)/1536 kw^2 dV[p, {p, p}] - I n (n - 1) (5 n - 1)/4608 kw^2 dV[kk, {p, p, p}] -
     I n (n + 1) (5 n - 2)/384 kw dV[p, {p, p, w}] + I n (n + 1) (5 n - 2)/768 kw dV[w, {p, p, p}];
   a3 = 5 I n (n - 1) (n + 1) (7 n - 2)/147456 kw^3 dV[p, {p, p, p}];
   rt = -n/32 dV[p, {p}];
   r1 = I n (3 n - 1)/256 kw dV[p, {p, p}] - n (3 n - 1)/256 dV[p, {p, p, w}];
   r2 = n (n - 1) (5 n - 1)/3072 kw^2 dV[p, {p, p, p}];
   Expand[DFDpw[at wu^(s - 1) + a1 wu^(s - 2) + a2 wu^(s - 3) + a3 wu^(s - 4)] + ww (rt wu^(s - 2) + r1 wu^(s - 3) + r2 wu^(s - 4))]];

(* draft coefficients of the F_H ansatz *)
DFDraftFCoefficients[comps_] := Module[{S = comps["F"]["structures"], d = DFDraftF[comps["n"]]},
   Thread[comps["F"]["unknowns"] -> (Lookup[DFGroup[d], #, 0] &) /@ S]];


(* ::Section:: *)
(*Step 2 \[LongDash] comparison with the draft*)


DFLinearSolveQ[eqs_, unk_] := Module[{sol = Quiet[Solve[(# == 0 &) /@ eqs, unk]]}, If[sol === {}, $Failed, First[sol]]];
DFCoefficientsOf[e_, vars_] := Last /@ CoefficientRules[Expand[e], vars];

DFCompareWithDraft[comps_] := Module[{n = comps["n"], br, dq, df, lie, vars, r1, r2, r3, solQ, draftF, qlUnk = comps["Qlambda"]["unknowns"]},
   br = comps["bracket"]; dq = DFDraftQlambda[n]; df = DFHtoV[DFDraftF[n]]; lie = comps["Lie"];
   Print["\n===== Step 2: comparison with the draft (n = ", n, ") ====="];
   r1 = Expand[br - DFDraftBracket[n]];
   Print["  ", comps["bracketSource"], " bracket vs the draft's (R0, R1, R2) formula: ", Length[DFTerms[r1]], " monomials differ"];
   If[r1 =!= 0, Module[{gb = DFGroup[br], gd = DFGroup[DFDraftBracket[n]], ks, rat},
      ks = Union[Keys[gb], Keys[gd]];
      rat = Union[Simplify[Lookup[gb, #, 0]/Lookup[gd, #, 0]] & /@ Select[ks, Lookup[gd, #, 0] =!= 0 &]];
      Print["    ratio ", comps["bracketSource"], "/draft on the draft's structures: ", rat,
       "; structures absent from the draft: ", Length[Complement[Select[ks, Lookup[gb, #, 0] =!= 0 &], Keys[gd]]]];
      Print["    ", comps["bracketSource"], " - draft = ", DFReadable[r1]]]];
   r2 = Expand[DFDraftBracket[n] + dq - lie - df];
   Print["  the draft's own V_n equation (its bracket + its Q lambda - L_{V/8}T0 - its F_{dV H}): residual ", Length[DFTerms[r2]], " monomials"];
   If[r2 =!= 0, Print["    residual = ", DFReadable[r2]]];
   vars = Join[DeleteDuplicates[Cases[{dq, comps["Qlambda"]["image"]}, _dV, {0, Infinity}]], {wu, kw, ww}];
   solQ = DFLinearSolveQ[DFCoefficientsOf[comps["Qlambda"]["image"] - dq, vars], qlUnk];
   Print["  the draft's Q lambda_n|V_n is ", If[solQ === $Failed, "NOT ", ""], "reproduced by the exported compensators with some profile"];
   r3 = Expand[br + dq - lie - df];
   Print["  ", comps["bracketSource"], " bracket + the draft's Q lambda - L_{V/8}T0 - the draft's F_{dV H}: residual ", Length[DFTerms[r3]], " monomials"];
   If[r3 =!= 0, Print["    residual = ", DFReadable[r3]]];
   <|"bracket" -> r1, "draftSystem" -> r2, "QlambdaRealized" -> (solQ =!= $Failed), "recordedWithDraft" -> r3|>];


(* ::Section:: *)
(*Step 3 \[LongDash] solve*)


(* linear algebra on eqs = b + A.x:  particular solution, and the F_H directions left free (projection of the null space of A) *)
DFSolve[comps_] := Module[{eqs = Last /@ comps["equations"], unk, b, A, xp, nul, fIdx, fdirs, t0 = AbsoluteTime[]},
   unk = Join[comps["F"]["unknowns"], Select[comps["Qlambda"]["unknowns"], !FreeQ[eqs, #] &]];
   {b, A} = Normal /@ CoefficientArrays[eqs, unk];
   Print["\n===== Step 3: solve ", Length[eqs], " equations for ", Length[unk], " unknowns (", Count[unk, _fH], " F_H coefficients fH, ",
    Count[unk, _lam], " compensator profile coefficients lam) ====="];
   xp = Quiet[Check[LinearSolve[A, -b], $Failed]];
   If[xp === $Failed, Print["  INCONSISTENT: no F_H and compensator profile solve the system"]; Return[<|"consistent" -> False|>]];
   nul = NullSpace[A];
   fIdx = Flatten[Position[unk, _fH, {1}, Heads -> False]];
   fdirs = DeleteCases[RowReduce[If[nul === {}, {ConstantArray[0, Length[fIdx]]}, nul[[All, fIdx]]]], {0 ..}];
   Print["  consistent. F_H is fixed up to ", Length[fdirs], " free direction(s) in the ", Length[fIdx], "-dimensional ansatz (",
    Round[AbsoluteTime[] - t0], " s)"];
   <|"consistent" -> True, "unknowns" -> unk, "particular" -> Thread[unk -> xp], "Fparticular" -> xp[[fIdx]], "Fdirections" -> fdirs|>];


(* ::Section:: *)
(*Step 4 \[LongDash] F_H and comparison with the draft*)


DFPrintSolution[comps_, sol_] := Module[{n = comps["n"], fa = comps["F"], S, fp, dirs, ker, gauge = {}, fd, inFamily, ref, determined},
   If[!TrueQ[sol["consistent"]], Print["no solution to print"]; Return[$Failed]];
   S = fa["structures"]; fp = sol["Fparticular"]; dirs = sol["Fdirections"];
   fd = Lookup[DFDraftFCoefficients[comps], fa["unknowns"]];
   inFamily = MatrixRank[Append[dirs, fd - fp]] == MatrixRank[dirs] || (dirs === {} && fd === fp);
   Print["\n===== Step 4: F_H(T0), all indices contracted with w (n = ", n, ") ====="];
   (* directions invisible in F_{dV H} (e.g. terms linear in the linearized Ricci tensor), then those absorbed by Q lambda_n *)
   ker = NullSpace[Transpose[First[DFMatrix[DFHtoV /@ S]]]];
   Do[If[MatrixRank[Join[ker, gauge, {v}]] > MatrixRank[Join[ker, gauge]], AppendTo[gauge, v]], {v, dirs}];
   ref = If[inFamily, fd, fp];
   Print["  F_H = ", If[inFamily, "F_H(draft)", "F_H(particular)"], " + sum_i c_i D_i, with"];
   Print["  ", If[inFamily, "F_H(draft)", "F_H(particular)"], ":\n    ", DFReadable[ref . S]];
   Print["  D_i dropping out of F_{dV H} (", Length[ker], "):"];
   Do[Print["    D", i, " = ", DFReadable[ker[[i]] . S]], {i, Length[ker]}];
   Print["  D_i absorbed by the compensators Q lambda_n (", Length[gauge], "):"];
   Do[Print["    D", Length[ker] + i, " = ", DFReadable[gauge[[i]] . S]], {i, Length[gauge]}];
   determined = Select[Range[Length[S]], AllTrue[dirs, Function[v, v[[#]] === 0]] &];
   Print["\n  coefficients fixed by the system (", Length[determined], " of ", Length[S], "), solution vs draft:"];
   Print[Grid[Prepend[Table[{DFMonoString[S[[i]]], DFCoefString[fp[[i]]], DFCoefString[fd[[i]]]}, {i, determined}], {"structure", "Solve", "draft"}],
     Alignment -> Left, Frame -> All]];
   Print["\n  the draft's F_H ", If[inFamily, "SOLVES", "does NOT solve"], " the V_", n, " component of (diffeoDemand)",
    If[inFamily, " (it differs from the particular solution only along the free directions)", ""]];
   <|"F" -> ref . S, "kernel" -> (# . S &) /@ ker, "gauge" -> (# . S &) /@ gauge, "draftSolves" -> inFamily|>];
