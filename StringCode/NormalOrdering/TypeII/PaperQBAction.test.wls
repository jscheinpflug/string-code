(* Run in a fresh Wolfram kernel:  wolframscript -file PaperQBAction.test.wls
   No runtime convention overrides: the gamma tables are built at package load.

   Convention-independent checks of the same-point cocycle convention (LOCAL_COCYCLE_CONVENTION.md)
   against arXiv:2507.12921 (Cho-Collier-Gomide-Yin et al., "AdS5 x S5 in superstring field theory").

   A. Split vs joined.  A same-point product :e^{q phi} psi^mu:(z) of mutually regular operators
      (phi.psi = 0) must equal the pos5 -> z limit of e^{q phi}(pos5) psi^mu(z).  Checked in correlators
      with spin-field spectators, q = -1 and +1, both chiral sectors.
   B. Paper OPE invariant.  App. A of the paper gives e^{-phi}psi^mu S^alpha and e^{+phi}psi^mu S^alpha
      the same (i/2) gamma^mu.  With the normalizations of e^{phi/2}S_alpha and e^{-3phi/2}S_alpha fixed
      by the paper's pairings (-delta), (C.P+)/(B.P-) must be exactly 1 for every mu and every entry.
   C. Q_B action, eq. (kinpart) of the paper, every line: RR (c0+, holomorphic and antiholomorphic eta),
      NSNS (e, g), ghost dilaton D (f, g), auxiliary V_aux (e, f, g), SUSY parameters eps / epsbar
      (v, u, w and bars), NSNS gauge parameter lambda_V.  Absolute normalization with
      der[P][mu] = d_mu P (alpha' = 1) and c0+ = (c0 + cbar0)/2.  The paper's gamma^mu is DEFINED by its
      e^{-phi}psi.S OPE and its S_alpha basis by its pairing, both evaluated with this package's own
      bosonizer.  Paper operators are entered in the paper's literal field order; every Grassmann
      reordering sign is supplied by R.  eps, epsbar are Grassmann odd, so Q(eps V) = - eps Q V.
   D. The same Q_B check in a Minkowski light-cone frame: vp = (e9 + I e10)/Sqrt[2], vm = (e9 - I e10)/Sqrt[2]
      (vp.vm = 1 = eta^{+-}, direction 10 Wick rotated), complex momentum k = vp + vm/2 + e3,
      null-polarized h, A, V.  The null pair straddles the Cartan planes {4,9} and {5,10}.

   The original (no internal cocycle) convention fails A, B and the RR / SUSY lines of C and D. *)

Needs["StringCode`"];
InitStringCode[<|"theory" -> "TypeII", "CFT" -> "FlatSpace", "conventions" -> "TypeII-Ashoke", "bracket" -> "Flat"|>];
Needs["StringCode`Utils`Canonicalize`"];

paperQBResults = {};
paperQBCheck::usage = "paperQBCheck[name, condition] records an exact regression assertion.";
paperQBCheck[name_, condition_] := (
  AppendTo[paperQBResults, {name, TrueQ[condition]}];
  Print[name, ": ", If[TrueQ[condition], "PASSED", "FAILED"]]
);

chiralStates = Private`spinProjectionSpinBasisState["chiral"];
antichiralStates = Private`spinProjectionSpinBasisState["antichiral"];
cartanPlane[i_] := Mod[i - 1, 5] + 1;

(* ================= A. split vs joined ================= *)
splitEval[sector_, ops_] := Together[
  (Private`spinProjectionSectorEvaluation[sector, 0, Bosonize /@ ops] /.
     (R[expH[qq_, _]] | R[expHt[qq_, _]]) :> 1 /; Rest[qq] === {0, 0, 0, 0, 0}) /. {pos5 -> pos0, posb5 -> posb0}];
spinsAllowedQ[mu_, sa_, sb_] := AnyTrue[{-1, 1},
  # UnitVector[5, cartanPlane[mu]] + chiralStates[[sa]] + chiralStates[[sb]] === {0, 0, 0, 0, 0} &];
Do[
  Module[{pairs, ratios = {}, zeroMismatch = 0, joined, split, vj, vs},
    pairs = Take[Select[Tuples[Range[16], 2], spinsAllowedQ[mu, #[[1]], #[[2]]] &], UpTo[6]];
    Do[
      If[sector === "Holo",
        joined = {R[exp\[Phi]f[qphi, pos0], \[Psi][mu, 0, pos0]], R[S[{chiralStates[[sp[[1]]]], "chiral"}, -1/2, {}, 0, pos1]], R[S[{chiralStates[[sp[[2]]]], "chiral"}, -1/2, {}, 0, pos2]]};
        split = {R[exp\[Phi]f[qphi, pos5]], R[\[Psi][mu, 0, pos0]], R[S[{chiralStates[[sp[[1]]]], "chiral"}, -1/2, {}, 0, pos1]], R[S[{chiralStates[[sp[[2]]]], "chiral"}, -1/2, {}, 0, pos2]]},
        joined = {R[exp\[Phi]tf[qphi, posb0], \[Psi]t[mu, 0, posb0]], R[St[{chiralStates[[sp[[1]]]], "chiral"}, -1/2, {}, 0, posb1]], R[St[{chiralStates[[sp[[2]]]], "chiral"}, -1/2, {}, 0, posb2]]};
        split = {R[exp\[Phi]tf[qphi, posb5]], R[\[Psi]t[mu, 0, posb0]], R[St[{chiralStates[[sp[[1]]]], "chiral"}, -1/2, {}, 0, posb1]], R[St[{chiralStates[[sp[[2]]]], "chiral"}, -1/2, {}, 0, posb2]]}
      ];
      vj = splitEval[sector, joined]; vs = splitEval[sector, split];
      Which[vj === 0 && vs === 0, Null, vj === 0 || vs === 0, zeroMismatch++, True, AppendTo[ratios, Factor[vj/vs]]],
      {sp, pairs}];
    paperQBCheck[{"A split = joined", sector, "e^{" <> ToString[qphi] <> " phi} psi", mu},
      zeroMismatch === 0 && ratios =!= {} && Union[ratios] === {1}]
  ],
  {sector, {"Holo", "Anti"}}, {qphi, {-1, 1}}, {mu, {1, 7}}
];

(* ================= paper bases (shared by B, C, D) ================= *)
leadHolo[x_, y_, pow_] := Expand[Private`projectScaledExpressionAtHoloPower[OPE[Bosonize[x[eps u]], Bosonize[y]], pow, eps] /. u -> 1];
leadAnti[x_, y_, pow_] := Expand[Private`projectScaledExpressionAtAntiHoloPower[OPE[Bosonize[x[eps u]], Bosonize[y]], pow, eps] /. u -> 1];
identityHolo = R[expH[qq_, 0]] :> 1 /; Rest[qq] === {0, 0, 0, 0, 0};
identityAnti = R[expHt[qq_, 0]] :> 1 /; Rest[qq] === {0, 0, 0, 0, 0};
pairPlusHolo = Table[leadHolo[R[S[{antichiralStates[[k]], "antichiral"}, 1/2, {}, 0, #]] &, R[S[{chiralStates[[j]], "chiral"}, -1/2, {}, 0, 0]], -1] /. identityHolo, {k, 16}, {j, 16}];
pairMinusHolo = Table[leadHolo[R[S[{antichiralStates[[k]], "antichiral"}, -3/2, {}, 0, #]] &, R[S[{chiralStates[[j]], "chiral"}, -1/2, {}, 0, 0]], -2] /. identityHolo, {k, 16}, {j, 16}];
pairPlusAnti = Table[leadAnti[R[St[{antichiralStates[[k]], "antichiral"}, 1/2, {}, 0, #]] &, R[St[{chiralStates[[j]], "chiral"}, -1/2, {}, 0, 0]], -1] /. identityAnti, {k, 16}, {j, 16}];
pairMinusAnti = Table[leadAnti[R[St[{antichiralStates[[k]], "antichiral"}, -3/2, {}, 0, #]] &, R[St[{chiralStates[[j]], "chiral"}, -1/2, {}, 0, 0]], -2] /. identityAnti, {k, 16}, {j, 16}];
paperQBCheck["pairings are numeric and invertible",
  And @@ (MatrixQ[#, NumericQ] && Det[#] =!= 0 & /@ {pairPlusHolo, pairMinusHolo, pairPlusAnti, pairMinusAnti})];
lowerHolo = -Inverse[pairPlusHolo];   (* paper e^{phi/2} S_alpha = Sum_k lowerHolo[[alpha,k]] (antichiral, +1/2)_k *)
lowerAnti = -Inverse[pairPlusAnti];
opeB[mu_] := Table[Coefficient[leadHolo[R[exp\[Phi]f[-1, #], \[Psi][mu, 0, #]] &, R[S[{chiralStates[[j]], "chiral"}, -1/2, {}, 0, 0]], -1],
  R[expH[Prepend[antichiralStates[[k]], -3/2], 0]]], {j, 16}, {k, 16}];
opeC[mu_] := Table[Coefficient[leadHolo[R[exp\[Phi]f[1, #], \[Psi][mu, 0, #]] &, R[S[{chiralStates[[j]], "chiral"}, -1/2, {}, 0, 0]], 0],
  R[expH[Prepend[antichiralStates[[k]], 1/2], 0]]], {j, 16}, {k, 16}];
gammaHolo = Table[2 I opeB[mu] . pairMinusHolo, {mu, 10}];   (* paper (gamma^mu)^{alpha beta} *)
gammaAnti = Table[2 I Table[Coefficient[leadAnti[R[exp\[Phi]tf[-1, #], \[Psi]t[mu, 0, #]] &, R[St[{chiralStates[[j]], "chiral"}, -1/2, {}, 0, 0]], -1],
  R[expHt[Prepend[antichiralStates[[k]], -3/2], 0]]], {j, 16}, {k, 16}] . pairMinusAnti, {mu, 10}];
paperQBCheck["paper gamma^mu symmetric, both sectors",
  And @@ Table[gammaHolo[[mu]] === Transpose[gammaHolo[[mu]]] && gammaAnti[[mu]] === Transpose[gammaAnti[[mu]]], {mu, 10}]];

(* ================= B. paper OPE invariant ================= *)
Do[
  paperQBCheck[{"B (C.P+) = (B.P-) entrywise", mu},
    Expand[opeC[mu] . pairPlusHolo - opeB[mu] . pairMinusHolo] === ConstantArray[0, {16, 16}] && opeB[mu] =!= ConstantArray[0, {16, 16}]],
  {mu, 10}];

(* ================= C, D. Q_B action vs eq. (kinpart) ================= *)
isVectorDummy[x_] := Head[x] === Symbol && StringContainsQ[SymbolName[x], "$"];
isSpinorDummy[x_] := Head[x] === Symbol && StringMatchQ[SymbolName[x], "\[Alpha]" ~~ ("t" | "") ~~ DigitCharacter ..] && !MemberQ[{\[Alpha]1, \[Beta]1}, x];
termList[e_] := If[Head[e] === Plus, List @@ e, {e}];
expandSpinorDummies[t_] := Module[{ds, doms, labels},
  ds = DeleteDuplicates[Cases[t, _Symbol?isSpinorDummy, Infinity]];
  doms = Function[dm, labels = Cases[t, (S | St)[{dm, cl_String}, ___] :> cl, Infinity];
    If[labels === {}, Print["unresolved spinor dummy ", dm]; {}, If[First[labels] === "chiral", chiralStates, antichiralStates]]] /@ ds;
  Total[Function[vals, t /. Thread[ds -> vals]] /@ Tuples[doms]]];
expandVectorDummies[t_] := Module[{vs = DeleteDuplicates[Cases[t, _?isVectorDummy, Infinity]]},
  If[vs === {}, t, Total[Function[vals, t /. Thread[vs -> vals]] /@ Tuples[Range[10], Length[vs]]]]];
concreteQB[vertex_, subs_] := Module[{ex},
  ex = Expand[ContractDelta[Expand[Private`actBRSTHolo[vertex] + Private`actBRSTAntiHolo[vertex]]]] /. subs /. \[Delta][x_Symbol, x_Symbol] :> 10 /. \[Delta][i_Integer, j_Integer] :> KroneckerDelta[i, j];
  ex = Flatten[termList[Expand[expandVectorDummies[#]]] & /@ termList[ex]];
  ex = Total[Private`spinProjectionEvaluateTensorScalars[expandSpinorDummies[#]] & /@ ex];
  Expand[ex /. \[Delta][i_Integer, j_Integer] :> KroneckerDelta[i, j] /. \[Alpha]p -> 1]];

(* paper operators, entered in the paper's literal field order *)
upS[j_] := S[{chiralStates[[j]], "chiral"}, -1/2, {}, 0, 0];         upSt[j_] := St[{chiralStates[[j]], "chiral"}, -1/2, {}, 0, 0];
lowS[k_] := S[{antichiralStates[[k]], "antichiral"}, 1/2, {}, 0, 0];  lowSt[k_] := St[{antichiralStates[[k]], "antichiral"}, 1/2, {}, 0, 0];
emphi = exp\[Phi]f[-1, 0]; emphit = exp\[Phi]tf[-1, 0]; em2phi = exp\[Phi]b[-2, 0]; em2phit = exp\[Phi]tb[-2, 0];
dxi = \[Xi][1, 0]; dxit = \[Xi]t[1, 0]; etaH = \[Eta][0, 0]; etaA = \[Eta]t[0, 0];
psiH[mu_] := \[Psi][mu, 0, 0]; psiA[mu_] := \[Psi]t[mu, 0, 0];
c0plus[prof_, rest__] := (R[prof, c[1, 0], c[0, 0], ct[0, 0], rest] - R[prof, c[0, 0], ct[1, 0], ct[0, 0], rest])/2;
opD[prof_] := R[prof, c[0, 0], ct[0, 0], etaH, em2phit, dxit] - R[prof, c[0, 0], ct[0, 0], em2phi, dxi, etaA];
opDc0[prof_] := c0plus[prof, etaH, em2phit, dxit] - c0plus[prof, em2phi, dxi, etaA];
opG[prof_, mu_] := R[prof, c[0, 0], ct[0, 0], etaH, emphit, psiA[mu]] + R[prof, c[0, 0], ct[0, 0], emphi, psiH[mu], etaA];
opAux[prof_, mu_] := c0plus[prof, emphi, psiH[mu], em2phit, dxit] + c0plus[prof, em2phi, dxi, emphit, psiA[mu]];
opNS[prof_, mu_, nu_] := R[prof, c[0, 0], ct[0, 0], emphi, psiH[mu], emphit, psiA[nu]];

(* momentum-space profiles: der[P][mu] -> kvec[[mu]] (for C: generic real k; for D: complex light-cone k) *)
pd[mu_] := kvec[[mu]]; box := kvec . kvec;
qbMatches[vertex_, subs_, prediction_] := Module[{scSide},
  scSide = concreteQB[vertex, subs] /. der[_][i_Integer] :> kvec[[i]];
  Expand[scSide - Expand[prediction]] === 0 && scSide =!= 0];

runQBBlocks[label_, polH_, polA_, polV_] := Module[{pf, prediction, hIn},
  (* RR: F_{ab} c cbar e^{-phi/2}S^a e^{-phibar/2}Sbar^b *)
  Do[
    pf = ProfileX[FF, {}, 0, 0];
    prediction = -1/2 box c0plus[pf, upS[sa], upSt[sb]]
      + Sum[(I/4) gammaHolo[[mu, al, sa]] lowerHolo[[al, k]] pd[mu] R[pf, c[0, 0], etaH, lowS[k], ct[0, 0], upSt[sb]], {mu, 10}, {al, 16}, {k, 16}]
      + Sum[(I/4) gammaAnti[[mu, sb, be]] lowerAnti[[be, k]] pd[mu] R[pf, c[0, 0], upS[sa], ct[0, 0], etaA, lowSt[k]], {mu, 10}, {be, 16}, {k, 16}];
    paperQBCheck[{label, "RR s, t, t^T", {sa, sb}},
      qbMatches[R[ProfileX[FF[\[Alpha]1, \[Beta]1], {}, 0, 0], c[0, 0], ct[0, 0], S[{\[Alpha]1, "chiral"}, -1/2, {}, 0, 0], St[{\[Beta]1, "chiral"}, -1/2, {}, 0, 0]],
        {\[Alpha]1 -> chiralStates[[sa]], \[Beta]1 -> chiralStates[[sb]], FF[__] -> FF}, prediction]],
    {pair, {{1, 1}, {7, 3}, {16, 9}}}, {sa, {pair[[1]]}}, {sb, {pair[[2]]}}];
  (* NSNS: h_{mu nu} V^{mu nu}, V = 4 c cbar e^{-phi}psi e^{-phibar}psibar, h symmetric *)
  pf = ProfileX[HH, {}, 0, 0];
  hIn = Sum[If[polH[[m1, m2]] === 0, 0, polH[[m1, m2]] 4 opNS[pf, m1, m2]], {m1, 10}, {m2, 10}];
  prediction = Sum[If[polH[[m1, m2]] === 0, 0, polH[[m1, m2]] (-2 box) c0plus[pf, emphi, psiH[m1], emphit, psiA[m2]]], {m1, 10}, {m2, 10}]
    + Sum[Sum[polH[[m1, m2]] pd[m2], {m2, 10}] opG[pf, m1], {m1, 10}];
  paperQBCheck[{label, "NSNS e, g"}, qbMatches[hIn, {}, prediction]];
  (* ghost dilaton *)
  pf = ProfileX[DD, {}, 0, 0];
  paperQBCheck[{label, "dilaton f, g"}, qbMatches[opD[pf], {}, -1/2 box opDc0[pf] + Sum[-1/2 pd[mu] opG[pf, mu], {mu, 10}]]];
  (* auxiliary field A_mu V_aux^mu *)
  pf = ProfileX[AA, {}, 0, 0];
  prediction = Sum[polA[[m1]] (Sum[-1/2 pd[mu] (c0plus[pf, emphi, psiH[mu], emphit, psiA[m1]] + c0plus[pf, emphi, psiH[m1], emphit, psiA[mu]]), {mu, 10}]
      - 1/4 pd[m1] opDc0[pf] + 1/4 opG[pf, m1]), {m1, 10}];
  paperQBCheck[{label, "aux e, f, g"}, qbMatches[Sum[polA[[m1]] opAux[pf, m1], {m1, 10}], {}, prediction]];
  (* SUSY parameters (Grassmann odd: compare with minus the paper's Q lambda) *)
  Do[
    pf = ProfileX[EE, {}, 0, 0];
    prediction = 1/2 box c0plus[pf, upS[sa], em2phit, dxit] + Sum[-1/2 pd[mu] R[pf, c[0, 0], upS[sa], ct[0, 0], emphit, psiA[mu]], {mu, 10}]
      + Sum[-(I/4) gammaHolo[[mu, al, sa]] lowerHolo[[al, k]] pd[mu] R[pf, c[0, 0], etaH, lowS[k], ct[0, 0], em2phit, dxit], {mu, 10}, {al, 16}, {k, 16}];
    paperQBCheck[{label, "SUSY eps v, u, w", sa},
      qbMatches[R[ProfileX[EE[\[Alpha]1], {}, 0, 0], c[0, 0], ct[0, 0], S[{\[Alpha]1, "chiral"}, -1/2, {}, 0, 0], em2phit, dxit], {\[Alpha]1 -> chiralStates[[sa]], EE[_] -> EE}, -prediction]];
    pf = ProfileX[EB, {}, 0, 0];
    prediction = 1/2 box c0plus[pf, em2phi, dxi, upSt[sa]] + Sum[-1/2 pd[mu] R[pf, c[0, 0], emphi, psiH[mu], ct[0, 0], upSt[sa]], {mu, 10}]
      + Sum[-(I/4) gammaAnti[[mu, be, sa]] lowerAnti[[be, k]] pd[mu] R[pf, c[0, 0], em2phi, dxi, ct[0, 0], etaA, lowSt[k]], {mu, 10}, {be, 16}, {k, 16}];
    paperQBCheck[{label, "SUSY epsbar vbar, ubar, wbar", sa},
      qbMatches[R[ProfileX[EB[\[Beta]1], {}, 0, 0], c[0, 0], ct[0, 0], em2phi, dxi, St[{\[Beta]1, "chiral"}, -1/2, {}, 0, 0]], {\[Beta]1 -> chiralStates[[sa]], EB[_] -> EB}, -prediction]],
    {sa, {1, 12}}];
  (* NSNS gauge parameter lambda_V: Q lambda = 1/8 (dV + dV) V_NSNS + 1/4 d.V D - 1/2 Box V V_aux *)
  pf = ProfileX[VV, {}, 0, 0];
  prediction = Sum[polV[[m1]] (Sum[1/8 pd[mu] 4 (opNS[pf, mu, m1] + opNS[pf, m1, mu]), {mu, 10}] + 1/4 pd[m1] opD[pf] - 1/2 box opAux[pf, m1]), {m1, 10}];
  paperQBCheck[{label, "gauge lambda_V"},
    qbMatches[Sum[polV[[m1]] (R[pf, c[0, 0], ct[0, 0], emphi, psiH[m1], em2phit, dxit] + R[pf, c[0, 0], ct[0, 0], em2phi, dxi, emphit, psiA[m1]]), {m1, 10}], {}, prediction]];
];

(* C: Euclidean frame, generic real momentum, Cartesian polarizations *)
kvec = {2, -1, 3, 0, 1, -2, 0, 1, 4, -3};
runQBBlocks["C euclidean",
  Normal[SparseArray[{{2, 3} -> 1, {3, 2} -> 1, {5, 5} -> 1}, {10, 10}]],
  UnitVector[10, 3], UnitVector[10, 5]];

(* D: Minkowski light-cone frame, direction 10 Wick rotated *)
lcPlus = (UnitVector[10, 9] + I UnitVector[10, 10])/Sqrt[2];
lcMinus = (UnitVector[10, 9] - I UnitVector[10, 10])/Sqrt[2];
paperQBCheck["D frame vp.vp = vm.vm = 0, vp.vm = 1", lcPlus . lcPlus === 0 && lcMinus . lcMinus === 0 && lcPlus . lcMinus === 1];
kvec = lcPlus + lcMinus/2 + UnitVector[10, 3];
runQBBlocks["D light-cone", Outer[Times, lcPlus, lcMinus] + Outer[Times, lcMinus, lcPlus], lcPlus, lcMinus];

Print["SUMMARY ", Count[paperQBResults[[All, 2]], True], "/", Length[paperQBResults]];
Quit[If[And @@ paperQBResults[[All, 2]], 0, 1]];
