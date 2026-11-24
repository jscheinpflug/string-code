(* Operators transcribed from the draft. Time is Wick rotated only when
   evaluating a StringCode component; the scalar coordinate t remains real. *)
auditCoords = Array[x, 10, 0];
(* StringCode reserves the bare p and m labels for fixed null directions. *)
nullU = p;
nullV = m;
auditNullRules = {
  HoldPattern[\[Delta][p, p] | \[Delta][m, m]] -> 0,
  HoldPattern[\[Delta][p, m] | \[Delta][m, p]] -> 2,
  HoldPattern[\[Delta][i_Integer, j_Integer]] :> KroneckerDelta[i, j],
  HoldPattern[\[Delta][i_Integer, p] | \[Delta][p, i_Integer]] :> Switch[i, 1, 1, 2, I, _, 0],
  HoldPattern[\[Delta][i_Integer, m] | \[Delta][m, i_Integer]] :> Switch[i, 1, 1, 2, -I, _, 0],
  \[Alpha]p -> 1
};
auditP = x[1] + I x[2];
auditProjectionCleanup[expr_] := FixedPoint[Expand[# /. auditNullRules] &, expr];
auditBackground[d_, tag_] := Module[{metric, tt, vector, jx, xa, xi},
  tt = x[0];
  xa = ReplacePart[Take[auditCoords, d], 1 -> I tt];
  xi = Drop[auditCoords, d];
  jx = Flatten[({#[[2]], -#[[1]]} & /@ Partition[xi, 2])];
  metric = ArrayFlatten[{{-Outer[Times, xa, xa], ConstantArray[0, {d, 10-d}]},
    {ConstantArray[0, {10-d, d}], If[d == 5, Outer[Times, xi, xi],
      (Outer[Times, xi, xi] - Outer[Times, jx, jx])/4]}}];
  vector = Join[(If[d == 5, 20, 16] # & /@ xa), (If[d == 5, -20, -8] # & /@ xi)];
  Switch[tag, "metric", metric, "phi", Tr[metric], "A", vector]
];

auditProfileDerivative[f_, ds_, energy_] := Fold[
  Function[{value, index}, Expand[Switch[index,
    0, -I D[value, x[0]] - energy value,
    nullU, D[value, x[1]] + I D[value, x[2]],
    nullV, D[value, x[1]] - I D[value, x[2]],
    _, D[value, x[index]]]]], f, ds];

auditNumericWord[expr_] := Expand[expr /. auditNullRules /. {
  dX[1, j_, q_] :> (dX[nullU, j, q] + dX[nullV, j, q])/2,
  dX[2, j_, q_] :> (dX[nullU, j, q] - dX[nullV, j, q])/(2I),
  dXt[1, j_, q_] :> (dXt[nullU, j, q] + dXt[nullV, j, q])/2,
  dXt[2, j_, q_] :> (dXt[nullU, j, q] - dXt[nullV, j, q])/(2I),
  \[Psi][1, j_, q_] :> (\[Psi][nullU, j, q] + \[Psi][nullV, j, q])/2,
  \[Psi][2, j_, q_] :> (\[Psi][nullU, j, q] - \[Psi][nullV, j, q])/(2I),
  \[Psi]t[1, j_, q_] :> (\[Psi]t[nullU, j, q] + \[Psi]t[nullV, j, q])/2,
  \[Psi]t[2, j_, q_] :> (\[Psi]t[nullU, j, q] - \[Psi]t[nullV, j, q])/(2I)
}];

auditQWord[word_R] := auditQWord[word] = auditTerms[Expand[
  cleanupBracket[Expand[actBRST[R[ProfileX[auditCoefficient, {}, 0, 0], word]]] /. auditNullRules]]];
auditQState[expr_, energy_] := Module[{words, eval, state = Expand[expr]},
  words = DeleteDuplicates[Cases[state, _R, Infinity]];
  eval[term_, f_] := Module[{ds, ids, rule, value, word},
    ds = First[Cases[term, ProfileX[auditCoefficient, jet_List, _, _] :> jet, Infinity]];
    ids = DeleteDuplicates[Cases[term, s_Symbol /; StringContainsQ[SymbolName[s], "$"], Infinity]];
    Total[Table[
      rule = Thread[ids -> vals];
      value = auditProfileDerivative[f, ds /. rule, energy];
      If[value === 0, 0, (term /. rule /. ProfileX[auditCoefficient, _, _, _] -> 1) value /. auditNullRules],
      {vals, Tuples[Range[0, 9], Length[ids]]}]]
  ];
  auditProjectionCleanup[auditNumericWord[Total[Table[
    Total[eval[#, Coefficient[state, word]] & /@ auditQWord[word]], {word, words}]]]]
];

auditExtraCore[n_, id_, pol_] := Switch[id,
  "B0", I (R @@ Join[{c[0, 0], exp\[Phi]f[-1, 0], \[Psi][0, 0, 0]},
    ConstantArray[dX[pol, 0, 0], n]]),
  "U0", I (R @@ Join[{c[0, 0], exp\[Phi]f[-1, 0], \[Psi][pol, 0, 0], dX[0, 0, 0]},
    ConstantArray[dX[pol, 0, 0], n-1]]),
  "F", R @@ Join[{c[0, 0], exp\[Phi]f[-1, 0], \[Psi][pol, 1, 0]},
    ConstantArray[dX[pol, 0, 0], n-1]],
  "Y", R @@ Join[{c[0, 0], exp\[Phi]f[-1, 0], \[Psi][pol, 0, 0], dX[pol, 1, 0]},
    ConstantArray[dX[pol, 0, 0], n-2]],
  "Z", I (R @@ Join[{c[0, 0], exp\[Phi]f[-1, 0], \[Psi][pol, 0, 0], \[Psi][0, 0, 0], \[Psi][pol, 1, 0]},
    ConstantArray[dX[pol, 0, 0], n-2]]),
  "D", R @@ Join[{c[0, 0], exp\[Phi]b[-2, 0], \[Xi][1, 0]}, ConstantArray[dX[pol, 0, 0], n]],
  "L", R @@ Join[{exp\[Phi]f[-1, 0], \[Psi][pol, 0, 0]}, ConstantArray[dX[pol, 0, 0], n-1]],
  "A", I (R @@ Join[{c[0, 0], \[Eta][0, 0], \[Psi][pol, 0, 0], \[Psi][0, 0, 0]},
    ConstantArray[dX[pol, 0, 0], n-1]]),
  "H", R @@ Join[{c[0, 0], \[Eta][0, 0], \[Psi][pol, 0, 0], \[Psi][pol, 1, 0]},
    ConstantArray[dX[pol, 0, 0], n-2]],
  _, auditCore[n, id, pol]
];
auditProduct[n_, left_, right_, kind_, extra_: False] := Module[{a, b, first, second},
  a = auditExtraCore[n, left, nullU]; b = auditExtraCore[n, right, nullU];
  first = R[a, auditBar[b]];
  second = R[b, auditBar[a]];
  Switch[kind, "vee", first + second, "wedge", first - second, "direct", first] //
    If[TrueQ[extra], R[auditC0, #] &, Identity]
];

auditCompanion[n_, d_, delta_, fitCoefficients_: False] := Module[{a, bb, cc, first, second, words, e = 2 Sqrt[n]},
  a = {delta(n+1)/(2n)+n(n+2)(3n-1)/(4n+4),
    delta(n^2-1)/(4n)+n(3n^3+3n^2-5n+3)/(8n+8), I e n/4, (d+n+3)/4, -n(d+n+3)/8};
  bb = {0, 0, 0, -I e/2, I e n/4};
  cc = {I delta/e, I delta(n-1)/(2e), 0, I e delta/4, I e delta(n-1)/8, 0,
    delta, delta(n-1)/2, 0, delta(n-1)^2/4, 0, 0, delta/(4n)+1/16, -delta/8-n/32,
    -delta/4-n/16, delta n/8+n^2/32, -I e/8, I e n/16, -I e n/8, I e n^2/16,
    -n/4, n^2/8, -n(n-1)/8, n^2(n-1)/16, 0, 0};
  If[TrueQ[fitCoefficients],
    a = Array[fitA,5]; bb = Array[fitB,5]; cc = Array[fitC,26]];
  first = {{"B","F","vee"}, {"B","Y","vee"}, {"B","Z","vee"}, {"B","D","wedge",True}, {"B","L","wedge",True}};
  second = {{"B0","F","vee"}, {"B0","Y","vee"}, {"B0","Z","vee"}, {"U0","F","vee"}, {"U0","Y","vee"},
    {"U0","Z","vee"}, {"F","F","direct"}, {"F","Y","vee"}, {"F","Z","vee"}, {"Y","Y","direct"},
    {"Y","Z","vee"}, {"Z","Z","direct"}, {"G","D","wedge"}, {"G","L","wedge"}, {"P","D","wedge"},
    {"P","L","wedge"}, {"B0","D","wedge",True}, {"B0","L","wedge",True}, {"U0","D","wedge",True},
    {"U0","L","wedge",True}, {"F","D","wedge",True}, {"F","L","wedge",True}, {"Y","D","wedge",True},
    {"Y","L","wedge",True}, {"Z","D","wedge",True}, {"Z","L","wedge",True}};
  words = Join[MapThread[{auditP (#1 + x[0] #2), #3} &, {a, bb, first}],
    MapThread[{auditP^2 #1, #2} &, {cc, second}]];
  2^(n+2)/n! Expand[Total[Function[row, If[row[[1]] === 0 ||
    (n == 1 && !FreeQ[row[[2]], "Y" | "Z"]), 0, row[[1]] (auditProduct @@ Prepend[row[[2]], n])]] /@ words]]
];

auditNSPrinted[n_, d_] := Module[{e = 2 Sqrt[n], t = x[0], z = auditP, b0, u0, f, y, g, p, aa, hh, b, dd, kk, ll, uu, alpha},
  {b0,u0,f,g,p,aa,b} = auditExtraCore[n, #, nullU] & /@ {"B0","U0","F","G","P","A","B"};
  {y,hh} = If[n == 1, {0,0}, auditExtraCore[n, #, nullU] & /@ {"Y","H"}];
  dd = f + (n-1)y/2;
  kk = b0+n u0-I e dd/2;
  ll = z (d I e+8 n t)(b0+n u0)/8-I n z (2 e t+(d+2)I)dd/4;
  uu = z (2n-d)g/16 + (d+2)n z p/16-I e n z aa/8-n(n-1)z hh/8;
  alpha = (8n t^2-2I e (n-d-1)t-3n^2-5+(d-4)(n+9))/4;
  2^(n+2)/n! Expand[R[auditC0, alpha R[b, auditBar[b]]+R[ll, auditBar[b]]+R[b, auditBar[ll]]+
    n z^2/2 R[kk, auditBar[kk]]] +R[uu, auditBar[b]]-R[b, auditBar[uu]]]
];

auditLRTBody[n_, pol_] := R[auditCore[n, "B", pol], auditBar[auditCore[n, "B", pol]]];
auditReplaceOne[scale_ word_R, vec_] /; FreeQ[scale,_R] := scale auditReplaceOne[word, vec];
auditReplaceOne[word_R, vec_] := Module[{fields = List @@ word, n, term},
  n = Length[fields];
  Expand[Total[Table[
    term = fields[[j]];
    If[MemberQ[{dX, dXt, \[Psi], \[Psi]t}, Head[term]] && term[[1]] === nullU,
      Sum[vec[[i+1]] (R @@ ReplacePart[fields, j -> ReplacePart[term, 1 -> i]]), {i, 0, Length[vec]-1}],
      0], {j, n}]]]
];
auditConversion[n_, d_] := Module[{s = 2n+2, e = 2 Sqrt[n], body, vec, k},
  body = auditLRTBody[n, nullU];
  vec = ReplacePart[Take[auditCoords, d], 1 -> I x[0]];
  k = Join[{I e}, ConstantArray[0, d-1]];
  Expand[2^(n+2)/n! ((Tr[auditBackground[d, "metric"]]/2 + I n e x[0]) body +
    auditP/2 auditReplaceOne[body, vec] +
    I n(3n+7)/(4s) auditP auditReplaceOne[body, k])]
];
auditJGeom[n_, d_, mass_] := Module[{s = 2n+2, e = 2 Sqrt[n], body, k, g, p},
  body = auditLRTBody[n, nullU];
  k = Join[{I e}, ConstantArray[0, d-1]];
  g = auditWedge[n, "G", nullU]; p = auditWedge[n, "P", nullU];
  2^(n+2)/n! Expand[
    -R[auditC0, ((-e^2 x[0]^2-I d e x[0]+s-mass) body +
      2 I auditP auditReplaceOne[body, k])]/2 +
    auditP (s+d-1-I e x[0])(n p-g)/4 +
    auditP^2 (If[n == 1, 0, n(n-1)/24 auditWedge[n, "K", nullU]] -
      n/4 (auditWedge[n, "R", nullU]+auditWedge[n, "S", nullU]))]
];
auditQFHPrinted[n_, d_] := Module[{e = 2 Sqrt[n], t = x[0], z = auditP, a, b},
  a = z/(8(n+1)) (I e (n+1)t-3n^3-9n^2-(d+2)n-d);
  b = auditLRTBody[n, nullU];
  2^(n+2)/n! Expand[
    R[auditC0, (-I e t+4n^2-n+9-2d) b -
      I e z/2 (auditProduct[n,"B","B0","vee"] + n auditProduct[n,"B","U0","vee"])] +
    a (auditWedge[n,"G",nullU] + n auditProduct[n,"B","P","wedge"]) +
    n z^2/4 (auditProduct[n,"B","S","wedge"]+auditProduct[n,"B","R","wedge"])]
];
auditRequired[n_, d_] := Module[{conversion, companion, qConversion, qCompanion, gaugeShift, e = 2 Sqrt[n],
    mass = 2(n-1)(3n+1), residual},
  conversion = auditConversion[n, d]; companion = auditCompanion[n, d, 0];
  qConversion = auditQState[conversion, e]; qCompanion = auditQState[companion, e];
  gaugeShift = auditQState[Expand[auditCompanion[n, d, 1] - companion], e];
  residual = Expand[qConversion + qCompanion + auditNSPrinted[n, d] - auditJGeom[n, d, mass]];
  Print["level ", n, " dim ", d, " QF-H difference terms ", Length[auditTerms[Expand[qConversion-auditQFHPrinted[n,d]]]],
    " Q companion terms ", Length[auditTerms[qCompanion]], " Q delta shift terms ", Length[auditTerms[gaugeShift]],
    " EOM residual using printed NS and canceling log terms ", Length[auditTerms[residual]]];
  <|"QF_H" -> qConversion, "QF_H_difference_on_defined_words" -> Expand[qConversion-auditQFHPrinted[n,d]],
    "QCompanion" -> qCompanion, "QOnPrintedFreeParameterShift" -> gaugeShift, "PrintedNS" -> auditNSPrinted[n,d],
    "Target" -> auditJGeom[n,d,mass], "ResidualWithPrintedNSAndLogCancellation" -> residual|>
];

auditSolvePrintedSystem[n_, d_] := Module[{answer, qC, residual, words, coefficientRows, variables, a, b, rows, lhs, rhs},
  answer = Get[FileNameJoin[{auditDirectory, "required_" <> ToString[n] <> "_" <> ToString[d] <> ".wl"}]];
  qC = auditQState[auditCompanion[n,d,0,True], 2 Sqrt[n]];
  residual = Expand[answer["QF_H"] + qC + answer["PrintedNS"] - auditJGeom[n,d,fitMass]];
  words = DeleteDuplicates[Cases[residual, _R, Infinity]];
  coefficientRows = DeleteCases[Flatten[Values[CoefficientRules[
    Expand[Coefficient[residual,#] /. Thread[auditCoords -> Array[auditX,10]]], Array[auditX,10]]] & /@ words],0];
  variables = DeleteDuplicates[Cases[coefficientRows, fitMass | (fitA|fitB|fitC)[_Integer], Infinity]];
  {b,a} = Normal /@ CoefficientArrays[coefficientRows,variables];
  lhs = MatrixRank[a]; rhs = MatrixRank[MapThread[Append,{a,-b}]];
  rows = RowReduce[MapThread[Append,{a,-b}]];
  Print["solve n=",n," d=",d," equations ",Length[coefficientRows]," variables ",Length[variables],
    " rank ",lhs," augmented ",rhs];
  <|"Rank"->lhs,"AugmentedRank"->rhs,"Variables"->variables,"ReducedRows"->rows,
    "MassOnlyRows"->Select[rows, Count[Most[#],v_ /; v =!= 0] == 1 &&
      #[[First@FirstPosition[variables,fitMass]]] =!= 0 &]|>
];

auditCompanionGauge[n_] := Module[{e = 2 Sqrt[n], generator, image, difference},
  generator = 1/(2n) auditProduct[n,"F","D","wedge"] -
    1/4 auditProduct[n,"F","L","wedge"];
  If[n >= 2, generator += (n-1)/(4n) auditProduct[n,"Y","D","wedge"] -
    (n-1)/8 auditProduct[n,"Y","L","wedge"]];
  generator = Expand[(2^(n+2)/n!) auditP^2 generator];
  image = auditQState[generator,e];
  difference = Expand[auditCompanion[n,5,1]-auditCompanion[n,5,0]-image];
  Print["Companion gauge identity n=",n," residual terms=",Length[auditTerms[difference]],
    " Q^2 terms=", Length[auditTerms[auditQState[image,e]]]];
  <|"PrintedGenerator"->generator,"NativeImage"->image,"DifferenceFromPrintedShift"->difference,
    "NativeQ2"->auditQState[image,e]|>
];
