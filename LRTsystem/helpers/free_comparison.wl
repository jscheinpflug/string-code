(* Rank-one symmetric polarization, with an unrestricted scalar profile. *)
auditPolarizedLRT[n_, pol_, f_] := (2^(n+2)/n!) (R @@ Join[
  {ProfileX[f, {}, 0, 0], c[0, 0], exp\[Phi]f[-1, 0]},
  ConstantArray[dX[pol, 0, 0], n], {\[Psi][pol, 0, 0], ct[0, 0],
  exp\[Phi]tf[-1, 0]}, ConstantArray[dXt[pol, 0, 0], n], {\[Psi]t[pol, 0, 0]}]);

auditCore[n_, id_, pol_] := Switch[id,
  "B", R @@ Join[{c[0, 0], exp\[Phi]f[-1, 0], \[Psi][pol, 0, 0]},
    ConstantArray[dX[pol, 0, 0], n]],
  "G", R @@ Join[{c[0, 0], \[Eta][0, 0]}, ConstantArray[dX[pol, 0, 0], n]],
  "P", R @@ Join[{c[0, 0], c[2, 0], exp\[Phi]f[-1, 0], \[Psi][pol, 0, 0]},
    ConstantArray[dX[pol, 0, 0], n-1]],
  "K", If[n == 1, 0, R @@ Join[{c[0, 0], c[3, 0], exp\[Phi]f[-1, 0], \[Psi][pol, 0, 0]},
    ConstantArray[dX[pol, 0, 0], n-2]]],
  "S", R @@ Join[{c[0, 0], \[Eta][0, 0], d\[Phi][0, 0]}, ConstantArray[dX[pol, 0, 0], n-1]],
  "R", R @@ Join[{c[0, 0], \[Eta][1, 0]}, ConstantArray[dX[pol, 0, 0], n-1]]
];
auditBar[expr_] := expr /. {c -> ct, b -> bt, exp\[Phi]f -> exp\[Phi]tf,
  exp\[Phi]b -> exp\[Phi]tb, \[Psi] -> \[Psi]t, \[Eta] -> \[Eta]t,
  \[Xi] -> \[Xi]t, d\[Phi] -> d\[Phi]t, dX -> dXt};
auditWedge[n_, id_, pol_] :=
  R[auditCore[n, id, pol], auditBar[auditCore[n, "B", pol]]] -
  R[auditCore[n, "B", pol], auditBar[auditCore[n, id, pol]]];
auditBox[f_] := Sum[ProfileX[f, {j, j}, 0, 0], {j, 1, 10}];
auditC0 = (c[1, 0] + ct[1, 0])/2;

auditPrintedFree[n_] := Module[{nn = 2^(n+2)/n!, wave, div, trace},
  wave = -(nn/2) R[auditBox[probe] - 4n ProfileX[probe, {}, 0, 0],
    auditC0, auditCore[n, "B", 1], auditBar[auditCore[n, "B", 1]]];
  div = (nn/4) R[ProfileX[probe, {1}, 0, 0],
    n auditWedge[n, "P", 1] - auditWedge[n, "G", 1]];
  trace = nn R[ProfileX[probe, {}, 0, 0],
    If[n == 1, 0, n(n-1)/24 auditWedge[n, "K", 1]] -
      n/4 (auditWedge[n, "S", 1] + auditWedge[n, "R", 1])];
  {wave, div, trace}
];
auditAppendixTrace[n_] := 2^(n+2)/n! R[ProfileX[probe, {}, 0, 0],
  If[n == 1, 0, n(n-1)/24 auditWedge[n, "K", 1]] -
    n/4 (auditWedge[n, "R", 1] + auditWedge[n, "S", 1])];

auditTestExpand[expr_] := Expand[expr /. {
  HoldPattern[\[Delta][j_Integer, k_Integer]] :> KroneckerDelta[j, k],
  \[Alpha]p -> 1
} /. HoldPattern[R[before___, ProfileX[f_, {j_Symbol, j_Symbol}, z_, zb_], after___]] :>
  R[before, auditBox[f], after]];

auditFreeComparison[n_] := Module[{actual, printed, appendix, res, trace, onShell},
  actual = auditTestExpand[auditClean[actBRST[auditPolarizedLRT[n, 1, probe]]]];
  printed = auditTestExpand /@ auditPrintedFree[n];
  appendix = auditTestExpand[auditAppendixTrace[n]];
  res = Expand[actual - Total[printed]];
  trace = Expand[actual - Total[Take[printed, 2]] - appendix];
  Print["n=", n, " printed-residual terms=", Length[auditTerms[res]],
    " appendix-trace-residual terms=", Length[auditTerms[trace]]];
  <|"actual" -> actual, "printed" -> Total[printed], "appendix" -> Total[Take[printed, 2]] + appendix,
    "printedResidual" -> res, "appendixResidual" -> trace|>
];
