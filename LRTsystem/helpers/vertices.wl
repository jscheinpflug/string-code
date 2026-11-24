(* Draft operators at the origin. Load StringCode before parsing this file. *)

auditTerms[expr_] := If[expr === 0, {}, If[Head[expr] === Plus, List @@ expr, {expr}]];
auditClean[expr_] := Expand[cleanupBracket[Expand[expr]]];

auditNSNS[profile_] := 4 R[ProfileX[profile, {}, 0, 0],
  c[0, 0], ct[0, 0], exp\[Phi]f[-1, 0], \[Psi][iH, 0, 0],
  exp\[Phi]tf[-1, 0], \[Psi]t[iA, 0, 0]];
auditDilaton[profile_] :=
  R[ProfileX[profile, {}, 0, 0], c[0, 0], ct[0, 0],
    \[Eta][0, 0], exp\[Phi]tb[-2, 0], \[Xi]t[1, 0]] -
  R[ProfileX[profile, {}, 0, 0], c[0, 0], ct[0, 0],
    exp\[Phi]b[-2, 0], \[Xi][1, 0], \[Eta]t[0, 0]];
auditGauge[profile_] :=
  R[ProfileX[profile, {}, 0, 0], c[0, 0], ct[0, 0],
    exp\[Phi]f[-1, 0], \[Psi][iH, 0, 0], exp\[Phi]tb[-2, 0], \[Xi]t[1, 0]] +
  R[ProfileX[profile, {}, 0, 0], c[0, 0], ct[0, 0],
    exp\[Phi]b[-2, 0], \[Xi][1, 0], exp\[Phi]tf[-1, 0], \[Psi]t[iH, 0, 0]];
auditC0Plus[expr_] := Expand[R[(c[1,0]+ct[1,0])/2,expr]];
auditAuxiliary[profile_] := Expand[R[(c[1, 0] + ct[1, 0])/2, auditGauge[profile]]];
auditRR[profile_, chirality_] := R[ProfileX[profile, {}, 0, 0],
  c[0, 0], ct[0, 0], S[{iSpin, "chiral"}, -1/2, {}, 0, 0],
  St[{jSpin, chirality}, -1/2, {}, 0, 0]];
auditSUSYLeft[profile_] := R[ProfileX[profile, {}, 0, 0], c[0, 0], ct[0, 0],
  S[{iSpin, "chiral"}, -1/2, {}, 0, 0], exp\[Phi]tb[-2, 0], \[Xi]t[1, 0]];
auditSUSYRight[profile_, chirality_] := R[ProfileX[profile, {}, 0, 0], c[0, 0], ct[0, 0],
  exp\[Phi]b[-2, 0], \[Xi][1, 0], St[{iSpin, chirality}, -1/2, {}, 0, 0]];

auditLRT[n_Integer, profile_] := Module[{indices, left, right},
  indices = Take[{lrtOne, lrtTwo, lrtThree, lrtFour, lrtFive, lrtSix, lrtSeven, lrtEight}, 2n+2];
  left = Take[indices, n+1];
  right = Drop[indices, n+1];
  (2^(n+2)/n!) (R @@ Join[
    {ProfileX[profile @@ indices, {}, 0, 0], c[0, 0],
      exp\[Phi]f[-1, 0]}, dX[#, 0, 0] & /@ Most[left],
    {\[Psi][Last[left], 0, 0], ct[0, 0],
      exp\[Phi]tf[-1, 0]}, dXt[#, 0, 0] & /@ Most[right],
    {\[Psi]t[Last[right], 0, 0]}])
];
