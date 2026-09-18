(* ::Package:: *)

(* Delta contraction with fixed null-polarization labels (TypeII FlatSpace).

   Representation contract: \[Delta] is the metric of an orthonormal Cartesian basis of complexified
   SO(10) and every summed internal index ranges over Cartesian components; bare labels m, p are
   fixed polarization directions u[p] = e2 + I e3, u[m] = e2 - I e3, so \[Delta][m,p] = 2 and
   \[Delta][m,m] = \[Delta][p,p] = 0. Under this contract psi[a] dX[a] needs no explicit lower metric.
   It is not coordinate-basis covariance: light-cone coordinate indices would need the metric.
   Contraction must never overwrite a fixed label, never read a delta power as a component sum,
   contract delta-only chains, and refuse malformed (non-Einstein) products. Expected values are
   explicit Cartesian sums or exact identities, never old outputs.

   Run: wolframscript -file StringCode/Symbols/TypeII/FlatSpace/DeltaContraction.test.wls
   Exit status 0 iff every assertion passes. *)

Needs["StringCode`"];
StringCode`InitStringCode[<|"theory" -> "TypeII", "CFT" -> "FlatSpace",
  "conventions" -> "TypeII-Ashoke", "bracket" -> "Flat"|>];
Needs["StringCode`Utils`Canonicalize`"];

ToExpression["
results = {};
report[name_, cond_] := (Print[name, \": \", If[TrueQ[cond], \"PASSED\", \"FAILED\"]];
  AppendTo[results, TrueQ[cond]]; cond);

(* frame: u[p] = e2 + I e3, u[m] = e2 - I e3 *)
frameVector[p] = {0, 1, I, 0, 0, 0, 0, 0, 0, 0};
frameVector[m] = {0, 1, -I, 0, 0, 0, 0, 0, 0, 0};
lightConeValue[expr_] := expr /. {\[Delta][p, p] -> 0, \[Delta][m, m] -> 0,
   \[Delta][m, p] -> 2, \[Delta][p, m] -> 2};

(* Cartesian evaluation of an expression polynomial in \[Delta] with free labels a, b and one
   internal dummy \[Mu]: substitute integer components and sum the dummy explicitly. *)
cartesian[expr_, la_, lb_] := Sum[
   frameVector[la][[i]] frameVector[lb][[j]] Sum[
     expr /. {a -> i, b -> j, \[Mu] -> mu} /. \[Delta][x_Integer, y_Integer] :> KroneckerDelta[x, y],
     {mu, 10}],
   {i, 10}, {j, 10}];

(* ---- 1. Frame metric algebra ---- *)
report[\"T1 frame components are the Euclidean dot products\",
  frameVector[p].frameVector[p] == 0 && frameVector[m].frameVector[m] == 0 &&
  frameVector[m].frameVector[p] == 2];

(* ---- 2. Supercurrent implicit contraction: identity term of psi^a dX^b(z) G(w) ---- *)
ope = OPE[R[\[Psi][a, 0, z], dX[b, 0, z]], R[\[Psi][\[Mu], 0, w], dX[\[Mu], 0, w]]];
id = Expand[Together[Total[Select[List @@ ope, FreeQ[#, _R] &]] (z - w)^3]];
report[\"T2 OPE identity term is the delta-only chain\",
  id === \[Alpha]p/4 \[Delta][a, \[Mu]] \[Delta][b, \[Mu]]];
report[\"T3 contractDeltasInline contracts delta-only chains\",
  Private`contractDeltasInline[id] === \[Alpha]p/4 \[Delta][b, a] ||
  Private`contractDeltasInline[id] === \[Alpha]p/4 \[Delta][a, b]];
Do[
  With[{la = pair[[1]], lb = pair[[2]]},
    Module[{contractFirst, labelsFirstInline, labelsFirstRules, cart},
      cart = Simplify[cartesian[id, la, lb]];
      contractFirst = lightConeValue[ContractDelta[id] /. {a -> la, b -> lb}];
      labelsFirstInline = lightConeValue[Private`contractDeltasInline[id /. {a -> la, b -> lb}]];
      labelsFirstRules = lightConeValue[Contract[ContractDelta[id /. {a -> la, b -> lb}]]];
      report[\"T4 (\" <> ToString[la] <> \",\" <> ToString[lb] <> \") contract-then-label = Cartesian = \" <> ToString[cart, InputForm],
        Simplify[contractFirst - cart] === 0];
      report[\"T5 (\" <> ToString[la] <> \",\" <> ToString[lb] <> \") label-then-contract (inline) = Cartesian\",
        Simplify[labelsFirstInline - cart] === 0];
      report[\"T6 (\" <> ToString[la] <> \",\" <> ToString[lb] <> \") label-then-ContractDelta/Contract = Cartesian\",
        Simplify[labelsFirstRules - cart] === 0]
    ]],
  {pair, {{p, p}, {p, m}, {m, m}}}];

(* ---- 3. Powers and traces ---- *)
report[\"T7 Contract never turns a labelled square into the dimension\",
  Contract[\[Delta][a, p]^2] === \[Delta][p, p] && Contract[\[Delta][m, p]^2] === \[Delta][m, p]^2 &&
  Contract[\[Delta][p, p]] === \[Delta][p, p]];
report[\"T8 Contract of genuinely summed traces gives 10\",
  Contract[\[Delta][a, a]] === 10 && Contract[\[Delta][a, b]^2] === 10];
report[\"T9 ContractDelta splits a labelled square\",
  ContractDelta[c1 \[Delta][p, \[Nu]]^2] === c1 \[Delta][p, p]];

(* ---- 4. Fixed labels and integer components are never overwritten ---- *)
report[\"T10 ContractDelta keeps a repeated fixed label\",
  ContractDelta[\[Delta][p, \[Nu]] X[\[Nu]] K[p, p]] === X[p] K[p, p]];
report[\"T11 contractDeltasInline keeps a repeated fixed label\",
  Private`contractDeltasInline[\[Delta][p, \[Nu]] X[\[Nu]] K[p, p]] === X[p] K[p, p]];
report[\"T12 integer components are values, not dummies\",
  Private`contractDeltasInline[\[Delta][3, \[Nu]] X[\[Nu]] Y[3]] === X[3] Y[3] &&
  Private`contractDeltasInline[\[Delta][3, 4] X[3]] === \[Delta][3, 4] X[3]];

(* ---- 5. Second saved target: delta[a,m4] psit[a] overlapped with psit[m] ---- *)
opeT = OPE[R[\[Psi]t[\[Nu], 0, z]], R[\[Psi]t[m, 0, w]]];
idT = Expand[Together[Total[Select[List @@ opeT, FreeQ[#, _R] &]] (z - w)]];
chain = \[Delta][\[Nu], m4] idT;
report[\"T13 psit overlap chain completes to delta[m4,m]\",
  FreeQ[ContractDelta[chain], \[Nu]] && FreeQ[Private`contractDeltasInline[chain], \[Nu]]];
report[\"T14 all-plus m4 -> p gives the Cartesian value 2 x (psit two-point coefficient)\",
  With[{coef = idT /. \[Delta][__] -> 1},
    Simplify[lightConeValue[ContractDelta[chain] /. m4 -> p] - 2 coef] === 0 &&
    Simplify[lightConeValue[Private`contractDeltasInline[chain /. m4 -> p]] - 2 coef] === 0 &&
    frameVector[p].frameVector[m] == 2]];

(* ---- 6. Wick pairings: null self-pairings vanish, mixed pairings carry 2, both chiralities ---- *)
wickPairs = {
  {Wick[\[Psi][p, 0, z], \[Psi][p, 0, w]], Wick[\[Psi][m, 0, z], \[Psi][p, 0, w]], Wick[\[Psi][1, 0, z], \[Psi][1, 0, w]]},
  {Wick[\[Psi]t[p, 0, z], \[Psi]t[p, 0, w]], Wick[\[Psi]t[m, 0, z], \[Psi]t[p, 0, w]], Wick[\[Psi]t[1, 0, z], \[Psi]t[1, 0, w]]},
  {Wick[dX[p, 0, z], dX[p, 0, w]], Wick[dX[m, 0, z], dX[p, 0, w]], Wick[dX[1, 0, z], dX[1, 0, w]]},
  {Wick[dXt[p, 0, z], dXt[p, 0, w]], Wick[dXt[m, 0, z], dXt[p, 0, w]], Wick[dXt[1, 0, z], dXt[1, 0, w]]}
};
report[\"T15 Wick null pairings vanish and mixed pairings are twice a Cartesian diagonal\",
  AllTrue[wickPairs, Function[w3,
    lightConeValue[w3[[1]]] === 0 &&
    Simplify[lightConeValue[w3[[2]]] - 2 (w3[[3]] /. \[Delta][1, 1] -> 1)] === 0]]];

(* ---- 7. Cached Taylor templates hand out fresh dummies ---- *)
dummiesOf[e_] := DeleteDuplicates @ Cases[e, s_Symbol /; StringContainsQ[SymbolName[s], \"$\"], {0, Infinity}];
e1 = Private`expXPoly[k, 2]; e2 = Private`expXPoly[k, 2];
f1 = Private`expXPolyT[k, 2]; f2 = Private`expXPolyT[k, 2];
report[\"T16 expXPoly/expXPolyT retrievals share no dummies\",
  dummiesOf[e1] =!= {} && Intersection[dummiesOf[e1], dummiesOf[e2]] === {} &&
  Intersection[dummiesOf[f1], dummiesOf[f2]] === {}];
report[\"T17 expXPoly retrievals are dummy-relabelings of each other\",
  canonicalizeDummies[e1] === canonicalizeDummies[e2]];

(* ---- 8. Taylor freshening keeps caller-supplied symbols (review finding A) ---- *)
kk = Module[{kk}, kk]; kk2 = Module[{kk}, kk]; hh = Module[{H}, H];
report[\"T18 Module-generated momentum survives expXPoly/expXPolyT, including as a head\",
  And @@ Flatten @ Table[!FreeQ[f[kk, n], kk[_]], {f, {Private`expXPoly, Private`expXPolyT}}, {n, {1, 2}}]];
report[\"T19 Module-generated profile survives ProfileXPoly/ProfileXPolyT\",
  And @@ Flatten @ Table[!FreeQ[f[hh, n], der[hh]], {f, {Private`ProfileXPoly, Private`ProfileXPolyT}}, {n, {1, 2}}]];
report[\"T20 distinct caller momenta stay distinct\",
  With[{a1 = Private`expXPoly[kk, 1], a2 = Private`expXPoly[kk2, 1]},
    !FreeQ[a1, kk] && FreeQ[a1, kk2] && !FreeQ[a2, kk2] && FreeQ[a2, kk]]];
internal[e_, inputs_] := Complement[dummiesOf[e], Cases[inputs, _Symbol, {0, Infinity}, Heads -> True]];
report[\"T21 retrievals with a Module momentum have disjoint internal dummies and are relabelings\",
  With[{g1 = Private`expXPolyT[kk, 2], g2 = Private`expXPolyT[kk, 2]},
    internal[g1, kk] =!= {} && Intersection[internal[g1, kk], internal[g2, kk]] === {} &&
    canonicalizeDummies[g1] === canonicalizeDummies[g2]]];

(* ---- 9. Standalone delta powers (review finding E) ---- *)
report[\"T22 bare delta powers contract on every path\",
  Private`contractDeltasInline[\[Delta][a, p]^2] === \[Delta][p, p] &&
  ContractDelta[\[Delta][a, p]^2] === \[Delta][p, p] &&
  Contract[\[Delta][a, b]^2] === 10 && Contract[\[Delta][a, a]] === 10 &&
  Private`contractDeltasInline[x0 + \[Delta][a, p]^2] === x0 + \[Delta][p, p]];

(* ---- 10. Malformed products are refused, not guessed (review finding D) ---- *)
refusedQ[f_, e_] := Module[{flagged = False, out},
  out = Check[f[e], flagged = True; Quiet[f[e], Private`contractDeltaFactors::malformed],
    Private`contractDeltaFactors::malformed];
  flagged && out === e];
malformedCases = {
  c1 \[Delta][a, b]^3,
  \[Delta][a, p]^2 X[a],
  \[Delta][a, a] X[a],
  \[Delta][a, b] X[a] Y[a]
};
report[\"T23 ContractDelta refuses malformed products\", AllTrue[malformedCases, refusedQ[ContractDelta, #] &]];
report[\"T24 contractDeltasInline (cleanupBracket path) refuses malformed products\",
  AllTrue[malformedCases, refusedQ[Private`contractDeltasInline, #] &]];
report[\"T25 Contract refuses malformed products\", AllTrue[malformedCases, refusedQ[Contract, #] &]];
report[\"T26 malformed product nested in a sum is refused in its own context\",
  refusedQ[ContractDelta, z9 (\[Delta][a, a] X[a] + W)] && refusedQ[Contract, z9 (\[Delta][a, a] X[a] + W)]];

(* ---- 11. Well-formed nested structures still contract ---- *)
report[\"T27 index in both summands of a sum counts once (distributivity)\",
  Expand[ContractDelta[(X[a] + Y[a]) \[Delta][a, b]]] === X[b] + Y[b] &&
  Expand[ContractDelta[c1 (\[Delta][a, b] X[a] + Z)]] === Expand[c1 (X[b] + Z)]];
report[\"T28 profile identity labels inside der[...] are not counted as index occurrences\",
  ContractDelta[\[Delta][a, b] ProfileX[H[a, c], {}, 0, 0] Q[c] (w0)^dot[der[H[a, c]], der[K]]] ===
    ProfileX[H[b, c], {}, 0, 0] Q[c] (w0)^dot[der[H[b, c]], der[K]]];

allPassed = And @@ results;
Print[\"\\n=== SUMMARY ===\"];
Print[\"Loaded package: \", FindFile[\"StringCode`\"]];
Print[\"Passed: \", Count[results, True], \"/\", Length[results]];
If[allPassed, Print[\"All tests PASSED!\"], Print[\"Some tests FAILED.\"]];
Exit[If[allPassed, 0, 1]];
"];
