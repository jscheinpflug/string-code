(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Utils`Canonicalize`"];
Needs["StringCode`Symbols`"];


(* ::Section:: *)
(*Declare public variables and methods*)


canonicalizeDummies::usage =
  "canonicalizeDummies[expr] splits expr into a sum of terms and, within each term, renumbers dummy indices to \[Mu]Canon1, \[Mu]Canon2, ... in order of first appearance. A symbol counts as a dummy if it (a) is Module-generated (name contains `$<digits>`), (b) already matches \[Mu]Canon<digits>, or (c) is a non-head, non-field, non-position leaf appearing exactly twice in the term (Einstein convention). Two terms differing only by a permutation of dummy names then collapse to identical forms and combine automatically under Plus. Idempotent and CFT-agnostic.";

$canonicalizeDummiesPositionPatterns::usage =
  "$canonicalizeDummiesPositionPatterns is the list of string patterns (matched via StringMatchQ) treated as world-sheet coordinate names and excluded from Einstein-dummy detection. Default catches z, z1, z2, ..., zbar, z1bar, ..., w, w1, ..., wbar, w1bar, ....";

derAppend::usage =
  "derAppend[expr] folds factors of the form der[F][\[Mu]] (or der[F][\[Mu]]^n) into the index list of any matching ProfileX[F, indices, ...] occurring inside an R[...] in the same Times product. Theory-agnostic: matches the heads R, ProfileX, der by SymbolName, so it works with both Bosonic and TypeII FlatSpace.";

cleanupBracket::usage =
  "cleanupBracket[expr] runs the end-of-pipeline cleanup chain on a bracket-like expression: contracts Kronecker deltas, folds der[F][\[Mu]] derivatives into ProfileX index lists, and canonicalizes dummy indices. Equivalent to canonicalizeDummies @ derAppend @ (\[Delta]-contraction). Delta-head and field heads are matched by SymbolName so the function is CFT-agnostic.";


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


$canonicalizeDummiesPositionPatterns = {
  ("z" | "w") ~~ ("" | DigitCharacter ..) ~~ ("" | "bar")
};

positionSymbolNameQ[name_String] := AnyTrue[
  $canonicalizeDummiesPositionPatterns, StringMatchQ[name, #] &
];

$canonicalizeDummiesProtectedPatterns::usage = "$canonicalizeDummiesProtectedPatterns is the list of string patterns (matched via StringMatchQ) naming symbols that must never be treated as Einstein dummies by canonicalizeDummies: physical parameters and moduli such as the plumbing coordinates q1/q1bar/r0, the string scale \[Alpha]p, the worldsheet moduli t$n/tbar$n, the external momenta k1/k2/... of plane-wave vertices, and the bare external index labels m/p used when a vertex's tensor slots are collapsed onto one symbol. It gates BOTH detection routes \[Dash] einsteinCandidatesIn (the \"appears exactly twice\" heuristic) and canonicalizeOneTermDummies' sysDummies (the \"$\"-named Module-symbol route) \[Dash] because a protected symbol may be caught by either. Extend it when introducing a new named parameter that can appear exactly twice in a term, or a new Module-generated symbol that is not a term-local Einstein index.";
$canonicalizeDummiesProtectedPatterns = {
  "q" ~~ ("" | DigitCharacter ..) ~~ ("" | "bar"),
  "r" ~~ DigitCharacter ..,
  "\[Alpha]p",
  (* Worldsheet moduli, minted one {t, tbar} pair per modulus by the flat vertex. They are
     Module-generated (so dummySymbolQ claims them) but they are INTEGRATION VARIABLES shared
     across terms, not term-local Einstein indices: renaming them per-term in order of first
     appearance gives the same modulus different names in different terms and silently corrupts
     the expression. Mirrors $projectionStrandProtectedPatterns in Brackets/TypeII. *)
  ("t" | "tbar") ~~ "$" ~~ DigitCharacter ..,
  (* External momenta k1, k2, ... of plane-wave vertices. They are EXTERNAL LABELS shared across
     terms, not term-local Einstein indices, but they occur as bare leaves (inside dot[k1,k2],
     dot[k1,der[f]], expX[k1,...]) and so are visible to the "appears exactly twice" heuristic.
     Whether they trip it depends on how many of those factors a term happens to carry: in the
     raw corrKGKExp export each momentum appears three times and is safe, but once the
     Koba-Nielsen exponentials carrying dot[k,der[H]] are substituted away the count drops to two
     and canonicalizeDummies renames the momenta into \[Mu]Canon dummies, silently destroying the
     kinematics. Protect them unconditionally rather than relying on the count. *)
  "k" ~~ DigitCharacter ..,
  (* Bare m and p: the EXTERNAL index labels used when a vertex's tensor slots are collapsed onto
     a single symbol (e.g. Kon1[m,m,m,m] against Kon2[p,p,p,p] for a trace/singlet contraction).
     They are shared across terms, not term-local Einstein indices, but their per-term occurrence
     count varies: in a 3-point KGK export m appeared twice in 119 of 172 terms and more often in
     the remaining 53, so canonicalizeDummies renamed it to \[Mu]Canon in some terms and left it
     in others. The sum then carries the same label under two names, and every downstream rule
     keyed on it (transversality cuts such as MemberQ[list, m | p], \[Delta][m,p] substitutions)
     fires on only part of the expression. Exact match only: p1/p2/s1/s2 and friends ARE genuine
     per-term dummies in the uncollapsed exports and must stay canonicalizable. *)
  "m" | "p"
};

protectedSymbolNameQ::usage = "protectedSymbolNameQ[name] checks whether a symbol name matches $canonicalizeDummiesProtectedPatterns and is therefore exempt from Einstein-dummy detection.";
protectedSymbolNameQ[name_String] := AnyTrue[
  $canonicalizeDummiesProtectedPatterns, StringMatchQ[name, #] &
];

holdMarkerNameQ[name_String] := StringEndsQ[name, "Hold"];

dummySymbolQ[s_Symbol] := With[{name = SymbolName[s]},
  StringContainsQ[name, "$" ~~ DigitCharacter ..] ||
  StringMatchQ[name, "\[Mu]Canon" ~~ ("$" | "") ~~ DigitCharacter ..] ||
  StringMatchQ[name, "\[Alpha]Dummies" ~~ ("$" | "") ~~ DigitCharacter ..] ||
  StringMatchQ[name, "\[Alpha]tDummies" ~~ ("$" | "") ~~ DigitCharacter ..]
];
dummySymbolQ[_] := False;

dummyKind[s_Symbol] := With[{name = SymbolName[s]},
  Which[
    StringStartsQ[name, "\[Alpha]t"], "AlphaT",
    StringStartsQ[name, "alphat"],     "AlphaT",
    StringStartsQ[name, "\[Alpha]"],   "Alpha",
    StringStartsQ[name, "alpha"],      "Alpha",
    True,                                "Mu"
  ]
];

(* Canonical names carry a "$" so that canonicalized dummies stay visible to every
   $-keyed integrity audit (BracketProjection/EffectiveBracketDirectPCO guards,
   projectionStrandViolations): canonicalization must not disarm the safety net. *)
canonicalNameFor["Alpha",  n_Integer] := Symbol["\[Alpha]Dummies$" <> ToString[n]];
canonicalNameFor["AlphaT", n_Integer] := Symbol["\[Alpha]tDummies$" <> ToString[n]];
canonicalNameFor[_,        n_Integer] := Symbol["\[Mu]Canon$" <> ToString[n]];

einsteinCandidatesIn::usage = "einsteinCandidatesIn[term] returns the symbols appearing exactly twice in argument position within term (integer powers counted with multiplicity, matching the projection guard's convention), excluding position/protected/field/hold-marker names. These are treated as Einstein-contracted dummies by canonicalizeOneTermDummies.";
einsteinCandidatesIn[term_] := Module[{exploded, leaves, freq},
  (* count integer powers with multiplicity: x^2 is an Einstein pair, and
     f[a] g[a]^2 has THREE occurrences of a, not two -- same convention as
     projectionStrandViolations in Brackets/TypeII *)
  exploded = term //. Power[b_, n_Integer /; n >= 2] :>
    canonicalizePowerHold @@ ConstantArray[b, n];
  leaves = Cases[exploded, _Symbol, {0, Infinity}, Heads -> False];
  leaves = Select[leaves,
    !positionSymbolNameQ[SymbolName[#]] &&
    !protectedSymbolNameQ[SymbolName[#]] &&
    !isField[#] &&
    !holdMarkerNameQ[SymbolName[#]] &
  ];
  freq = Tally[leaves];
  Select[freq, #[[2]] == 2 &][[All, 1]]
];

canonicalizeOneTermDummies[term_] := Module[
  {candidates, sysDummies, allDummies, ordered, temps, finals, counters},
  candidates = einsteinCandidatesIn[term];
  (* einsteinCandidatesIn already filters protected/position names; sysDummies must too, or
     Module-generated non-indices (worldsheet moduli t$n/tbar$n) get renamed per-term. *)
  sysDummies = Select[
    Cases[term, s_Symbol?dummySymbolQ, {0, Infinity}, Heads -> True],
    !protectedSymbolNameQ[SymbolName[#]] &
  ];
  allDummies = Join[candidates, sysDummies];
  If[allDummies === {}, Return[term]];
  ordered = DeleteDuplicates[
    Cases[term, s_Symbol /; MemberQ[allDummies, s], {0, Infinity}, Heads -> True]
  ];
  If[ordered === {}, Return[term]];
  counters = <|"Mu" -> 0, "Alpha" -> 0, "AlphaT" -> 0|>;
  finals = Map[
    Function[s, With[{k = dummyKind[s]},
      counters[k] = counters[k] + 1;
      canonicalNameFor[k, counters[k]]
    ]],
    ordered
  ];
  temps = Array[Symbol["\[Mu]CanonPlaceholder$" <> ToString[#]] &, Length[ordered]];
  term /. Thread[ordered -> temps] /. Thread[temps -> finals]
];

canonicalizeDummies[expr_] := Module[{expanded, terms},
  expanded = Expand[expr];
  terms = If[Head[expanded] === Plus, List @@ expanded, {expanded}];
  Total[canonicalizeOneTermDummies /@ terms]
];


deltaFactorQ[fac_] := MatchQ[fac, (d_Symbol)[_, _] /; SymbolName[d] === "\[Delta]"];

(* Representation contract for delta contraction.
   \[Delta] is the metric of an ORTHONORMAL Cartesian basis (complexified SO(10)), and every summed
   internal index ranges over Cartesian components. Bare external labels such as m, p are fixed
   polarization directions (e.g. u[p] = e2 + I e3, u[m] = e2 - I e3, so \[Delta][p,p] = 0 and
   \[Delta][m,p] = 2), never summed coordinate indices. Substitution contraction is valid ONLY under
   this contract; if summed indices were light-cone coordinate indices, contraction would need
   the metric/inverse metric explicitly. The name test deltaContractibleIndexQ says which symbols
   MAY be summed; the multiplicity guard deltaMalformedIndices checks that a candidate actually is
   a well-formed Einstein dummy (exactly two occurrences) before any destructive step. *)

deltaContractibleIndexQ::usage = "deltaContractibleIndexQ[index] is True when index is a symbol whose name is not protected by $canonicalizeDummiesProtectedPatterns, i.e. it MAY be a summed Cartesian index. Protected external labels (bare m, p) and literal components (integers) are fixed values and are never overwritten. This is a name test only: the role of an index (exactly two occurrences in its product) is checked separately by deltaMalformedIndices before any contraction, trace or square reduction.";
deltaContractibleIndexQ[s_Symbol] := !protectedSymbolNameQ[SymbolName[s]];
deltaContractibleIndexQ[_] := False;

deltaIndexOccurrences::usage = "deltaIndexOccurrences[expr, s] counts occurrences of the symbol s in expr as an Einstein index: integer powers count with multiplicity, alternative summands of a Plus count as their maximum (distributivity), heads are ignored, and the profile identity inside der[...] (a label copy such as dot[der[H[a,b]], der[K[..]]], renamed consistently by substitution) is not counted, whereas the slot of der[f][a] is.";
deltaIndexOccurrences[e_, s_] := Which[
  e === s, 1,
  AtomQ[e], 0,
  MatchQ[e, (d_Symbol)[_] /; SymbolName[d] === "der"], 0,
  Head[e] === Plus, Max[deltaIndexOccurrences[#, s] & /@ List @@ e],
  Head[e] === Power && IntegerQ[e[[2]]] && e[[2]] > 0, e[[2]] deltaIndexOccurrences[e[[1]], s],
  True, Total[deltaIndexOccurrences[#, s] & /@ List @@ e]
];

deltaMalformedIndices::usage = "deltaMalformedIndices[factors] returns {{index, occurrences}, ...} for every contractible index of a delta factor in the product whose occurrence count (deltaIndexOccurrences over the whole product, powers split) exceeds two. A well-formed summed index occurs exactly twice; three or more (a delta cube, a squared delta whose dummy also appears elsewhere, a trace index used elsewhere) has no Einstein meaning, so contraction must not guess.";
deltaMalformedIndices[factors_List] := Module[{candidates},
  candidates = Select[
    DeleteDuplicates @ Flatten[List @@@ Select[factors, deltaFactorQ]],
    deltaContractibleIndexQ];
  Select[
    Function[s, {s, Total[deltaIndexOccurrences[#, s] & /@ factors]}] /@ candidates,
    #[[2]] > 2 &]
];

deltaFactorOrPowerQ::usage = "deltaFactorOrPowerQ[f] is True for a delta factor or an integer power of one.";
deltaFactorOrPowerQ[f_] := deltaFactorQ[f] || MatchQ[f, Power[_?deltaFactorQ, _Integer?Positive]];

contractDeltaFactors::malformed = "Delta contraction left a product unchanged: summed index `1` occurs `2` times (a well-formed Einstein dummy occurs exactly twice). Product: `3`.";

splitDeltaPowers::usage = "splitDeltaPowers[factors] replaces integer powers of delta factors by repeated factors.";
splitDeltaPowers[factors_List] := Flatten[
  Replace[factors, Power[d_?deltaFactorQ, n_Integer /; n >= 2] :> ConstantArray[d, n], {1}], 1];

contractOneDelta::usage = "contractOneDelta[factors] contracts the first Kronecker delta one of whose contractible indices (see deltaContractibleIndexQ) also occurs in another factor, including another delta, replacing that index and removing the delta. Delta-only chains such as \[Delta][a,m1] \[Delta][a,m2] therefore collapse to \[Delta][m1,m2] (they used to survive whenever a occurred only inside deltas). Protected labels are never overwritten, so \[Delta][p,a] X[a] K[p,p] gives X[p] K[p,p]. Trace deltas \[Delta][a,a] are deliberately left untouched: their value (the spacetime dimension, or a null-label component) is a downstream convention, and dropping them here would silently lose dimension factors. Callers must pass integer powers of deltas as repeated factors (contractDeltasInTimes does).";
contractOneDelta[factors_List] := Catch[
  Module[{a, b, otherPositions},
    Do[
      If[deltaFactorQ[factors[[i]]] && factors[[i, 1]] =!= factors[[i, 2]],
        a = factors[[i, 1]]; b = factors[[i, 2]];
        otherPositions = Delete[Range[Length[factors]], i];
        If[deltaContractibleIndexQ[a] && AnyTrue[otherPositions, !FreeQ[factors[[#]], a] &],
          Throw[Delete[factors /. {a -> b}, i]]
        ];
        If[deltaContractibleIndexQ[b] && AnyTrue[otherPositions, !FreeQ[factors[[#]], b] &],
          Throw[Delete[factors /. {b -> a}, i]]
        ];
      ],
      {i, 1, Length[factors]}
    ];
    factors
  ]
];

contractDeltaFactors::usage = "contractDeltaFactors[factors] contracts the Kronecker deltas of one product given as a factor list. Integer powers of deltas are split first, so \[Delta][p,a]^2 (the image of \[Delta][a,m1] \[Delta][a,m2] after m1,m2 -> p) contracts to the component \[Delta][p,p]. Guarded: if any contractible delta index occurs more than twice (deltaMalformedIndices), a contractDeltaFactors::malformed message is issued and the ORIGINAL factors are returned unchanged. Substitution preserves the exactly-two property, so the guard need only run once.";
contractDeltaFactors[factors_List] := Module[{split, bad},
  split = splitDeltaPowers[factors];
  If[FreeQ[split, _?deltaFactorQ, {1}], Return[factors]];
  bad = deltaMalformedIndices[split];
  If[bad =!= {},
    Message[contractDeltaFactors::malformed, bad[[1, 1]], bad[[1, 2]], Short[Times @@ factors, 2]];
    Return[factors]
  ];
  FixedPoint[contractOneDelta, split]
];

contractDeltasInTimes::usage = "contractDeltasInTimes[t] contracts Kronecker deltas inside the product t via contractDeltaFactors (power splitting and malformed-index guard).";
contractDeltasInTimes[t_Times] := Times @@ contractDeltaFactors[List @@ t];

contractDeltasInline::usage = "contractDeltasInline[expr] contracts deltas in each outermost product of expr, and in delta factors or delta powers that stand alone (e.g. a bare \[Delta][a,p]^2 term). Products nested inside a matched product are not revisited; use contractDeltasDeep for that.";
contractDeltasInline[expr_] := expr /. {
  t_Times :> contractDeltasInTimes[t],
  d_?deltaFactorOrPowerQ :> Times @@ contractDeltaFactors[{d}]
};

contractDeltasDeep::usage = "contractDeltasDeep[expr] applies contractDeltaFactors to every product and standalone delta (power) at any depth through Plus, Times, integer Power and List, top-down so that each product is guarded in its own context. Used by the TypeII FlatSpace ContractDelta.";
contractDeltasDeep[e_] := Which[
  AtomQ[e], e,
  Head[e] === Times, Times @@ (If[deltaFactorOrPowerQ[#], #, contractDeltasDeep[#]] & /@ contractDeltaFactors[List @@ e]),
  deltaFactorOrPowerQ[e], Times @@ contractDeltaFactors[{e}],
  MatchQ[Head[e], Plus | List], contractDeltasDeep /@ e,
  Head[e] === Power && IntegerQ[e[[2]]], contractDeltasDeep[e[[1]]]^e[[2]],
  True, e
];

traceDeltaFactors::usage = "traceDeltaFactors[factors, dim] evaluates delta traces and squares in one product, guarded like contractDeltaFactors: a square \[Delta][a,b]^2 through a contractible index a (occurring only in the square) becomes \[Delta][b,b]; a trace \[Delta][a,a] over a contractible index becomes dim. Traces and squares over fixed labels are components, not the dimension, and are left alone. Malformed products are returned unchanged with a contractDeltaFactors::malformed message.";
traceDeltaFactors[factors_List, dim_] := Module[{split, bad, pos, d, rest},
  split = splitDeltaPowers[factors];
  If[FreeQ[split, _?deltaFactorQ, {1}], Return[factors]];
  bad = deltaMalformedIndices[split];
  If[bad =!= {},
    Message[contractDeltaFactors::malformed, bad[[1, 1]], bad[[1, 2]], Short[Times @@ factors, 2]];
    Return[factors]
  ];
  (* squares: two identical off-diagonal deltas sharing a contractible index *)
  While[(pos = SelectFirst[Range[Length[split]],
        deltaFactorQ[split[[#]]] && split[[#, 1]] =!= split[[#, 2]] &&
          Count[split, split[[#]]] >= 2 &&
          (deltaContractibleIndexQ[split[[#, 1]]] || deltaContractibleIndexQ[split[[#, 2]]]) &,
        Missing[]]) =!= Missing[],
    d = split[[pos]];
    rest = Delete[split, Take[Position[split, d, {1}, Heads -> False], 2]];
    split = Append[rest,
      If[deltaContractibleIndexQ[d[[1]]], Head[d][d[[2]], d[[2]]], Head[d][d[[1]], d[[1]]]]]
  ];
  Replace[split, t_?deltaFactorQ /; t[[1]] === t[[2]] && deltaContractibleIndexQ[t[[1]]] :> dim, {1}]
];

contractTracesDeep::usage = "contractTracesDeep[expr, dim] applies traceDeltaFactors to every product and standalone delta (power) at any depth through Plus, Times, integer Power and List. Used by the TypeII FlatSpace Contract.";
contractTracesDeep[e_, dim_] := Which[
  AtomQ[e], e,
  Head[e] === Times, Times @@ (If[deltaFactorOrPowerQ[#], #, contractTracesDeep[#, dim]] & /@ traceDeltaFactors[List @@ e, dim]),
  deltaFactorOrPowerQ[e], Times @@ traceDeltaFactors[{e}, dim],
  MatchQ[Head[e], Plus | List], contractTracesDeep[#, dim] & /@ e,
  Head[e] === Power && IntegerQ[e[[2]]], contractTracesDeep[e[[1]], dim]^e[[2]],
  True, e
];


cleanupBracket[expr_] := canonicalizeDummies @ derAppend @ contractDeltasInline[expr];


derFactorQ[fac_] :=
  MatchQ[fac, (d_Symbol)[_][_] /; SymbolName[d] === "der"] ||
  MatchQ[fac, Power[(d_Symbol)[_][_], _Integer] /; SymbolName[d] === "der"];

derFactorInfo[fac_] := If[Head[fac] === Power,
  {fac[[1, 0, 1]], fac[[1, 1]], fac[[2]]},
  {fac[[0, 1]], fac[[1]], 1}
];

rFactorQ[fac_] := MatchQ[fac, (r_Symbol)[___] /; SymbolName[r] === "R"];

profileXFactorQ[arg_] := MatchQ[arg, (p_Symbol)[_, _List, _, _] /; SymbolName[p] === "ProfileX"];

derAppend::ambiguousProfile = "Term contains `1` ProfileX factors with the identical profile `2`; folding der[...] factors into it is ambiguous, so they are left standalone for this term. Resolve by distinguishing the profiles (labels) or folding upstream where the association is known.";

derAppendInTimes[t_Times] := Module[
  {factors, profileMap, ambiguous, toRemove, info, profHead, idx, exponent, pos},
  factors = List @@ t;
  profileMap = <||>;
  ambiguous = <||>;
  Do[
    If[rFactorQ[factors[[i]]],
      Do[
        If[profileXFactorQ[factors[[i, j]]],
          If[KeyExistsQ[profileMap, factors[[i, j, 1]]],
            (* identical profile appears twice: folding target is ambiguous *)
            ambiguous[factors[[i, j, 1]]] =
              Lookup[ambiguous, Key[factors[[i, j, 1]]], 1] + 1,
            profileMap[factors[[i, j, 1]]] = {i, j}
          ]
        ],
        {j, 1, Length[factors[[i]]]}
      ]
    ],
    {i, 1, Length[factors]}
  ];
  If[profileMap === <||>, Return[t]];

  toRemove = {};
  Do[
    If[derFactorQ[factors[[i]]],
      info = derFactorInfo[factors[[i]]];
      profHead = info[[1]]; idx = info[[2]]; exponent = info[[3]];
      Which[
        KeyExistsQ[ambiguous, profHead],
        Message[derAppend::ambiguousProfile, ambiguous[profHead], profHead],
        KeyExistsQ[profileMap, profHead],
        pos = profileMap[profHead];
        factors[[pos[[1]], pos[[2]], 2]] =
          Join[factors[[pos[[1]], pos[[2]], 2]], ConstantArray[idx, exponent]];
        AppendTo[toRemove, i]
      ]
    ],
    {i, 1, Length[factors]}
  ];
  If[toRemove === {}, Return[t]];

  Times @@ Delete[factors, List /@ toRemove]
];

derAppend[expr_] := expr /. t_Times :> derAppendInTimes[t];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
