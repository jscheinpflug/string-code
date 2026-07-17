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

$canonicalizeDummiesProtectedPatterns::usage = "$canonicalizeDummiesProtectedPatterns is the list of string patterns (matched via StringMatchQ) naming symbols that must never be treated as Einstein dummies by canonicalizeDummies: physical parameters and moduli such as the plumbing coordinates q1/qbar1/r0, the string scale \[Alpha]p, and the worldsheet moduli t$n/tbar$n. It gates BOTH detection routes \[Dash] einsteinCandidatesIn (the \"appears exactly twice\" heuristic) and canonicalizeOneTermDummies' sysDummies (the \"$\"-named Module-symbol route) \[Dash] because a protected symbol may be caught by either. Extend it when introducing a new named parameter that can appear exactly twice in a term, or a new Module-generated symbol that is not a term-local Einstein index.";
$canonicalizeDummiesProtectedPatterns = {
  "q" ~~ ("" | DigitCharacter ..) ~~ ("" | "bar"),
  "r" ~~ DigitCharacter ..,
  "\[Alpha]p",
  (* Worldsheet moduli, minted one {t, tbar} pair per modulus by the flat vertex. They are
     Module-generated (so dummySymbolQ claims them) but they are INTEGRATION VARIABLES shared
     across terms, not term-local Einstein indices: renaming them per-term in order of first
     appearance gives the same modulus different names in different terms and silently corrupts
     the expression. Mirrors $projectionStrandProtectedPatterns in Brackets/TypeII. *)
  ("t" | "tbar") ~~ "$" ~~ DigitCharacter ..
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

contractOneDelta::usage = "contractOneDelta[factors] contracts the first Kronecker delta whose index occurs in another factor, replacing the index and removing the delta. Trace deltas \[Delta][a,a] are deliberately left untouched: their value (the spacetime dimension) is a downstream convention (e.g. \[Delta][a_,a_] :> 10), and dropping them here would silently lose dimension factors.";
contractOneDelta[factors_List] := Catch[
  Module[{a, b, nonDeltaPositions},
    Do[
      If[deltaFactorQ[factors[[i]]] && factors[[i, 1]] =!= factors[[i, 2]],
        a = factors[[i, 1]]; b = factors[[i, 2]];
        nonDeltaPositions = Select[
          Range[Length[factors]],
          # =!= i && !deltaFactorQ[factors[[#]]] &
        ];
        If[AnyTrue[nonDeltaPositions, !FreeQ[factors[[#]], a] &],
          Throw[Delete[factors /. {a -> b}, i]]
        ];
        If[AnyTrue[nonDeltaPositions, !FreeQ[factors[[#]], b] &],
          Throw[Delete[factors /. {b -> a}, i]]
        ];
      ],
      {i, 1, Length[factors]}
    ];
    factors
  ]
];

contractDeltasInTimes[t_Times] := Module[{factors},
  factors = FixedPoint[contractOneDelta, List @@ t];
  Times @@ factors
];

contractDeltasInline[expr_] := expr /. t_Times :> contractDeltasInTimes[t];


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
