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

holdMarkerNameQ[name_String] := StringEndsQ[name, "Hold"];

dummySymbolQ[s_Symbol] := With[{name = SymbolName[s]},
  StringContainsQ[name, "$" ~~ DigitCharacter ..] ||
  StringMatchQ[name, "\[Mu]Canon" ~~ DigitCharacter ..] ||
  StringMatchQ[name, "\[Alpha]Dummies" ~~ DigitCharacter ..] ||
  StringMatchQ[name, "\[Alpha]tDummies" ~~ DigitCharacter ..]
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

canonicalNameFor["Alpha",  n_Integer] := Symbol["\[Alpha]Dummies" <> ToString[n]];
canonicalNameFor["AlphaT", n_Integer] := Symbol["\[Alpha]tDummies" <> ToString[n]];
canonicalNameFor[_,        n_Integer] := Symbol["\[Mu]Canon" <> ToString[n]];

einsteinCandidatesIn[term_] := Module[{leaves, freq},
  leaves = Cases[term, _Symbol, {0, Infinity}, Heads -> False];
  leaves = Select[leaves,
    !positionSymbolNameQ[SymbolName[#]] &&
    !isField[#] &&
    !holdMarkerNameQ[SymbolName[#]] &
  ];
  freq = Tally[leaves];
  Select[freq, #[[2]] == 2 &][[All, 1]]
];

canonicalizeOneTermDummies[term_] := Module[
  {candidates, sysDummies, allDummies, ordered, temps, finals, counters},
  candidates = einsteinCandidatesIn[term];
  sysDummies = Cases[term, s_Symbol?dummySymbolQ, {0, Infinity}, Heads -> True];
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

contractOneDelta[factors_List] := Catch[
  Module[{a, b, nonDeltaPositions},
    Do[
      If[deltaFactorQ[factors[[i]]],
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

derAppendInTimes[t_Times] := Module[
  {factors, profileMap, toRemove, info, profHead, idx, exponent, pos},
  factors = List @@ t;
  profileMap = <||>;
  Do[
    If[rFactorQ[factors[[i]]],
      Do[
        If[profileXFactorQ[factors[[i, j]]],
          profileMap[factors[[i, j, 1]]] = {i, j}
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
      If[KeyExistsQ[profileMap, profHead],
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
