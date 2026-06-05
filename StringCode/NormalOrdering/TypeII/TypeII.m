(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`NormalOrdering`TypeII`"];


Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];
Needs["StringCode`Symbols`TypeII`FlatSpace`"];
Needs["StringCode`NormalOrdering`"]


(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Define Grassmann parity*)


regcomm::usage = "Give Grassmann sign under commutation";
regcomm[f_,g_]:=(-1)^(parity[f] parity[g])(-1)^(exp\[Phi]parity[f] exp\[Phi]parity[g])(-1)^(exp\[Phi]tparity[f] exp\[Phi]tparity[g])

exp\[Phi]parity::usage = "Compute Grassmann parity of exp\[Phi]";
containsExpPhiHoloFermionQ[expr_] := !FreeQ[expr, field_ /; fieldProperty[field, "ExpPhiFermionFamily"] === "Holo"];
exp\[Phi]parity[f_]:=0/;!containsExpPhiHoloFermionQ[f]
exp\[Phi]parity[f_]:=1/;containsExpPhiHoloFermionQ[f]
exp\[Phi]parity[R[f__,g__]]:=Mod[exp\[Phi]parity[R[f]]+exp\[Phi]parity[R[g]],2]
exp\[Phi]parity[R[f_]]:=exp\[Phi]parity[f]
exp\[Phi]parity[U[f__,g__]]:=Mod[exp\[Phi]parity[U[f]]+exp\[Phi]parity[U[g]],2]
exp\[Phi]parity[U[f_]]:=exp\[Phi]parity[f]

exp\[Phi]tparity::usage = "Compute Grassmann parity of exp\[Phi]t";
containsExpPhiAntiHoloFermionQ[expr_] := !FreeQ[expr, field_ /; fieldProperty[field, "ExpPhiFermionFamily"] === "AntiHolo"];
exp\[Phi]tparity[f_]:=0/;!containsExpPhiAntiHoloFermionQ[f]
exp\[Phi]tparity[f_]:=1/;containsExpPhiAntiHoloFermionQ[f]
exp\[Phi]tparity[R[f__,g__]]:=Mod[exp\[Phi]tparity[R[f]]+exp\[Phi]tparity[R[g]],2]
exp\[Phi]tparity[R[f_]]:=exp\[Phi]tparity[f]
exp\[Phi]tparity[U[f__,g__]]:=Mod[exp\[Phi]tparity[U[f]]+exp\[Phi]tparity[U[g]],2]
exp\[Phi]tparity[U[f_]]:=exp\[Phi]tparity[f]


oddBosChirFieldQ::usage = "Checks if field is odd chiral bosonized exponential.";
oddBosChirFieldQ[x_] := MatchQ[Head[x], exp\[Phi]f];

oddBosAntiChFieldQ::usage = "Checks if field is odd antichiral bosonized exponential.";
oddBosAntiChFieldQ[x_] := MatchQ[Head[x], exp\[Phi]tf];

bosExpRules::usage = "Combines bosonized exponentials during U canonicalization.";
bosExpRules = {
  tmpR[cc___, aa_, aa_, dd___] /; Head[aa] == exp\[Phi]f :>
    tmpR[cc, exp\[Phi]b[2 aa[[1]], aa[[2]]], dd],
  tmpR[cc___, aa_, aa_, dd___] /; Head[aa] == exp\[Phi]tf :>
    tmpR[cc, exp\[Phi]tb[2 aa[[1]], aa[[2]]], dd],
  tmpR[cc___, aa_, bb_, dd___] /; Head[aa] == exp\[Phi]b && Head[bb] == exp\[Phi]b && aa[[2]] == bb[[2]] :>
    tmpR[cc, exp\[Phi]b[aa[[1]] + bb[[1]], aa[[2]]], dd],
  tmpR[cc___, aa_, bb_, dd___] /; Head[aa] == exp\[Phi]tb && Head[bb] == exp\[Phi]tb && aa[[2]] == bb[[2]] :>
    tmpR[cc, exp\[Phi]tb[aa[[1]] + bb[[1]], aa[[2]]], dd],
  tmpR[cc___, aa_, bb_, dd___] /; Head[aa] == exp\[Phi]f && Head[bb] == exp\[Phi]f && aa[[2]] == bb[[2]] :>
    tmpR[cc, exp\[Phi]b[aa[[1]] + bb[[1]], aa[[2]]], dd],
  tmpR[cc___, aa_, bb_, dd___] /; Head[aa] == exp\[Phi]tf && Head[bb] == exp\[Phi]tf && aa[[2]] == bb[[2]] :>
    tmpR[cc, exp\[Phi]tb[aa[[1]] + bb[[1]], aa[[2]]], dd],
  tmpR[cc___, aa_, bb_, dd___] /; Head[aa] == exp\[Phi]b && Head[bb] == exp\[Phi]f && aa[[2]] == bb[[2]] :>
    tmpR[cc, exp\[Phi]f[aa[[1]] + bb[[1]], aa[[2]]], dd],
  tmpR[cc___, aa_, bb_, dd___] /; Head[aa] == exp\[Phi]tb && Head[bb] == exp\[Phi]tf && aa[[2]] == bb[[2]] :>
    tmpR[cc, exp\[Phi]tf[aa[[1]] + bb[[1]], aa[[2]]], dd],
  tmpR[cc___, aa_, bb_, dd___] /; SymbolName[Head[aa]] == "expH" && Head[bb] === Head[aa] && aa[[2]] == bb[[2]] :>
    With[{head = Head[aa]}, tmpR[cc, head[aa[[1]] + bb[[1]], aa[[2]]], dd]],
  tmpR[cc___, aa_, bb_, dd___] /; SymbolName[Head[aa]] == "expHt" && Head[bb] === Head[aa] && aa[[2]] == bb[[2]] :>
    With[{head = Head[aa]}, tmpR[cc, head[aa[[1]] + bb[[1]], aa[[2]]], dd]]
};


bosonizedExponentialFieldQ::usage = "bosonizedExponentialFieldQ[field] checks whether field is expH or expHt.";
bosonizedExponentialFieldQ[field_] := Length[field] == 2 && ListQ[field[[1]]] && MemberQ[{"expH", "expHt"}, SymbolName[Head[field]]];


bosonizedTermSpec::usage = "bosonizedTermSpec[expr] parses one bosonized single-field term into coefficient, charge, and field-factor data.";
(* Multi-field bosonization works termwise. Each single-field term is reduced to
   scalar data plus at most one charge-carrying exponential so later code can
   take cartesian products of term lists without re-running rewrite logic. *)
bosonizedTermSpec[expr_] := Module[
  {factors, scalarFactors, fieldFactors, expFactors, charge, chirality, coord},
  factors = If[Head[expr] === Times, List @@ expr, {expr}];
  factors = Flatten[If[SymbolName[Head[#]] === "R", List @@ #, {#}] & /@ factors];
  scalarFactors = Select[factors, isScalarFactorQ];
  fieldFactors = Select[factors, Not @* isScalarFactorQ];
  expFactors = Select[fieldFactors, bosonizedExponentialFieldQ];
  (* A single source field should not bosonize into multiple independent expH
     factors; if that ever happens, abort tuple bosonization and leave the
     original Bosonize[R[...]] unevaluated. *)
  If[Length[expFactors] > 1, Return[$Failed]];
  {charge, chirality, coord} = If[
    expFactors === {},
    {charge6Zero, None, None},
    {
      expFactors[[1, 1]],
      If[SymbolName[Head[expFactors[[1]]]] === "expH", "Holo", "AntiHolo"],
      expFactors[[1, 2]]
    }
  ];
  <|
    "coefficient" -> Times @@ scalarFactors,
    "charge" -> charge,
    "chirality" -> chirality,
    "coordinate" -> coord,
    "fields" -> fieldFactors
  |>
];


bosonizedSingleFieldTerms::usage = "bosonizedSingleFieldTerms[field] expands Bosonize[field] into a list of parsed term specifications.";
bosonizedSingleFieldTerms[field_] := Module[{raw, terms, parsed},
  raw = Expand[Bosonize[field]];
  If[Head[raw] === Bosonize, Return[$Failed]];
  terms = If[Head[raw] === Plus, List @@ raw, {raw}];
  parsed = bosonizedTermSpec /@ terms;
  If[MemberQ[parsed, $Failed], $Failed, parsed]
];


mergeBosonizedExponentials::usage = "mergeBosonizedExponentials[fields] merges same-head exponentials inserted at the same coordinate by adding charges.";
(* Preserve the left-to-right order of ordinary factors while collecting each
   same-point expH/expHt slot once. The stored sequence records where each
   merged exponential should be reinserted after charges are summed. *)
mergeBosonizedExponentials[fields_List] := Module[{sequence = {}, sums = <||>, key},
  Scan[
    Function[field,
      If[
        bosonizedExponentialFieldQ[field],
        key = {Head[field], field[[2]]};
        If[
          KeyExistsQ[sums, key],
          sums[key] = sums[key] + field[[1]],
          sums[key] = field[[1]];
          sequence = Append[sequence, key]
        ],
        sequence = Append[sequence, field]
      ]
    ],
    fields
  ];
  DeleteCases[
    sequence /. key : {head_Symbol, coord_} :> head[sums[key], coord],
    1
  ]
];


bosonizedCocycleFactor::usage = "bosonizedCocycleFactor[combo] returns the scalar prefactor used when bosonizing one normal-ordered tuple; the current convention inserts no internal cocycles.";
bosonizedCocycleFactor[combo_List] := 1;


bosonizedTupleExpression::usage = "bosonizedTupleExpression[combo] rebuilds one bosonized tuple of term data as a scalar or normal-ordered product.";
bosonizedTupleExpression[combo_List] := Module[{coeff, fields},
  coeff = bosonizedCocycleFactor[combo] Times @@ Lookup[combo, "coefficient"];
  fields = mergeBosonizedExponentials[Flatten[Lookup[combo, "fields"], 1]];
  Which[
    coeff === 0, 0,
    fields === {}, coeff,
    True, coeff R @@ fields
  ]
];

samePointPureFieldProductQ0::usage =
  "samePointPureFieldProductQ0[ops, head] is True exactly for same-point local products of two or more fields with the requested head.";
samePointPureFieldProductQ0[ops_List, head_Symbol] := Length[ops] > 1 &&
  AllTrue[ops, Head[#] === head &] &&
  SameQ @@ ((List @@ #)[[-1]] & /@ ops);

samePointProjectedPsiClusterSpec0::usage =
  "samePointProjectedPsiClusterSpec0[ops] returns the same-point projected psi-cluster specification for one local R-product, or $Failed when no such collapse applies.";
samePointProjectedPsiClusterSpec0[ops_List] := Module[
  {coords, psiOps, psitOps, orderedPiecesFor},
  If[ops === {}, Return[$Failed]];
  coords = (List @@ #)[[-1]] & /@ ops;
  If[!SameQ @@ coords, Return[$Failed]];
  psiOps = Select[ops, Head[#] === ψ &];
  psitOps = Select[ops, Head[#] === ψt &];
  orderedPiecesFor[head_Symbol] := Module[{inserted = False},
    Reap[
      Scan[
        Function[op,
          If[
            Head[op] === head,
            If[!inserted,
              Sow[Missing["PsiCluster"]];
              inserted = True
            ],
            Sow[op]
          ]
        ],
        ops
      ]
    ][[2, 1]]
  ];
  Which[
    Length[psiOps] > 1 && psitOps === {},
      <|
        "Sector" -> "Holo",
        "ClusterOps" -> psiOps,
        "Coord" -> First[coords],
        "OrderedPieces" -> orderedPiecesFor[ψ]
      |>,
    Length[psitOps] > 1 && psiOps === {},
      <|
        "Sector" -> "Anti",
        "ClusterOps" -> psitOps,
        "Coord" -> First[coords],
        "OrderedPieces" -> orderedPiecesFor[ψt]
      |>,
    True,
      $Failed
  ]
];

bosonizedExpressionTerms0::usage =
  "bosonizedExpressionTerms0[expr] expands one already bosonized expression into parsed single-term specifications compatible with bosonizedTupleExpression.";
bosonizedExpressionTerms0[expr_] := Module[{terms, parsed},
  terms = If[Head[Expand[expr]] === Plus, List @@ Expand[expr], {Expand[expr]}];
  parsed = bosonizedTermSpec /@ terms;
  If[MemberQ[parsed, $Failed], $Failed, parsed]
];

splitBosonizedProbeCoordinates0::usage =
  "splitBosonizedProbeCoordinates0[n] returns the canonical point-splitting coordinates used to collapse an n-field same-point ψ-product through one projected OPE.";
splitBosonizedProbeCoordinates0[n_Integer?Positive] := Join[Range[n - 1], {0}];

rewriteFieldCoordinate0::usage =
  "rewriteFieldCoordinate0[field, coord] rewrites the last coordinate slot of one field to coord.";
rewriteFieldCoordinate0[field_ /; isField[Head[field]], coord_] :=
  ReplacePart[field, Length[List @@ field] -> coord];
rewriteFieldCoordinate0[field_, _] := field;

restoreBosonizedCoordinate0::usage =
  "restoreBosonizedCoordinate0[sector, expr, coord] restores a projected bosonized same-point product from the origin to coord.";
restoreBosonizedCoordinate0["Holo", expr_, coord_] := Expand[expr /. {
  dH[i_, n_, 0] :> dH[i, n, coord],
  field_ /; SymbolName[Head[field]] === "expH" && MatchQ[field, _[_, 0]] :>
    With[{head = Head[field]}, head[field[[1]], coord]]
}];
restoreBosonizedCoordinate0["Anti", expr_, coord_] := Expand[expr /. {
  dHt[i_, n_, 0] :> dHt[i, n, coord],
  field_ /; SymbolName[Head[field]] === "expHt" && MatchQ[field, _[_, 0]] :>
    With[{head = Head[field]}, head[field[[1]], coord]]
}];

bosonizedProjectedSectorWeight0::usage =
  "bosonizedProjectedSectorWeight0[sector, ops] returns the total chiral conformal weight of one pure-ψ same-point product.";
bosonizedProjectedSectorWeight0["Holo", ops_List] := Total[totalWeightHolo /@ (R /@ ops)];
bosonizedProjectedSectorWeight0["Anti", ops_List] := Total[totalWeightAntiHolo /@ (R /@ ops)];

bosonizedProjectedSamePointProduct0::usage =
  "bosonizedProjectedSamePointProduct0[sector, ops, coord] bosonizes a pure same-sector same-point ψ-product by bosonizing each factor once and collapsing the full product through one projected chiral OPE.";
bosonizedProjectedSamePointProduct0[sector : ("Holo" | "Anti"), ops_List, coord_] := Module[
  {probeCoords, projectedFn, bosonizedFactors, projected},
  Needs["StringCode`OPE`"];
  probeCoords = splitBosonizedProbeCoordinates0[Length[ops]];
  projectedFn = If[sector === "Holo", StringCode`OPE`OPEProjectedHolo, StringCode`OPE`OPEProjectedAntiHolo];
  bosonizedFactors = MapThread[
    Function[{op, probeCoord},
      Bosonize[R[rewriteFieldCoordinate0[op, probeCoord]]]
    ],
    {ops, probeCoords}
  ];
  projected = Expand[
    projectedFn[bosonizedProjectedSectorWeight0[sector, ops]][Sequence @@ bosonizedFactors]
  ];
  restoreBosonizedCoordinate0[sector, projected, coord]
];

bosonizeSamePointMultiPsiLocal0::usage =
  "bosonizeSamePointMultiPsiLocal0[Ra] bosonizes a same-point local ψ/ψt cluster, with or without same-point spectators, via one projected bosonized free-field OPE.";
bosonizeSamePointMultiPsiLocal0[Ra_ /; RTest[Ra]] := Module[
  {ops = List @@ Ra, spec, collapsedCluster, termLists, tuples},
  spec = samePointProjectedPsiClusterSpec0[ops];
  If[spec === $Failed, Return[Unevaluated[Bosonize[Ra]]]];
  collapsedCluster = bosonizedProjectedSamePointProduct0[spec["Sector"], spec["ClusterOps"], spec["Coord"]];
  termLists = Replace[
    spec["OrderedPieces"],
    {
      Missing["PsiCluster"] :> bosonizedExpressionTerms0[collapsedCluster],
      op_ :> bosonizedSingleFieldTerms[op]
    },
    {1}
  ];
  If[MemberQ[termLists, $Failed], Return[Unevaluated[Bosonize[Ra]]]];
  tuples = Tuples[termLists];
  Expand[Total[bosonizedTupleExpression /@ tuples]]
];


(* ::Subsection::Closed:: *)
(*Define normal-ordered product*)


R[ c___,a_,a_,d___]:=R[c,exp\[Phi]b[2a[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]f)
R[ c___,a_,a_,d___]:=R[c,exp\[Phi]tb[2a[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]tf)
R[ c___,a_,b_,d___]:=R[c,exp\[Phi]b[a[[1]]+b[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]b && Head[b]==exp\[Phi]b && a[[2]]==b[[2]])
R[ c___,a_,b_,d___]:=R[c,exp\[Phi]tb[a[[1]]+b[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]tb && Head[b]==exp\[Phi]tb && a[[2]]==b[[2]])
R[ c___,a_,b_,d___]:=R[c,exp\[Phi]b[a[[1]]+b[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]f && Head[b]==exp\[Phi]f && a[[2]]==b[[2]])
R[ c___,a_,b_,d___]:=R[c,exp\[Phi]tb[a[[1]]+b[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]tf && Head[b]==exp\[Phi]tf && a[[2]]==b[[2]])
R[ c___,a_,b_,d___]:=R[c,exp\[Phi]f[a[[1]]+b[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]b && Head[b]==exp\[Phi]f && a[[2]]==b[[2]])
R[ c___,a_,b_,d___]:=R[c,exp\[Phi]tf[a[[1]]+b[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]tb && Head[b]==exp\[Phi]tf && a[[2]]==b[[2]])
R[ c___,a_,b_,d___]:=With[{head = Head[a]}, R[c, head[a[[1]]+b[[1]],a[[2]]],d]]/;(SymbolName[Head[a]]=="expH" && Head[b]===Head[a] && a[[2]]==b[[2]])
R[ c___,a_,b_,d___]:=With[{head = Head[a]}, R[c, head[a[[1]]+b[[1]],a[[2]]],d]]/;(SymbolName[Head[a]]=="expHt" && Head[b]===Head[a] && a[[2]]==b[[2]])

(* ::Subsection:: *)
(*Define total picture number*)


totalHolPicture::usage = "Computes total holomorphic picture";
totalAntiHolPicture::usage = "Computes total antiholomorphic picture";

totalHolPicture[Ra_/;RTest[Ra]]:= Map[pictureHol, List @@ Ra]//Total;
totalHolPicture[Times[a_, Ra_/;RTest[Ra]]] := totalHolPicture[Ra];

totalAntiHolPicture[Ra_/;RTest[Ra]]:= Map[pictureAntiHol, List @@ Ra]//Total;
totalAntiHolPicture[Times[a_, Ra_/;RTest[Ra]]] := totalAntiHolPicture[Ra];

GSOParity[Ra_/;RTest[Ra]]:= Times @@ Map[GSOParity, List @@ Ra];
GSOParity[Times[a_, Ra_/;RTest[Ra]]] := GSOParity[Ra];

Bosonize[Ra_ /; RTest[Ra]] := Module[{ops = List @@ Ra, termLists, tuples},
  If[samePointProjectedPsiClusterSpec0[ops] =!= $Failed,
    Return[bosonizeSamePointMultiPsiLocal0[Ra]]
  ];
  (* Bosonize each input field independently, form all term combinations, then
     rebuild one normal-ordered tuple per combination so coincident bosonized
     exponentials merge only after every source field has contributed. *)
  termLists = bosonizedSingleFieldTerms /@ (List @@ Ra);
  If[MemberQ[termLists, $Failed], Return[Unevaluated[Bosonize[Ra]]]];
  tuples = Tuples[termLists];
  Expand[Total[bosonizedTupleExpression /@ tuples]]
];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
