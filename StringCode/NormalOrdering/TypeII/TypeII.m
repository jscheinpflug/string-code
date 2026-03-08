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
    tmpR[cc, exp\[Phi]tf[aa[[1]] + bb[[1]], aa[[2]]], dd]
};


bosonizedExponentialFieldQ::usage = "bosonizedExponentialFieldQ[field] checks whether field is expH or expHt.";
bosonizedExponentialFieldQ[field_] := MatchQ[field, expH[_List, _] | expHt[_List, _]];


bosonizedTermSpec::usage = "bosonizedTermSpec[expr] parses one bosonized single-field term into coefficient, charge, and field-factor data.";
bosonizedTermSpec[expr_] := Module[
  {factors, scalarFactors, fieldFactors, expFactors, charge, chirality, coord},
  factors = If[Head[expr] === Times, List @@ expr, {expr}];
  scalarFactors = Select[factors, isScalarFactorQ];
  fieldFactors = Select[factors, Not @* isScalarFactorQ];
  expFactors = Select[fieldFactors, bosonizedExponentialFieldQ];
  If[Length[expFactors] > 1, Return[$Failed]];
  {charge, chirality, coord} = If[
    expFactors === {},
    {charge6Zero, None, None},
    {
      expFactors[[1, 1]],
      If[Head[expFactors[[1]]] === expH, "Holo", "AntiHolo"],
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
R[ c___,a_,b_,d___]:=R[c,expH[a[[1]]+b[[1]],a[[2]]],d]/;(Head[a]==expH && Head[b]==expH && a[[2]]==b[[2]])
R[ c___,a_,b_,d___]:=R[c,expHt[a[[1]]+b[[1]],a[[2]]],d]/;(Head[a]==expHt && Head[b]==expHt && a[[2]]==b[[2]])

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


Bosonize[Ra_ /; RTest[Ra]] := Module[{termLists, tuples},
  termLists = bosonizedSingleFieldTerms /@ (List @@ Ra);
  If[MemberQ[termLists, $Failed], Return[Unevaluated[Bosonize[Ra]]]];
  tuples = Tuples[termLists];
  Expand[Total[bosonizedTupleExpression /@ tuples]]
];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
