(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`NormalOrdering`"];


Needs["StringCode`Symbols`"];


(* ::Section:: *)
(*Declare public variables and methods*)


R::usage = "A sorted normal-ordered product of fields";


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


containsFieldQ::usage = "Checks if expression contains any registered field.";
containsFieldQ[expr_] := !FreeQ[expr, field_ /; isField[Head[field]]];

containsFermionQ::usage = "Checks if expression contains any registered fermion field.";
containsFermionQ[expr_] := !FreeQ[expr, field_ /; isFermion[Head[field]]];

containsRegularFermionQ::usage = "Checks if expression contains any registered regular fermion field.";
containsRegularFermionQ[expr_] := !FreeQ[expr, field_ /; isRegFermion[Head[field]]];

isScalarFactorQ::usage = "Checks if expression is scalar factor with respect to registered fields.";
isScalarFactorQ[expr_] := !containsFieldQ[expr];

needsOrdering::usage = "Private flag controlling whether R auto-orders. Default True.";
needsOrdering = True;

oddFieldQ::usage = "Checks if expression has regular-fermion content.";
oddFieldQ[x_] := containsRegularFermionQ[x];

oddBosChirFieldQ::usage = "Checks if field is odd-parity bosonized chiral.";
oddBosChirFieldQ[_] := False;

oddBosAntiChFieldQ::usage = "Checks if field is odd-parity bosonized antichiral.";
oddBosAntiChFieldQ[_] := False;

bosExpRules::usage = "Rules for combining bosonized exponentials. Empty for bosonic theories.";
bosExpRules = {};

SepGradedFields::usage = "Separates graded fields and counts moves for canonical sign.";
SepGradedFields[list_] := Module[{nChir = 0, nAntiChir = 0, moves = 0, oddfields = {}},
  Do[
    Which[
      oddFieldQ[tmp], moves += nChir + nAntiChir; AppendTo[oddfields, tmp],
      oddBosChirFieldQ[tmp], moves += nAntiChir; nChir++,
      oddBosAntiChFieldQ[tmp], nAntiChir++,
      True, Null
    ],
    {tmp, list}
  ];
  <|"moves" -> moves, "nChir" -> nChir, "nAntiChir" -> nAntiChir, "oddfields" -> oddfields|>
];


(* ::Subsection:: *)
(*Test normal-ordering and length*)


RTest::usage = "Test if product is normal-ordered";
RTest[f_]:=(Head[f]===R)

RLength::usage = "Test if is normal-ordered and has nonzero length";
RLength[f_]:=If[RTest[f],Length[List @@ f],0]

ROne::usage = "Test if is normal-ordered of length one";
ROne[f_]:=(RLength[f]==1)


RTestUpToConstant::usage = "Test if product is normal-ordered up to a constant prefactor";

RTestUpToConstant[c___,a_ f_,d___]:=RTestUpToConstant[c,f,d]/;isScalarFactorQ[a]
RTestUpToConstant[c___,a_ ,d___]:= RTestUpToConstant[c,d]/;isScalarFactorQ[a]
RTestUpToConstant[f_]:=(Head[f]===R)
RTestUpToConstant[]:=False;

(* ::Subsection::Closed:: *)
(*Define Grassmann parity*)


parity::usage = "Define Grassmann parity for fields including composites";

parity[f_]:=0/;!containsFermionQ[f]
parity[f_+g_]:=parity[f]
parity[f_ g_]:=parity[g]/;!containsFermionQ[f]
parity[R[f__,g__]]:=Mod[parity[R[f]]+parity[R[g]],2]
parity[R[f_]]:=1/;containsFermionQ[f]
parity[U[f__,g__]]:=Mod[parity[U[f]]+parity[U[g]],2]
parity[U[f_]]:=1/;containsFermionQ[f]
parity[f_]:=1/;containsFermionQ[f]


regparity::usage = "Define Grassmann parity for fundamental fields";

regparity[f_+g_]:=regparity[f]
regparity[f_ g_]:=regparity[g]/;!containsRegularFermionQ[f]
regparity[f_]:=0/;!containsRegularFermionQ[f]
regparity[f_]:=1/;containsRegularFermionQ[f]


(* ::Subsection:: *)
(*Define normal-ordered product*)


R[c___,b_,a_,d___] := Block[
  {needsOrdering = False},
  regcomm[a,b] Canonicalize[R[c,a,b,d]]
] /; (needsOrdering && !OrderedQ[{b,a}])
R[ c___,a_,a_,d___]:=0/;(regparity[a]==1)


R[c___, a_, d___] := (R[c, #, d] & /@ a) /; Head[a] == Plus
R[c___,a_ f_,d___]:=a R[c,f,d]/;isScalarFactorQ[a]
R[c___,a_ ,d___]:=a R[c,d]/;isScalarFactorQ[a]
R[]:=1
R[a___, r_?RTest, c___] := R[a, Sequence @@ (List @@ r), c]


R[g___,a_ f_,h___]:=R[g,a,f,h]/;isBoson[Head[a]]
R[g___,a_^n_ f_,h___]:=R[g,(R @@ ConstantArray[a,n]),f,h]/;isBoson[Head[a]]
R[g___,a_^n_,h___]:=R[g,(R @@ ConstantArray[a,n]),h]/;isBoson[Head[a]]

Canonicalize::usage = "Canonicalizes an unsorted U or R product and returns a sorted product with the same head.";
Canonicalize[prod_] := Module[
  {head = Head[prod], fieldList = List @@ prod, gradedFieldList, gradedFieldAssoc, sgn, sortedFields, combinedFields},
  gradedFieldList = Select[fieldList, !isBoson[Head[#]] &];
  gradedFieldAssoc = SepGradedFields[gradedFieldList];

  If[OddQ[gradedFieldAssoc[["nChir"]]], AppendTo[gradedFieldAssoc[["oddfields"]], exp\[Phi]f[]]];
  If[OddQ[gradedFieldAssoc[["nAntiChir"]]], AppendTo[gradedFieldAssoc[["oddfields"]], exp\[Phi]tf[]]];

  sgn = (-1)^(gradedFieldAssoc[["moves"]]) Signature[gradedFieldAssoc[["oddfields"]]];
  If[sgn == 0, Return[0]];

  sortedFields = Sort[fieldList];
  If[gradedFieldAssoc[["nChir"]] == 0 && gradedFieldAssoc[["nAntiChir"]] == 0,
    Return[
      sgn If[
        head === R,
        Block[{needsOrdering = False}, R @@ sortedFields],
        U @@ sortedFields
      ]
    ]
  ];

  combinedFields = Sort[((tmpR @@ sortedFields) //. bosExpRules /. tmpR -> List)];
  sgn If[
    head === R,
    Block[{needsOrdering = False}, R @@ combinedFields],
    U @@ combinedFields
  ]
] /; (UTest[prod] || RTest[prod]);

Canonicalize[a_ + b_] := Canonicalize[a] + Canonicalize[b];
Canonicalize[c_ a_] := c Canonicalize[a] /; isScalarFactorQ[c];
Canonicalize[0] := 0;
Canonicalize[a_] := a /; isScalarFactorQ[a];

(* ::Subsection::Closed:: *)
(*Define total ghost number*)


totalHolGhostNumber::usage = "Computes total holomorphic ghost number";
totalAntiHolGhostNumber::usage = "Computes total antiholomorphic ghost number";

totalHolGhostNumber[Ra_/;RTest[Ra]]:= Map[ghostNumberHolo, List @@ Ra]//Total;
totalHolGhostNumber[Times[a_, Ra_/;RTest[Ra]]] := totalHolGhostNumber[Ra];

totalAntiHolGhostNumber[Ra_/;RTest[Ra]]:= Map[ghostNumberAntiHolo, List @@ Ra]//Total;
totalAntiHolGhostNumber[Times[a_, Ra_/;RTest[Ra]]] := totalAntiHolGhostNumber[Ra];


(* ::Subsection::Closed:: *)
(*Define cached dropping of normal-ordered product elements*)


dropFirstFromR::usage = "Drops first element from normal-ordered product";
dropFirstFromR[Ra_]:= dropFirstFromR[Ra] = R @@ (Drop[(List @@ Ra),1])


(* ::Subsection::Closed:: *)
(*Define weight of normal-ordered product*)


totalWeightHolo::usage = "Computes total holomorphic weight of a normal-ordered product";
totalWeightAntiHolo::usage = "Computes total holomorphic weight of a normal-ordered product";
totalWeight::usage = "Computes total weight of a normal-ordered product";

totalWeightHolo[Times[a_, Ra_/;RTest[Ra]]] := totalWeightHolo[Ra];
totalWeightHolo[Ra_/;RTest[Ra]] := Map[weightHolo, List @@ Ra] // Total;

totalWeightAntiHolo[Times[a_, Ra_/;RTest[Ra]]] := totalWeightAntiHolo[Ra];
totalWeightAntiHolo[Ra_/;RTest[Ra]] := Map[weightAntiHolo, List @@ Ra] // Total;

totalWeight[Times[a_, Ra_/;RTest[Ra]]] := totalWeight[Ra];
totalWeight[Ra_/;RTest[Ra]] := {totalWeightHolo[Ra], totalWeightAntiHolo[Ra]};



(* ::Section:: *)
(*End*)


End[];


EndPackage[];
