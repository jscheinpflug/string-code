(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Symbols`TypeII`FlatSpace`"]
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"]
Needs["StringCode`Conventions`TypeII`"]


(* ::Section:: *)
(*Declare public variables and methods*)


expXAntiHolo::usage = "Antiholomorphic part of the wave primary in free boson CFT";


expXHolo::usage = "Holomorphic part of the wave primary in free boson CFT";


expX::usage = "Plane wave primary in free boson CFT";


dX::usage = "Holomorphic del X primary in free boson CFT";


dXt::usage = "Antiholomorphic del X primary in free boson CFT";


dH::usage = "Holomorphic derivative of a bosonized H-field in the six-charge basis.";


dHt::usage = "Antiholomorphic derivative of a bosonized H-field in the six-charge basis.";


expH::usage = "Holomorphic bosonized exponential carrying a six-component charge vector.";


expHt::usage = "Antiholomorphic bosonized exponential carrying a six-component charge vector.";


ProfileXAntiHolo::usage = "Antiolomorphic part of an X-profile"


ProfileXHolo::usage = "Holomorphic part of an X-profile"


ProfileX::usage = "An X-profile";


\[Psi]::usage = "Holomorphic free matter fermion";


\[Psi]t::usage = "Antiholomorphic free matter fermion";

S::usage = "Holomorphic spin field";

St::usage = "Antiholomorphic spin field";


\[Alpha]p::usage = "Symbol for alpha prime";

dot::usage = "Symbol for dot product";

der::usage = "Symbol for a derivative";

\[Delta]::usage = "Inert Kronecker delta tensor for flat-space vector-index contractions.";

CGamma::usage =
  "CGamma[mu] returns the exact 16x16 chiral-chiral charge-conjugated gamma matrix with both spinor indices up in the canonical TypeII flat-space basis.";

CGammaSparse::usage =
  "CGammaSparse[mu] returns the exact 16x16 sparse chiral-chiral charge-conjugated gamma matrix with both spinor indices up in the canonical TypeII flat-space basis.";

CIGamma::usage =
  "CIGamma[mu] returns the exact 16x16 antichiral-antichiral charge-conjugated gamma matrix with both spinor indices up in the canonical TypeII flat-space basis.";

CIGammaSparse::usage =
  "CIGammaSparse[mu] returns the exact 16x16 sparse antichiral-antichiral charge-conjugated gamma matrix with both spinor indices up in the canonical TypeII flat-space basis.";

GammaUD::usage =
  "GammaUD[mu] returns the exact 16x16 mixed-chirality gamma matrix mapping chiral to antichiral spinors in the canonical TypeII flat-space basis.";

GammaUDSparse::usage =
  "GammaUDSparse[mu] returns the exact 16x16 sparse mixed-chirality gamma matrix mapping chiral to antichiral spinors in the canonical TypeII flat-space basis.";

GammaDU::usage =
  "GammaDU[mu] returns the exact 16x16 mixed-chirality gamma matrix mapping antichiral to chiral spinors in the canonical TypeII flat-space basis.";

GammaDUSparse::usage =
  "GammaDUSparse[mu] returns the exact 16x16 sparse mixed-chirality gamma matrix mapping antichiral to chiral spinors in the canonical TypeII flat-space basis.";

CUD::usage =
  "CUD is the exact 16x16 chiral-antichiral spinor pairing matrix in the canonical TypeII flat-space basis.";

CUDSparse::usage =
  "CUDSparse is the exact 16x16 sparse chiral-antichiral spinor pairing matrix in the canonical TypeII flat-space basis.";

CDU::usage =
  "CDU is the exact 16x16 antichiral-chiral spinor pairing matrix in the canonical TypeII flat-space basis.";

CDUSparse::usage =
  "CDUSparse is the exact 16x16 sparse antichiral-chiral spinor pairing matrix in the canonical TypeII flat-space basis.";

Gamma11UU::usage =
  "Gamma11UU is the exact 16x16 chiral Weyl-block of the SO(10) chirality operator in the canonical TypeII flat-space basis.";

Gamma11UUSparse::usage =
  "Gamma11UUSparse is the exact 16x16 sparse chiral Weyl-block of the SO(10) chirality operator in the canonical TypeII flat-space basis.";

Gamma11DD::usage =
  "Gamma11DD is the exact 16x16 antichiral Weyl-block of the SO(10) chirality operator in the canonical TypeII flat-space basis.";

Gamma11DDSparse::usage =
  "Gamma11DDSparse is the exact 16x16 sparse antichiral Weyl-block of the SO(10) chirality operator in the canonical TypeII flat-space basis.";

GammaAntisymmetricProduct::usage =
  "GammaAntisymmetricProduct[{link1,...}] returns the exact 16x16 matrix represented by one concrete antisymmetrized gamma-link list, and GammaAntisymmetricProduct[{link1,...}, alpha, beta] returns one exact matrix element.";

GammaAntisymmetricProductHold::usage =
  "GammaAntisymmetricProductHold[{link1,...}, alpha, beta] denotes an inert antisymmetrized gamma tensor structure between spinor endpoints; when needed, CUDHold/CDUHold appears as the first list element.";

GammaProductHold::usage =
  "GammaProductHold[{link1,...}, alpha, beta] is a deprecated alias for GammaAntisymmetricProductHold[{link1,...}, alpha, beta].";

GammaUDHold::usage =
  "GammaUDHold[mu] denotes an inert single-link gamma block carrying chiral-to-antichiral spinor index flow.";

GammaDUHold::usage =
  "GammaDUHold[mu] denotes an inert single-link gamma block carrying antichiral-to-chiral spinor index flow.";

Gamma11UUHold::usage =
  "Gamma11UUHold[] denotes an inert chirality-preserving Gamma11 insertion with chiral end-index type.";

Gamma11DDHold::usage =
  "Gamma11DDHold[] denotes an inert chirality-preserving Gamma11 insertion with antichiral end-index type.";

CUDHold::usage =
  "CUDHold denotes an inert charge-conjugation insertion used as the first element in GammaAntisymmetricProductHold link lists for incoming chiral-chiral chains.";

CDUHold::usage =
  "CDUHold denotes an inert charge-conjugation insertion used as the first element in GammaAntisymmetricProductHold link lists for incoming antichiral-antichiral chains.";

CGammaHold::usage = "CGammaHold[{mu1,...}, alpha, beta] denotes an inert Clifford tensor with two chiral spinor indices.";

CIGammaHold::usage = "CIGammaHold[{mu1,...}, alpha, beta] denotes an inert Clifford tensor with two antichiral spinor indices.";

GammaMHold::usage = "GammaMHold[{mu1,...}, alpha, beta] denotes an inert Clifford tensor with one chiral and one antichiral spinor index.";

Gamma11CGammaHold::usage =
  "Gamma11CGammaHold[{mu1,...}, alpha, beta] denotes an inert Gamma11 times chiral-chiral Clifford tensor.";

Gamma11CIGammaHold::usage =
  "Gamma11CIGammaHold[{mu1,...}, alpha, beta] denotes an inert Gamma11 times antichiral-antichiral Clifford tensor.";

Gamma11GammaMHold::usage =
  "Gamma11GammaMHold[{mu1,...}, alpha, beta] denotes an inert Gamma11 times mixed-chirality Clifford tensor.";


Bosonize::usage = "Bosonize[expr] rewrites supported TypeII flat-space fermion and spin fields into the bosonized H-boson basis.";


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


flatSpaceContractRules::usage = "flatSpaceContractRules[dim] returns TypeII FlatSpace contraction rules for \\[Delta] tensors.";
flatSpaceContractRules[dim_] := {\[Delta][\[Mu]_, \[Mu]_] :> dim, \[Delta][\[Mu]_, \[Nu]_]^2 :> dim};

Contract[f_, dim_] := f /. flatSpaceContractRules[dim];
Contract[f_] := Contract[f, 10];

ContractDelta[f_] := f //. {
  g_ \[Delta][\[Mu]_, \[Mu]1_] :> (g /. {\[Mu] -> \[Mu]1}) /; !FreeQ[g, \[Mu]],
  g_ \[Delta][\[Mu]1_, \[Mu]_] :> (g /. {\[Mu] -> \[Mu]1}) /; !FreeQ[g, \[Mu]]
};

GammaProductHold[args___] := GammaAntisymmetricProductHold[args];


(* ::Subsection:: *)
(*Define symbols*)


charge6Zero::usage = "charge6Zero is the zero six-charge vector used by bosonized H-fields.";
charge6Zero = ConstantArray[0, 6];


charge6Q::usage = "charge6Q[charges] checks that charges is a length-6 numeric bosonization charge vector.";
charge6Q[charges_] := VectorQ[charges, NumericQ] && Length[charges] == 6;


spinVectorQ::usage = "spinVectorQ[spinVec] checks that spinVec is a length-5 numeric spin assignment.";
spinVectorQ[spinVec_] := VectorQ[spinVec, NumericQ] && Length[spinVec] == 5;


chiralspins::usage = "chiralspins is the notebook-derived ordered list of 16 chiral SO(10) spin weights.";
chiralspins = Join[
  {{1/2, 1/2, 1/2, 1/2, 1/2}},
  Permutations[{1/2, 1/2, 1/2, -1/2, -1/2}],
  Permutations[{1/2, -1/2, -1/2, -1/2, -1/2}]
];


antichiralspins::usage = "antichiralspins is the ordered list of 16 antichiral SO(10) spin weights.";
antichiralspins = -chiralspins;


spinVectorChiralityQ::usage = "spinVectorChiralityQ[spinVec, chirality] checks that an explicit spin vector matches the requested chirality.";
spinVectorChiralityQ[spinVec_, "chiral"] := MemberQ[chiralspins, spinVec];
spinVectorChiralityQ[spinVec_, "antichiral"] := MemberQ[antichiralspins, spinVec];
spinVectorChiralityQ[_, _] := False;


vectors::usage = "vectors is the ordered list of 10 vector-basis matter charges used in bosonized psi-components.";
vectors = Join[
  Permutations[{1, 0, 0, 0, 0}],
  Permutations[{-1, 0, 0, 0, 0}]
];


basisChangeM::usage = "basisChangeM is the notebook-derived 10x10 change-of-basis matrix from vector-charge basis to spacetime mu-basis.";
basisChangeM = Table[
  Which[
    1 <= i <= 5 && j == i, 1/Sqrt[2],
    1 <= i <= 5 && j == i + 5, 1/Sqrt[2],
    6 <= i <= 10 && j == i - 5, I/Sqrt[2],
    6 <= i <= 10 && j == i, -I/Sqrt[2],
    True, 0
  ],
  {i, 1, 10},
  {j, 1, 10}
];


hMetric::usage = "hMetric is the bosonized six-boson metric with phi signature -1 and matter signature +1.";
hMetric = DiagonalMatrix[{-1, 1, 1, 1, 1, 1}];


chargeDot::usage = "chargeDot[q, p] computes the hMetric bilinear form on two six-charge vectors.";
chargeDot[q_List, p_List] := Sum[hMetric[[i, i]] q[[i]] p[[i]], {i, 1, 6}] /; (charge6Q[q] && charge6Q[p]);


x::usage = "x[i, j] is the notebook-derived antisymmetric cocycle matrix entry.";
x[i_, i_] := 0;
x[i_, j_] := -x[j, i] /; i < j;
x[i_, j_] := (-1)^(i j)/2 /; i > j && j =!= 1;
x[i_, 1] := 1/2 /; i > 1;


cocycle::usage = "cocycle[a, b] gives the bosonization cocycle phase for two six-charge vectors.";
cocycle[a_List, b_List] := Exp[I Pi Sum[x[i, j] a[[i]] b[[j]], {i, 1, 6}, {j, 1, 6}]] /; (charge6Q[a] && charge6Q[b]);


derivativeOfBosonizedExponential::usage = "derivativeOfBosonizedExponential[n] caches the nth derivative of Exp[func[x]].";
(* Use a dummy scalar exponential to let Mathematica generate the nth-derivative
   combinatorics once; later rules rewrite each Derivative[func] back into the
   appropriate linear combination of dH or dHt fields. *)
derivativeOfBosonizedExponential[n_Integer?NonNegative] :=
  derivativeOfBosonizedExponential[n] = D[E^(func[x]), {x, n}];


bosonizedExponentDerivative::usage = "bosonizedExponentDerivative[charges, derivativeHead, order, coord] gives the linear combination of dH-derivatives appearing in the exponent derivative.";
bosonizedExponentDerivative[charges_List, derivativeHead_Symbol, order_Integer?Positive, coord_] :=
  Sum[charges[[i]] derivativeHead[i, order - 1, coord], {i, 1, Length[charges]}] /; charge6Q[charges];


bosonizedExponentialDerivative::usage = "bosonizedExponentialDerivative[charges, n, coord, derivativeHead, exponentialHead] differentiates a bosonized exponential and rewrites the result in dH/expH fields.";
bosonizedExponentialDerivative[
  charges_List,
  n_Integer?NonNegative,
  coord_,
  derivativeHead_Symbol,
  exponentialHead_Symbol
] := Expand[
  (* After the cached scalar derivative is generated, replace func^(m) by the
     charge-weighted H-derivative sum and replace the base exponential by the
     concrete expH/expHt carrying the requested six-charge vector. *)
  derivativeOfBosonizedExponential[n] /. {
    E^(func[x]) :> exponentialHead[charges, coord],
    Power[Derivative[m_][func][x], p_] :> bosonizedExponentDerivative[charges, derivativeHead, m, coord]^p,
    Derivative[m_][func][x] :> bosonizedExponentDerivative[charges, derivativeHead, m, coord]
  }
] /; charge6Q[charges];


bosonizedProductDerivative::usage = "bosonizedProductDerivative[expr, derivativeHead, exponentialHead] takes one same-sector derivative of a bosonized same-point product written with ordinary Times.";
bosonizedProductDerivative[0, derivativeHead_Symbol, exponentialHead_Symbol] := 0;
bosonizedProductDerivative[a_ + b_, derivativeHead_Symbol, exponentialHead_Symbol] :=
  bosonizedProductDerivative[a, derivativeHead, exponentialHead] +
    bosonizedProductDerivative[b, derivativeHead, exponentialHead];
bosonizedProductDerivative[c_ a_, derivativeHead_Symbol, exponentialHead_Symbol] :=
  c bosonizedProductDerivative[a, derivativeHead, exponentialHead] /; isScalarFactorQ[c];
bosonizedProductDerivative[a_ /; isScalarFactorQ[a], derivativeHead_Symbol, exponentialHead_Symbol] := 0;
bosonizedProductDerivative[expr_Times, derivativeHead_Symbol, exponentialHead_Symbol] := Module[{factors = List @@ expr},
  Total@Table[
    bosonizedProductDerivative[factors[[i]], derivativeHead, exponentialHead] Times @@ Drop[factors, {i}],
    {i, 1, Length[factors]}
  ]
];
bosonizedProductDerivative[field_, derivativeHead_Symbol, exponentialHead_Symbol] :=
  derivativeHead[field[[1]], field[[2]] + 1, field[[3]]] /;
    Head[field] === derivativeHead && Length[field] == 3;
bosonizedProductDerivative[field_, derivativeHead_Symbol, exponentialHead_Symbol] :=
  bosonizedExponentialDerivative[field[[1]], 1, field[[2]], derivativeHead, exponentialHead] /;
    Head[field] === exponentialHead && Length[field] == 2 && charge6Q[field[[1]]];
bosonizedProductDerivative[field_, derivativeHead_Symbol, exponentialHead_Symbol] := 0;


restoreBosonizedProducts::usage = "restoreBosonizedProducts[expr] rewrites products of same-point bosonized fields back into R wrappers term by term.";
restoreBosonizedProducts[0] := 0;
restoreBosonizedProducts[a_ + b_] := restoreBosonizedProducts[a] + restoreBosonizedProducts[b];
restoreBosonizedProducts[c_ a_] := c restoreBosonizedProducts[a] /; isScalarFactorQ[c];
restoreBosonizedProducts[a_ /; isScalarFactorQ[a]] := a;
restoreBosonizedProducts[expr_Times] := Module[{factors, scalarFactors, fieldFactors},
  factors = List @@ expr;
  scalarFactors = Select[factors, isScalarFactorQ];
  fieldFactors = Select[factors, Not @* isScalarFactorQ];
  Times @@ scalarFactors Switch[Length[fieldFactors], 0, 1, 1, First[fieldFactors], _, R @@ fieldFactors]
];
restoreBosonizedProducts[field_] := field;


bosonizedStateDerivative::usage = "bosonizedStateDerivative[expr, order, derivativeHead, exponentialHead] takes repeated same-sector derivatives of a bosonized spin-state expression.";
bosonizedStateDerivative[expr_, 0, derivativeHead_Symbol, exponentialHead_Symbol] := expr;
bosonizedStateDerivative[expr_, order_Integer?Positive, derivativeHead_Symbol, exponentialHead_Symbol] :=
  restoreBosonizedProducts @ Nest[
    Expand @ bosonizedProductDerivative[#, derivativeHead, exponentialHead] &,
    expr /. ra_ /; RTest[ra] :> Times @@ (List @@ ra),
    order
  ];


bosonizedSpinDerivative::usage = "bosonizedSpinDerivative[field, order, derivativeHead, exponentialHead] bosonizes field with derivative label stripped and then acts order same-sector derivatives on the bosonized result.";
bosonizedSpinDerivative[field_, order_Integer?Positive, derivativeHead_Symbol, exponentialHead_Symbol] := Module[{base},
  base = Bosonize[field];
  If[!FreeQ[base, _Bosonize | _S | _St], Return[$Failed]];
  bosonizedStateDerivative[base, order, derivativeHead, exponentialHead]
];


bosonizedPsiBasisComponent::usage = "bosonizedPsiBasisComponent[a, n, coord, derivativeHead, exponentialHead] returns the nth derivative bosonization of the ath vector-basis fermion component.";
bosonizedPsiBasisComponent[a_Integer, n_Integer?NonNegative, coord_, derivativeHead_Symbol, exponentialHead_Symbol] :=
  bosonizedExponentialDerivative[Join[{0}, vectors[[a]]], n, coord, derivativeHead, exponentialHead] /; 1 <= a <= Length[vectors];


expH[charge6Zero, z_] := 1;
expHt[charge6Zero, zbar_] := 1;


DefineField[dH,
  "Statistics" -> "Boson",
  "Simple" -> True,
  "Composite" -> False,
  "Holomorphic" -> True,
  "AntiHolomorphic" -> False,
  "Indexed" -> True,
  "Collapsable" -> True,
  "Factorizable" -> False,
  "RegularFermion" -> False,
  "PairsWith" -> {dH, expH},
  "WeightHolo" -> Function[field, 1 + field[[2]]],
  "WeightAntiHolo" -> 0,
  "GSOParityHolo" -> 1,
  "GSOParityAntiHolo" -> 1
];


DefineField[dHt,
  "Statistics" -> "Boson",
  "Simple" -> True,
  "Composite" -> False,
  "Holomorphic" -> False,
  "AntiHolomorphic" -> True,
  "Indexed" -> True,
  "Collapsable" -> True,
  "Factorizable" -> False,
  "RegularFermion" -> False,
  "PairsWith" -> {dHt, expHt},
  "WeightHolo" -> 0,
  "WeightAntiHolo" -> Function[field, 1 + field[[2]]],
  "GSOParityHolo" -> 1,
  "GSOParityAntiHolo" -> 1
];


DefineField[expH,
  "Statistics" -> "Boson",
  "Simple" -> False,
  "Composite" -> True,
  "Holomorphic" -> True,
  "AntiHolomorphic" -> False,
  "Indexed" -> False,
  "Collapsable" -> True,
  "Factorizable" -> False,
  "RegularFermion" -> False,
  "PairsWith" -> {expH, dH},
  "WeightHolo" -> Function[field, -field[[1, 1]] (field[[1, 1]] + 2)/2 + Total[field[[1, 2 ;;]]^2]/2],
  "WeightAntiHolo" -> 0,
  "GSOParityHolo" -> 1,
  "GSOParityAntiHolo" -> 1
];


DefineField[expHt,
  "Statistics" -> "Boson",
  "Simple" -> False,
  "Composite" -> True,
  "Holomorphic" -> False,
  "AntiHolomorphic" -> True,
  "Indexed" -> False,
  "Collapsable" -> True,
  "Factorizable" -> False,
  "RegularFermion" -> False,
  "PairsWith" -> {expHt, dHt},
  "WeightHolo" -> 0,
  "WeightAntiHolo" -> Function[field, -field[[1, 1]] (field[[1, 1]] + 2)/2 + Total[field[[1, 2 ;;]]^2]/2],
  "GSOParityHolo" -> 1,
  "GSOParityAntiHolo" -> 1
];


DefineField[dX,
  "Statistics" -> "Boson",
  "Simple" -> True,
  "Composite" -> False,
  "Holomorphic" -> True,
  "AntiHolomorphic" -> False,
  "Indexed" -> True,
  "Collapsable" -> True,
  "Factorizable" -> False,
  "RegularFermion" -> False,
  "PairsWith" -> {dX, expX, ProfileX, expXHolo, ProfileXHolo},
  "WeightHolo" -> Function[field, 1 + field[[2]]],
  "WeightAntiHolo" -> 0,
  "GSOParityHolo" -> 1,
  "GSOParityAntiHolo" -> 1
];

DefineField[dXt,
  "Statistics" -> "Boson",
  "Simple" -> True,
  "Composite" -> False,
  "Holomorphic" -> False,
  "AntiHolomorphic" -> True,
  "Indexed" -> True,
  "Collapsable" -> True,
  "Factorizable" -> False,
  "RegularFermion" -> False,
  "PairsWith" -> {dXt, expX, ProfileX, expXAntiHolo, ProfileXAntiHolo},
  "WeightHolo" -> 0,
  "WeightAntiHolo" -> Function[field, 1 + field[[2]]],
  "GSOParityHolo" -> 1,
  "GSOParityAntiHolo" -> 1
];

DefineField[expX,
  "Statistics" -> "Boson",
  "Simple" -> False,
  "Composite" -> True,
  "Holomorphic" -> True,
  "AntiHolomorphic" -> True,
  "Indexed" -> False,
  "Collapsable" -> True,
  "Factorizable" -> True,
  "RegularFermion" -> False,
  "PairsWith" -> {expX, ProfileX, dX, dXt},
  "FactorizationRule" -> (expX[k_, z_, zbar_] :> {expXHolo[k, z], expXAntiHolo[k, zbar]}),
  "WeightHolo" -> 0,
  "WeightAntiHolo" -> 0,
  "GSOParityHolo" -> 1,
  "GSOParityAntiHolo" -> 1
];

DefineField[expXHolo,
  "Statistics" -> "Boson",
  "Simple" -> False,
  "Composite" -> True,
  "Holomorphic" -> True,
  "AntiHolomorphic" -> False,
  "Indexed" -> False,
  "Collapsable" -> True,
  "Factorizable" -> False,
  "RegularFermion" -> False,
  "PairsWith" -> {expXHolo, ProfileXHolo, dX},
  "WeightHolo" -> 0,
  "WeightAntiHolo" -> 0,
  "GSOParityHolo" -> 1,
  "GSOParityAntiHolo" -> 1
];

DefineField[expXAntiHolo,
  "Statistics" -> "Boson",
  "Simple" -> False,
  "Composite" -> True,
  "Holomorphic" -> False,
  "AntiHolomorphic" -> True,
  "Indexed" -> False,
  "Collapsable" -> True,
  "Factorizable" -> False,
  "RegularFermion" -> False,
  "PairsWith" -> {expXAntiHolo, ProfileXAntiHolo, dXt},
  "WeightHolo" -> 0,
  "WeightAntiHolo" -> 0,
  "GSOParityHolo" -> 1,
  "GSOParityAntiHolo" -> 1
];

DefineField[ProfileX,
  "Statistics" -> "Boson",
  "Simple" -> False,
  "Composite" -> True,
  "Holomorphic" -> True,
  "AntiHolomorphic" -> True,
  "Indexed" -> False,
  "Collapsable" -> True,
  "Factorizable" -> True,
  "RegularFermion" -> False,
  "PairsWith" -> {ProfileX, expX, dX, dXt},
  "FactorizationRule" -> (ProfileX[profile_, ders_, z_, zbar_] :> {ProfileXHolo[profile, ders, z], ProfileXAntiHolo[profile, ders, zbar]}),
  "WeightHolo" -> 0,
  "WeightAntiHolo" -> 0,
  "GSOParityHolo" -> 1,
  "GSOParityAntiHolo" -> 1
];

DefineField[ProfileXHolo,
  "Statistics" -> "Boson",
  "Simple" -> False,
  "Composite" -> True,
  "Holomorphic" -> True,
  "AntiHolomorphic" -> False,
  "Indexed" -> False,
  "Collapsable" -> True,
  "Factorizable" -> False,
  "RegularFermion" -> False,
  "PairsWith" -> {ProfileXHolo, expXHolo, dX},
  "WeightHolo" -> 0,
  "WeightAntiHolo" -> 0,
  "GSOParityHolo" -> 1,
  "GSOParityAntiHolo" -> 1
];

DefineField[ProfileXAntiHolo,
  "Statistics" -> "Boson",
  "Simple" -> False,
  "Composite" -> True,
  "Holomorphic" -> False,
  "AntiHolomorphic" -> True,
  "Indexed" -> False,
  "Collapsable" -> True,
  "Factorizable" -> False,
  "RegularFermion" -> False,
  "PairsWith" -> {ProfileXAntiHolo, expXAntiHolo, dXt},
  "WeightHolo" -> 0,
  "WeightAntiHolo" -> 0,
  "GSOParityHolo" -> 1,
  "GSOParityAntiHolo" -> 1
];

DefineField[\[Psi],
  "Statistics" -> "Fermion",
  "Simple" -> True,
  "Composite" -> False,
  "Holomorphic" -> True,
  "AntiHolomorphic" -> False,
  "Indexed" -> True,
  "Collapsable" -> False,
  "Factorizable" -> False,
  "RegularFermion" -> True,
  "PairsWith" -> {\[Psi]},
  "WeightHolo" -> Function[field, 1/2 + field[[2]]],
  "WeightAntiHolo" -> 0,
  "GSOParityHolo" -> -1,
  "GSOParityAntiHolo" -> 1
];

DefineField[\[Psi]t,
  "Statistics" -> "Fermion",
  "Simple" -> True,
  "Composite" -> False,
  "Holomorphic" -> False,
  "AntiHolomorphic" -> True,
  "Indexed" -> True,
  "Collapsable" -> False,
  "Factorizable" -> False,
  "RegularFermion" -> True,
  "PairsWith" -> {\[Psi]t},
  "WeightHolo" -> 0,
  "WeightAntiHolo" -> Function[field, 1/2 + field[[2]]],
  "GSOParityHolo" -> 1,
  "GSOParityAntiHolo" -> -1
];

DefineField[S,
  "Statistics" -> "Fermion",
  "Simple" -> True,
  "Composite" -> False,
  "Holomorphic" -> True,
  "AntiHolomorphic" -> False,
  "Indexed" -> True,
  "Collapsable" -> False,
  "Factorizable" -> False,
  "RegularFermion" -> True,
  "PairsWith" -> {},
  "WeightHolo" -> Function[
    field,
    5/8 - field[[2]] (field[[2]] + 2)/2 + field[[4]] +
      Total[spinModeWeightContribution /@ field[[3]]]
  ],
  "WeightAntiHolo" -> 0,
  "GSOParityHolo" -> Function[field, spinAlphaChiralitySign[field[[1, 2]]] (-1)^(field[[2]] + 1/2 + Length[field[[3]]])],
  "GSOParityAntiHolo" -> 1
];

DefineField[St,
  "Statistics" -> "Fermion",
  "Simple" -> True,
  "Composite" -> False,
  "Holomorphic" -> False,
  "AntiHolomorphic" -> True,
  "Indexed" -> True,
  "Collapsable" -> False,
  "Factorizable" -> False,
  "RegularFermion" -> True,
  "PairsWith" -> {},
  "WeightHolo" -> 0,
  "WeightAntiHolo" -> Function[
    field,
    5/8 - field[[2]] (field[[2]] + 2)/2 + field[[4]] +
      Total[spinModeWeightContribution /@ field[[3]]]
  ],
  "GSOParityHolo" -> 1,
  "GSOParityAntiHolo" -> Function[field, spinAlphaChiralitySign[field[[1, 2]]] (-1)^(field[[2]] + 1/2 + Length[field[[3]]])]
];

spinModeIndexLikeQ::usage =
  "spinModeIndexLikeQ[idx] is True when idx can serve as a spin-mode vector label.";
spinModeIndexLikeQ[idx_] := !NumericQ[idx] || MatchQ[idx, _Integer?Positive];

spinModeWeightContribution::usage =
  "spinModeWeightContribution[spinMode] returns the conformal-weight contribution carried by one spin-mode tuple.";
spinModeWeightContribution[{idx_ /; spinModeIndexLikeQ[idx], modding_Integer?NonPositive}] := -modding;
spinModeWeightContribution[{modding_Integer?NonPositive, idx_ /; spinModeIndexLikeQ[idx]}] := -modding;
spinModeWeightContribution[{_, mode_?NumericQ}] := mode;
spinModeWeightContribution[{mode_?NumericQ, _}] := mode;

spinModeCanonicalRepresentative::usage =
  "spinModeCanonicalRepresentative[spinMode] canonicalizes negative-integer descendant modding to the index-first form {idx, r}.";
spinModeCanonicalRepresentative[{idx_ /; spinModeIndexLikeQ[idx], modding_Integer?NonPositive}] := {idx, modding};
spinModeCanonicalRepresentative[{modding_Integer?NonPositive, idx_ /; spinModeIndexLikeQ[idx]}] := {idx, modding};
spinModeCanonicalRepresentative[spinMode_] := spinMode;

spinModeOrderingKey::usage =
  "spinModeOrderingKey[spinMode] returns the canonical ordering key used to sort spin-mode lists.";
spinModeOrderingKey[spinMode_] := Module[{canonicalSpinMode = spinModeCanonicalRepresentative[spinMode]},
  Replace[
    canonicalSpinMode,
    {
      {idx_ /; spinModeIndexLikeQ[idx], modding_Integer?NonPositive} :> {idx, -modding},
      _ :> canonicalSpinMode
    }
  ]
];

spinDescendantModeData::usage =
  "spinDescendantModeData[spinMode] returns {idx, r} for one bosonizable descendant spin mode with nonpositive integer modding, or $Failed.";
spinDescendantModeData[{idx_Integer?Positive, modding_Integer?NonPositive}] := {idx, modding};
spinDescendantModeData[{modding_Integer?NonPositive, idx_Integer?Positive}] := {idx, modding};
spinDescendantModeData[spinMode_] := $Failed;

spinDescendantModeQ::usage =
  "spinDescendantModeQ[spinMode, maxIndex] is True when spinMode is a bosonizable descendant mode with index in 1..maxIndex.";
spinDescendantModeQ[spinMode_, maxIndex_Integer?Positive] := MatchQ[
  spinDescendantModeData[spinMode],
  {idx_Integer /; 1 <= idx <= maxIndex, _Integer?NonPositive}
];

spinDescendantModeVectorIndex::usage =
  "spinDescendantModeVectorIndex[spinMode] returns the vector index carried by one bosonizable descendant spin mode.";
spinDescendantModeVectorIndex[spinMode_] := First[spinDescendantModeData[spinMode]] /; spinDescendantModeData[spinMode] =!= $Failed;

spinDescendantModeExcitationLevel::usage =
  "spinDescendantModeExcitationLevel[spinMode] returns the positive excitation level -r of one bosonizable descendant spin mode.";
spinDescendantModeExcitationLevel[spinMode_] := -Last[spinDescendantModeData[spinMode]] /; spinDescendantModeData[spinMode] =!= $Failed;

canonicalizeSpinModes::usage =
  "canonicalizeSpinModes[modes] canonicalizes descendant negative-modding tuples and sorts spin modes with the fermionic permutation sign.";
canonicalizeSpinModes[modes_List] := Module[{canonicalModes, ordering, sortedModes},
  canonicalModes = spinModeCanonicalRepresentative /@ modes;
  ordering = Ordering[spinModeOrderingKey /@ canonicalModes];
  sortedModes = canonicalModes[[ordering]];
  If[DuplicateFreeQ[sortedModes],
    {Signature[ordering], sortedModes},
    {0, sortedModes}
  ]
];

spinAlphaChiralitySign["chiral"] := 1;
spinAlphaChiralitySign["antichiral"] := -1;

S::alpha = "Spin index must be given as {alpha, \"chiral\"|\"antichiral\"}.";
St::alpha = "Spin index must be given as {alpha, \"chiral\"|\"antichiral\"}.";

S[alpha_, q_, modes_List, der_, z_] := (Message[S::alpha]; $Failed) /; !MatchQ[alpha, {_, ("chiral" | "antichiral")}];
St[alpha_, q_, modes_List, der_, zbar_] := (Message[St::alpha]; $Failed) /; !MatchQ[alpha, {_, ("chiral" | "antichiral")}];

S[{alpha_, chirality : ("chiral" | "antichiral")}, q_, modes_List, der_, z_] := Module[{canonicalized = canonicalizeSpinModes[modes]},
  If[canonicalized[[1]] == 0,
    0,
    canonicalized[[1]] S[{alpha, chirality}, q, canonicalized[[2]], der, z]
  ]
] /; With[{canonicalized = canonicalizeSpinModes[modes]}, canonicalized[[1]] == 0 || modes =!= canonicalized[[2]]];

St[{alpha_, chirality : ("chiral" | "antichiral")}, q_, modes_List, der_, zbar_] := Module[{canonicalized = canonicalizeSpinModes[modes]},
  If[canonicalized[[1]] == 0,
    0,
    canonicalized[[1]] St[{alpha, chirality}, q, canonicalized[[2]], der, zbar]
  ]
] /; With[{canonicalized = canonicalizeSpinModes[modes]}, canonicalized[[1]] == 0 || modes =!= canonicalized[[2]]];


bosonizationStateNormalization::usage =
  "bosonizationStateNormalization[expr] returns the convention-dependent normalization multiplier attached to one bosonized TypeII Hilbert-space state.";
bosonizationStateNormalization[0] := 0;
bosonizationStateNormalization[a_ + b_] := bosonizationStateNormalization[a] + bosonizationStateNormalization[b];
bosonizationStateNormalization[c_ a_] := c bosonizationStateNormalization[a] /; isScalarFactorQ[c];
bosonizationStateNormalization[a_ /; isScalarFactorQ[a]] := a;
bosonizationStateNormalization[Ra_ /; RTest[Ra]] := Times @@ (bosonizationFieldNormalization /@ (List @@ Ra));
bosonizationStateNormalization[field_ /; isField[Head[field]]] := bosonizationFieldNormalization[field];
bosonizationStateNormalization[_] := 1;

bosonizationFieldNormalization::usage =
  "bosonizationFieldNormalization[field] returns the convention-dependent normalization multiplier attached to one TypeII field before bosonization.";
bosonizationFieldNormalization[\[Psi][_, _, _]] := psiBosonizationScale[];
bosonizationFieldNormalization[\[Psi]t[_, _, _]] := psiBosonizationScale[];
bosonizationFieldNormalization[HoldPattern[S[{_, chirality_}, _, modes_List, _, _]]] /; MemberQ[{"chiral", "antichiral"}, chirality] :=
  spinBosonizationScale[chirality] psiBosonizationScale[]^Length[modes];
bosonizationFieldNormalization[HoldPattern[St[{_, chirality_}, _, modes_List, _, _]]] /; MemberQ[{"chiral", "antichiral"}, chirality] :=
  spinBosonizationScale[chirality] psiBosonizationScale[]^Length[modes];
bosonizationFieldNormalization[_] := 1;

bosonizeStateRaw::usage =
  "bosonizeStateRaw[expr] rewrites supported TypeII flat-space fermion and spin fields into the convention-independent H-boson basis before any convention-dependent Hilbert-space normalization is applied.";
bosonizeStateRaw[0] := 0;
bosonizeStateRaw[a_ + b_] := bosonizeStateRaw[a] + bosonizeStateRaw[b];
bosonizeStateRaw[c_ a_] := c bosonizeStateRaw[a] /; isScalarFactorQ[c];
bosonizeStateRaw[a_ /; isScalarFactorQ[a]] := a;
bosonizeStateRaw[Ra_ /; RTest[Ra]] := R @@ (bosonizeStateRaw /@ (List @@ Ra));


bosonizeStateRaw[dH[i_, n_, z_]] := dH[i, n, z];
bosonizeStateRaw[dHt[i_, n_, zbar_]] := dHt[i, n, zbar];
bosonizeStateRaw[expH[charges_, z_]] := expH[charges, z];
bosonizeStateRaw[expHt[charges_, zbar_]] := expHt[charges, zbar];
bosonizeStateRaw[field_ /; (SymbolName[Head[field]] === "d\:03d5" && MatchQ[field[[1]], _Integer?NonNegative])] := dH[1, field[[1]], field[[2]]];
bosonizeStateRaw[field_ /; (SymbolName[Head[field]] === "d\:03d5t" && MatchQ[field[[1]], _Integer?NonNegative])] := dHt[1, field[[1]], field[[2]]];
bosonizeStateRaw[field_ /; (MemberQ[{"exp\:03d5b", "exp\:03d5f"}, SymbolName[Head[field]]] && NumericQ[field[[1]]])] := expH[{field[[1]], 0, 0, 0, 0, 0}, field[[2]]];
bosonizeStateRaw[field_ /; (MemberQ[{"exp\:03d5tb", "exp\:03d5tf"}, SymbolName[Head[field]]] && NumericQ[field[[1]]])] := expHt[{field[[1]], 0, 0, 0, 0, 0}, field[[2]]];


bosonizeStateRaw[HoldPattern[S[{spinVec_List, chirality : ("chiral" | "antichiral")}, q_?NumericQ, modes_List, der_Integer?Positive, z_]]] := Module[{result},
  result = bosonizedSpinDerivative[S[{spinVec, chirality}, q, modes, 0, z], der, dH, expH];
  If[result === $Failed, S[{spinVec, chirality}, q, modes, der, z], result]
] /;
  spinVectorQ[spinVec] &&
  spinVectorChiralityQ[spinVec, chirality] &&
  AllTrue[modes, spinDescendantModeQ[#, Length[vectors]] &];


bosonizeStateRaw[HoldPattern[St[{spinVec_List, chirality : ("chiral" | "antichiral")}, q_?NumericQ, modes_List, der_Integer?Positive, zbar_]]] := Module[{result},
  result = bosonizedSpinDerivative[St[{spinVec, chirality}, q, modes, 0, zbar], der, dHt, expHt];
  If[result === $Failed, St[{spinVec, chirality}, q, modes, der, zbar], result]
] /;
  spinVectorQ[spinVec] &&
  spinVectorChiralityQ[spinVec, chirality] &&
  AllTrue[modes, spinDescendantModeQ[#, Length[vectors]] &];


(* Ramond ground states become a single six-charge exponential: the picture
   charge q occupies the first slot and the SO(10) spin weight fills the last
   five entries. *)
bosonizeStateRaw[HoldPattern[S[{spinVec_List, chirality : ("chiral" | "antichiral")}, q_?NumericQ, {}, 0, z_]]] :=
  expH[Join[{q}, spinVec], z] /; (spinVectorQ[spinVec] && spinVectorChiralityQ[spinVec, chirality]);


bosonizeStateRaw[HoldPattern[St[{spinVec_List, chirality : ("chiral" | "antichiral")}, q_?NumericQ, {}, 0, zbar_]]] :=
  expHt[Join[{q}, spinVec], zbar] /; (spinVectorQ[spinVec] && spinVectorChiralityQ[spinVec, chirality]);


(* Excited spin fields are delegated to the contour-based helpers from
   BasisGeneration once those helpers have been loaded and every mode label is
   concrete. If those prerequisites are missing, Bosonize stays unevaluated. *)
bosonizeStateRaw[HoldPattern[S[{spinVec_List, chirality : ("chiral" | "antichiral")}, q_?NumericQ, modes_List, 0, z_]]] :=
  bosonizeSpinModesHolo[{spinVec, chirality}, q, modes, z] /;
    modes =!= {} &&
    spinVectorQ[spinVec] &&
    spinVectorChiralityQ[spinVec, chirality] &&
    Length[DownValues[bosonizeSpinModesHolo]] > 0 &&
    AllTrue[modes, spinDescendantModeQ[#, Length[vectors]] &];


bosonizeStateRaw[HoldPattern[St[{spinVec_List, chirality : ("chiral" | "antichiral")}, q_?NumericQ, modes_List, 0, zbar_]]] :=
  bosonizeSpinModesAntiHolo[{spinVec, chirality}, q, modes, zbar] /;
    modes =!= {} &&
    spinVectorQ[spinVec] &&
    spinVectorChiralityQ[spinVec, chirality] &&
    Length[DownValues[bosonizeSpinModesAntiHolo]] > 0 &&
    AllTrue[modes, spinDescendantModeQ[#, Length[vectors]] &];


(* The fermion bosonization is stored in the vector-charge basis and then
   rotated back to the spacetime mu-basis with the fixed notebook-derived
   change-of-basis matrix. *)
bosonizeStateRaw[\[Psi][mu_Integer, n_Integer?NonNegative, z_]] :=
  Sum[basisChangeM[[mu, a]] bosonizedPsiBasisComponent[a, n, z, dH, expH], {a, 1, Length[vectors]}] /; 1 <= mu <= Length[vectors];


bosonizeStateRaw[\[Psi]t[mu_Integer, n_Integer?NonNegative, zbar_]] :=
  Sum[basisChangeM[[mu, a]] bosonizedPsiBasisComponent[a, n, zbar, dHt, expHt], {a, 1, Length[vectors]}] /; 1 <= mu <= Length[vectors];


bosonizeStateRaw[field_ /; isField[Head[field]]] := field;


Bosonize[0] := 0;
(* Bosonize is linear on sums and scalar multiples so larger expressions can be
   pushed down to single-field rules before the normal-ordering layer rebuilds
   mixed products. *)
Bosonize[a_ + b_] := Bosonize[a] + Bosonize[b];
Bosonize[c_ a_] := c Bosonize[a] /; isScalarFactorQ[c];
Bosonize[a_ /; isScalarFactorQ[a]] := a;
Bosonize[Ra_ /; RTest[Ra]] := bosonizationStateNormalization[Ra] bosonizeStateRaw[Ra];
Bosonize[field_ /; isField[Head[field]]] := bosonizationStateNormalization[field] bosonizeStateRaw[field];


(* ::Subsection:: *)
(*Define weight of symbols*)


(*Weights are provided via DefineField metadata and evaluated generically in Symbols.m.*)


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
