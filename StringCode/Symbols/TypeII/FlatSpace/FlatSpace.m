(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Symbols`TypeII`FlatSpace`"]
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"]


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

GammaUD::usage =
  "GammaUD[mu] denotes a single-link gamma block carrying an undotted-to-dotted spinor index flow.";

GammaDU::usage =
  "GammaDU[mu] denotes a single-link gamma block carrying a dotted-to-undotted spinor index flow.";

Gamma11UU::usage =
  "Gamma11UU[] denotes a chirality-preserving Gamma11 insertion with undotted end-index type.";

Gamma11DD::usage =
  "Gamma11DD[] denotes a chirality-preserving Gamma11 insertion with dotted end-index type.";

CUD::usage =
  "CUD denotes a charge-conjugation insertion used as the first element in GammaProduct link lists for incoming chiral/chiral chains.";

CDU::usage =
  "CDU denotes a charge-conjugation insertion used as the first element in GammaProduct link lists for incoming antichiral/antichiral chains.";

GammaProduct::usage =
  "GammaProduct[{link1,...}, alpha, beta] denotes an ordered gamma chain between spinor endpoints; when needed, CUD/CDU appears as the first list element.";

CGamma::usage = "CGamma[{mu1,...}, alpha, beta] denotes a Clifford tensor with two chiral spinor indices.";

CIGamma::usage = "CIGamma[{mu1,...}, alpha, beta] denotes a Clifford tensor with two antichiral spinor indices.";

GammaM::usage = "GammaM[{mu1,...}, alpha, beta] denotes a Clifford tensor with one chiral and one antichiral spinor index.";

Gamma11CGamma::usage =
  "Gamma11CGamma[{mu1,...}, alpha, beta] denotes Gamma11 times a chiral-chiral Clifford tensor.";

Gamma11CIGamma::usage =
  "Gamma11CIGamma[{mu1,...}, alpha, beta] denotes Gamma11 times an antichiral-antichiral Clifford tensor.";

Gamma11GammaM::usage =
  "Gamma11GammaM[{mu1,...}, alpha, beta] denotes Gamma11 times a mixed-chirality Clifford tensor.";

Eps10::usage =
  "Eps10[upIndices, downIndices] denotes the 10D Levi-Civita tensor with explicit upper/lower index lists.";


Bosonize::usage = "Bosonize[expr] rewrites supported TypeII flat-space fermion and spin fields into the bosonized H-boson basis.";


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


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
  derivativeOfBosonizedExponential[n] /. {
    E^(func[x]) :> exponentialHead[charges, coord],
    Power[Derivative[m_][func][x], p_] :> bosonizedExponentDerivative[charges, derivativeHead, m, coord]^p,
    Derivative[m_][func][x] :> bosonizedExponentDerivative[charges, derivativeHead, m, coord]
  }
] /; charge6Q[charges];


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
      Total[
        Join[
          Cases[field[[3]], {_, mode_?NumericQ} :> mode],
          Cases[field[[3]], {mode_?NumericQ, _} :> mode]
        ]
      ]
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
      Total[
        Join[
          Cases[field[[3]], {_, mode_?NumericQ} :> mode],
          Cases[field[[3]], {mode_?NumericQ, _} :> mode]
        ]
      ]
  ],
  "GSOParityHolo" -> 1,
  "GSOParityAntiHolo" -> Function[field, spinAlphaChiralitySign[field[[1, 2]]] (-1)^(field[[2]] + 1/2 + Length[field[[3]]])]
];

canonicalizeSpinModes[modes_List] := Module[{ordering, sortedModes},
  ordering = Ordering[modes];
  sortedModes = modes[[ordering]];
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
] /; (!DuplicateFreeQ[modes] || !OrderedQ[modes]);

St[{alpha_, chirality : ("chiral" | "antichiral")}, q_, modes_List, der_, zbar_] := Module[{canonicalized = canonicalizeSpinModes[modes]},
  If[canonicalized[[1]] == 0,
    0,
    canonicalized[[1]] St[{alpha, chirality}, q, canonicalized[[2]], der, zbar]
  ]
] /; (!DuplicateFreeQ[modes] || !OrderedQ[modes]);


Bosonize[0] := 0;
Bosonize[a_ + b_] := Bosonize[a] + Bosonize[b];
Bosonize[c_ a_] := c Bosonize[a] /; isScalarFactorQ[c];
Bosonize[a_ /; isScalarFactorQ[a]] := a;


Bosonize[dH[i_, n_, z_]] := dH[i, n, z];
Bosonize[dHt[i_, n_, zbar_]] := dHt[i, n, zbar];
Bosonize[expH[charges_, z_]] := expH[charges, z];
Bosonize[expHt[charges_, zbar_]] := expHt[charges, zbar];
Bosonize[d\[Phi][n_Integer?NonNegative, z_]] := dH[1, n, z];
Bosonize[d\[Phi]t[n_Integer?NonNegative, zbar_]] := dHt[1, n, zbar];
Bosonize[exp\[Phi]b[q_?NumericQ, z_]] := expH[{q, 0, 0, 0, 0, 0}, z];
Bosonize[exp\[Phi]f[q_?NumericQ, z_]] := expH[{q, 0, 0, 0, 0, 0}, z];
Bosonize[exp\[Phi]tb[q_?NumericQ, zbar_]] := expHt[{q, 0, 0, 0, 0, 0}, zbar];
Bosonize[exp\[Phi]tf[q_?NumericQ, zbar_]] := expHt[{q, 0, 0, 0, 0, 0}, zbar];


Bosonize[HoldPattern[S[{spinVec_List, chirality : ("chiral" | "antichiral")}, q_?NumericQ, {}, 0, z_]]] :=
  expH[Join[{q}, spinVec], z] /; (spinVectorQ[spinVec] && spinVectorChiralityQ[spinVec, chirality]);


Bosonize[HoldPattern[St[{spinVec_List, chirality : ("chiral" | "antichiral")}, q_?NumericQ, {}, 0, zbar_]]] :=
  expHt[Join[{q}, spinVec], zbar] /; (spinVectorQ[spinVec] && spinVectorChiralityQ[spinVec, chirality]);


Bosonize[\[Psi][mu_Integer, n_Integer?NonNegative, z_]] :=
  Sum[basisChangeM[[mu, a]] bosonizedPsiBasisComponent[a, n, z, dH, expH], {a, 1, Length[vectors]}] /; 1 <= mu <= Length[vectors];


Bosonize[\[Psi]t[mu_Integer, n_Integer?NonNegative, zbar_]] :=
  Sum[basisChangeM[[mu, a]] bosonizedPsiBasisComponent[a, n, zbar, dHt, expHt], {a, 1, Length[vectors]}] /; 1 <= mu <= Length[vectors];


(* ::Subsection:: *)
(*Define weight of symbols*)


(*Weights are provided via DefineField metadata and evaluated generically in Symbols.m.*)


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
