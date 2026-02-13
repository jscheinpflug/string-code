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


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Define symbols*)


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


(* ::Subsection:: *)
(*Define weight of symbols*)


(* ::Subsubsection:: *)
(*Free boson*)


weightSymbolHolo[dX] := 1;
weightHolo[dX[\[Mu]_, n_, z_]] := weightSymbolHolo[dX] + n;

weightHolo[expX[k_, z_,zbar_]] := 0;
weightHolo[expXHolo[k_, z_]] := 0;
weightHolo[ProfileX[profile_, ders_, z_, zbar_]] := 0;
weightHolo[ProfileXHolo[profile_, ders_, z_]] := 0;

weightSymbolAntiHolo[dXt] := 1;
weightAntiHolo[dXt[\[Mu]_, n_, zbar_]] := weightSymbolAntiHolo[dXt] + n;

weightAntiHolo[expX[k_, z_,zbar_]] := 0;
weightAntiHolo[expXAntiHolo[k_, zbar_]] := 0;
weightAntiHolo[ProfileX[profile_, ders_, z_, zbar_]] := 0;
weightAntiHolo[ProfileXAntiHolo[profile_, ders_, zbar_]] := 0;


(* ::Subsubsection:: *)
(*Free fermion*)


weightSymbolHolo[\[Psi]]:= 1/2;
weightHolo[\[Psi][\[Mu]_, n_, z_]] := weightSymbolHolo[\[Psi]] + n;
weightSymbolAntiHolo[\[Psi]t] := 1/2;
weightAntiHolo[\[Psi]t[\[Mu]_, n_, zbar_]] := weightSymbolAntiHolo[\[Psi]t] + n;

weightHolo[S[{alpha_, chirality : ("chiral" | "antichiral")}, q_, modes_List, der_, z_]] := 5/8 - q (q + 2)/2 + der + Total[First /@ modes];
weightHolo[St[{alpha_, chirality : ("chiral" | "antichiral")}, q_, modes_List, der_, zbar_]] := 0;
weightAntiHolo[S[{alpha_, chirality : ("chiral" | "antichiral")}, q_, modes_List, der_, z_]] := 0;
weightAntiHolo[St[{alpha_, chirality : ("chiral" | "antichiral")}, q_, modes_List, der_, zbar_]] := 5/8 - q (q + 2)/2 + der + Total[First /@ modes];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
