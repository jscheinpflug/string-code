(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Symbols`Bosonic`FlatSpace`"]
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`Bosonic`"];


(* ::Section:: *)
(*Declare public variables and methods*)


expXAntiHolo::usage = "Antiholomorphic part of the wave primary in free boson CFT";


expXHolo::usage = "Holomorphic part of the wave primary in free boson CFT";


expX::usage = "Plane wave primary in free boson CFT";


dX::usage = "Holomorphic del X primary in free boson CFT"


dXt::usage = "Antiholomorphic del X primary in free boson CFT"


ProfileXAntiHolo::usage = "Antiolomorphic part of an X-profile"


ProfileXHolo::usage = "Holomorphic part of an X-profile"


ProfileX::usage = "A polynomial X-profile"


\[Alpha]p::usage = "Symbol for alpha prime";

dot::usage = "Symbol for dot product";

der::usage = "Symbol for a derivative";

\[Delta]::usage = "Inert Kronecker delta tensor for flat-space vector-index contractions.";


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


flatSpaceContractRules::usage = "flatSpaceContractRules[dim] returns bosonic FlatSpace contraction rules for \\[Delta] tensors.";
flatSpaceContractRules[dim_] := {\[Delta][\[Mu]_, \[Mu]_] :> dim, \[Delta][\[Mu]_, \[Nu]_]^2 :> dim};

Contract[f_, dim_] := f /. flatSpaceContractRules[dim];
Contract[f_] := Contract[f, 10];

ContractDelta[f_] := f //. {
  g_ \[Delta][\[Mu]_, \[Mu]1_] :> (g /. {\[Mu] -> \[Mu]1}) /; !FreeQ[g, \[Mu]],
  g_ \[Delta][\[Mu]1_, \[Mu]_] :> (g /. {\[Mu] -> \[Mu]1}) /; !FreeQ[g, \[Mu]]
};


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
  "WeightHolo" -> Function[field, 1 + field[[2]]],
  "WeightAntiHolo" -> 0
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
  "WeightAntiHolo" -> Function[field, 1 + field[[2]]]
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
  "WeightAntiHolo" -> 0
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
  "WeightAntiHolo" -> 0
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
  "WeightAntiHolo" -> 0
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
  "WeightAntiHolo" -> 0
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
  "WeightAntiHolo" -> 0
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
  "WeightAntiHolo" -> 0
];


(* ::Subsection:: *)
(*Define weight of symbols*)


(*Weights are provided via DefineField metadata and evaluated generically in Symbols.m.*)


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
