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
  "PairsWith" -> {dX, expX, ProfileX, expXHolo, ProfileXHolo}
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
  "PairsWith" -> {dXt, expX, ProfileX, expXAntiHolo, ProfileXAntiHolo}
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
  "FactorizationRule" -> (expX[k_, z_, zbar_] :> {expXHolo[k, z], expXAntiHolo[k, zbar]})
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
  "PairsWith" -> {expXHolo, ProfileXHolo, dX}
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
  "PairsWith" -> {expXAntiHolo, ProfileXAntiHolo, dXt}
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
  "FactorizationRule" -> (ProfileX[profile_, ders_, z_, zbar_] :> {ProfileXHolo[profile, ders, z], ProfileXAntiHolo[profile, ders, zbar]})
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
  "PairsWith" -> {ProfileXHolo, expXHolo, dX}
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
  "PairsWith" -> {ProfileXAntiHolo, expXAntiHolo, dXt}
];


(* ::Subsection:: *)
(*Define weight of symbols*)


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


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
