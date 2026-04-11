(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Symbols`TypeII`"]
Needs["StringCode`Symbols`"];


(* ::Section:: *)
(*Declare public variables and methods*)


d\[Phi]::usage = "Holomorphic del \[Phi] primary in linear dilaton CFT"


d\[Phi]t::usage = "Antiholomorphic del \[Phi] primary in linear dilaton CFT"


exp\[Phi]b::usage = "Holomorphic bosonic exponential of the \[Phi] linear dilaton"


exp\[Phi]tb::usage = "Antiholomorphic bosonic exponential of the \[Phi] linear dilaton"


exp\[Phi]f::usage = "Holomorphic fermionic exponential of the \[Phi] linear dilaton"


exp\[Phi]tf::usage = "Antiholomorphic fermionic exponential of the \[Phi] linear dilaton"


\[Xi]::usage = "Holomorphic \[Xi]-ghost";


\[Xi]t::usage = "Antiholomorphic \[Xi]-ghost";


\[Eta]::usage = "Holomorphic \[Eta]-ghost";


\[Eta]t::usage = "Antiholomorphic \[Eta]-ghost";


\[Beta]::usage = "Holomorphic \[Beta]-ghost";


\[Beta]t::usage = "Antiholomorphic \[Beta]-ghost";


\[Gamma]::usage = "Holomorphic \[Gamma]-ghost";


\[Gamma]t::usage = "Antiholomorphic \[Gamma]-ghost";

GSOParity::usage = "Computes total GSO parity for TypeII fields";


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Define symbols*)


extendAllowedFieldPropertyKeys[{"ExpPhiFermionFamily", "GSOParityHolo", "GSOParityAntiHolo"}];

exp\[Phi]b[0,z_]:=1;
exp\[Phi]tb[0,z_]:=1;

DefineField[d\[Phi],
  "Statistics" -> "Boson",
  "Simple" -> True,
  "Composite" -> False,
  "Holomorphic" -> True,
  "AntiHolomorphic" -> False,
  "Indexed" -> False,
  "Collapsable" -> False,
  "Factorizable" -> False,
  "RegularFermion" -> False,
  "PairsWith" -> {d\[Phi], exp\[Phi]b, exp\[Phi]f},
  "WeightHolo" -> Function[field, 1 + field[[1]]],
  "WeightAntiHolo" -> 0,
  "GSOParityHolo" -> 1,
  "GSOParityAntiHolo" -> 1
];

DefineField[d\[Phi]t,
  "Statistics" -> "Boson",
  "Simple" -> True,
  "Composite" -> False,
  "Holomorphic" -> False,
  "AntiHolomorphic" -> True,
  "Indexed" -> False,
  "Collapsable" -> False,
  "Factorizable" -> False,
  "RegularFermion" -> False,
  "PairsWith" -> {d\[Phi]t, exp\[Phi]tb, exp\[Phi]tf},
  "WeightHolo" -> 0,
  "WeightAntiHolo" -> Function[field, 1 + field[[1]]],
  "GSOParityHolo" -> 1,
  "GSOParityAntiHolo" -> 1
];

DefineField[\[Xi],
  "Statistics" -> "Fermion",
  "Simple" -> True,
  "Composite" -> False,
  "Holomorphic" -> True,
  "AntiHolomorphic" -> False,
  "Indexed" -> False,
  "Collapsable" -> True,
  "Factorizable" -> False,
  "RegularFermion" -> True,
  "PairsWith" -> {\[Eta]},
  "WeightHolo" -> Function[field, field[[1]]],
  "WeightAntiHolo" -> 0,
  "GSOParityHolo" -> 1,
  "GSOParityAntiHolo" -> 1
];

DefineField[\[Xi]t,
  "Statistics" -> "Fermion",
  "Simple" -> True,
  "Composite" -> False,
  "Holomorphic" -> False,
  "AntiHolomorphic" -> True,
  "Indexed" -> False,
  "Collapsable" -> True,
  "Factorizable" -> False,
  "RegularFermion" -> True,
  "PairsWith" -> {\[Eta]t},
  "WeightHolo" -> 0,
  "WeightAntiHolo" -> Function[field, field[[1]]],
  "GSOParityHolo" -> 1,
  "GSOParityAntiHolo" -> 1
];

DefineField[\[Eta],
  "Statistics" -> "Fermion",
  "Simple" -> True,
  "Composite" -> False,
  "Holomorphic" -> True,
  "AntiHolomorphic" -> False,
  "Indexed" -> False,
  "Collapsable" -> True,
  "Factorizable" -> False,
  "RegularFermion" -> True,
  "PairsWith" -> {\[Xi]},
  "WeightHolo" -> Function[field, 1 + field[[1]]],
  "WeightAntiHolo" -> 0,
  "GSOParityHolo" -> 1,
  "GSOParityAntiHolo" -> 1
];

DefineField[\[Eta]t,
  "Statistics" -> "Fermion",
  "Simple" -> True,
  "Composite" -> False,
  "Holomorphic" -> False,
  "AntiHolomorphic" -> True,
  "Indexed" -> False,
  "Collapsable" -> True,
  "Factorizable" -> False,
  "RegularFermion" -> True,
  "PairsWith" -> {\[Xi]t},
  "WeightHolo" -> 0,
  "WeightAntiHolo" -> Function[field, 1 + field[[1]]],
  "GSOParityHolo" -> 1,
  "GSOParityAntiHolo" -> 1
];

DefineField[\[Beta],
  "Statistics" -> "Boson",
  "Simple" -> True,
  "Composite" -> False,
  "Holomorphic" -> True,
  "AntiHolomorphic" -> False,
  "Indexed" -> False,
  "Collapsable" -> True,
  "Factorizable" -> False,
  "RegularFermion" -> False,
  "PairsWith" -> {\[Gamma]},
  "WeightHolo" -> Function[field, 3/2 + field[[1]]],
  "WeightAntiHolo" -> 0,
  "GSOParityHolo" -> -1,
  "GSOParityAntiHolo" -> 1
];

DefineField[\[Beta]t,
  "Statistics" -> "Boson",
  "Simple" -> True,
  "Composite" -> False,
  "Holomorphic" -> False,
  "AntiHolomorphic" -> True,
  "Indexed" -> False,
  "Collapsable" -> True,
  "Factorizable" -> False,
  "RegularFermion" -> False,
  "PairsWith" -> {\[Gamma]t},
  "WeightHolo" -> 0,
  "WeightAntiHolo" -> Function[field, 3/2 + field[[1]]],
  "GSOParityHolo" -> 1,
  "GSOParityAntiHolo" -> -1
];

DefineField[\[Gamma],
  "Statistics" -> "Boson",
  "Simple" -> True,
  "Composite" -> False,
  "Holomorphic" -> True,
  "AntiHolomorphic" -> False,
  "Indexed" -> False,
  "Collapsable" -> True,
  "Factorizable" -> False,
  "RegularFermion" -> False,
  "PairsWith" -> {\[Beta]},
  "WeightHolo" -> Function[field, -1/2 + field[[1]]],
  "WeightAntiHolo" -> 0,
  "GSOParityHolo" -> -1,
  "GSOParityAntiHolo" -> 1
];

DefineField[\[Gamma]t,
  "Statistics" -> "Boson",
  "Simple" -> True,
  "Composite" -> False,
  "Holomorphic" -> False,
  "AntiHolomorphic" -> True,
  "Indexed" -> False,
  "Collapsable" -> True,
  "Factorizable" -> False,
  "RegularFermion" -> False,
  "PairsWith" -> {\[Beta]t},
  "WeightHolo" -> 0,
  "WeightAntiHolo" -> Function[field, -1/2 + field[[1]]],
  "GSOParityHolo" -> 1,
  "GSOParityAntiHolo" -> -1
];

DefineField[exp\[Phi]b,
  "Statistics" -> "Boson",
  "Simple" -> False,
  "Composite" -> True,
  "Holomorphic" -> True,
  "AntiHolomorphic" -> False,
  "Indexed" -> False,
  "Collapsable" -> False,
  "Factorizable" -> False,
  "RegularFermion" -> False,
  "PairsWith" -> {exp\[Phi]b, exp\[Phi]f, d\[Phi]},
  "WeightHolo" -> Function[field, (-1/2)*(field[[1]])*(field[[1]]+2)],
  "WeightAntiHolo" -> 0,
  "GSOParityHolo" -> Function[field, (-1)^(field[[1]])],
  "GSOParityAntiHolo" -> 1
];

DefineField[exp\[Phi]tb,
  "Statistics" -> "Boson",
  "Simple" -> False,
  "Composite" -> True,
  "Holomorphic" -> False,
  "AntiHolomorphic" -> True,
  "Indexed" -> False,
  "Collapsable" -> False,
  "Factorizable" -> False,
  "RegularFermion" -> False,
  "PairsWith" -> {exp\[Phi]tb, exp\[Phi]tf, d\[Phi]t},
  "WeightHolo" -> 0,
  "WeightAntiHolo" -> Function[field, (-1/2)*(field[[1]])*(field[[1]]+2)],
  "GSOParityHolo" -> 1,
  "GSOParityAntiHolo" -> Function[field, (-1)^(field[[1]])]
];

DefineField[exp\[Phi]f,
  "Statistics" -> "Fermion",
  "Simple" -> False,
  "Composite" -> True,
  "Holomorphic" -> True,
  "AntiHolomorphic" -> False,
  "Indexed" -> False,
  "Collapsable" -> False,
  "Factorizable" -> False,
  "RegularFermion" -> False,
  "PairsWith" -> {exp\[Phi]f, exp\[Phi]b, d\[Phi]},
  "WeightHolo" -> Function[field, (-1/2)*(field[[1]])*(field[[1]]+2)],
  "WeightAntiHolo" -> 0,
  "ExpPhiFermionFamily" -> "Holo",
  "GSOParityHolo" -> Function[field, (-1)^(field[[1]])],
  "GSOParityAntiHolo" -> 1
];

DefineField[exp\[Phi]tf,
  "Statistics" -> "Fermion",
  "Simple" -> False,
  "Composite" -> True,
  "Holomorphic" -> False,
  "AntiHolomorphic" -> True,
  "Indexed" -> False,
  "Collapsable" -> False,
  "Factorizable" -> False,
  "RegularFermion" -> False,
  "PairsWith" -> {exp\[Phi]tf, exp\[Phi]tb, d\[Phi]t},
  "WeightHolo" -> 0,
  "WeightAntiHolo" -> Function[field, (-1/2)*(field[[1]])*(field[[1]]+2)],
  "ExpPhiFermionFamily" -> "AntiHolo",
  "GSOParityHolo" -> 1,
  "GSOParityAntiHolo" -> Function[field, (-1)^(field[[1]])]
];


(* ::Subsection:: *)
(*Define picture numbers*)


pictureHol::usage = "Gives holomorphic picture number";

pictureHol[\[Xi][n_, z_]]:= 1;
pictureHol[\[Eta][n_, z_]]:= -1;
pictureHol[exp\[Phi]f[exp_, z_]]:= exp;
pictureHol[exp\[Phi]b[exp_, z_]]:= exp;
pictureHol[a_/;isField[Head[a]]]:= 0;

pictureAntiHol::usage = "Gives antiholomorphic picture number";

pictureAntiHol[\[Xi]t[n_, zbar_]]:= 1;
pictureAntiHol[\[Eta]t[n_, zbar_]]:= -1;
pictureAntiHol[exp\[Phi]tf[exp_, zbar_]]:= exp;
pictureAntiHol[exp\[Phi]tb[exp_, zbar_]]:= exp;
pictureAntiHol[a_/;isField[Head[a]]]:= 0;


(* ::Subsection:: *)
(*Define ghost numbers*)


ghostNumberHolo[\[Xi][der_, z_]]:= -1;
ghostNumberHolo[\[Eta][der_, z_]]:= 1;
ghostNumberHolo[\[Beta][der_, z_]]:= -1;
ghostNumberHolo[\[Gamma][der_, z_]]:= 1;
ghostNumberHolo[a_/;isField[Head[a]]]:= 0;

ghostNumberAntiHolo[\[Xi]t[der_, zbar_]]:= -1;
ghostNumberAntiHolo[\[Eta]t[der_, zbar_]]:= 1;
ghostNumberAntiHolo[\[Beta]t[der_, zbar_]]:= -1;
ghostNumberAntiHolo[\[Gamma]t[der_, zbar_]]:= 1;
ghostNumberAntiHolo[a_/;isField[Head[a]]]:= 0;

GSOParityHolo::usage = "Computes holomorphic GSO parity of a TypeII field.";
GSOParityHolo[a_/;isField[Head[a]]]:= evaluateFieldProperty[a, "GSOParityHolo", 1];

GSOParityAntiHolo::usage = "Computes antiholomorphic GSO parity of a TypeII field.";
GSOParityAntiHolo[a_/;isField[Head[a]]]:= evaluateFieldProperty[a, "GSOParityAntiHolo", 1];
GSOParity[a_/;isField[Head[a]]]:= GSOParityHolo[a] GSOParityAntiHolo[a];


(* ::Subsection:: *)
(*Define weight of symbols*)


(* ::Subsubsection:: *)
(*Superghosts*)


weightSymbolHolo[\[Xi]] := 0;
weightSymbolHolo[\[Eta]] := 1;
weightSymbolHolo[\[Beta]] := 3/2;
weightSymbolHolo[\[Gamma]] := -1/2;
weightSymbolHolo[d\[Phi]] := 1;
weightHolo[\[Xi][der_, z_]] := weightSymbolHolo[\[Xi]] + der;
weightHolo[\[Eta][der_, z_]] := weightSymbolHolo[\[Eta]] + der;
weightHolo[\[Beta][der_, z_]] := weightSymbolHolo[\[Beta]] + der;
weightHolo[\[Gamma][der_, z_]] := weightSymbolHolo[\[Gamma]] + der;
weightHolo[d\[Phi][der_, z_]] := weightSymbolHolo[d\[Phi]] + der;

weightHolo[exp\[Phi]f[n_, z_]] := -1/2*(n)*(n + 2);
weightHolo[exp\[Phi]b[n_, z_]] := -1/2*(n)*(n + 2);

weightSymbolAntiHolo[\[Xi]t] := 0;
weightSymbolAntiHolo[\[Eta]t] := 1;
weightSymbolAntiHolo[\[Beta]t] := 3/2;
weightSymbolAntiHolo[\[Gamma]t] := -1/2;
weightSymbolAntiHolo[d\[Phi]t] := 1;
weightAntiHolo[\[Xi]t[der_, zbar_]] := weightSymbolAntiHolo[\[Xi]t] + der;
weightAntiHolo[\[Eta]t[der_, zbar_]] := weightSymbolAntiHolo[\[Eta]t] + der;
weightAntiHolo[\[Beta]t[der_, zbar_]] := weightSymbolAntiHolo[\[Beta]t] + der;
weightAntiHolo[\[Gamma]t[der_, zbar_]] := weightSymbolAntiHolo[\[Gamma]t] + der;
weightAntiHolo[d\[Phi]t[der_, zbar_]] := weightSymbolAntiHolo[d\[Phi]t] + der;

weightAntiHolo[exp\[Phi]tf[n_, z_]] := -1/2*(n)*(n + 2);
weightAntiHolo[exp\[Phi]tb[n_, z_]] := -1/2*(n)*(n + 2);


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
