(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Symbols`"]


(* ::Section:: *)
(*Declare public variables and methods*)


isCollapsable::usage = "Checks if is collapsable field";


isFactorizable::usage = "Checks if a field is factorizable";


factorizeOperator::usage = "Factorizes an operator into a tuple {holoPart, antiHoloPart} if it is both holomorphic and antiholomorphic and marked as factorizable";


Contract::usage = "Contract traced indices";


ContractDelta::usage = "Contract repeated indices";


b::usage = "Holomorphic b-ghost"


bt::usage = "Antiholomorphic b-ghost"


c::usage = "Holomorphic c-ghost"


ct::usage = "Antiholomorphic c-ghost"


isBoson::usage = "Checks if is bosonic field";


isFermion::usage = "Checks if is fermionic field";


isSimple::usage = "Checks if is simple field";


isComposite::usage = "Checks if is composite field";


isField::usage = "Checks if is field";

isHolomorphic::usage = "Checks if is holomorphic";


isAntiHolomorphic::usage = "Checks if is antiholomorphic";


isIndexed::usage = "Checks if is indexed";


(* ::Section:: *)
(*Logic*)


(* ::Subsection:: *)
(*Define index contractions*)


Contract[f_,dim_]:=f /.{\[Delta][\[Mu]_,\[Mu]_]:>dim,\[Delta][\[Mu]_,\[Nu]_]^2:>dim};
Contract[f_]:=Contract[f,10];


ContractDelta[f_]:=f//.{g_ \[Delta][\[Mu]_,\[Mu]1_]:>(g/.{\[Mu]->\[Mu]1})/;!FreeQ[g,\[Mu]],g_ \[Delta][\[Mu]1_,\[Mu]_]:>(g/.{\[Mu]->\[Mu]1})/;!FreeQ[g,\[Mu]]};


Begin["Private`"];


(* ::Subsection:: *)
(*Field registry*)


$FieldRegistry = <||>;

$DefaultFieldMetadata = <|
  "Statistics" -> "Boson",
  "Simple" -> False,
  "Composite" -> False,
  "Holomorphic" -> False,
  "AntiHolomorphic" -> False,
  "Indexed" -> False,
  "Collapsable" -> False,
  "Factorizable" -> False,
  "RegularFermion" -> False,
  "PairsWith" -> {}
|>;

$AllowedFieldPropertyKeys = Keys[$DefaultFieldMetadata] ~Join~ {
  "GhostNumber", "WeightHolo", "WeightAntiHolo", "FactorizationRule"
};

extendAllowedFieldPropertyKeys::usage = "Extends allowed metadata keys accepted by DefineField.";
extendAllowedFieldPropertyKeys[keys_List] := ($AllowedFieldPropertyKeys = Union[$AllowedFieldPropertyKeys, keys]);

DefineField::badkey = "Unknown field property key(s): `1`.";
DefineField::pairs = "PairsWith for `1` must be a Symbol or list of Symbols.";

normalizePairsWith[sym_Symbol] := {sym};
normalizePairsWith[list_List] /; VectorQ[list, MatchQ[#, _Symbol] &] := DeleteDuplicates[list];
normalizePairsWith[_] := $Failed;

normalizeFieldHead[expr_] := Which[
  MatchQ[expr, _Symbol], expr,
  MatchQ[Head[expr], _Symbol], Head[expr],
  True, $Failed
];

DefineField::usage = "Registers field metadata in the internal field registry.";
DefineField[symbol_Symbol, properties___Rule] := Module[
  {assoc, unknownKeys, normalizedPairs},
  assoc = Association[properties];
  unknownKeys = Complement[Keys[assoc], $AllowedFieldPropertyKeys];
  If[unknownKeys =!= {},
    Message[DefineField::badkey, unknownKeys];
    Return[$Failed];
  ];

  assoc = Join[$DefaultFieldMetadata, assoc];
  normalizedPairs = normalizePairsWith[assoc["PairsWith"]];
  If[normalizedPairs === $Failed,
    Message[DefineField::pairs, symbol];
    Return[$Failed];
  ];
  assoc["PairsWith"] = normalizedPairs;
  $FieldRegistry[symbol] = assoc;
  symbol
];

fieldProperty::usage = "Looks up a metadata property for a field.";
fieldProperty[expr_, prop_String] := Module[{symbol = normalizeFieldHead[expr]},
  If[symbol === $Failed,
    Missing["NotAvailable"],
    Lookup[Lookup[$FieldRegistry, symbol, <||>], prop, Missing["NotAvailable"]]
  ]
];

evaluateFieldProperty::usage = "Resolves a metadata property, evaluating function-valued entries on the field.";
evaluateFieldProperty[field_, prop_String, default_] := Module[{value = fieldProperty[field, prop]},
  Which[
    value === Missing["NotAvailable"], default,
    MatchQ[value, _Function], value[field],
    True, value
  ]
];


(* ::Subsection:: *)
(*Define base fields*)


DefineField[c,
  "Statistics" -> "Fermion",
  "Simple" -> True,
  "Composite" -> False,
  "Holomorphic" -> True,
  "AntiHolomorphic" -> False,
  "Indexed" -> False,
  "Collapsable" -> True,
  "Factorizable" -> False,
  "RegularFermion" -> True,
  "PairsWith" -> {b},
  "GhostNumber" -> 1,
  "WeightHolo" -> -1
];

DefineField[b,
  "Statistics" -> "Fermion",
  "Simple" -> True,
  "Composite" -> False,
  "Holomorphic" -> True,
  "AntiHolomorphic" -> False,
  "Indexed" -> False,
  "Collapsable" -> True,
  "Factorizable" -> False,
  "RegularFermion" -> True,
  "PairsWith" -> {c},
  "GhostNumber" -> -1,
  "WeightHolo" -> 2
];

DefineField[ct,
  "Statistics" -> "Fermion",
  "Simple" -> True,
  "Composite" -> False,
  "Holomorphic" -> False,
  "AntiHolomorphic" -> True,
  "Indexed" -> False,
  "Collapsable" -> True,
  "Factorizable" -> False,
  "RegularFermion" -> True,
  "PairsWith" -> {bt},
  "GhostNumber" -> 1,
  "WeightAntiHolo" -> -1
];

DefineField[bt,
  "Statistics" -> "Fermion",
  "Simple" -> True,
  "Composite" -> False,
  "Holomorphic" -> False,
  "AntiHolomorphic" -> True,
  "Indexed" -> False,
  "Collapsable" -> True,
  "Factorizable" -> False,
  "RegularFermion" -> True,
  "PairsWith" -> {ct},
  "GhostNumber" -> -1,
  "WeightAntiHolo" -> 2
];


(* ::Subsection:: *)
(*Predicates and helpers*)


isField[symbol_] := Module[{head = normalizeFieldHead[symbol]},
  head =!= $Failed && KeyExistsQ[$FieldRegistry, head]
];

isBoson[symbol_] := isField[symbol] && fieldProperty[symbol, "Statistics"] === "Boson";
isFermion[symbol_] := isField[symbol] && fieldProperty[symbol, "Statistics"] === "Fermion";
isSimple[symbol_] := isField[symbol] && TrueQ[fieldProperty[symbol, "Simple"]];
isComposite[symbol_] := isField[symbol] && TrueQ[fieldProperty[symbol, "Composite"]];
isHolomorphic[symbol_] := isField[symbol] && TrueQ[fieldProperty[symbol, "Holomorphic"]];
isAntiHolomorphic[symbol_] := isField[symbol] && TrueQ[fieldProperty[symbol, "AntiHolomorphic"]];
isIndexed[symbol_] := isField[symbol] && TrueQ[fieldProperty[symbol, "Indexed"]];
isCollapsable[symbol_] := isField[symbol] && TrueQ[fieldProperty[symbol, "Collapsable"]];
isFactorizable[symbol_] := isField[symbol] && TrueQ[fieldProperty[symbol, "Factorizable"]];

isRegFermion::usage = "Checks if is regular fermion field.";
isRegFermion[symbol_] := isField[symbol] && TrueQ[fieldProperty[symbol, "RegularFermion"]];

containsFieldQ::usage = "Checks if expression contains any registered field.";
containsFieldQ[expr_] := !FreeQ[expr, field_ /; isField[Head[field]]];

containsFermionQ::usage = "Checks if expression contains any registered fermion field.";
containsFermionQ[expr_] := !FreeQ[expr, field_ /; isFermion[Head[field]]];

containsRegularFermionQ::usage = "Checks if expression contains any registered regular fermion field.";
containsRegularFermionQ[expr_] := !FreeQ[expr, field_ /; isRegFermion[Head[field]]];

isScalarFactorQ::usage = "Checks if expression is scalar factor with respect to registered fields.";
isScalarFactorQ[expr_] := !containsFieldQ[expr];

factorizeOperator[op_] := Module[{symbol = Head[op], rule},
  If[isHolomorphic[symbol] && isAntiHolomorphic[symbol] && isFactorizable[symbol],
    rule = fieldProperty[symbol, "FactorizationRule"];
    If[MatchQ[rule, _Rule | _RuleDelayed],
      op /. rule,
      op
    ],
    op
  ]
];


(* ::Subsection:: *)
(*Define ghost numbers*)


ghostNumberHolo[c[der_, z_]]:= fieldProperty[c, "GhostNumber"];
ghostNumberHolo[b[der_, z_]]:= fieldProperty[b, "GhostNumber"];

ghostNumberAntiHolo[ct[der_, zbar_]]:= fieldProperty[ct, "GhostNumber"];
ghostNumberAntiHolo[bt[der_, zbar_]]:= fieldProperty[bt, "GhostNumber"];

ghostNumberHolo[a_/;isField[Head[a]]]:= 0;
ghostNumberAntiHolo[a_/;isField[Head[a]]]:= 0;


(* ::Subsection:: *)
(*Define weight of symbols*)


weightSymbolHolo[symbol_/;!isHolomorphic[symbol] && isField[symbol]]:= 0;
weightSymbolHolo[symbol_/;isHolomorphic[symbol] && isField[symbol]]:= Module[{weight = fieldProperty[symbol, "WeightHolo"]},
  If[weight === Missing["NotAvailable"], 0, weight]
];

weightHolo[field_/;MatchQ[Head[field], _Symbol] && (!isHolomorphic[Head[field]] && isField[Head[field]])] := 0;
weightHolo[b[der_, z_]] := weightSymbolHolo[b] + der;
weightHolo[c[der_, z_]] := weightSymbolHolo[c] + der;

weightSymbolAntiHolo[symbol_/;(!isAntiHolomorphic[symbol] && isField[symbol])] := 0;
weightSymbolAntiHolo[symbol_/;isAntiHolomorphic[symbol] && isField[symbol]]:= Module[{weight = fieldProperty[symbol, "WeightAntiHolo"]},
  If[weight === Missing["NotAvailable"], 0, weight]
];

weightAntiHolo[field_/;MatchQ[Head[field], _Symbol] && (!isAntiHolomorphic[Head[field]] && isField[Head[field]])] := 0;
weightAntiHolo[bt[der_, zbar_]] := weightSymbolAntiHolo[bt] + der;
weightAntiHolo[ct[der_, zbar_]] := weightSymbolAntiHolo[ct] + der;


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
