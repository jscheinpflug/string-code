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

supportedSignatures::usage = "supportedSignatures[] returns the allowed flat-space target-signature labels.";

currentSignature::usage = "currentSignature[] returns the active flat-space target-signature label.";

setCurrentSignature::usage = "setCurrentSignature[signature] sets the active flat-space target-signature label.";

flatSpaceVectorDimension::usage = "flatSpaceVectorDimension[] returns the target-space vector dimension used by flat-space modules.";

flatSpaceVectorIndexDomain::usage = "flatSpaceVectorIndexDomain[] returns the active public vector-index domain for flat-space tensors.";

flatSpaceVectorIndexSlot::usage = "flatSpaceVectorIndexSlot[idx] maps one active public vector index to its canonical 1-based basis slot, or $Failed.";

flatSpaceMetricHead::usage = "flatSpaceMetricHead[] returns the active inert metric tensor head (\\[Delta] in Euclidean mode, EtaMetric in Lorentzian mode).";

flatSpaceMetricTensor::usage = "flatSpaceMetricTensor[mu, nu] returns one active inert metric tensor factor in the current signature.";

flatSpaceMetricScalar::usage = "flatSpaceMetricScalar[mu, nu] evaluates the active flat-space metric on concrete numeric vector indices.";

flatSpaceMetricTrace::usage = "flatSpaceMetricTrace[] returns the summed diagonal value of the active flat-space metric over the configured vector-index domain.";

(* ::Section:: *)
(*Logic*)


(* ::Subsection:: *)
(*Define index contractions*)


Begin["Private`"];

$currentSignature = "Euclidean";

supportedSignatures[] := {"Euclidean", "Lorentzian"};

currentSignature[] := $currentSignature;

setCurrentSignature::invalid =
  "Unsupported signature `1`. Allowed signatures are `2`.";
setCurrentSignature[signature_String] := Module[{},
  If[!MemberQ[supportedSignatures[], signature],
    Message[setCurrentSignature::invalid, signature, supportedSignatures[]];
    Return[$Failed]
  ];
  $currentSignature = signature
];
setCurrentSignature[_] := $Failed;

flatSpaceVectorDimension[] := 10;

flatSpaceVectorIndexDomain[] := If[
  currentSignature[] === "Lorentzian",
  Range[0, flatSpaceVectorDimension[] - 1],
  Range[1, flatSpaceVectorDimension[]]
];

flatSpaceVectorIndexSlot[idx_Integer] := Module[{pos},
  pos = FirstPosition[flatSpaceVectorIndexDomain[], idx, Missing["NotFound"], {1}, Heads -> False];
  If[pos === Missing["NotFound"], $Failed, First[pos]]
];
flatSpaceVectorIndexSlot[_] := $Failed;

flatSpaceMetricHead[] := If[
  currentSignature[] === "Lorentzian",
  ToExpression["EtaMetric"],
  ToExpression["\[Delta]"]
];

flatSpaceMetricTensor[mu_, nu_] := flatSpaceMetricHead[][mu, nu];

flatSpaceMetricScalar[mu_Integer, nu_Integer] := Module[{slotMu, slotNu},
  slotMu = flatSpaceVectorIndexSlot[mu];
  slotNu = flatSpaceVectorIndexSlot[nu];
  If[slotMu === $Failed || slotNu === $Failed, Return[0]];
  If[currentSignature[] =!= "Lorentzian", KroneckerDelta[slotMu, slotNu], Which[
    slotMu =!= slotNu, 0,
    slotMu == 1, -1,
    True, 1
  ]]
];
flatSpaceMetricScalar[_, _] := 0;

flatSpaceMetricTrace[] := Total[flatSpaceMetricScalar[#, #] & /@ flatSpaceVectorIndexDomain[]];


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

weightHolo[b[der_, z_]] := weightSymbolHolo[b] + der;
weightHolo[c[der_, z_]] := weightSymbolHolo[c] + der;
weightHolo[field_/;MatchQ[Head[field], _Symbol] && isField[Head[field]]] := Module[{symbol = Head[field]},
  evaluateFieldProperty[field, "WeightHolo", If[isHolomorphic[symbol], weightSymbolHolo[symbol], 0]]
];

weightSymbolAntiHolo[symbol_/;(!isAntiHolomorphic[symbol] && isField[symbol])] := 0;
weightSymbolAntiHolo[symbol_/;isAntiHolomorphic[symbol] && isField[symbol]]:= Module[{weight = fieldProperty[symbol, "WeightAntiHolo"]},
  If[weight === Missing["NotAvailable"], 0, weight]
];

weightAntiHolo[bt[der_, zbar_]] := weightSymbolAntiHolo[bt] + der;
weightAntiHolo[ct[der_, zbar_]] := weightSymbolAntiHolo[ct] + der;
weightAntiHolo[field_/;MatchQ[Head[field], _Symbol] && isField[Head[field]]] := Module[{symbol = Head[field]},
  evaluateFieldProperty[field, "WeightAntiHolo", If[isAntiHolomorphic[symbol], weightSymbolAntiHolo[symbol], 0]]
];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
