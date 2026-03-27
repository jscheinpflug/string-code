(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Correlators`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`Wick`"];
Needs["StringCode`OPE`"];
Needs["StringCode`Operators`"];


(* ::Section:: *)
(*Declare public methods*)


Corr::usage = "Computes worldsheet correlators for supported free-field sectors and leaves unsupported residual sectors symbolic.";
Vev::usage = "Evaluates the zero-mode/background-charge part of a local operator after contractions.";


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


$VevTopFormSectors::usage = "$VevTopFormSectors stores registered top-form VEV sectors keyed by sector name.";
$VevTopFormSectors = <||>;

$VevChargeSectors::usage = "$VevChargeSectors stores registered charge VEV sectors keyed by sector name.";
$VevChargeSectors = <||>;

$TopFormModeCutoffByHead::usage = "$TopFormModeCutoffByHead maps heads used in top-form sectors to the largest mode needed during localization.";
$TopFormModeCutoffByHead = <||>;


registerTopFormVevSector::usage = "registerTopFormVevSector[name, basis, normalization, killHeads] registers a top-form VEV sector.";
registerTopFormVevSector[name_String, basis_List, normalization_, killHeads_List : {}] := Module[
  {heads, modeCutoffs},
  heads = DeleteDuplicates[Head /@ basis];
  modeCutoffs = Association @ KeyValueMap[
    Function[{head, fields}, head -> Max[Replace[fields, field_ :> field[[1]], {1}] ]],
    GroupBy[basis, Head]
  ];
  $VevTopFormSectors[name] = <|
    "Basis" -> basis,
    "Heads" -> heads,
    "KillHeads" -> DeleteDuplicates[killHeads],
    "Normalization" -> normalization
  |>;
  KeyValueMap[($TopFormModeCutoffByHead[#1] = #2) &, modeCutoffs];
  name
];


registerChargeVevSector::usage = "registerChargeVevSector[name, chargeHeads, backgroundCharge, triggerHeads, killHeads, bosonizeFunction, chargeExtractor, normalization] registers a charge VEV sector.";
registerChargeVevSector[
  name_String,
  chargeHeads_List,
  backgroundCharge_,
  triggerHeads_List,
  killHeads_List : {},
  bosonizeFunction_ : Identity,
  chargeExtractor_ : (#[[1]] &),
  normalization_ : 1
] := (
  $VevChargeSectors[name] = <|
    "ChargeHeads" -> DeleteDuplicates[chargeHeads],
    "BackgroundCharge" -> backgroundCharge,
    "TriggerHeads" -> DeleteDuplicates[triggerHeads],
    "KillHeads" -> DeleteDuplicates[killHeads],
    "BosonizeFunction" -> bosonizeFunction,
    "ChargeExtractor" -> chargeExtractor,
    "Normalization" -> normalization
  |>;
  name
);


CorrWickList::usage = "CorrWickList[rList] evaluates the free-sector local operator product and then applies Vev to the result.";
CorrWickList[rList_List] := Vev[corrOpeOfRList[rList]];


corrEvaluableRListQ::usage = "corrEvaluableRListQ[rList] is the shared-private predicate used by Corr to decide whether a list of local operators has a supported generic free-sector evaluation path.";
corrEvaluableRListQ[rList_List] := AnyTrue[rList, hasCollapsable];


corrEntirelyFreeQ::usage = "corrEntirelyFreeQ[rList] is the shared-private predicate used by Corr to route a list of operators directly to CorrWickList without collapsable splitting.";
corrEntirelyFreeQ[_List] := False;


corrOpeOfRList::usage = "corrOpeOfRList[rList] folds OPE over a list of local operators.";
corrOpeOfRList[rList_List] := Which[
  rList === {}, 1,
  Length[rList] == 1, First[rList],
  True, OPE @@ rList
];


corrMultiplyFactors::usage = "corrMultiplyFactors[a, b] multiplies correlator factors while simplifying identities for 0 and 1.";
corrMultiplyFactors[a_, b_] := Which[
  a === 0 || b === 0, 0,
  a === 1, b,
  b === 1, a,
  True, a b
];


corrFieldWeightHolo::usage = "corrFieldWeightHolo[field] gives the holomorphic conformal weight used by the internal Infinity/BPZ correlator limits.";
corrFieldWeightHolo[field_ /; MemberQ[{"expϕf", "expϕb"}, SymbolName[Head[field]]]] := -field[[1]] (field[[1]] + 2)/2;
corrFieldWeightHolo[field_ /; isField[Head[field]]] := weightHolo[field];


corrFieldWeightAntiHolo::usage = "corrFieldWeightAntiHolo[field] gives the antiholomorphic conformal weight used by the internal Infinity/BPZ correlator limits.";
corrFieldWeightAntiHolo[field_ /; MemberQ[{"expϕtf", "expϕtb"}, SymbolName[Head[field]]]] := -field[[1]] (field[[1]] + 2)/2;
corrFieldWeightAntiHolo[field_ /; isField[Head[field]]] := weightAntiHolo[field];


corrOperatorWeightHolo::usage = "corrOperatorWeightHolo[Ra] sums the holomorphic weights of all fields in a local operator for the internal Infinity/BPZ limit.";
corrOperatorWeightHolo[Ra_ /; RTest[Ra]] := Total[corrFieldWeightHolo /@ (List @@ Ra)];


corrOperatorWeightAntiHolo::usage = "corrOperatorWeightAntiHolo[Ra] sums the antiholomorphic weights of all fields in a local operator for the internal Infinity/BPZ limit.";
corrOperatorWeightAntiHolo[Ra_ /; RTest[Ra]] := Total[corrFieldWeightAntiHolo /@ (List @@ Ra)];


containsInfinityInsertionQ::usage = "containsInfinityInsertionQ[expr] is True when expr contains a literal Infinity insertion coordinate.";
containsInfinityInsertionQ[expr_] := !FreeQ[expr, Infinity];


containsInfinityHoloQ::usage = "containsInfinityHoloQ[Ra] is True when a local operator contains a holomorphic field inserted at Infinity.";
containsInfinityHoloQ[Ra_ /; RTest[Ra]] := AnyTrue[List @@ Ra, Function[field,
  isField[Head[field]] && isHolomorphic[Head[field]] && (
    (isAntiHolomorphic[Head[field]] && field[[-2]] === Infinity) ||
    (!isAntiHolomorphic[Head[field]] && field[[-1]] === Infinity)
  )
]];


containsInfinityAntiHoloQ::usage = "containsInfinityAntiHoloQ[Ra] is True when a local operator contains an antiholomorphic field inserted at Infinity.";
containsInfinityAntiHoloQ[Ra_ /; RTest[Ra]] := AnyTrue[List @@ Ra, Function[field,
  isField[Head[field]] && isAntiHolomorphic[Head[field]] && (
    (isHolomorphic[Head[field]] && field[[-1]] === Infinity) ||
    (!isHolomorphic[Head[field]] && field[[-1]] === Infinity)
  )
]];


replaceInfinityField::usage = "replaceInfinityField[field, uH, uA] replaces literal Infinity coordinates in one field by finite placeholders.";
replaceInfinityField[field_ /; isField[Head[field]] && isHolomorphic[Head[field]] && isAntiHolomorphic[Head[field]], uH_, uA_] := Module[
  {args = List @@ field, h = Head[field], z, zbar},
  z = If[args[[-2]] === Infinity, uH, args[[-2]]];
  zbar = If[args[[-1]] === Infinity, uA, args[[-1]]];
  h @@ Join[Drop[args, -2], {z, zbar}]
];
replaceInfinityField[field_ /; isField[Head[field]] && isHolomorphic[Head[field]], uH_, uA_] := Module[
  {args = List @@ field, h = Head[field], z},
  z = If[args[[-1]] === Infinity, uH, args[[-1]]];
  h @@ Join[Drop[args, -1], {z}]
];
replaceInfinityField[field_ /; isField[Head[field]] && isAntiHolomorphic[Head[field]], uH_, uA_] := Module[
  {args = List @@ field, h = Head[field], zbar},
  zbar = If[args[[-1]] === Infinity, uA, args[[-1]]];
  h @@ Join[Drop[args, -1], {zbar}]
];
replaceInfinityField[field_, _, _] := field;


replaceInfinityInR::usage = "replaceInfinityInR[Ra, uH, uA] replaces literal Infinity coordinates in a local operator by finite placeholders.";
replaceInfinityInR[Ra_ /; RTest[Ra], uH_, uA_] := R @@ (replaceInfinityField[#, uH, uA] & /@ (List @@ Ra));


corrWithInfinity::usage = "corrWithInfinity[rList] evaluates correlators with insertions at Infinity by BPZ-weighted finite-point limits.";
corrWithInfinity[rList_List] := Module[{data, expr, limitRules},
  data = Map[
    Function[Ra,
      Module[{uH = Unique["uH"], uA = Unique["uA"], weightFactor = 1, rules = {}, replaced = Ra},
        If[containsInfinityHoloQ[Ra],
          replaced = replaceInfinityInR[replaced, uH, uA];
          weightFactor = weightFactor uH^(2 corrOperatorWeightHolo[Ra]);
          AppendTo[rules, uH -> Infinity];
        ];
        If[containsInfinityAntiHoloQ[Ra],
          replaced = replaceInfinityInR[replaced, uH, uA];
          weightFactor = weightFactor uA^(2 corrOperatorWeightAntiHolo[Ra]);
          AppendTo[rules, uA -> Infinity];
        ];
        <|"Operator" -> replaced, "WeightFactor" -> weightFactor, "LimitRules" -> rules|>
      ]
    ],
    rList
  ];
  expr = Times @@ Lookup[data, "WeightFactor"] corrRList[Lookup[data, "Operator"]];
  limitRules = Flatten[Lookup[data, "LimitRules"], 1];
  Fold[Function[{acc, rule}, Limit[acc, Evaluate[rule]]], expr, limitRules]
];


corrRList::usage = "corrRList[rList] is the shared-private engine for Corr on local operator lists.";
corrRList[rList_List] := Module[{splitData, freeList, residualList, signFactor, freeFactor, residualFactor},
  If[corrEntirelyFreeQ[rList], Return[CorrWickList[rList]]];
  splitData = splitCollapsable /@ rList;
  freeList = Select[splitData[[All, 1]], # =!= 1 &];
  residualList = Select[splitData[[All, 2]], # =!= 1 &];
  signFactor = Times @@ splitData[[All, 3]];
  If[freeList === {}, Return[Unevaluated[Apply[Corr, rList]]]];
  freeFactor = signFactor CorrWickList[freeList];
  residualFactor = Which[
    residualList === {}, 1,
    Length[residualList] == 1, Corr[First[residualList]],
    True, Apply[Corr, residualList]
  ];
  corrMultiplyFactors[freeFactor, residualFactor]
];


extractScalarAndRest::usage = "extractScalarAndRest[expr] separates scalar factors from the remaining nonscalar expression inside one Vev term.";
extractScalarAndRest[expr_Times] := Module[{factors = List @@ expr, scalarFactors, nonScalarFactors},
  scalarFactors = Select[factors, isScalarFactorQ];
  nonScalarFactors = Select[factors, Not @* isScalarFactorQ];
  {
    If[scalarFactors === {}, 1, Times @@ scalarFactors],
    Which[
      nonScalarFactors === {}, 1,
      Length[nonScalarFactors] == 1, First[nonScalarFactors],
      True, Times @@ nonScalarFactors
    ]
  }
];
extractScalarAndRest[expr_] := {1, expr};


dropFieldInstances::usage = "dropFieldInstances[fields, toDrop] removes one instance of each field in toDrop from fields while preserving the remaining order.";
dropFieldInstances[fields_List, toDrop_List] := Fold[
  Function[{current, field}, DeleteCases[current, field, 1, 1]],
  fields,
  toDrop
];


fieldsToExpr::usage = "fieldsToExpr[fields] rebuilds a localized scalar or normal-ordered product from a field list.";
fieldsToExpr[fields_List] := Which[
  fields === {}, 1,
  True, Block[{needsOrdering = False}, R @@ fields]
];


topFormSectorPresentQ::usage = "topFormSectorPresentQ[fields, sector] is True when any field in fields belongs to a top-form sector or its kill set.";
topFormSectorPresentQ[fields_List, sector_Association] := AnyTrue[fields, MemberQ[Join[sector["Heads"], sector["KillHeads"]], Head[#]] &];


applyTopFormSectorToR::usage = "applyTopFormSectorToR[Ra, sector] applies one registered top-form sector to a localized normal-ordered term.";
applyTopFormSectorToR[1, _Association] := {1, 1};
applyTopFormSectorToR[Ra_ /; RTest[Ra], sector_Association] := Module[{fields = List @@ Ra, sectorFields, killPresent, restFields},
  If[!topFormSectorPresentQ[fields, sector], Return[{1, Ra}]];
  killPresent = AnyTrue[fields, MemberQ[sector["KillHeads"], Head[#]] &];
  If[killPresent, Return[{0, 1}]];
  sectorFields = Select[fields, MemberQ[sector["Heads"], Head[#]] &];
  If[sectorFields === {}, Return[{1, Ra}]];
  If[sectorFields =!= sector["Basis"], Return[{0, 1}]];
  restFields = dropFieldInstances[fields, sectorFields];
  {sector["Normalization"], fieldsToExpr[restFields]}
];


chargeSectorTriggeredQ::usage = "chargeSectorTriggeredQ[expr, sector] is True when expr contains any trigger head for the given charge sector.";
chargeSectorTriggeredQ[expr_, sector_Association] := !FreeQ[expr, field_ /; MemberQ[sector["TriggerHeads"], Head[field]]];


prepareChargeSectors::usage = "prepareChargeSectors[expr] applies any registered bosonization/preparation functions needed before charge-sector VEV evaluation.";
prepareChargeSectors[expr_] := Fold[
  Function[{current, sector}, If[chargeSectorTriggeredQ[current, sector], sector["BosonizeFunction"][current], current]],
  expr,
  Values[$VevChargeSectors]
];


applyChargeSectorToR::usage = "applyChargeSectorToR[Ra, sector] applies one registered charge sector to a localized normal-ordered term.";
applyChargeSectorToR[1, _Association] := {1, 1};
applyChargeSectorToR[Ra_ /; RTest[Ra], sector_Association] := Module[{fields = List @@ Ra, killPresent, chargeFields, restFields, totalCharge},
  If[!AnyTrue[fields, MemberQ[Join[sector["ChargeHeads"], sector["KillHeads"]], Head[#]] &], Return[{1, Ra}]];
  killPresent = AnyTrue[fields, MemberQ[sector["KillHeads"], Head[#]] &];
  If[killPresent, Return[{0, 1}]];
  chargeFields = Select[fields, MemberQ[sector["ChargeHeads"], Head[#]] &];
  If[chargeFields === {}, Return[{1, Ra}]];
  totalCharge = Total[sector["ChargeExtractor"] /@ chargeFields];
  If[!TrueQ[totalCharge == sector["BackgroundCharge"]], Return[{0, 1}]];
  restFields = dropFieldInstances[fields, chargeFields];
  {sector["Normalization"], fieldsToExpr[restFields]}
];


localizeTopFormFieldAtOrigin::usage = "localizeTopFormFieldAtOrigin[field, maxMode] expands a top-form field around the origin up to the maximum needed mode.";
localizeTopFormFieldAtOrigin[field_, maxMode_Integer?NonNegative] := Module[{head = Head[field], mode = field[[1]], coord = field[[-1]], upper},
  upper = Max[0, maxMode - mode];
  Sum[
    If[i == 0, head[mode, 0], (coord^i/i!) head[mode + i, 0]],
    {i, 0, upper}
  ]
];


localizeFieldAtOrigin::usage = "localizeFieldAtOrigin[field] moves a supported field to the origin, expanding top-form fields only as far as needed for zero-mode saturation.";
localizeFieldAtOrigin[field_ /; isField[Head[field]] && KeyExistsQ[$TopFormModeCutoffByHead, Head[field]]] :=
  localizeTopFormFieldAtOrigin[field, $TopFormModeCutoffByHead[Head[field]]];
localizeFieldAtOrigin[field_ /; isField[Head[field]] && isHolomorphic[Head[field]] && isAntiHolomorphic[Head[field]]] := Module[
  {args = List @@ field, head = Head[field]},
  head @@ Join[Drop[args, -2], {0, 0}]
];
localizeFieldAtOrigin[field_ /; isField[Head[field]] && (isHolomorphic[Head[field]] || isAntiHolomorphic[Head[field]])] := Module[
  {args = List @@ field, head = Head[field]},
  head @@ Join[Drop[args, -1], {0}]
];
localizeFieldAtOrigin[field_] := field;


localizeRAtOrigin::usage = "localizeRAtOrigin[Ra] moves every field in a local operator to the origin with the truncations required by registered VEV sectors.";
localizeRAtOrigin[Ra_ /; RTest[Ra]] := R @@ (localizeFieldAtOrigin /@ (List @@ Ra));


finalizeVevR::usage = "finalizeVevR[Ra] converts the localized residual operator left after known sector evaluation into a scalar, zero, or residual origin operator.";
finalizeVevR[1] := 1;
finalizeVevR[Ra_ /; RTest[Ra]] := Module[{fields = List @@ Ra},
  If[AnyTrue[fields, isSimple[Head[#]] &],
    0,
    fieldsToExpr[fields]
  ]
];
finalizeVevR[expr_] := expr;


applySectorListToState::usage = "applySectorListToState[state, sectors, applier] threads a {factor, operator} state through a list of registered VEV sectors.";
applySectorListToState[0, _List, _] := 0;
applySectorListToState[state : {_, _}, sectors_List, applier_] := Fold[
  Function[{currentState, sector},
    If[currentState === 0,
      0,
      Module[{stateFactor, stateOperator, sectorFactor, nextOperator},
        {stateFactor, stateOperator} = currentState;
        {sectorFactor, nextOperator} = applier[stateOperator, sector];
        If[sectorFactor === 0,
          0,
          {stateFactor sectorFactor, nextOperator}
        ]
      ]
    ]
  ],
  state,
  sectors
];


vevEvaluateTerm::usage = "vevEvaluateTerm[term] evaluates one localized term of a Vev expression.";
vevEvaluateTerm[0] := 0;
vevEvaluateTerm[expr_ /; isScalarFactorQ[expr]] := expr;
vevEvaluateTerm[expr_Times] := Module[{scalar, rest},
  {scalar, rest} = extractScalarAndRest[expr];
  Which[
    rest === 1, scalar,
    True, scalar vevEvaluateTerm[rest]
  ]
];
vevEvaluateTerm[Ra_ /; RTest[Ra]] := Module[{state},
  state = applySectorListToState[{1, Ra}, Values[$VevTopFormSectors], applyTopFormSectorToR];
  state = applySectorListToState[state, Values[$VevChargeSectors], applyChargeSectorToR];
  If[state === 0,
    0,
    state[[1]] finalizeVevR[state[[2]]]
  ]
];
vevEvaluateTerm[expr_] := expr;


vevEvaluateExpandedExpr::usage = "vevEvaluateExpandedExpr[expr] evaluates Vev term-by-term on an already localized and prepared expression.";
vevEvaluateExpandedExpr[expr_] := Module[{terms},
  terms = If[Head[expr] === Plus, List @@ expr, {expr}];
  Total[vevEvaluateTerm /@ terms]
];


Vev[0] := 0;
Vev[a_ + b_] := Vev[a] + Vev[b];
Vev[expr_Times] := Module[{scalar, rest},
  {scalar, rest} = extractScalarAndRest[expr];
  Which[
    rest === 1, scalar,
    True, scalar Vev[rest]
  ]
];
Vev[expr_ /; isScalarFactorQ[expr]] := expr;
Vev[Ra_ /; RTest[Ra]] := Module[{localized},
  localized = prepareChargeSectors[localizeRAtOrigin[Ra]];
  vevEvaluateExpandedExpr[Expand[localized]]
];


Corr[] := 1;
Corr[a___, 0, b___] := 0;
Corr[a___, x_ + y_, b___] := Corr[a, x, b] + Corr[a, y, b];
Corr[a___, c_ x_, b___] := c Corr[a, x, b] /; isScalarFactorQ[c];
Corr[a___, Ma_ /; MultiOpTest[Ma], b___] := Corr[a, Sequence @@ (List @@ Ma), b];
Corr[ops__ /; (AllTrue[{ops}, RTest] && AnyTrue[{ops}, containsInfinityInsertionQ] && corrEvaluableRListQ[{ops}])] := corrWithInfinity[{ops}];
Corr[ops__ /; (AllTrue[{ops}, RTest] && corrEvaluableRListQ[{ops}])] := corrRList[{ops}];


registerTopFormVevSector[
  "bc-holo",
  {c[0, 0], c[1, 0], c[2, 0]},
  -2,
  {b}
];

registerTopFormVevSector[
  "bc-anti",
  {ct[0, 0], ct[1, 0], ct[2, 0]},
  -2,
  {bt}
];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
