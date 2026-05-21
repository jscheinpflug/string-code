(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Utils`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`NormalOrdering`"];


(* ::Section:: *)
(*Declare public variables and methods*)


ContractDelta::usage =
  "ContractDelta[expr] contracts repeated Kronecker-delta indices when the active theory/CFT provides contraction rules; the generic implementation is identity.";


AbsorbProfileDerivatives::usage =
  "AbsorbProfileDerivatives[expr] folds FlatSpace profile derivative factors der[profile][idx] into matching ProfileX/ProfileXHolo/ProfileXAntiHolo derivative lists when the active theory/CFT provides absorption rules.";


CanonicalizeDummyIndices::usage =
  "CanonicalizeDummyIndices[expr] renames detected dummy index symbols to a canonical sequence \[Mu]1, \[Mu]2, ... while avoiding collisions with existing non-dummy canonical names.";


OperatorTerms::usage =
  "OperatorTerms[expr] returns the distinct normal-ordered operator terms R[...] appearing additively in expr after expansion.";


OperatorCoefficient::usage =
  "OperatorCoefficient[expr, template] extracts the coefficient of one normal-ordered operator template from expr. The template may be a sum of operators when all matched terms share one common coefficient.";


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


ContractDelta[expr_] := expr;


exprTerms0::usage = "exprTerms0[expr] expands expr and returns its additive terms as a list.";
exprTerms0[expr_] := With[{expanded = Expand[expr]},
  If[Head[expanded] === Plus, List @@ expanded, {expanded}]
];


derivativeHeadQ0::usage =
  "derivativeHeadQ0[expr] is True iff expr has the structural form der[inner].";
derivativeHeadQ0[expr_] := TrueQ @ Replace[
  Unevaluated[expr],
  h_[_] /; Head[h] === Symbol && SymbolName[h] === "der" :> True,
  {0}
];


derivativeApplicationQ0::usage =
  "derivativeApplicationQ0[expr] is True iff expr has head der[...] and one applied derivative index.";
derivativeApplicationQ0[expr_] := derivativeHeadQ0[Head[Unevaluated[expr]]];


extractDerivativeBaseAndIndices0::usage =
  "extractDerivativeBaseAndIndices0[derExpr] returns {base, indices} for nested derivative expressions der[...][idx].";
extractDerivativeBaseAndIndices0[expr_?derivativeApplicationQ0] := Module[{base, indices},
  {base, indices} = extractDerivativeBaseAndIndices0[Head[expr]];
  {base, Append[indices, First[List @@ expr]]}
];
extractDerivativeBaseAndIndices0[expr_ /; derivativeHeadQ0[expr]] := Module[{base, indices},
  {base, indices} = extractDerivativeBaseAndIndices0[expr[[1]]];
  {base, indices}
];
extractDerivativeBaseAndIndices0[base_] := {base, {}};


matchingProfileDerivativeAppendListFromData0::usage =
  "matchingProfileDerivativeAppendListFromData0[derExpr, profile, ders] returns the derivative indices that should be appended to a matching FlatSpace profile derivative list.";
matchingProfileDerivativeAppendListFromData0[derExpr_, profile_, ders_List] := Module[{base, allDers},
  {base, allDers} = extractDerivativeBaseAndIndices0[derExpr];
  If[!SameQ[base, profile],
    Return[{}]
  ];
  If[Length[allDers] > Length[ders] && Take[allDers, Length[ders]] === ders,
    Drop[allDers, Length[ders]],
    If[allDers === {}, {}, {Last[allDers]}]
  ]
];


matchingProfileDerivativeAppendList0::usage =
  "matchingProfileDerivativeAppendList0[derExpr, field] returns the derivative-list suffix that a field can absorb; the generic implementation absorbs nothing.";
matchingProfileDerivativeAppendList0[_, _] := {};


appendProfileDerivativeIndices0::usage =
  "appendProfileDerivativeIndices0[field, indices] appends derivative indices to one profile-like field; the generic implementation leaves the field unchanged.";
appendProfileDerivativeIndices0[field_, _List] := field;


profileDerivativeMatchPositions0::usage =
  "profileDerivativeMatchPositions0[ra, derExpr] returns the operator-field positions inside ra that can absorb derExpr.";
profileDerivativeMatchPositions0[ra_ /; RTest[ra], derExpr_] := Module[{ops = List @@ ra},
  Flatten @ Position[ops, field_ /; matchingProfileDerivativeAppendList0[derExpr, field] =!= {}, {1}]
];


absorbOneProfileDerivativeInOperator0::usage =
  "absorbOneProfileDerivativeInOperator0[ra, derExpr] absorbs one derivative factor into exactly one matching profile field in ra when unambiguous.";
absorbOneProfileDerivativeInOperator0[ra_ /; RTest[ra], derExpr_] := Module[
  {ops = List @@ ra, positions, pos, appendList},
  positions = profileDerivativeMatchPositions0[ra, derExpr];
  If[Length[positions] =!= 1,
    Return[ra]
  ];
  pos = First[positions];
  appendList = matchingProfileDerivativeAppendList0[derExpr, ops[[pos]]];
  ops[[pos]] = appendProfileDerivativeIndices0[ops[[pos]], appendList];
  R @@ ops
];


hasAbsorbableProfileDerivative0::usage =
  "hasAbsorbableProfileDerivative0[ra, derExpr] is True iff derExpr can be absorbed into exactly one profile field in ra.";
hasAbsorbableProfileDerivative0[ra_ /; RTest[ra], derExpr_] :=
  absorbOneProfileDerivativeInOperator0[ra, derExpr] =!= ra;


absorbOneProfileDerivativeInFactor0::usage =
  "absorbOneProfileDerivativeInFactor0[factor, derExpr] absorbs one derivative factor into one matching top-level factor when possible.";
absorbOneProfileDerivativeInFactor0[ra_ /; RTest[ra], derExpr_] :=
  absorbOneProfileDerivativeInOperator0[ra, derExpr];
absorbOneProfileDerivativeInFactor0[field_, derExpr_] := Module[{appendList},
  appendList = matchingProfileDerivativeAppendList0[derExpr, field];
  If[appendList === {},
    field,
    appendProfileDerivativeIndices0[field, appendList]
  ]
];


hasAbsorbableProfileDerivativeInFactor0::usage =
  "hasAbsorbableProfileDerivativeInFactor0[factor, derExpr] is True iff derExpr can be absorbed into factor.";
hasAbsorbableProfileDerivativeInFactor0[factor_, derExpr_] :=
  absorbOneProfileDerivativeInFactor0[factor, derExpr] =!= factor;


profileDerivativeTargetPositions0::usage =
  "profileDerivativeTargetPositions0[factors, derExpr] returns the top-level factor positions that can absorb derExpr.";
profileDerivativeTargetPositions0[factors_List, derExpr_] := Flatten @ Position[
  factors,
  factor_ /; hasAbsorbableProfileDerivativeInFactor0[factor, derExpr],
  {1}
];


absorbOneProfileDerivativeInFactorList0::usage =
  "absorbOneProfileDerivativeInFactorList0[factors, derExpr] absorbs derExpr into exactly one matching top-level factor when unambiguous.";
absorbOneProfileDerivativeInFactorList0[factors_List, derExpr_] := Module[{positions, pos},
  positions = profileDerivativeTargetPositions0[factors, derExpr];
  If[Length[positions] =!= 1,
    Return[factors]
  ];
  pos = First[positions];
  ReplacePart[factors, pos -> absorbOneProfileDerivativeInFactor0[factors[[pos]], derExpr]]
];


hasAbsorbableProfileDerivativeInFactorList0::usage =
  "hasAbsorbableProfileDerivativeInFactorList0[factors, derExpr] is True iff derExpr can be absorbed into exactly one top-level factor.";
hasAbsorbableProfileDerivativeInFactorList0[factors_List, derExpr_] :=
  absorbOneProfileDerivativeInFactorList0[factors, derExpr] =!= factors;


absorbProfileDerivativePower0::usage =
  "absorbProfileDerivativePower0[ra, derExpr, n] repeatedly absorbs derExpr up to n times and returns {newOperator, remainingPower}.";
absorbProfileDerivativePower0[ra_ /; RTest[ra], derExpr_, n_Integer?Positive] := Module[
  {next = ra, remaining = n},
  While[remaining > 0 && hasAbsorbableProfileDerivative0[next, derExpr],
    next = absorbOneProfileDerivativeInOperator0[next, derExpr];
    remaining--
  ];
  {next, remaining}
];


absorbProfileDerivativePowerInFactorList0::usage =
  "absorbProfileDerivativePowerInFactorList0[factors, derExpr, n] repeatedly absorbs derExpr into one top-level factor list up to n times and returns {newFactors, remainingPower}.";
absorbProfileDerivativePowerInFactorList0[factors_List, derExpr_, n_Integer?Positive] := Module[
  {next = factors, remaining = n},
  While[remaining > 0 && hasAbsorbableProfileDerivativeInFactorList0[next, derExpr],
    next = absorbOneProfileDerivativeInFactorList0[next, derExpr];
    remaining--
  ];
  {next, remaining}
];


absorbProfileDerivativesInTerm0::usage =
  "absorbProfileDerivativesInTerm0[term] absorbs profile derivative factors into uniquely matching profile-like factors across one multiplicative term.";
absorbProfileDerivativesInTerm0[term_Times] := Module[
  {factors, derivativeFactorQ, coreFactors, derivativeFactors, newCoreFactors, kept},
  factors = List @@ term;
  derivativeFactorQ = derivativeApplicationQ0[#] || MatchQ[#, Power[_?derivativeApplicationQ0, _Integer?Positive]] &;
  derivativeFactors = Select[factors, derivativeFactorQ];
  If[derivativeFactors === {},
    Return[term]
  ];
  coreFactors = Select[factors, !derivativeFactorQ[#] &];
  If[coreFactors === {},
    Return[term]
  ];
  {newCoreFactors, kept} = Fold[
    Function[{state, factor},
      Module[{currentCoreFactors = state[[1]], currentKept = state[[2]], repeated, derExpr, powerData},
        Which[
          derivativeApplicationQ0[factor],
            If[hasAbsorbableProfileDerivativeInFactorList0[currentCoreFactors, factor],
              {absorbOneProfileDerivativeInFactorList0[currentCoreFactors, factor], currentKept},
              {currentCoreFactors, Append[currentKept, factor]}
            ],
          MatchQ[factor, Power[_?derivativeApplicationQ0, _Integer?Positive]],
            derExpr = factor[[1]];
            repeated = factor[[2]];
            powerData = absorbProfileDerivativePowerInFactorList0[currentCoreFactors, derExpr, repeated];
            If[powerData[[2]] == 0,
              {powerData[[1]], currentKept},
              {powerData[[1]], Append[currentKept, Power[derExpr, powerData[[2]]]]}
            ],
          True,
            {currentCoreFactors, Append[currentKept, factor]}
        ]
      ]
    ],
    {coreFactors, {}},
    derivativeFactors
  ];
  If[newCoreFactors === coreFactors && kept === derivativeFactors,
    term,
    Times @@ Join[kept, newCoreFactors]
  ]
];
absorbProfileDerivativesInTerm0[term_] := term;


absorbProfileDerivativesFixedPoint0::usage =
  "absorbProfileDerivativesFixedPoint0[expr] repeatedly absorbs profile derivative factors across additive terms until stable.";
absorbProfileDerivativesFixedPoint0[expr_] := FixedPoint[
  Module[{terms, absorbedTerms},
    terms = exprTerms0[Expand[#]];
    absorbedTerms = absorbProfileDerivativesInTerm0 /@ terms;
    Expand[Total[absorbedTerms]]
  ] &,
  Expand[expr]
];


dummyIndexCandidateSymbols0::usage =
  "dummyIndexCandidateSymbols0[expr] returns the ordered dummy-index symbol candidates recognized by the active theory/CFT; the generic implementation returns none.";
dummyIndexCandidateSymbols0[_] := {};


dummyIndexProtectedSymbols0::usage =
  "dummyIndexProtectedSymbols0[expr] returns symbols occupying non-dummy index slots that must not be renamed during dummy-index canonicalization.";
dummyIndexProtectedSymbols0[_] := {};


dummyIndexCandidateData0::usage =
  "dummyIndexCandidateData0[expr] returns ordered candidate dummy-index records <|\"Symbol\", \"Class\"|> for the active theory/CFT.";
dummyIndexCandidateData0[expr_] := (<|"Symbol" -> #, "Class" -> "Default"|> &) /@ dummyIndexCandidateSymbols0[expr];


dummyIndexProtectedData0::usage =
  "dummyIndexProtectedData0[expr] returns protected non-dummy index records <|\"Symbol\", \"Class\"|> for the active theory/CFT.";
dummyIndexProtectedData0[expr_] := (<|"Symbol" -> #, "Class" -> "Default"|> &) /@ dummyIndexProtectedSymbols0[expr];


canonicalDummyIndexStem0::usage =
  "canonicalDummyIndexStem0[class, expr] returns the string stem used for one dummy-index class.";
canonicalDummyIndexStem0[_, _] := "\[Mu]";


canonicalDummyIndexNameQ0::usage =
  "canonicalDummyIndexNameQ0[name, stem] tests whether name has the canonical dummy-index form stem<>digits.";
canonicalDummyIndexNameQ0[name_String, stem_String] :=
  StringStartsQ[name, stem] && StringMatchQ[StringDrop[name, StringLength[stem]], NumberString];


canonicalDummyIndexNumber0::usage =
  "canonicalDummyIndexNumber0[name, stem] extracts the numeric suffix from one canonical dummy-index name.";
canonicalDummyIndexNumber0[name_String, stem_String] := ToExpression[StringDrop[name, StringLength[stem]]];


dummyIndexDataKey0::usage =
  "dummyIndexDataKey0[data] returns the {class, symbol} key used to deduplicate typed dummy-index records.";
dummyIndexDataKey0[data_Association] := {data["Class"], data["Symbol"]};


conflictingDummyIndexSymbols0::usage =
  "conflictingDummyIndexSymbols0[data] returns symbols that appear in more than one dummy-index class and are therefore left unchanged.";
conflictingDummyIndexSymbols0[data_List] := Cases[
  GatherBy[data, #["Symbol"] &],
  group_ /; Length[DeleteDuplicates[group[[All, "Class"]]]] > 1 :> group[[1, "Symbol"]]
];


orderedActualDummyIndexData0::usage =
  "orderedActualDummyIndexData0[expr] returns candidate dummy-index records with protected/free and class-conflicting symbols removed, preserving first occurrence order.";
orderedActualDummyIndexData0[expr_] := Module[{candidates, protected, protectedKeys, conflictingSymbols},
  candidates = DeleteDuplicatesBy[dummyIndexCandidateData0[expr], dummyIndexDataKey0];
  protected = DeleteDuplicatesBy[dummyIndexProtectedData0[expr], dummyIndexDataKey0];
  protectedKeys = dummyIndexDataKey0 /@ protected;
  conflictingSymbols = conflictingDummyIndexSymbols0[candidates];
  Select[
    candidates,
    !MemberQ[protectedKeys, dummyIndexDataKey0[#]] && !MemberQ[conflictingSymbols, #["Symbol"]] &
  ]
];


orderedActualDummyIndexSymbols0::usage =
  "orderedActualDummyIndexSymbols0[expr] returns candidate dummy indices with protected/free symbols removed, preserving first-occurrence order.";
orderedActualDummyIndexSymbols0[expr_] := orderedActualDummyIndexData0[expr][[All, "Symbol"]];


occupiedCanonicalDummyIndexNumbers0::usage =
  "occupiedCanonicalDummyIndexNumbers0[expr, dummyData, stem] returns canonical dummy-index numbers already occupied by non-dummy symbols for one canonical name stem.";
occupiedCanonicalDummyIndexNumbers0[expr_, dummyData_List, stem_String] := Module[{dummySymbols, numbers},
  dummySymbols = Cases[
    dummyData,
    data_Association /; canonicalDummyIndexStem0[data["Class"], expr] === stem :> data["Symbol"]
  ];
  numbers = DeleteDuplicates @ Cases[
    expr,
    sym_Symbol /; !MemberQ[dummySymbols, sym] && canonicalDummyIndexNameQ0[SymbolName[sym], stem] :>
      canonicalDummyIndexNumber0[SymbolName[sym], stem],
    Infinity
  ];
  If[numbers === {}, {}, numbers]
];


canonicalDummyIndexSymbols0::usage =
  "canonicalDummyIndexSymbols0[expr, class, count, offset] builds count canonical dummy-index symbols for one class starting at offset.";
canonicalDummyIndexSymbols0[expr_, class_, count_Integer?NonNegative, offset_Integer?Positive] := Module[{stem},
  stem = canonicalDummyIndexStem0[class, expr];
  Symbol[stem <> ToString[#]] & /@ Range[offset, offset + count - 1]
];


canonicalDummyIndexRules0::usage =
  "canonicalDummyIndexRules0[expr] returns the deterministic symbol-renaming rules used by CanonicalizeDummyIndices.";
canonicalDummyIndexRules0[expr_] := Module[{dummyData, stems},
  dummyData = orderedActualDummyIndexData0[expr];
  If[dummyData === {},
    Return[{}]
  ];
  stems = DeleteDuplicates[canonicalDummyIndexStem0[#["Class"], expr] & /@ dummyData];
  Flatten @ Map[
    Function[{stem},
      Module[{stemData, occupiedNumbers, startIndex},
        stemData = Select[dummyData, canonicalDummyIndexStem0[#["Class"], expr] === stem &];
        occupiedNumbers = occupiedCanonicalDummyIndexNumbers0[expr, dummyData, stem];
        startIndex = If[occupiedNumbers === {}, 1, Max[occupiedNumbers] + 1];
        Thread[
          stemData[[All, "Symbol"]] ->
            (Symbol[stem <> ToString[#]] & /@ Range[startIndex, startIndex + Length[stemData] - 1])
        ]
      ]
    ],
    stems
  ]
];


extractScalarAndOperator0::usage =
  "extractScalarAndOperator0[term] splits one additive term into its scalar prefactor and single R[...] factor, or returns Missing when the term does not have exactly one operator factor.";
extractScalarAndOperator0[term_] := Module[{factors, operatorPositions},
  factors = If[Head[term] === Times, List @@ term, {term}];
  operatorPositions = Flatten @ Position[factors, factor_ /; RTest[factor]];
  If[Length[operatorPositions] =!= 1,
    Return[Missing["NoSingleOperator"]]
  ];
  <|
    "Scalar" -> Times @@ Delete[factors, List /@ operatorPositions],
    "Operator" -> factors[[First[operatorPositions]]]
  |>
];


coefficientCarrierFieldQ0::usage =
  "coefficientCarrierFieldQ0[field] marks operator entries that should be factored out of R[...] into the extracted coefficient; the generic implementation factors out nothing.";
coefficientCarrierFieldQ0[_] := False;


extractCoefficientCarrierFactor0::usage =
  "extractCoefficientCarrierFactor0[ops] splits one operator list into extracted coefficient carriers and the core operator entries that remain inside R.";
extractCoefficientCarrierFactor0[ops_List] := Module[{carrierOps, coreOps},
  carrierOps = Select[ops, coefficientCarrierFieldQ0];
  coreOps = Select[ops, !coefficientCarrierFieldQ0[#] &];
  <|
    "Coefficient" -> If[carrierOps === {}, 1, Times @@ carrierOps],
    "CoreOps" -> coreOps
  |>
];


normalizedOperatorTermData0::usage =
  "normalizedOperatorTermData0[term] returns the scalar coefficient and core operator after factoring out configured coefficient-carrying entries from inside one R term.";
normalizedOperatorTermData0[term_] := Module[{splitData, carrierData},
  splitData = extractScalarAndOperator0[term];
  If[Head[splitData] === Missing,
    Return[splitData]
  ];
  carrierData = extractCoefficientCarrierFactor0[List @@ splitData["Operator"]];
  <|
    "Coefficient" -> splitData["Scalar"] carrierData["Coefficient"],
    "Operator" -> R @@ carrierData["CoreOps"]
  |>
];


renamableOperatorSymbols0::usage =
  "renamableOperatorSymbols0[expr] lists the symbols that may be consistently renamed when matching one operator template to another; the generic implementation allows no renaming.";
renamableOperatorSymbols0[_] := {};


canonicalMatchSymbols0::usage =
  "canonicalMatchSymbols0[n] returns the deterministic placeholder symbols used to compare renamable operator structures.";
canonicalMatchSymbols0[n_Integer?NonNegative] := Table[
  Symbol["StringCode`Utils`Private`matchIndex$" <> ToString[i]],
  {i, 1, n}
];


operatorMatchRenameRules0::usage =
  "operatorMatchRenameRules0[termOperator, targetOperator] returns symbol-renaming rules that map one matched operator term to the target operator template, or $Failed when the operators do not match.";
operatorMatchRenameRules0[termOperator_, targetOperator_] := Module[
  {termSymbols, targetSymbols, termCanonical, targetCanonical},
  termSymbols = DeleteDuplicates[renamableOperatorSymbols0[termOperator]];
  targetSymbols = DeleteDuplicates[renamableOperatorSymbols0[targetOperator]];

  If[Length[termSymbols] =!= Length[targetSymbols],
    Return[If[SameQ[termOperator, targetOperator], {}, $Failed]]
  ];

  termCanonical = termOperator /. Thread[termSymbols -> canonicalMatchSymbols0[Length[termSymbols]]];
  targetCanonical = targetOperator /. Thread[targetSymbols -> canonicalMatchSymbols0[Length[targetSymbols]]];

  If[SameQ[termCanonical, targetCanonical],
    Thread[termSymbols -> targetSymbols],
    If[SameQ[termOperator, targetOperator], {}, $Failed]
  ]
];


postProcessMatchedCoefficient0::usage =
  "postProcessMatchedCoefficient0[expr] post-processes one extracted coefficient contribution after operator matching; the generic implementation is identity.";
postProcessMatchedCoefficient0[expr_] := expr;


matchedCoefficientContribution0::usage =
  "matchedCoefficientContribution0[exprTerm, templateTerm] returns the coefficient contribution from one additive expression term relative to one additive operator template term.";
matchedCoefficientContribution0[exprTerm_, templateTerm_] := Module[
  {exprData, templateData, renameRules},
  exprData = normalizedOperatorTermData0[exprTerm];
  templateData = normalizedOperatorTermData0[templateTerm];

  If[Head[exprData] === Missing || Head[templateData] === Missing,
    Return[0]
  ];

  renameRules = operatorMatchRenameRules0[exprData["Operator"], templateData["Operator"]];
  If[renameRules === $Failed,
    Return[0]
  ];

  postProcessMatchedCoefficient0[
    (exprData["Coefficient"] /. renameRules)/templateData["Coefficient"]
  ]
];


singleTemplateCoefficient0::usage =
  "singleTemplateCoefficient0[exprTerms, templateTerm] sums all contributions in exprTerms that match one additive template term.";
singleTemplateCoefficient0[exprTerms_List, templateTerm_] :=
  postProcessMatchedCoefficient0 @ Expand @ Total[matchedCoefficientContribution0[#, templateTerm] & /@ exprTerms];


commonCoefficientQ0::usage =
  "commonCoefficientQ0[coeffs] is True when the extracted coefficient list is pairwise equal up to symbolic simplification.";
commonCoefficientQ0[coeffs_List] := Module[{first},
  If[coeffs === {}, Return[False]];
  first = First[coeffs];
  AllTrue[
    Rest[coeffs],
    Function[coeff,
      SameQ[coeff, first] || TrueQ[Simplify[Expand[coeff - first]] === 0]
    ]
  ]
];


operatorTermKey0::usage =
  "operatorTermKey0[op] provides a stable textual key for deduplicating operator terms.";
operatorTermKey0[op_] := ToString[InputForm[op]];


AbsorbProfileDerivatives[expr_] := absorbProfileDerivativesFixedPoint0[expr];


CanonicalizeDummyIndices[expr_] := Module[
  {renamingRules},
  renamingRules = canonicalDummyIndexRules0[expr];
  If[renamingRules === {},
    Return[expr]
  ];
  expr /. renamingRules
];


OperatorTerms[expr_] := DeleteDuplicatesBy[
  Cases[
    normalizedOperatorTermData0 /@ exprTerms0[expr],
    data_Association :> data["Operator"]
  ],
  operatorTermKey0
];


OperatorCoefficient::notemplate =
  "Template `1` does not contain any additive term with exactly one normal-ordered operator factor.";
OperatorCoefficient::nonuniform =
  "Template `1` does not have one common coefficient in the expression; extracted coefficients were `2`.";

OperatorCoefficient[expr_, template_] := Module[{templateTerms, exprTerms, coefficients},
  templateTerms = Select[exprTerms0[template], Head[extractScalarAndOperator0[#]] =!= Missing &];
  If[templateTerms === {},
    Message[OperatorCoefficient::notemplate, HoldForm[template]];
    Return[$Failed]
  ];

  exprTerms = exprTerms0[expr];
  coefficients = singleTemplateCoefficient0[exprTerms, #] & /@ templateTerms;

  If[Length[coefficients] == 1,
    Return[First[coefficients]]
  ];

  If[commonCoefficientQ0[coefficients],
    First[coefficients],
    Message[OperatorCoefficient::nonuniform, HoldForm[template], coefficients];
    $Failed
  ]
];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
