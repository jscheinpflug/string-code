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
