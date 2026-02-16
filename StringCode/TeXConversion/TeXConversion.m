(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`TeXConversion`"]
Needs["StringCode`Symbols`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`Operators`"];


(* ::Section:: *)
(*Declare public variables and methods*)


ToTeX::usage = "ToTeX[expr, opts] converts a StringCode expression to a TeX string. Options: \"OutputMode\", \"DifferentialNotation\", \"CanonicalizeWedgeOrder\", \"BracketFormatting\".";


(* ::Section:: *)
(*Private section*)


Begin["Private`"];


(* ::Section:: *)
(*Options*)


Options[ToTeX] = {
  "OutputMode" -> "Inline",
  "DifferentialNotation" -> "Compact",
  "CanonicalizeWedgeOrder" -> True,
  "BracketFormatting" -> True
};


normalizeToTeXOptions::usage = "normalizeToTeXOptions[userOpts] validates ToTeX options and fills defaults.";
normalizeToTeXOptions[userOpts_List] := Module[{opts},
  opts = Association[Join[Options[ToTeX], userOpts]];

  If[!MemberQ[{"Inline", "Display"}, opts["OutputMode"]],
    opts["OutputMode"] = "Inline"
  ];

  If[!MemberQ[{"Compact", "Functional", "Auto"}, opts["DifferentialNotation"]],
    opts["DifferentialNotation"] = "Compact"
  ];

  If[!MemberQ[{True, False}, opts["CanonicalizeWedgeOrder"]],
    opts["CanonicalizeWedgeOrder"] = True
  ];

  If[!MemberQ[{True, False}, opts["BracketFormatting"]],
    opts["BracketFormatting"] = True
  ];

  opts
];


ToTeX[expr_, opts : OptionsPattern[]] := Module[{settings, rendered},
  settings = normalizeToTeXOptions[{opts}];
  rendered = toTeXDispatch[expr, settings];
  If[settings["OutputMode"] === "Display",
    "\\[" <> rendered <> "\\]",
    rendered
  ]
];


(* ::Section:: *)
(*Shared helpers*)


mathToTeX::usage = "mathToTeX[expr] uses TeXForm as a fallback and strips wrapper artifacts used by Mathematica string output.";
mathToTeX[expr_] := StringReplace[
  ToString[TeXForm[expr]],
  {
    "$" -> "",
    "\\text{" ~~ x : Shortest[__] ~~ "}" :> x,
    "\n" -> " "
  }
];


formatIndex::usage = "formatIndex[idx] converts an index-like expression to TeX.";
formatIndex[idx_, opts_Association] := toTeXDispatch[idx, opts];


derivativePrefix::usage = "derivativePrefix[n, holo] gives TeX for derivative operator prefixes.";
derivativePrefix[0, holo_ : True] := "";
derivativePrefix[1, True] := "\\partial ";
derivativePrefix[1, False] := "\\bar{\\partial} ";
derivativePrefix[n_, True] := "\\partial^" <> ToString[n] <> " ";
derivativePrefix[n_, False] := "\\bar{\\partial}^" <> ToString[n] <> " ";


formatPosition::usage = "formatPosition[...] formats insertion positions for local operators.";
formatPosition[0, opts_Association] := "";
formatPosition[0, 0, opts_Association] := "(0)";
formatPosition[z_, opts_Association] := "(" <> toTeXDispatch[z, opts] <> ")";
formatPosition[z_, zbar_, opts_Association] := "(" <> toTeXDispatch[z, opts] <> ", " <> toTeXDispatch[zbar, opts] <> ")";


needsParenthesesQ::usage = "needsParenthesesQ[expr] is True when expr should be parenthesized in multiplicative/exponent contexts.";
needsParenthesesQ[expr_] := MatchQ[expr, _Plus | _Rule | _RuleDelayed];


wrapIfNeeded::usage = "wrapIfNeeded[expr, opts] formats expr and wraps it in \\left(\\right) when required by context.";
wrapIfNeeded[expr_, opts_Association] := Module[{rendered},
  rendered = toTeXDispatch[expr, opts];
  If[needsParenthesesQ[expr], "\\left(" <> rendered <> "\\right)", rendered]
];


numericFactorQ::usage = "numericFactorQ[expr] checks whether expr is a purely numeric factor handled as a coefficient.";
numericFactorQ[expr_] := MatchQ[expr, _Integer | _Rational | _Real | Complex[_, _]];


stripLeadingMinus::usage = "stripLeadingMinus[str] removes a leading minus sign and trims leading whitespace.";
stripLeadingMinus[str_String] := StringTrim[StringDrop[str, 1]];


(* ::Section:: *)
(*Bracket-oriented helpers*)


localCoordinateData::usage = "localCoordinateData[expr] extracts {baseName, order, index} from known local coordinate symbols.";
localCoordinateData[(head_Symbol)[order_, index_][___]] := localCoordinateData[head[order, index]];
localCoordinateData[head_Symbol[order_, index_]] := Module[{name = SymbolName[Unevaluated[head]], baseName},
  baseName = Switch[name,
    "z" | "zR", "z",
    "zbar" | "zbarR", "\\bar{z}",
    "q" | "qR", "q",
    "qbar" | "qbarR", "\\bar{q}",
    _, $Failed
  ];
  If[baseName === $Failed, $Failed, {baseName, order, index}]
];
localCoordinateData[_] := $Failed;


formatLocalCoordinate::usage = "formatLocalCoordinate[expr, opts] renders local coordinate symbols in canonical indexed form.";
formatLocalCoordinate[expr_, opts_Association] := Module[{data, baseName, indexTeX},
  data = localCoordinateData[expr];
  If[data === $Failed, Return[mathToTeX[expr]]];
  baseName = data[[1]];
  indexTeX = toTeXDispatch[data[[3]], opts];
  baseName <> "_{" <> indexTeX <> "}"
];


formatDifferential::usage = "formatDifferential[expr, moduli, opts] renders Differential[...] according to the selected notation mode.";
formatDifferential[expr_, moduli_, opts_Association] := Module[{notation, data, localTex},
  notation = opts["DifferentialNotation"];

  If[notation === "Functional",
    Return["d\\left(" <> toTeXDispatch[expr, opts] <> "\\right)"]
  ];

  data = localCoordinateData[expr];
  If[data =!= $Failed,
    localTex = formatLocalCoordinate[expr, opts];
    Return["d" <> localTex]
  ];

  If[notation === "Auto" || notation === "Compact",
    "d\\left(" <> toTeXDispatch[expr, opts] <> "\\right)",
    "d\\left(" <> toTeXDispatch[expr, opts] <> "\\right)"
  ]
];


canonicalizeWedgeArgs::usage = "canonicalizeWedgeArgs[args] returns {sign, sortedArgs} using lexical canonical ordering for display.";
canonicalizeWedgeArgs[args_List] := Module[{keys, ord, sign},
  keys = ToString[InputForm[#]] & /@ args;
  ord = Ordering[keys];
  sign = Signature[ord];
  If[sign === 0, {0, args}, {sign, args[[ord]]}]
];


formatWedge::usage = "formatWedge[args, opts] renders wedge products with optional canonicalized argument ordering.";
formatWedge[args_List, opts_Association] := Module[{flatArgs, sign = 1, orderedArgs, texPieces},
  flatArgs = Flatten[args /. {
      Verbatim[Private`Wedge][a___] :> {a},
      Verbatim[System`Wedge][a___] :> {a}
    }];

  If[flatArgs === {}, Return["1"]];

  If[TrueQ[opts["CanonicalizeWedgeOrder"]],
    {sign, orderedArgs} = canonicalizeWedgeArgs[flatArgs],
    orderedArgs = flatArgs
  ];

  If[sign === 0, Return["0"]];

  texPieces = toTeXDispatch[#, opts] & /@ orderedArgs;
  If[sign === -1,
    "-" <> StringRiffle[texPieces, " \\wedge "],
    StringRiffle[texPieces, " \\wedge "]
  ]
];


(* ::Section:: *)
(*Dispatch rules*)


toTeXDispatch::usage = "toTeXDispatch[expr, opts] is the internal recursive TeX renderer used by ToTeX.";


(* Wrapper conversions *)
toTeXDispatch[Ra_ /; RTest[Ra], opts_Association] :=
  ":" <> StringJoin[toTeXDispatch[#, opts] & /@ (List @@ Ra)] <> ":";

toTeXDispatch[Verbatim[MultiOp][ops__], opts_Association] :=
  StringRiffle[toTeXDispatch[#, opts] & /@ {ops}, " \\otimes "];

toTeXDispatch[Verbatim[Global`Op][expr_], opts_Association] := toTeXDispatch[expr, opts];
toTeXDispatch[Verbatim[Global`Op][expr_, rest__], opts_Association] :=
  ":" <> StringRiffle[toTeXDispatch[#, opts] & /@ {expr, rest}, " "] <> ":";

toTeXDispatch[Verbatim[Op][expr_], opts_Association] := toTeXDispatch[expr, opts];
toTeXDispatch[Verbatim[Op][expr_, rest__], opts_Association] :=
  ":" <> StringRiffle[toTeXDispatch[#, opts] & /@ {expr, rest}, " "] <> ":";

toTeXDispatch[Verbatim[Interacting][expr_], opts_Association] :=
  "\\mathcal{I}\\left(" <> toTeXDispatch[expr, opts] <> "\\right)";


(* Ghost fields *)
toTeXDispatch[c[n_, z_], opts_Association] := derivativePrefix[n, True] <> "c" <> formatPosition[z, opts];
toTeXDispatch[b[n_, z_], opts_Association] := derivativePrefix[n, True] <> "b" <> formatPosition[z, opts];
toTeXDispatch[ct[n_, zbar_], opts_Association] := derivativePrefix[n, False] <> "\\bar{c}" <> formatPosition[zbar, opts];
toTeXDispatch[bt[n_, zbar_], opts_Association] := derivativePrefix[n, False] <> "\\bar{b}" <> formatPosition[zbar, opts];


(* Kronecker delta *)
toTeXDispatch[\[Delta][idx1_, idx2_], opts_Association] :=
  "\\delta_{" <> formatIndex[idx1, opts] <> formatIndex[idx2, opts] <> "}";


(* Bracket-generated structures *)
toTeXDispatch[Verbatim[Differential][expr_, moduli_], opts_Association] /; TrueQ[opts["BracketFormatting"]] :=
  formatDifferential[expr, moduli, opts];

toTeXDispatch[Verbatim[Private`Wedge][args___], opts_Association] /; TrueQ[opts["BracketFormatting"]] :=
  formatWedge[{args}, opts];

toTeXDispatch[Verbatim[System`Wedge][args___], opts_Association] /; TrueQ[opts["BracketFormatting"]] :=
  formatWedge[{args}, opts];


toTeXDispatch[expr_, opts_Association] /; localCoordinateData[expr] =!= $Failed :=
  formatLocalCoordinate[expr, opts];


(* Arithmetic conversions *)
toTeXDispatch[Verbatim[Plus][terms__], opts_Association] := Module[{termList = {terms}, result = "", termTeX, i},
  For[i = 1, i <= Length[termList], i++,
    termTeX = toTeXDispatch[termList[[i]], opts];
    If[i == 1,
      result = termTeX,
      If[StringStartsQ[termTeX, "-"],
        result = result <> " - " <> stripLeadingMinus[termTeX],
        result = result <> " + " <> termTeX
      ]
    ]
  ];
  result
];


toTeXDispatch[Verbatim[Times][factors__], opts_Association] := Module[
  {factorList = {factors}, numericPart, nonNumericParts, prefix, renderedFactors},

  numericPart = Times @@ Select[factorList, numericFactorQ];
  nonNumericParts = Select[factorList, !numericFactorQ[#] &];

  If[nonNumericParts === {}, Return[toTeXDispatch[numericPart, opts]]];
  If[numericPart === 0, Return["0"]];

  prefix = Which[
    numericPart === 1, "",
    numericPart === -1, "-",
    True, toTeXDispatch[numericPart, opts] <> " "
  ];

  renderedFactors = wrapIfNeeded[#, opts] & /@ nonNumericParts;
  StringTrim[prefix <> StringRiffle[renderedFactors, " "]]
];


toTeXDispatch[Verbatim[Power][base_, exp_], opts_Association] := Which[
  exp === 1/2,
  "\\sqrt{" <> toTeXDispatch[base, opts] <> "}",

  exp === -1,
  "\\frac{1}{" <> toTeXDispatch[base, opts] <> "}",

  True,
  wrapIfNeeded[base, opts] <> "^{" <> toTeXDispatch[exp, opts] <> "}"
];


toTeXDispatch[Rational[p_, q_], opts_Association] :=
  "\\frac{" <> ToString[p] <> "}{" <> ToString[q] <> "}";


toTeXDispatch[Complex[0, 1], opts_Association] := "i";
toTeXDispatch[Complex[0, -1], opts_Association] := "-i";
toTeXDispatch[Complex[a_, b_], opts_Association] :=
  toTeXDispatch[a, opts] <> " + " <> toTeXDispatch[b, opts] <> "i";


toTeXDispatch[n_Integer, opts_Association] := ToString[n];
toTeXDispatch[n_Real, opts_Association] := ToString[n];


toTeXDispatch[s_String, opts_Association] := s;
toTeXDispatch[s_Symbol, opts_Association] := mathToTeX[s];
toTeXDispatch[expr_, opts_Association] := mathToTeX[expr];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
