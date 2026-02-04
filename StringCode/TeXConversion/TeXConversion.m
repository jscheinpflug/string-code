(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`TeXConversion`"]
Needs["StringCode`Symbols`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`Operators`"];
Needs["StringCode`StringFields`"];


(* ::Section:: *)
(*Declare public variables and methods*)


ToTeXString::usage = "ToTeXString[expr] converts a StringCode expression to TeX string";


(* ::Section:: *)
(*Private section*)


Begin["Private`"];

(* ::Section:: *)
(*Helper functions*)


(* Format Greek letter indices *)
greekToTeX[\[Mu]] := "\\mu";
greekToTeX[\[Nu]] := "\\nu";
greekToTeX[\[Rho]] := "\\rho";
greekToTeX[\[Sigma]] := "\\sigma";
greekToTeX[\[Lambda]] := "\\lambda";
greekToTeX[\[Alpha]] := "\\alpha";
greekToTeX[\[Beta]] := "\\beta";
greekToTeX[\[Gamma]] := "\\gamma";
greekToTeX[\[Delta]] := "\\delta";
greekToTeX[\[Epsilon]] := "\\epsilon";
greekToTeX[\[Kappa]] := "\\kappa";
greekToTeX[\[Tau]] := "\\tau";
greekToTeX[x_] := ToString[x];

formatIndex[idx_] := greekToTeX[idx];

derivativePrefix[0, holo_:True] := "";
derivativePrefix[1, True] := "\\partial ";
derivativePrefix[1, False] := "\\bar{\\partial} ";
derivativePrefix[n_, True] := "\\partial^" <> ToString[n] <> " ";
derivativePrefix[n_, False] := "\\bar{\\partial}^" <> ToString[n] <> " ";

formatPosition[0] := "";
formatPosition[0, 0] := "(0)";
formatPosition[z_] := "(" <> ToString[z] <> ")";
formatPosition[z_, zbar_] := "(" <> ToString[z] <> ", " <> ToString[zbar] <> ")";

(* Wrapper conversions *)
ToTeXString[Ra_/;RTest[Ra]] := ":" <> StringJoin[ToTeXString /@ {List @@ Ra}] <> ":";
ToTeXString[SF[content_]] := ToTeXString[content];
ToTeXString[Op[contents__]] := StringJoin[ToTeXString /@ {contents}];
ToTeXString[Interacting[content_]] := ToTeXString[content];

(* Ghost fields *)
ToTeXString[c[n_, z_]] := derivativePrefix[n, True] <> "c" <> formatPosition[z];
ToTeXString[b[n_, z_]] := derivativePrefix[n, True] <> "b" <> formatPosition[z];
ToTeXString[ct[n_, zbar_]] := derivativePrefix[n, False] <> "\\bar{c}" <> formatPosition[zbar];
ToTeXString[bt[n_, zbar_]] := derivativePrefix[n, False] <> "\\bar{b}" <> formatPosition[zbar];

(* Kronecker delta *)
ToTeXString[\[Delta][idx1_, idx2_]] := "\\delta_{" <> formatIndex[idx1] <> formatIndex[idx2] <> "}";

(* Arithmetic conversions *)
ToTeXString[Plus[terms__]] := Module[{termList = {terms}, result = "", i, termTeX},
  For[i = 1, i <= Length[termList], i++,
    termTeX = ToTeXString[termList[[i]]];
    If[i == 1,
      result = termTeX,
      If[StringTake[termTeX, 1] === "-",
        result = result <> " " <> termTeX,
        result = result <> " + " <> termTeX
      ]
    ]
  ];
  result
];

ToTeXString[Times[factors__]] := Module[{factorList = {factors}, numericPart = 1, fieldParts = {}, f, result},
  Do[
    If[NumericQ[f] || MatchQ[f, _Rational] || f === I,
      numericPart = numericPart * f,
      AppendTo[fieldParts, f]
    ],
    {f, factorList}
  ];
  result = If[numericPart === 1, "",
    If[numericPart === -1, "-",
      If[numericPart === I, "i",
        If[numericPart === -I, "-i",
          ToTeXString[numericPart]
        ]
      ]
    ]
  ];
  result <> StringJoin[ToTeXString /@ fieldParts]
];

ToTeXString[Power[base_, exp_]] := Module[{},
  If[exp === 1/2,
    "\\sqrt{" <> ToTeXString[base] <> "}",
    If[exp === -1,
      "\\frac{1}{" <> ToTeXString[base] <> "}",
      ToTeXString[base] <> "^{" <> ToTeXString[exp] <> "}"
    ]
  ]
];

ToTeXString[Rational[p_, q_]] := "\\frac{" <> ToString[p] <> "}{" <> ToString[q] <> "}";

ToTeXString[Complex[0, 1]] := "i";
ToTeXString[Complex[0, -1]] := "-i";
ToTeXString[Complex[a_, b_]] := ToTeXString[a] <> " + " <> ToTeXString[b] <> "i";

ToTeXString[n_Integer] := ToString[n];
ToTeXString[n_Real] := ToString[n];

(* Fallbacks *)
ToTeXString[expr_] := ToString[expr, InputForm] /; !AtomQ[expr];
ToTeXString[s_Symbol] := ToString[s];
ToTeXString[s_String] := s;


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
