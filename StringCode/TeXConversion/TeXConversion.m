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


ToTeX::usage = "ToTeX[expr] converts a StringCode expression to TeX string";


(* ::Section:: *)
(*Private section*)


Begin["Private`"];

(* ::Section:: *)
(*Helper functions*)


(* Use Mathematica's TeXForm for general expressions, strip $ escapes *)
mathToTeX[expr_] := StringReplace[
  ToString[TeXForm[expr]],
  {"$" -> "", "\text{" ~~ x:Shortest[__] ~~ "}" :> x}
];

(* Index formatting - use TeXForm for Greek letters *)
formatIndex[idx_] := mathToTeX[idx];

derivativePrefix[0, holo_:True] := "";
derivativePrefix[1, True] := "\\partial ";
derivativePrefix[1, False] := "\\bar{\\partial} ";
derivativePrefix[n_, True] := "\\partial^" <> ToString[n] <> " ";
derivativePrefix[n_, False] := "\\bar{\\partial}^" <> ToString[n] <> " ";

formatPosition[0] := "";
formatPosition[0, 0] := "(0)";
formatPosition[z_] := "(" <> mathToTeX[z] <> ")";
formatPosition[z_, zbar_] := "(" <> mathToTeX[z] <> ", " <> mathToTeX[zbar] <> ")";

(* Wrapper conversions *)
ToTeX[Ra_/;RTest[Ra]] := ":" <> StringJoin[ToTeX /@ List @@ Ra] <> ":";
ToTeX[SFa_/;SFTest[SFa]] := ToTeX @@ SFa;

(* Ghost fields *)
ToTeX[c[n_, z_]] := derivativePrefix[n, True] <> "c" <> formatPosition[z];
ToTeX[b[n_, z_]] := derivativePrefix[n, True] <> "b" <> formatPosition[z];
ToTeX[ct[n_, zbar_]] := derivativePrefix[n, False] <> "\\bar{c}" <> formatPosition[zbar];
ToTeX[bt[n_, zbar_]] := derivativePrefix[n, False] <> "\\bar{b}" <> formatPosition[zbar];

(* Kronecker delta *)
ToTeX[\[Delta][idx1_, idx2_]] := "\\delta_{" <> formatIndex[idx1] <> formatIndex[idx2] <> "}";

(* Arithmetic conversions *)
ToTeX[Plus[terms__]] := Module[{termList = {terms}, result = "", i, termTeX},
  For[i = 1, i <= Length[termList], i++,
    termTeX = ToTeX[termList[[i]]];
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

ToTeX[Times[factors__]] := Module[{factorList = {factors}, numericPart = 1, fieldParts = {}, f, result},
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
          ToTeX[numericPart]
        ]
      ]
    ]
  ];
  result <> StringJoin[ToTeX /@ fieldParts]
];

ToTeX[Power[base_, exp_]] := Module[{},
  If[exp === 1/2,
    "\\sqrt{" <> ToTeX[base] <> "}",
    If[exp === -1,
      "\\frac{1}{" <> ToTeX[base] <> "}",
      ToTeX[base] <> "^{" <> ToTeX[exp] <> "}"
    ]
  ]
];

ToTeX[Rational[p_, q_]] := "\\frac{" <> ToString[p] <> "}{" <> ToString[q] <> "}";

ToTeX[Complex[0, 1]] := "i";
ToTeX[Complex[0, -1]] := "-i";
ToTeX[Complex[a_, b_]] := ToTeX[a] <> " + " <> ToTeX[b] <> "i";

ToTeX[n_Integer] := ToString[n];
ToTeX[n_Real] := ToString[n];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
