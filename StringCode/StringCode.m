(* ::Package:: *)

BeginPackage["StringCode`"]


InitStringCode::usage = "InitStringCode[conventions] initializes StringCode with a given set of conventions";


Begin["Private`"];
InitStringCode[options_] := Module[{userContext={}, theoryValue = options["theory"], conventionValue = options["conventions"], bracketValue = options["bracket"]},
Switch[theoryValue, 
"TypeII", userContext = {
    "StringCode`Symbols`TypeII`",
    "StringCode`Taylor`TypeII`",
    "StringCode`Conventions`TypeII`",
    "StringCode`Wick`TypeII`",
    "StringCode`StringFields`TypeII`",
    "StringCode`Brackets`TypeII`"},
"Bosonic", userContext = {
    "StringCode`Symbols`Bosonic`",
    "StringCode`Taylor`Bosonic`",
    "StringCode`Conventions`Bosonic`",
    "StringCode`Wick`Bosonic`",
    "StringCode`StringFields`Bosonic`",
    "StringCode`Brackets`Bosonic`"},
_, Print["There is no such theory"]];

Switch[conventionValue, 
"TypeII-Xi", If[theoryValue == "TypeII", AppendTo[userContext, "StringCode`Conventions`TypeII`Xi`"], Print["No such conventions for theory ", theoryValue]],
"TypeII-Ashoke", If[theoryValue == "TypeII", AppendTo[userContext,"StringCode`Conventions`TypeII`Ashoke`"], Print["No such conventions for theory ", theoryValue]],
"Bosonic-Xi", If[theoryValue == "Bosonic", AppendTo[userContext,"StringCode`Conventions`Bosonic`Xi`"], Print["No such conventions for theory ", theoryValue]],
_, Print["There are no such conventions"]];

Switch[bracketValue, 
"Flat", 
Switch[theoryValue,
"TypeII", AppendTo[userContext, "StringCode`Brackets`TypeII`Flat`"],
"Bosonic", AppendTo[userContext, "StringCode`Brackets`Bosonic`Flat`"],
_, Print["No such bracket for theory ", theoryValue]
],
_, Print["There is no such bracket"]];
Needs["StringCode`Symbols`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`Taylor`"];
Needs["StringCode`Wick`"];
Needs["StringCode`StringFields`"];
Needs["StringCode`OPE`"];
Needs["StringCode`Brackets`"];
Needs["StringCode`Correlators`"];
Scan[
  (AppendTo[$ContextPath, #] &) ,
 userContext
];
Scan[(Needs[#] &) ,
 userContext
];
];
End[];
EndPackage[];
