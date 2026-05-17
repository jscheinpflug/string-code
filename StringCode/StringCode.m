(* ::Package:: *)

BeginPackage["StringCode`"]


InitStringCode::usage = "InitStringCode[conventions] initializes StringCode with a given set of conventions";
FlushKernelCache::usage = "FlushKernelCache[] flushes the persistent TypeII flat-space gamma-kernel cache when that subsystem is loaded and otherwise returns Null";


Begin["Private`"];
StringCode`FlushKernelCache[] := Null;
InitStringCode[options_] := 
Module[{userContext={}, theoryValue = options["theory"], CFTValue = options["CFT"], conventionValue = options["conventions"], bracketValue = options["bracket"]},
Switch[theoryValue,
"TypeII", userContext = {
    "StringCode`Symbols`TypeII`",
    "StringCode`Taylor`TypeII`",
    "StringCode`Conventions`TypeII`",
    "StringCode`Wick`TypeII`",
    "StringCode`NormalOrdering`TypeII`",
    "StringCode`BasisGeneration`TypeII`",
    "StringCode`Operators`TypeII`",
    "StringCode`OPE`TypeII`",
    "StringCode`Correlators`TypeII`",
    "StringCode`Brackets`TypeII`",
    "StringCode`TeXConversion`TypeII`"},
"Bosonic", userContext = {
    "StringCode`Symbols`Bosonic`",
    "StringCode`Taylor`Bosonic`",
    "StringCode`Conventions`Bosonic`",
    "StringCode`Wick`Bosonic`",
    "StringCode`NormalOrdering`Bosonic`",
    "StringCode`BasisGeneration`Bosonic`",
    "StringCode`Operators`Bosonic`",
    "StringCode`OPE`Bosonic`",
    "StringCode`Correlators`Bosonic`",
    "StringCode`Brackets`Bosonic`",
    "StringCode`TeXConversion`Bosonic`"},
_, Print["There is no such theory"]];

Switch[CFTValue,
"FlatSpace",
Switch[theoryValue,
"TypeII", AppendTo[userContext, "StringCode`Symbols`TypeII`FlatSpace`"]; AppendTo[userContext, "StringCode`Wick`TypeII`FlatSpace`"];
AppendTo[userContext, "StringCode`Operators`TypeII`FlatSpace`"]; AppendTo[userContext, "StringCode`Taylor`TypeII`FlatSpace`"];
AppendTo[userContext, "StringCode`OPE`TypeII`FlatSpace`"]; AppendTo[userContext, "StringCode`Brackets`TypeII`FlatSpace`"]; 
AppendTo[userContext, "StringCode`TeXConversion`TypeII`FlatSpace`"]; AppendTo[userContext, "StringCode`BasisGeneration`TypeII`FlatSpace`"];
AppendTo[userContext, "StringCode`Correlators`TypeII`FlatSpace`"];
AppendTo[userContext, "StringCode`OPE`TypeII`FlatSpace`GammaMatrices`"];
AppendTo[userContext, "StringCode`OPE`TypeII`FlatSpace`TensorStructures`"];
AppendTo[userContext, "StringCode`OPE`TypeII`FlatSpace`TensorStructures`CountSinglet`"];
AppendTo[userContext, "StringCode`OPE`TypeII`FlatSpace`TensorStructures`IndependentTensorStructures`"],
"Bosonic", AppendTo[userContext,"StringCode`Symbols`Bosonic`FlatSpace`"]; AppendTo[userContext,"StringCode`Wick`Bosonic`FlatSpace`"];
AppendTo[userContext, "StringCode`Operators`Bosonic`FlatSpace`"]; AppendTo[userContext, "StringCode`OPE`Bosonic`FlatSpace`"];
AppendTo[userContext, "StringCode`Taylor`Bosonic`FlatSpace`"]; AppendTo[userContext, "StringCode`Brackets`Bosonic`FlatSpace`"]; 
AppendTo[userContext, "StringCode`TeXConversion`Bosonic`FlatSpace`"]; AppendTo[userContext, "StringCode`BasisGeneration`Bosonic`FlatSpace`"];
AppendTo[userContext, "StringCode`Correlators`Bosonic`FlatSpace`"],
_, Print["No such CFT for theory ", theoryValue]
],
"MinimalModel", If[theoryValue == "Bosonic", AppendTo[userContext, "StringCode`Symbols`Bosonic`MinimalModel`"];
 AppendTo[userContext, "StringCode`Taylor`Bosonic`MinimalModel`"]; AppendTo[userContext, "StringCode`Operators`Bosonic`MinimalModel`"];
 AppendTo[userContext, "StringCode`OPE`Bosonic`MinimalModel`"]; AppendTo[userContext, "StringCode`Brackets`Bosonic`MinimalModel`"];
  AppendTo[userContext, "StringCode`TeXConversion`Bosonic`MinimalModel`"]; AppendTo[userContext, "StringCode`BasisGeneration`Bosonic`MinimalModel`"];,
 Print["No such CFT for theory ", theoryValue]],
_, Print["There are no such CFTs"]];

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
Needs["StringCode`BasisGeneration`"];
Needs["StringCode`Operators`"];
Needs["StringCode`OPE`"];
Needs["StringCode`Correlators`"];
Needs["StringCode`Brackets`"];
Needs["StringCode`TeXConversion`"];
Needs["StringCode`Utils`Canonicalize`"];

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
