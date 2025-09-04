(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Symbols`Bosonic`MinimalModel`"]
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`Bosonic`"]


(* ::Section:: *)
(*Declare public variables and methods*)


V::usage = "The (1,3) operator in c = 1 + O(1/m) minimal model of total weight 2 + y with y = 2/(m+1)";


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Define symbols*)


bosons=Join[bosons, {V}];
fermions=Join[fermions, {}];
regfermions=Join[regfermions,{}];
simplefields=Join[simplefields, {}];
simplefieldsnotc=Join[simplefieldsnotc, {}];
compositefields= Join[compositefields, {}];
holomorphicFields = Join[holomorphicFields, {}];
antiHolomorphicFields = Join[antiHolomorphicFields, {}];
indexedFields = Join[indexedFields, {}];
interactingOperators = Join[interactingOperators, {V}];
allfields=Join[simplefields, compositefields];
allOperators = Join[allfields, interactingOperators];


(* ::Subsection:: *)
(*Define weight of symbols*)


weightSymbolHolo[V] := 1;
weightSymbolAntiHolo[V] := 1;


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
