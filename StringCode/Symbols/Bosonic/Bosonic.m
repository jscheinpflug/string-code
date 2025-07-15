(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Symbols`Bosonic`"]
Needs["StringCode`Symbols`"];


(* ::Section:: *)
(*Declare public variables and methods*)


X::usage = "Noncompact boson in free boson CFT";


expX::usage = "Plane wave primary in free boson CFT";


dX::usage = "Holomorphic del X primary in free boson CFT"


dXt::usage = "Antiholomorphic del X primary in free boson CFT"


ProfileX::usage = "A polynomial X-profile"


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Define symbols*)


bosons=Join[bosons, {X,expX,dX,dXt,ProfileX}];
fermions=Join[fermions, {}];
regfermions=Join[regfermions,{}];
simplefields=Join[simplefields, {X, dX,dXt}];
simplefieldsnotc=Join[simplefieldsnotc, {X,dX,dXt}];
compositefields= Join[compositefields, {expX}];
holomorphicFields = Join[holomorphicFields, {X,dX,expX}];
antiHolomorphicFields = Join[antiHolomorphicFields, {X, dXt, expX}];
allfields=Join[bosons,fermions];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
