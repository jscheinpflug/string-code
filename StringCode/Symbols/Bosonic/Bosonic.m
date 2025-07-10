(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Symbols`Bosonic`"]
Needs["StringCode`Symbols`"];


(* ::Section:: *)
(*Declare public variables and methods*)


expX::usage = "Plane wave primary in free boson CFT";


dX::usage = "Holomorphic del X primary in free boson CFT"


dXt::usage = "Antiholomorphic del X primary in free boson CFT"


ProfileX::usage = "A polynomial X-profile"


(* ::Section:: *)
(*Logic*)


Begin["`Private`"];


(* ::Subsection:: *)
(*Define symbols*)


bosons=Join[bosons, {expX,dX,dXt,ProfileX}];
fermions=Join[fermions, {}];
regfermions=Join[regfermions,{}];
simplefields=Join[simplefields, {dX,dXt}];
simplefieldsnotc=Join[simplefieldsnotc, {dX,dXt}];
compositefields= Join[compositefields, {expX}];
holomorphicFields = Join[holomorphicFields, {dX,expX}];
antiHolomorphicFields = Join[antiHolomorphicFields, {dXt, expX}];
allfields=Join[bosons,fermions];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
