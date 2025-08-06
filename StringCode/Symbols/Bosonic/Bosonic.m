(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Symbols`Bosonic`"]
Needs["StringCode`Symbols`"];


(* ::Section:: *)
(*Declare public variables and methods*)


expXAntiHolo::usage = "Antiholomorphic part of the wave primary in free boson CFT";


expXHolo::usage = "Holomorphic part of the wave primary in free boson CFT";


expX::usage = "Plane wave primary in free boson CFT";


dX::usage = "Holomorphic del X primary in free boson CFT"


dXt::usage = "Antiholomorphic del X primary in free boson CFT"


ProfileXAntiHolo::usage = "Antiolomorphic part of an X-profile"


ProfileXHolo::usage = "Holomorphic part of an X-profile"


ProfileX::usage = "A polynomial X-profile"


\[Alpha]p::usage = "Symbol for alpha prime";


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Define symbols*)


bosons=Join[bosons, {X,expX,dX,dXt,ProfileX}];
fermions=Join[fermions, {}];
regfermions=Join[regfermions,{}];
simplefields=Join[simplefields, {dX,dXt}];
simplefieldsnotc=Join[simplefieldsnotc, {dX,dXt}];
compositefields= Join[compositefields, {ProfileXHolo, ProfileXAntiHolo, ProfileX, expXHolo, expXAntiHolo, expX}];
holomorphicFields = Join[holomorphicFields, {ProfileXHolo, dX,expXHolo}];
antiHolomorphicFields = Join[antiHolomorphicFields, {ProfileXAntiHolo, dXt, expXAntiHolo}];
allfields=Join[bosons,fermions];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
