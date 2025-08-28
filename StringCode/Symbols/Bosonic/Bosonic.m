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


bosons=Join[bosons, {expX, expXHolo, expXAntiHolo, dX,dXt,ProfileX, ProfileXHolo, ProfileXAntiHolo}];
fermions=Join[fermions, {}];
regfermions=Join[regfermions,{}];
simplefields=Join[simplefields, {dX,dXt}];
simplefieldsnotc=Join[simplefieldsnotc, {dX,dXt}];
compositefields= Join[compositefields, {ProfileXHolo, ProfileXAntiHolo, ProfileX, expXHolo, expXAntiHolo, expX}];
holomorphicFields = Join[holomorphicFields, {ProfileX, expX, ProfileXHolo, dX,expXHolo}];
antiHolomorphicFields = Join[antiHolomorphicFields, {ProfileX, expX, ProfileXAntiHolo, dXt, expXAntiHolo}];
indexedFields = Join[indexedFields, {dX, dXt}];
allfields=Join[bosons,fermions];


(* ::Subsection:: *)
(*Define ghost numbers*)


ghostNumberHolo[a_/;isField[Head[a]]]:= 0;
ghostNumberHolo[a_/;isField[Head[a]]]:= 0;


(* ::Subsection:: *)
(*Define weight of symbols*)


weightSymbolHolo[dX] := 1;

weightHolo[expX[k_, z_,zbar_]] := 0;
weightHolo[expXHolo[k_, z_]] := 0;
weightHolo[ProfileX[profile_, ders_, z_, zbar_]] := 0;
weightHolo[ProfileXHolo[profile_, ders_, z_]] := 0;

weightSymbolAntiHolo[dXt] := 1;

weightAntiHolo[expX[k_, z_,zbar_]] := 0;
weightAntiHolo[expXAntiHolo[k_, zbar_]] := 0;
weightAntiHolo[ProfileX[profile_, ders_, z_, zbar_]] := 0;
weightAntiHolo[ProfileXAntiHolo[profile_, ders_, zbar_]] := 0;


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
