(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Symbols`TypeII`FlatSpace`"]
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"]


(* ::Section:: *)
(*Declare public variables and methods*)


expXAntiHolo::usage = "Antiholomorphic part of the wave primary in free boson CFT";


expXHolo::usage = "Holomorphic part of the wave primary in free boson CFT";


expX::usage = "Plane wave primary in free boson CFT";


dX::usage = "Holomorphic del X primary in free boson CFT";


dXt::usage = "Antiholomorphic del X primary in free boson CFT";


ProfileXAntiHolo::usage = "Antiolomorphic part of an X-profile"


ProfileXHolo::usage = "Holomorphic part of an X-profile"


ProfileX::usage = "An X-profile";


\[Psi]::usage = "Holomorphic free matter fermion";


\[Psi]t::usage = "Antiholomorphic free matter fermion";


\[Alpha]p::usage = "Symbol for alpha prime";


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Define symbols*)


bosons=Join[bosons, {expXHolo, expXAntiHolo, expX,dX,dXt,ProfileXHolo, ProfileXAntiHolo, ProfileX}];
fermions=Join[fermions, {\[Psi],\[Psi]t}];
regfermions=Join[regfermions,{\[Psi],\[Psi]t}];
simplefields=Join[simplefields, {dX,dXt,\[Psi],\[Psi]t}];
simplefieldsnotc=Join[simplefieldsnotc, {dX,dXt,\[Psi],\[Psi]t}];
compositefields= Join[compositefields, {ProfileXHolo, ProfileXAntiHolo, ProfileX, expXHolo, expXAntiHolo, expX}];
holomorphicFields = Join[holomorphicFields, {ProfileX, expX, dX,expXHolo, ProfileXHolo, \[Psi]}];
antiHolomorphicFields = Join[antiHolomorphicFields, {ProfileX, expX, expXAntiHolo, ProfileXAntiHolo, dXt, \[Psi]t}];
indexedFields = Join[indexedFields, {dX, dXt, \[Psi], \[Psi]t}];
allfields=Join[bosons,fermions];
interactingOperators = Join[interactingOperators, {}];
allOperators = Join[allfields, interactingOperators];


(* ::Subsection:: *)
(*Define weight of symbols*)


(* ::Subsubsection:: *)
(*Free boson*)


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


(* ::Subsubsection:: *)
(*Free fermion*)


weightSymbolHolo[\[Psi]]:= 1/2;
weightSymbolAntiHolo[\[Psi]t] := 1/2;


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
