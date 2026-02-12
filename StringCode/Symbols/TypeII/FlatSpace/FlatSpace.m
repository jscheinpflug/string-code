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

S::usage = "Holomorphic spin field";

St::usage = "Antiholomorphic spin field";


\[Alpha]p::usage = "Symbol for alpha prime";

dot::usage = "Symbol for dot product";

der::usage = "Symbol for a derivative";


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Define symbols*)


bosons=Join[bosons, {expXHolo, expXAntiHolo, expX,dX,dXt,ProfileXHolo, ProfileXAntiHolo, ProfileX}];
fermions=Join[fermions, {\[Psi],\[Psi]t,S,St}];
regfermions=Join[regfermions,{\[Psi],\[Psi]t,S,St}];
simplefields=Join[simplefields, {dX,dXt,\[Psi],\[Psi]t,S,St}];
simplefieldsnotc=Join[simplefieldsnotc, {dX,dXt,\[Psi],\[Psi]t,S,St}];
compositefields= Join[compositefields, {ProfileXHolo, ProfileXAntiHolo, ProfileX, expXHolo, expXAntiHolo, expX}];
holomorphicFields = Join[holomorphicFields, {ProfileX, expX, dX,expXHolo, ProfileXHolo, \[Psi], S}];
antiHolomorphicFields = Join[antiHolomorphicFields, {ProfileX, expX, expXAntiHolo, ProfileXAntiHolo, dXt, \[Psi]t, St}];
indexedFields = Join[indexedFields, {dX, dXt, \[Psi], \[Psi]t, S, St}];
allfields=Join[bosons,fermions];
collapsable = Join[collapsable, {dX, dXt, expX, expXHolo, expXAntiHolo, ProfileX, ProfileXHolo, ProfileXAntiHolo}];
factorizable = Join[factorizable, {expX, ProfileX}];
factorizationReplacement = Join[factorizationReplacement, {
  ProfileX[profile_, ders_, z_, zbar_] :> {ProfileXHolo[profile, ders, z], ProfileXAntiHolo[profile, ders, zbar]},
  expX[k_, z_, zbar_] :> {expXHolo[k, z], expXAntiHolo[k, zbar]}
}];

canonicalizeSpinModes[modes_List] := Module[{ordering, sortedModes},
  ordering = Ordering[modes];
  sortedModes = modes[[ordering]];
  If[DuplicateFreeQ[sortedModes],
    {Signature[ordering], sortedModes},
    {0, sortedModes}
  ]
];

spinAlphaChiralitySign["chiral"] := 1;
spinAlphaChiralitySign["antichiral"] := -1;

S::alpha = "Spin index must be given as {alpha, \"chiral\"|\"antichiral\"}.";
St::alpha = "Spin index must be given as {alpha, \"chiral\"|\"antichiral\"}.";

S[alpha_, q_, modes_List, der_, z_] := (Message[S::alpha]; $Failed) /; !MatchQ[alpha, {_, ("chiral" | "antichiral")}];
St[alpha_, q_, modes_List, der_, zbar_] := (Message[St::alpha]; $Failed) /; !MatchQ[alpha, {_, ("chiral" | "antichiral")}];

S[{alpha_, chirality : ("chiral" | "antichiral")}, q_, modes_List, der_, z_] := Module[{canonicalized = canonicalizeSpinModes[modes]},
  If[canonicalized[[1]] == 0,
    0,
    canonicalized[[1]] S[{alpha, chirality}, q, canonicalized[[2]], der, z]
  ]
] /; (!DuplicateFreeQ[modes] || !OrderedQ[modes]);

St[{alpha_, chirality : ("chiral" | "antichiral")}, q_, modes_List, der_, zbar_] := Module[{canonicalized = canonicalizeSpinModes[modes]},
  If[canonicalized[[1]] == 0,
    0,
    canonicalized[[1]] St[{alpha, chirality}, q, canonicalized[[2]], der, zbar]
  ]
] /; (!DuplicateFreeQ[modes] || !OrderedQ[modes]);


(* ::Subsection:: *)
(*Define weight of symbols*)


(* ::Subsubsection:: *)
(*Free boson*)


weightSymbolHolo[dX] := 1;
weightHolo[dX[\[Mu]_, n_, z_]] := weightSymbolHolo[dX] + n;

weightHolo[expX[k_, z_,zbar_]] := 0;
weightHolo[expXHolo[k_, z_]] := 0;
weightHolo[ProfileX[profile_, ders_, z_, zbar_]] := 0;
weightHolo[ProfileXHolo[profile_, ders_, z_]] := 0;

weightSymbolAntiHolo[dXt] := 1;
weightAntiHolo[dXt[\[Mu]_, n_, zbar_]] := weightSymbolAntiHolo[dXt] + n;

weightAntiHolo[expX[k_, z_,zbar_]] := 0;
weightAntiHolo[expXAntiHolo[k_, zbar_]] := 0;
weightAntiHolo[ProfileX[profile_, ders_, z_, zbar_]] := 0;
weightAntiHolo[ProfileXAntiHolo[profile_, ders_, zbar_]] := 0;


(* ::Subsubsection:: *)
(*Free fermion*)


weightSymbolHolo[\[Psi]]:= 1/2;
weightHolo[\[Psi][\[Mu]_, n_, z_]] := weightSymbolHolo[\[Psi]] + n;
weightSymbolAntiHolo[\[Psi]t] := 1/2;
weightAntiHolo[\[Psi]t[\[Mu]_, n_, zbar_]] := weightSymbolAntiHolo[\[Psi]t] + n;

weightHolo[S[{alpha_, chirality : ("chiral" | "antichiral")}, q_, modes_List, der_, z_]] := 5/8 - q (q + 2)/2 + der + Total[First /@ modes];
weightHolo[St[{alpha_, chirality : ("chiral" | "antichiral")}, q_, modes_List, der_, zbar_]] := 0;
weightAntiHolo[S[{alpha_, chirality : ("chiral" | "antichiral")}, q_, modes_List, der_, z_]] := 0;
weightAntiHolo[St[{alpha_, chirality : ("chiral" | "antichiral")}, q_, modes_List, der_, zbar_]] := 5/8 - q (q + 2)/2 + der + Total[First /@ modes];


(* ::Subsection:: *)
(*Define GSO parity*)


GSOParityHolo[a_/;isField[Head[a]]]=.;
GSOParityAntiHolo[a_/;isField[Head[a]]]=.;

GSOParityHolo[dX[\[Mu]_, n_, z_]] := 1;
GSOParityAntiHolo[dXt[\[Mu]_, n_, zbar_]] := 1;

GSOParityHolo[expX[k_, z_, zbar_]] := 1;
GSOParityAntiHolo[expX[k_, z_, zbar_]] := 1;
GSOParityHolo[expXHolo[k_, z_]] := 1;
GSOParityAntiHolo[expXAntiHolo[k_, zbar_]] := 1;

GSOParityHolo[ProfileX[profile_, ders_, z_, zbar_]] := 1;
GSOParityAntiHolo[ProfileX[profile_, ders_, z_, zbar_]] := 1;
GSOParityHolo[ProfileXHolo[profile_, ders_, z_]] := 1;
GSOParityAntiHolo[ProfileXAntiHolo[profile_, ders_, zbar_]] := 1;

GSOParityHolo[\[Psi][\[Mu]_, n_, z_]] := -1;
GSOParityAntiHolo[\[Psi]t[\[Mu]_, n_, zbar_]] := -1;

GSOParityHolo[S[{alpha_, chirality : ("chiral" | "antichiral")}, q_, modes_List, der_, z_]] := spinAlphaChiralitySign[chirality] (-1)^(q + 1/2 + Length[modes]);
GSOParityAntiHolo[St[{alpha_, chirality : ("chiral" | "antichiral")}, q_, modes_List, der_, zbar_]] := spinAlphaChiralitySign[chirality] (-1)^(q + 1/2 + Length[modes]);

GSOParityAntiHolo[S[{alpha_, chirality : ("chiral" | "antichiral")}, q_, modes_List, der_, z_]] := 1;
GSOParityHolo[St[{alpha_, chirality : ("chiral" | "antichiral")}, q_, modes_List, der_, zbar_]] := 1;

GSOParityHolo[a_/;isField[Head[a]]]:= 1;
GSOParityAntiHolo[a_/;isField[Head[a]]]:= 1;


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
