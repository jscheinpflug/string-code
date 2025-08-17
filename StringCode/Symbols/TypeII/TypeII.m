(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Symbols`TypeII`"]
Needs["StringCode`Symbols`"];


(* ::Section:: *)
(*Declare public variables and methods*)


d\[Phi]::usage = "Holomorphic del \[Phi] primary in linear dilaton CFT"


d\[Phi]t::usage = "Antiholomorphic del \[Phi] primary in linear dilaton CFT"


exp\[Phi]b::usage = "Holomorphic bosonic exponential of the \[Phi] linear dilaton"


exp\[Phi]tb::usage = "Antiholomorphic bosonic exponential of the \[Phi] linear dilaton"


exp\[Phi]f::usage = "Holomorphic fermionic exponential of the \[Phi] linear dilaton"


exp\[Phi]tf::usage = "Antiholomorphic fermionic exponential of the \[Phi] linear dilaton"


expXAntiHolo::usage = "Antiholomorphic part of the wave primary in free boson CFT";


expXHolo::usage = "Holomorphic part of the wave primary in free boson CFT";


expX::usage = "Plane wave primary in free boson CFT";


dX::usage = "Holomorphic del X primary in free boson CFT";


dXt::usage = "Antiholomorphic del X primary in free boson CFT";


ProfileXAntiHolo::usage = "Antiolomorphic part of an X-profile"


ProfileXHolo::usage = "Holomorphic part of an X-profile"


ProfileX::usage = "An X-profile";


\[Xi]::usage = "Holomorphic \[Xi]-ghost";


\[Xi]t::usage = "Antiholomorphic \[Xi]-ghost";


\[Eta]::usage = "Holomorphic \[Eta]-ghost";


\[Eta]t::usage = "Antiholomorphic \[Eta]-ghost";


\[Psi]::usage = "Holomorphic free matter fermion";


\[Psi]t::usage = "Antiholomorphic free matter fermion";


\[Alpha]p::usage = "Symbol for alpha prime";


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Define symbols*)


exp\[Phi]b[0,z_]:=1;
exp\[Phi]tb[0,z_]:=1;
bosons=Join[bosons, {expXHolo, expXAntiHolo, expX,dX,dXt,ProfileXHolo, ProfileXAntiHolo, ProfileX, d\[Phi],d\[Phi]t,exp\[Phi]b,exp\[Phi]tb}];
fermions=Join[fermions, {\[Psi],\[Psi]t,\[Xi],\[Xi]t,\[Eta],\[Eta]t,exp\[Phi]f,exp\[Phi]tf}];
regfermions=Join[regfermions,{\[Psi],\[Psi]t,\[Xi],\[Xi]t,\[Eta],\[Eta]t}];
exp\[Phi]fermions={exp\[Phi]f};
exp\[Phi]tfermions={exp\[Phi]tf};
simplefields=Join[simplefields, {dX,dXt,d\[Phi],d\[Phi]t,\[Psi],\[Psi]t,\[Xi],\[Xi]t,\[Eta],\[Eta]t}];
simplefieldsnotc=Join[simplefieldsnotc, {dX,dXt,d\[Phi],d\[Phi]t,\[Psi],\[Psi]t,\[Xi],\[Xi]t,\[Eta],\[Eta]t}];
compositefields= Join[compositefields, {ProfileXHolo, ProfileXAntiHolo, ProfileX, expXHolo, expXAntiHolo, expX,exp\[Phi]b,exp\[Phi]tb,exp\[Phi]f,exp\[Phi]tf}];
holomorphicFields = Join[holomorphicFields, {ProfileX, expX, dX,expXHolo, ProfileXHolo, d\[Phi],\[Psi],\[Xi],\[Eta],exp\[Phi]f,exp\[Phi]b}];
antiHolomorphicFields = Join[antiHolomorphicFields, {ProfileX, expX, expXAntiHolo, ProfileXAntiHolo, dXt, d\[Phi]t, \[Psi]t,\[Xi]t,\[Eta]t,exp\[Phi]tf,exp\[Phi]tb}];
indexedFields = Join[indexedFields, {dX, dXt, \[Psi], \[Psi]t}];
allfields=Join[bosons,fermions];


(* ::Subsection:: *)
(*Define picture numbers*)


pictureHol::usage = "Gives holomorphic picture number";

pictureHol[\[Xi][n_, z_]]:= 1;
pictureHol[\[Eta][n_, z_]]:= -1;
pictureHol[exp\[Phi]f[exp_, z_]]:= exp;
pictureHol[exp\[Phi]b[exp_, z_]]:= exp;
pictureHol[a_/;isField[Head[a]]]:= 0;

pictureAntiHol::usage = "Gives antiholomorphic picture number";

pictureAntiHol[\[Xi]t[n_, zbar_]]:= 1;
pictureAntiHol[\[Eta]t[n_, zbar_]]:= -1;
pictureAntiHol[exp\[Phi]tf[exp_, zbar_]]:= exp;
pictureAntiHol[exp\[Phi]tb[exp_, zbar_]]:= exp;
pictureAntiHol[a_/;isField[Head[a]]]:= 0;


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


(* ::Subsubsection:: *)
(*Superghosts*)


weightSymbolHolo[\[Xi]] := 0;
weightSymbolHolo[\[Eta]] := 1;
weightSymbolHolo[d\[Phi]] := 1;

weightHolo[exp\[Phi]f[n_, z_]] := -1/2*(n)*(n + 2);
weightHolo[exp\[Phi]b[n_, z_]] := -1/2*(n)*(n + 2);

weightSymbolAntiHolo[\[Xi]t] := 0;
weightSymbolAntiHolo[\[Eta]t] := 1;
weightSymbolAntiHolo[d\[Phi]t] := 1;

weightAntiHolo[exp\[Phi]tf[n_, z_]] := -1/2*(n)*(n + 2);
weightAntiHolo[exp\[Phi]tb[n_, z_]] := -1/2*(n)*(n + 2);


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
