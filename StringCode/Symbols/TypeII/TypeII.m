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


\[Xi]::usage = "Holomorphic \[Xi]-ghost";


\[Xi]t::usage = "Antiholomorphic \[Xi]-ghost";


\[Eta]::usage = "Holomorphic \[Eta]-ghost";


\[Eta]t::usage = "Antiholomorphic \[Eta]-ghost";


\[Beta]::usage = "Holomorphic \[Beta]-ghost";


\[Beta]t::usage = "Antiholomorphic \[Beta]-ghost";


\[Gamma]::usage = "Holomorphic \[Gamma]-ghost";


\[Gamma]t::usage = "Antiholomorphic \[Gamma]-ghost";


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Define symbols*)


exp\[Phi]b[0,z_]:=1;
exp\[Phi]tb[0,z_]:=1;
bosons=Join[bosons, {d\[Phi],d\[Phi]t,exp\[Phi]b,exp\[Phi]tb,\[Beta],\[Beta]t,\[Gamma],\[Gamma]t}];
fermions=Join[fermions, {\[Xi],\[Xi]t,\[Eta],\[Eta]t,exp\[Phi]f,exp\[Phi]tf}];
regfermions=Join[regfermions,{\[Xi],\[Xi]t,\[Eta],\[Eta]t}];
exp\[Phi]fermions={exp\[Phi]f};
exp\[Phi]tfermions={exp\[Phi]tf};
simplefields=Join[simplefields, {d\[Phi],d\[Phi]t,\[Xi],\[Xi]t,\[Eta],\[Eta]t,\[Beta],\[Beta]t,\[Gamma],\[Gamma]t}];
simplefieldsnotc=Join[simplefieldsnotc, {d\[Phi],d\[Phi]t,\[Xi],\[Xi]t,\[Eta],\[Eta]t,\[Beta],\[Beta]t,\[Gamma],\[Gamma]t}];
compositefields= Join[compositefields, {exp\[Phi]b,exp\[Phi]tb,exp\[Phi]f,exp\[Phi]tf}];
holomorphicFields = Join[holomorphicFields, {d\[Phi],\[Xi],\[Eta],\[Beta],\[Gamma],exp\[Phi]f,exp\[Phi]b}];
antiHolomorphicFields = Join[antiHolomorphicFields, {d\[Phi]t, \[Xi]t,\[Eta]t,\[Beta]t,\[Gamma]t,exp\[Phi]tf,exp\[Phi]tb}];
indexedFields = Join[indexedFields, {}];
allfields=Join[bosons,fermions];
collapsable = Join[collapsable, {\[Xi], \[Xi]t, \[Eta], \[Eta]t,\[Beta],\[Beta]t,\[Gamma],\[Gamma]t}];


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
(*Define ghost numbers*)


ghostNumberHolo[\[Xi][der_, z_]]:= -1;
ghostNumberHolo[\[Eta][der_, z_]]:= 1;
ghostNumberHolo[\[Beta][der_, z_]]:= -1;
ghostNumberHolo[\[Gamma][der_, z_]]:= 1;
ghostNumberHolo[a_/;isField[Head[a]]]:= 0;

ghostNumberAntiHolo[\[Xi]t[der_, zbar_]]:= -1;
ghostNumberAntiHolo[\[Eta]t[der_, zbar_]]:= 1;
ghostNumberAntiHolo[\[Beta]t[der_, zbar_]]:= -1;
ghostNumberAntiHolo[\[Gamma]t[der_, zbar_]]:= 1;
ghostNumberAntiHolo[a_/;isField[Head[a]]]:= 0;

GSOParityHolo[a_/;isField[Head[a]]]=.;
GSOParityAntiHolo[a_/;isField[Head[a]]]=.;

GSOParityHolo[\[Xi][der_, z_]]:= 1;
GSOParityHolo[\[Eta][der_, z_]]:= 1;
GSOParityAntiHolo[\[Xi]t[der_, zbar_]]:= 1;
GSOParityAntiHolo[\[Eta]t[der_, zbar_]]:= 1;

GSOParityHolo[\[Beta][der_, z_]]:= -1;
GSOParityHolo[\[Gamma][der_, z_]]:= -1;
GSOParityAntiHolo[\[Beta]t[der_, zbar_]]:= -1;
GSOParityAntiHolo[\[Gamma]t[der_, zbar_]]:= -1;

GSOParityHolo[d\[Phi][der_, z_]]:= 1;
GSOParityAntiHolo[d\[Phi]t[der_, zbar_]]:= 1;

GSOParityHolo[exp\[Phi]b[n_, z_]]:= (-1)^n;
GSOParityHolo[exp\[Phi]f[n_, z_]]:= (-1)^n;
GSOParityAntiHolo[exp\[Phi]tb[n_, zbar_]]:= (-1)^n;
GSOParityAntiHolo[exp\[Phi]tf[n_, zbar_]]:= (-1)^n;

GSOParityHolo[a_/;isField[Head[a]]]:= 1;
GSOParityAntiHolo[a_/;isField[Head[a]]]:= 1;


(* ::Subsection:: *)
(*Define weight of symbols*)


(* ::Subsubsection:: *)
(*Superghosts*)


weightSymbolHolo[\[Xi]] := 0;
weightSymbolHolo[\[Eta]] := 1;
weightSymbolHolo[\[Beta]] := 3/2;
weightSymbolHolo[\[Gamma]] := -1/2;
weightSymbolHolo[d\[Phi]] := 1;
weightHolo[\[Xi][der_, z_]] := weightSymbolHolo[\[Xi]] + der;
weightHolo[\[Eta][der_, z_]] := weightSymbolHolo[\[Eta]] + der;
weightHolo[\[Beta][der_, z_]] := weightSymbolHolo[\[Beta]] + der;
weightHolo[\[Gamma][der_, z_]] := weightSymbolHolo[\[Gamma]] + der;
weightHolo[d\[Phi][der_, z_]] := weightSymbolHolo[d\[Phi]] + der;

weightHolo[exp\[Phi]f[n_, z_]] := -1/2*(n)*(n + 2);
weightHolo[exp\[Phi]b[n_, z_]] := -1/2*(n)*(n + 2);

weightSymbolAntiHolo[\[Xi]t] := 0;
weightSymbolAntiHolo[\[Eta]t] := 1;
weightSymbolAntiHolo[\[Beta]t] := 3/2;
weightSymbolAntiHolo[\[Gamma]t] := -1/2;
weightSymbolAntiHolo[d\[Phi]t] := 1;
weightAntiHolo[\[Xi]t[der_, zbar_]] := weightSymbolAntiHolo[\[Xi]t] + der;
weightAntiHolo[\[Eta]t[der_, zbar_]] := weightSymbolAntiHolo[\[Eta]t] + der;
weightAntiHolo[\[Beta]t[der_, zbar_]] := weightSymbolAntiHolo[\[Beta]t] + der;
weightAntiHolo[\[Gamma]t[der_, zbar_]] := weightSymbolAntiHolo[\[Gamma]t] + der;
weightAntiHolo[d\[Phi]t[der_, zbar_]] := weightSymbolAntiHolo[d\[Phi]t] + der;

weightAntiHolo[exp\[Phi]tf[n_, z_]] := -1/2*(n)*(n + 2);
weightAntiHolo[exp\[Phi]tb[n_, z_]] := -1/2*(n)*(n + 2);


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
