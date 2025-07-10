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


expX::usage = "Plane wave primary in free boson CFT";


dX::usage = "Holomorphic del X primary in free boson CFT"


dXt::usage = "Antiholomorphic del X primary in free boson CFT"


ProfileX::usage = "A polynomial X-profile"


\[Xi]::usage = "Holomorphic \[Xi]-ghost"


\[Xi]t::usage = "Antiholomorphic \[Xi]-ghost"


\[Eta]::usage = "Holomorphic \[Eta]-ghost"


\[Eta]t::usage = "Antiholomorphic \[Eta]-ghost"


\[Psi]::usage = "Holomorphic free matter fermion"


\[Psi]t::usage = "Antiholomorphic free matter fermion"


pictureHol::usage = "Gives holomorphic picture number";


pictureAntiHol::usage = "Gives antiholomorphic picture number";


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Define symbols*)


exp\[Phi]b[0,z_]:=1;
exp\[Phi]tb[0,z_]:=1;
bosons=Join[bosons, {expX,dX,dXt,ProfileX, d\[Phi],d\[Phi]t,exp\[Phi]b,exp\[Phi]tb}];
fermions=Join[fermions, {\[Psi],\[Psi]t,\[Xi],\[Xi]t,\[Eta],\[Eta]t,exp\[Phi]f,exp\[Phi]tf}];
regfermions=Join[regfermions,{\[Psi],\[Psi]t,\[Xi],\[Xi]t,\[Eta],\[Eta]t}];
exp\[Phi]fermions={exp\[Phi]f};
exp\[Phi]tfermions={exp\[Phi]tf};
simplefields=Join[simplefields, {dX,dXt,d\[Phi],d\[Phi]t,\[Psi],\[Psi]t,\[Xi],\[Xi]t,\[Eta],\[Eta]t}];
simplefieldsnotc=Join[simplefieldsnotc, {dX,dXt,d\[Phi],d\[Phi]t,\[Psi],\[Psi]t,\[Xi],\[Xi]t,\[Eta],\[Eta]t}];
compositefields= Join[compositefields, {expX, exp\[Phi]b,exp\[Phi]tb,exp\[Phi]f,exp\[Phi]tf}];
holomorphicFields = Join[holomorphicFields, {dX,expX,d\[Phi],\[Psi],\[Xi],\[Eta],exp\[Phi]f,exp\[Phi]b}];
antiHolomorphicFields = Join[antiHolomorphicFields, {dXt, d\[Phi]t, \[Psi]t,\[Xi]t,\[Eta]t,exp\[Phi]tf,exp\[Phi]tb,expX}];
allfields=Join[bosons,fermions];


(* ::Subsection:: *)
(*Define picture numbers*)


pictureHol[\[Xi][n_, z_]]:= 1;
pictureHol[\[Eta][n_, z_]]:= -1;
pictureHol[exp\[Phi]f[exp_, z_]]:= exp;
pictureHol[exp\[Phi]b[exp_, z_]]:= exp;
pictureHol[a_/;isField[Head[a]]]:= 0;
pictureAntiHol[\[Xi]t[n_, zbar_]]:= 1;
pictureAntiHol[\[Eta]t[n_, zbar_]]:= -1;
pictureAntiHol[exp\[Phi]tf[exp_, zbar_]]:= exp;
pictureAntiHol[exp\[Phi]tb[exp_, zbar_]]:= exp;
pictureAntiHol[a_/;isField[Head[a]]]:= 0;


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
