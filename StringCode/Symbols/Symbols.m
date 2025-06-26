(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Symbols`"]


(* ::Section:: *)
(*Declare public variables and methods*)


bosons::usage = "A list of bosons, including composites";


fermions::usage = "A list of fermions, including composites";


allfields::usage = "A list of all bosons and fermions";


regfermions::usage = "A list of fundamental fermions";


exp\[Phi]fermions::usage="A list of fermionized holomorphic exponentials";


exp\[Phi]tfermions::usage = "A list of fermionized antiholomorphic exponentials";


simplefields::usage = "A list of fundamental fields";


simplefieldsnotc::usage = "A list of fundamental fields not c-ghost";


compositefields::usage = "A list of composite fields";


Contract::usage = "Contract traced indices";


ContractDelta::usage = "Contract repeated indices";


expX::usage = "Plane wave primary in free boson CFT";


dX::usage = "Holomorphic del X primary in free boson CFT"


dXt::usage = "Antiholomorphic del X primary in free boson CFT"


d\[Phi]::usage = "Holomorphic del \[Phi] primary in linear dilaton CFT"


d\[Phi]t::usage = "Antiholomorphic del \[Phi] primary in linear dilaton CFT"


exp\[Phi]b::usage = "Holomorphic bosonic exponential of the \[Phi] linear dilaton"


exp\[Phi]tb::usage = "Antiholomorphic bosonic exponential of the \[Phi] linear dilaton"


exp\[Phi]f::usage = "Holomorphic fermionic exponential of the \[Phi] linear dilaton"


exp\[Phi]tf::usage = "Antiholomorphic fermionic exponential of the \[Phi] linear dilaton"


b::usage = "Holomorphic b-ghost"


bt::usage = "Antiholomorphic b-ghost"


c::usage = "Holomorphic c-ghost"


ct::usage = "Antiholomorphic c-ghost"


\[Xi]::usage = "Holomorphic \[Xi]-ghost"


\[Xi]t::usage = "Antiholomorphic \[Xi]-ghost"


\[Eta]::usage = "Holomorphic \[Eta]-ghost"


\[Eta]t::usage = "Antiholomorphic \[Eta]-ghost"


\[Psi]::usage = "Holomorphic free matter fermion"


\[Psi]t::usage = "Antiholomorphic free matter fermion"


(* ::Section:: *)
(*Logic*)


Contract[f_,dim_]:=f /.{\[Delta][\[Mu]_,\[Mu]_]:>dim,\[Delta][\[Mu]_,\[Nu]_]^2:>dim};
Contract[f_]:=Contract[f,10];


ContractDelta[f_]:=f//.{g_ \[Delta][\[Mu]_,\[Mu]1_]:>(g/.{\[Mu]->\[Mu]1})/;!FreeQ[g,\[Mu]],g_ \[Delta][\[Mu]1_,\[Mu]_]:>(g/.{\[Mu]->\[Mu]1})/;!FreeQ[g,\[Mu]]};


Begin["`Private`"];


(* ::Subsection:: *)
(*Define symbols*)


exp\[Phi]b[0,z_]:=1;
exp\[Phi]tb[0,z_]:=1;
bosons={expX,dX,dXt,d\[Phi],d\[Phi]t,exp\[Phi]b,exp\[Phi]tb};
fermions={\[Psi],\[Psi]t,b,bt,c,ct,\[Xi],\[Xi]t,\[Eta],\[Eta]t,exp\[Phi]f,exp\[Phi]tf};
regfermions={\[Psi],\[Psi]t,b,bt,c,ct,\[Xi],\[Xi]t,\[Eta],\[Eta]t};
exp\[Phi]fermions={exp\[Phi]f};
exp\[Phi]tfermions={exp\[Phi]tf};
simplefields={dX,dXt,d\[Phi],d\[Phi]t,\[Psi],\[Psi]t,b,bt,c,ct,\[Xi],\[Xi]t,\[Eta],\[Eta]t};
simplefieldsnotc={dX,dXt,d\[Phi],d\[Phi]t,\[Psi],\[Psi]t,b,bt,\[Xi],\[Xi]t,\[Eta],\[Eta]t};
compositefields={expX,exp\[Phi]b,exp\[Phi]tb,exp\[Phi]f,exp\[Phi]tf};
allfields=Join[bosons,fermions];


(* ::Subsection:: *)
(*Define index contractions*)


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
