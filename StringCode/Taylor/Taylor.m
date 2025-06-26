(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Taylor`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`NormalOrdering`"];


(* ::Section:: *)
(*Declare public variables and methods*)


Taylor::usage = "Taylor expands a normal ordered product";
Polar::usage = "Picks out the first-order pole from a function";


(* ::Section:: *)
(*Public Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Define Taylor*)


Taylor[f_,z0_,z0bar_,ord_]:= Block[{i,j,x,func,n,z},f/.{
b[n_,z_]:>Sum[If[i==0,1,(z-z0)^i/i!] b[n+i,z0],{i,0,ord}],
c[n_,z_]:>Sum[If[i==0,1,(z-z0)^i/i!] c[n+i,z0],{i,0,ord}],
\[Eta][n_,z_]:>Sum[If[i==0,1,(z-z0)^i/i!] \[Eta][n+i,z0],{i,0,ord}],
\[Xi][n_,z_]:>Sum[If[i==0,1,(z-z0)^i/i!] \[Xi][n+i,z0],{i,0,ord}],
d\[Phi][n_,z_]:>Sum[If[i==0,1,(z-z0)^i/i!] d\[Phi][n+i,z0],{i,0,ord}],
dX[\[Mu]_,n_,z_]:>Sum[If[i==0,1,(z-z0)^i/i!] dX[\[Mu],n+i,z0],{i,0,ord}],
\[Psi][\[Mu]_,n_,z_]:>Sum[If[i==0,1,(z-z0)^i/i!]\[Psi][\[Mu],n+i,z0],{i,0,ord}],
exp\[Phi]f[a_,z_]:>Sum[If[i==0,1,(z-z0)^i/i!](R[D[E^(a func[x]),{x,i}]/.{E^(a func[x]):>exp\[Phi]f[a,x],Derivative[n_][func][x]:>d\[Phi][n-1,x]}]/.x->z0),{i,0,ord}],
exp\[Phi]b[a_,z_]:>Sum[If[i==0,1,(z-z0)^i/i!](R[D[E^(a func[x]),{x,i}]/.{E^(a func[x]):>exp\[Phi]b[a,x],Derivative[n_][func][x]:>d\[Phi][n-1,x]}]/.x->z0),{i,0,ord}],
bt[n_,z_]:>Sum[If[i==0,1,(z-z0bar)^i/i!] bt[n+i,z0bar],{i,0,ord}],
ct[n_,z_]:>Sum[If[i==0,1,(z-z0bar)^i/i!]ct[n+i,z0bar],{i,0,ord}],
\[Eta]t[n_,z_]:>Sum[If[i==0,1,(z-z0bar)^i/i!] \[Eta]t[n+i,z0bar],{i,0,ord}],
\[Xi]t[n_,z_]:>Sum[If[i==0,1,(z-z0bar)^i/i!]\[Xi]t[n+i,z0bar],{i,0,ord}],
d\[Phi]t[n_,z_]:>Sum[If[i==0,1,(z-z0bar)^i/i!] d\[Phi]t[n+i,z0bar],{i,0,ord}],
dXt[\[Mu]_,n_,z_]:>Sum[If[i==0,1,(z-z0bar)^i/i!] dXt[\[Mu],n+i,z0bar],{i,0,ord}],
\[Psi]t[\[Mu]_,n_,z_]:>Sum[If[i==0,1,(z-z0bar)^i/i!] \[Psi]t[\[Mu],n+i,z0bar],{i,0,ord}],
exp\[Phi]tf[a_,z_]:>Sum[If[i==0,1,(z-z0bar)^i/i!](R[D[E^(a func[x]),{x,i}]/.{E^(a func[x]):>exp\[Phi]tf[a,x],Derivative[n_][func][x]:>d\[Phi]t[n-1,x]}]/.x->z0bar),{i,0,ord}],
exp\[Phi]tb[a_,z_]:>Sum[If[i==0,1,(z-z0bar)^i/i!](R[D[E^(a func[x]),{x,i}]/.{E^(a func[x]):>exp\[Phi]tb[a,x],Derivative[n_][func][x]:>d\[Phi]t[n-1,x]}]/.x->z0bar),{i,0,ord}],
expX[k_,z_,zbar_]:>Sum[If[i==0,1,(z-z0)^i/i!]If[j==0,1,(zbar-z0bar)^j/j!] 
(R[expX[k,z0,z0bar],D[E^(I func[x]),{x,i}]/.{E^(I func[x]):>1,Derivative[n_][func][x]:>Module[{\[Mu]},k[\[Mu]] dX[\[Mu],n-1,x]]}/.x->z0,D[E^(I func[x]),{x,j}]/.{E^(I func[x]):>1,Derivative[n_][func][x]:>Module[{\[Mu]},k[\[Mu]] dXt[\[Mu],n-1,x]]}/.x->z0bar]),{i,0,ord},{j,0,ord}]}];


(* ::Subsection:: *)
(*Define Polar*)


Polar[f_,z_,z0_]:=Block[{x},(Series[(f/.{z->z0+x}),{x,0,-1}]//Normal)/.{x->z-z0}]


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
