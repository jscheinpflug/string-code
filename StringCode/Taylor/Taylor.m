(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Taylor`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`NormalOrdering`"];


(* ::Section:: *)
(*Declare public variables and methods*)


Taylor::usage = "Taylor expands a normal ordered product up to a given order";
TaylorAtOrder::usage = "Taylor expands a normal ordered product at a given order";
Polar::usage = "Picks out the first-order pole from a function";


(* ::Section:: *)
(*Public Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Define Taylor*)


Taylor[f_,z0_,z0bar_,ord_]:= Block[{i,j,x,func,n,z}, f/.{
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


(* ::Subsection::Closed:: *)
(*Define TaylorAtOrder*)


TaylorAtOrder[Ra_/;Rtest[Ra], ord_, z0_,z0bar_]:= Module[{lengthR = Rlength[Ra],partitions = Select[Tuples[Range[0,ord],Rlength[Ra]],Total[#]==ord&], RList = List @@ R[Ra], result = 0}, 
result = R @@@ Transpose[Table[addDerivatives[RList[[i]], partitions[[j]][[i]],z0,z0bar],{i, 1,lengthR},{j,1,Length[partitions]}]]//Total; result]


TaylorAtOrder[a_+b_,c_,d_,e_]:=TaylorAtOrder[a,c,d,e]+TaylorAtOrder[b,c,d,e]
TaylorAtOrder[a_ b_,c_,d_,e_]:=a TaylorAtOrder[b,c,d,e]/;(And @@(FreeQ[a,#]&/@ allfields))


(* ::Subsubsection::Closed:: *)
(*Define addDerivatives*)


addDerivatives[b[n_,z_], ord_,z0_,z0bar_]:= (z-z0)^ord/Factorial[ord] b[n+ord,z0];


addDerivatives[c[n_,z_], ord_, z0_,z0bar_]:= (z-z0)^ord/Factorial[ord]c[n+ord,z0];


addDerivatives[\[Eta][n_,z_], ord_, z0_,z0bar_]:= (z-z0)^ord/Factorial[ord]\[Eta][n+ord,z0];


addDerivatives[\[Xi][n_,z_], ord_, z0_,z0bar_]:= (z-z0)^ord/Factorial[ord]\[Xi][n+ord,z0];


addDerivatives[d\[Phi][n_,z_], ord_, z0_,z0bar_]:= (z-z0)^ord/Factorial[ord]d\[Phi][n+ord,z0];


addDerivatives[dX[\[Mu]_,n_,z_], ord_, z0_,z0bar_]:= (z-z0)^ord/Factorial[ord]dX[\[Mu],n+ord,z0];


addDerivatives[\[Psi][\[Mu]_,n_,z_], ord_, z0_,z0bar_]:= (z-z0)^ord/Factorial[ord]\[Psi][\[Mu],n+ord,z0];


addDerivatives[exp\[Phi]f[a_,z_], ord_, z0_,z0bar_]:= (z-z0)^ord/Factorial[ord](R[D[E^(a func[x]),{x,ord}]/.{E^(a func[x]):>exp\[Phi]f[a,x],Derivative[n_][func][x]:>d\[Phi][n-1,x]}]/.x->z0)


addDerivatives[bt[n_,z_], ord_,z0_,z0bar_]:= (z-z0bar)^ord/Factorial[ord] bt[n+ord,z0bar];


addDerivatives[ct[n_,z_], ord_, z0_,z0bar_]:= (z-z0bar)^ord/Factorial[ord]c[n+ord,z0bar];


addDerivatives[\[Eta]t[n_,z_], ord_, z0_,z0bar_]:= (z-z0bar)^ord/Factorial[ord]\[Eta][n+ord,z0bar];


addDerivatives[\[Xi]t[n_,z_], ord_, z0_,z0bar_]:= (z-z0bar)^ord/Factorial[ord]\[Xi][n+ord,z0bar];


addDerivatives[d\[Phi]t[n_,z_], ord_, z0_,z0bar_]:= (z-z0bar)^ord/Factorial[ord]d\[Phi][n+ord,z0bar];


addDerivatives[dXt[\[Mu]_,n_,z_], ord_, z0_,z0bar_]:= (z-z0bar)^ord/Factorial[ord]dXt[\[Mu],n+ord,z0bar];


addDerivatives[\[Psi]t[\[Mu]_,n_,z_], ord_, z0_,z0bar_]:= (z-z0bar)^ord/Factorial[ord]\[Psi]t[\[Mu],n+ord,z0bar];


addDerivatives[exp\[Phi]f[a_,z_], ord_, z0_,z0bar_]:= (z-z0bar)^ord/Factorial[ord](R[D[E^(a func[x]),{x,ord}]/.{E^(a func[x]):>exp\[Phi]f[a,x],Derivative[n_][func][x]:>d\[Phi][n-1,x]}]/.x->z0bar)


addDerivatives[expX[k_,z_,zbar_],ord_,z0_,z0bar_]:= 
Sum[
(z-z0)^ord1/Factorial[ord1](zbar-z0bar)^(ord-ord1)/Factorial[ord-ord1](R[expX[k,z0,z0bar],D[E^(I func[x]),{x,ord1}]/.{E^(I func[x]):>1,Derivative[n_][func][x]:>Module[{\[Mu]},k[\[Mu]] dX[\[Mu],n-1,x]]}/.x->z0,D[E^(I func[x]),{x,ord-ord1}]/.{E^(I func[x]):>1,Derivative[n_][func][x]:>Module[{\[Mu]},k[\[Mu]] dXt[\[Mu],n-1,x]]}/.x->z0bar]),{ord1,0,ord}];


(* ::Subsection::Closed:: *)
(*Define Polar*)


Polar[f_,z_,z0_]:=Block[{x},(Series[(f/.{z->z0+x}),{x,0,-1}]//Normal)/.{x->z-z0}]


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
