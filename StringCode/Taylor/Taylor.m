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


(* ::Subsection::Closed:: *)
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


(* ::Subsection:: *)
(*Define TaylorAtOrder*)


isHolomorphic[Relem_]:= MemberQ[holomorphicFields, Head[Relem]];


isAntiHolomorphic[Relem_]:= MemberQ[antiHolomorphicFields, Head[Relem]];


holomorphicLength[Ra_/; Rtest[Ra]]:= Module[{length = 0}, 
Scan[Function[Relem, If[isHolomorphic[Relem], length = length + 1]],Ra];
length
];


antiHolomorphicLength[Ra_/; Rtest[Ra]]:= Module[{length = 0}, 
Scan[Function[Relem, If[isAntiHolomorphic[Relem], length = length + 1]],Ra];
length
];


TaylorAtOrderHolo[Ra_/;Rtest[Ra], ord_, z0_]:= Module[{holoLengthR = holomorphicLength[Ra],RLength = Length[Ra], RList = List @@ R[Ra], resultForGivenPartition = {}, result = 0, partitions = {}, i=1}, 
partitions = Select[Tuples[Range[0,ord],holoLengthR],Total[#]==ord&];
resultForGivenPartition = ConstantArray[None, RLength];
Scan[Function[partition, 
	Scan[Function[partitionNumber,
	While[i <= RLength && !isHolomorphic[Ra[[i]]], resultForGivenPartition[[i]] = Ra[[i]]; i++];
	resultForGivenPartition[[i]] = addHoloDerivatives[Ra[[i]], partitionNumber, z0];
	i++],
	 partition];
	 result = result + R @@ Join[resultForGivenPartition[[;; i - 1]], RList[[i;;]]];
	 i = 1;
	 resultForGivenPartition = ConstantArray[None, RLength];
], partitions];
result]


TaylorAtOrderAntiHolo[Ra_/;Rtest[Ra], ord_, z0_]:= Module[{antiHoloLengthR = antiHolomorphicLength[Ra],RLength = Length[Ra], RList = List @@ R[Ra], resultForGivenPartition = {}, result = 0, partitions = {}, i=1}, 
partitions = Select[Tuples[Range[0,ord],antiHoloLengthR],Total[#]==ord&];
resultForGivenPartition = ConstantArray[None, RLength];
Scan[Function[partition, 
	Scan[Function[partitionNumber,
	While[i <= RLength && !isAntiHolomorphic[Ra[[i]]], resultForGivenPartition[[i]] = Ra[[i]]; i++];
	resultForGivenPartition[[i]] = addAntiHoloDerivatives[Ra[[i]], partitionNumber, z0];
	i++],
	 partition];
	 result = result + R @@ Join[resultForGivenPartition[[;; i - 1]], RList[[i;;]]];
	 i=1;
	 resultForGivenPartition = ConstantArray[None, RLength];
], partitions];
result]


TaylorAtOrder[Ra_/;Rtest[Ra], ordHolo_,ordAntiHolo_, z0_,z0bar_]:= TaylorAtOrderAntiHolo[TaylorAtOrderHolo[Ra, ordHolo, z0], ordAntiHolo, z0bar] 


TaylorAtOrder[a_+b_,c_,d_,e_,f_]:=TaylorAtOrder[a,c,d,e,f]+TaylorAtOrder[b,c,d,e,f]
TaylorAtOrder[a_ b_,c_,d_,e_,f_]:=a TaylorAtOrder[b,c,d,e,f]/;(And @@(FreeQ[a,#]&/@ allfields))


TaylorAtOrderHolo[a_+b_,c_,d_]:=TaylorAtOrderHolo[a,c,d]+TaylorAtOrderHolo[b,c,d]
TaylorAtOrderHolo[a_ b_,c_,d_]:=a TaylorAtOrderHolo[b,c,d]/;(And @@(FreeQ[a,#]&/@ allfields))


TaylorAtOrderAntiHolo[a_+b_,c_,d_]:=TaylorAtOrderAntiHolo[a,c,d]+TaylorAtOrderAntiHolo[b,c,d]
TaylorAtOrderAntiHolo[a_ b_,c_,d_]:=a TaylorAtOrderAntiHolo[b,c,d]/;(And @@(FreeQ[a,#]&/@ allfields))


(* ::Subsubsection:: *)
(*Define adding derivatives*)


addHoloDerivatives[b[n_,z_], ord_,z0_]:= (z-z0)^ord/Factorial[ord] b[n+ord,z0];


addHoloDerivatives[c[n_,z_], ord_, z0_]:= (z-z0)^ord/Factorial[ord]c[n+ord,z0];


addHoloDerivatives[\[Eta][n_,z_], ord_, z0_]:= (z-z0)^ord/Factorial[ord]\[Eta][n+ord,z0];


addHoloDerivatives[\[Xi][n_,z_], ord_, z0_]:= (z-z0)^ord/Factorial[ord]\[Xi][n+ord,z0];


addHoloDerivatives[d\[Phi][n_,z_], ord_, z0_]:= (z-z0)^ord/Factorial[ord]d\[Phi][n+ord,z0];


addHoloDerivatives[dX[\[Mu]_,n_,z_], ord_, z0_]:= (z-z0)^ord/Factorial[ord]dX[\[Mu],n+ord,z0];


addHoloDerivatives[\[Psi][\[Mu]_,n_,z_], ord_, z0_]:= (z-z0)^ord/Factorial[ord]\[Psi][\[Mu],n+ord,z0];


addHoloDerivatives[exp\[Phi]f[a_,z_], ord_, z0_]:= (z-z0)^ord/Factorial[ord](R[D[E^(a func[x]),{x,ord}]/.{E^(a func[x]):>exp\[Phi]f[a,x],Derivative[n_][func][x]:>d\[Phi][n-1,x]}]/.x->z0)


addHoloDerivatives[exp\[Phi]b[a_,z_], ord_, z0_]:= (z-z0)^ord/Factorial[ord](R[D[E^(a func[x]),{x,ord}]/.{E^(a func[x]):>exp\[Phi]b[a,x],Derivative[n_][func][x]:>d\[Phi][n-1,x]}]/.x->z0)


addHoloDerivatives[expX[k_, z_, zbar_], ord_, z0_] :=
 (z - z0)^ord/
   Factorial[ord] (R[expX[k, z0, zbar],
    D[E^(I func[x]), {x, ord}] /. {E^(I func[x]) :> 1,
       Derivative[n_][func][x] :>
        Module[{\[Mu]}, k[\[Mu]] dX[\[Mu], n - 1, x]]} /. x -> z0])


addAntiHoloDerivatives[bt[n_,z_], ord_,z0bar_]:= (z-z0bar)^ord/Factorial[ord] bt[n+ord,z0bar];


addAntiHoloDerivatives[ct[n_,z_], ord_, z0bar_]:= (z-z0bar)^ord/Factorial[ord]ct[n+ord,z0bar];


addAntiHoloDerivatives[\[Eta]t[n_,z_], ord_, z0bar_]:= (z-z0bar)^ord/Factorial[ord]\[Eta]t[n+ord,z0bar];


addAntiHoloDerivatives[\[Xi]t[n_,z_], ord_, z0bar_]:= (z-z0bar)^ord/Factorial[ord]\[Xi]t[n+ord,z0bar];


addAntiHoloDerivatives[d\[Phi]t[n_,z_], ord_, z0bar_]:= (z-z0bar)^ord/Factorial[ord]d\[Phi]t[n+ord,z0bar];


addAntiHoloDerivatives[dXt[\[Mu]_,n_,z_], ord_, z0bar_]:= (z-z0bar)^ord/Factorial[ord]dXt[\[Mu],n+ord,z0bar];


addAntiHoloDerivatives[\[Psi]t[\[Mu]_,n_,z_], ord_, z0bar_]:= (z-z0bar)^ord/Factorial[ord]\[Psi]t[\[Mu],n+ord,z0bar];


addAntiHoloDerivatives[exp\[Phi]tf[a_,z_], ord_, z0bar_]:= (z-z0bar)^ord/Factorial[ord](R[D[E^(a func[x]),{x,ord}]/.{E^(a func[x]):>exp\[Phi]tf[a,x],Derivative[n_][func][x]:>d\[Phi]t[n-1,x]}]/.x->z0bar)


addAntiHoloDerivatives[exp\[Phi]tb[a_,z_], ord_, z0bar_]:= (z-z0bar)^ord/Factorial[ord](R[D[E^(a func[x]),{x,ord}]/.{E^(a func[x]):>exp\[Phi]tb[a,x],Derivative[n_][func][x]:>d\[Phi]t[n-1,x]}]/.x->z0bar)


addAntiHoloDerivatives[expX[k_, z_, zbar_], ord_, z0bar_] :=
 (zbar - z0bar)^ord/
   Factorial[ord] (R[expX[k, z, z0bar],
    D[E^(I func[x]), {x, ord}] /. {E^(I func[x]) :> 1,
       Derivative[n_][func][x] :>
        Module[{\[Mu]}, k[\[Mu]] dXt[\[Mu], n - 1, x]]} /.
     x -> z0bar])


(* ::Subsection::Closed:: *)
(*Define Polar*)


Polar[f_,z_,z0_]:=Block[{x},(Series[(f/.{z->z0+x}),{x,0,-1}]//Normal)/.{x->z-z0}]


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
