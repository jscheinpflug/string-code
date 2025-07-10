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
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Define Taylor*)


taylorRule[z0_, z0bar_, ord_] = {b[n_,z_]:>Sum[If[i==0,1,(z-z0)^i/i!] b[n+i,z0],{i,0,ord}],
c[n_,z_]:>Sum[If[i==0,1,(z-z0)^i/i!] c[n+i,z0],{i,0,ord}],
bt[n_,z_]:>Sum[If[i==0,1,(z-z0bar)^i/i!] bt[n+i,z0bar],{i,0,ord}],
ct[n_,z_]:>Sum[If[i==0,1,(z-z0bar)^i/i!]ct[n+i,z0bar],{i,0,ord}]};

Taylor[f_,z0_,z0bar_,ord_]:= Block[{i,j,x,func,n,z}, f/.taylorRule;];


(* ::Subsection:: *)
(*Define TaylorAtOrder*)


holomorphicLength[Ra_/; Rtest[Ra], z0_]:= Module[{length = 0}, 
Scan[Function[Relem, If[isHolomorphic[Head[Relem]] && !isAtPointHolo[Relem,z0],length = length + 1]],Ra];
length
];


antiHolomorphicLength[Ra_/; Rtest[Ra], z0bar_]:= Module[{length = 0}, 
Scan[Function[Relem, If[isAntiHolomorphic[Head[Relem]] && !isAtPointAntiHolo[Relem,z0bar], length = length + 1]],Ra];
length
];


TaylorAtOrderHolo[Ra_/;Rtest[Ra], 0, z0_]:= Ra;


TaylorAtOrderHolo[Ra_/;Rtest[Ra], ord_, z0_]:= Module[{holoLengthR = holomorphicLength[Ra, z0],RLength = Length[Ra], RList = List @@ Ra, resultForGivenPartition = {}, result = 0, partitions = {}, i=1}, 
partitions = DeleteDuplicates@Flatten[Permutations/@(Select[IntegerPartitions[ord,{holoLengthR},Range[0,ord]],Length[#]==holoLengthR&]),1];
resultForGivenPartition = ConstantArray[None, RLength];
Scan[Function[partition, 
	Scan[Function[partitionNumber,
	While[i <= RLength && (!isHolomorphic[Head[Ra[[i]]]] || isAtPointHolo[Ra[[i]], z0]), resultForGivenPartition[[i]] = Ra[[i]]; i++];
	resultForGivenPartition[[i]] = addHoloDerivatives[Ra[[i]], partitionNumber, z0];
	i++],
	 partition];
	 result = result + R @@ Join[resultForGivenPartition[[;; i - 1]], RList[[i;;]]];
	 i = 1;
	 resultForGivenPartition = ConstantArray[None, RLength];
], partitions];
result]


TaylorAtOrderAntiHolo[Ra_/;Rtest[Ra], 0, z0bar_]:= Ra;


TaylorAtOrderAntiHolo[Ra_/;Rtest[Ra], ord_, z0bar_]:= Module[{antiHoloLengthR = antiHolomorphicLength[Ra, z0bar],RLength = Length[Ra], RList = List @@ Ra, resultForGivenPartition = {}, result = 0, partitions = {}, i=1}, 
partitions = DeleteDuplicates@Flatten[Permutations/@(Select[IntegerPartitions[ord,{antiHoloLengthR},Range[0,ord]],Length[#]==antiHoloLengthR&]),1];
resultForGivenPartition = ConstantArray[None, RLength];
Scan[Function[partition, 
	Scan[Function[partitionNumber,
	While[i <= RLength && (!isAntiHolomorphic[Head[Ra[[i]]]] || isAtPointAntiHolo[Ra[[i]], z0bar]), resultForGivenPartition[[i]] = Ra[[i]]; i++];
	resultForGivenPartition[[i]] = addAntiHoloDerivatives[Ra[[i]], partitionNumber, z0bar];
	i++],
	 partition];
	 result = result + R @@ Join[resultForGivenPartition[[;; i - 1]], RList[[i;;]]];
	 i=1;
	 resultForGivenPartition = ConstantArray[None, RLength];
], partitions];
result]


TaylorAtOrder[0, ord1_, ord2_, z0_, z0bar_]:= 0;


TaylorAtOrderHolo[0, ord_, z0_]:= 0;


TaylorAtOrderAntiHolo[0, ord_, z0bar_]:= 0;


TaylorAtOrder[Ra_/;Rtest[Ra], ordHolo_,ordAntiHolo_, z0_,z0bar_]:= TaylorAtOrderAntiHolo[TaylorAtOrderHolo[Ra, ordHolo, z0], ordAntiHolo, z0bar] 


TaylorAtOrder[a_+b_,c_,d_,e_,f_]:=TaylorAtOrder[a,c,d,e,f]+TaylorAtOrder[b,c,d,e,f]
TaylorAtOrder[a_ b_,c_,d_,e_,f_]:=a TaylorAtOrder[b,c,d,e,f]/;(And @@(FreeQ[a,#]&/@ allfields))


TaylorAtOrderHolo[a_+b_,c_,d_]:=TaylorAtOrderHolo[a,c,d]+TaylorAtOrderHolo[b,c,d]
TaylorAtOrderHolo[a_ b_,c_,d_]:=a TaylorAtOrderHolo[b,c,d]/;(And @@(FreeQ[a,#]&/@ allfields))


TaylorAtOrderAntiHolo[a_+b_,c_,d_]:=TaylorAtOrderAntiHolo[a,c,d]+TaylorAtOrderAntiHolo[b,c,d]
TaylorAtOrderAntiHolo[a_ b_,c_,d_]:=a TaylorAtOrderAntiHolo[b,c,d]/;(And @@(FreeQ[a,#]&/@ allfields))


(* ::Subsubsection:: *)
(*Check if field needs expanding*)


isAtPointHolo[b[n_, z_], z0_] := SameQ[z,z0];
isAtPointHolo[c[n_, z_], z0_] := SameQ[z,z0];
isAtPointHolo[dX[\[Mu]_, n_, z_], z0_] := SameQ[z,z0];
isAtPointHolo[expX[k_, z_, zbar_], z0_] := SameQ[z,z0];
isAtPointHolo[field_, z0_] := False /; isAntiHolomorphic[Head[field]];
isAtPointAntiHolo[bt[n_, zbar_], z0bar_] := SameQ[zbar,z0bar];
isAtPointAntiHolo[ct[n_, zbar_], z0bar_] := SameQ[zbar,z0bar];
isAtPointAntiHolo[dXt[\[Mu]_, n_, zbar_], z0bar_] := SameQ[zbar,z0bar];
isAtPointAntiHolo[expX[k_, z_, zbar_], z0bar_] := SameQ[zbar,z0bar];
isAtPointAntiHolo[field_, z0bar_] := False /; isHolomorphic[Head[field]];


(* ::Subsubsection:: *)
(*Define adding derivatives*)


addHoloDerivatives[b[n_,z_], ord_,z0_]:= (z-z0)^ord/Factorial[ord] b[n+ord,z0];


addHoloDerivatives[c[n_,z_], ord_, z0_]:= (z-z0)^ord/Factorial[ord]c[n+ord,z0];


addAntiHoloDerivatives[bt[n_,z_], ord_,z0bar_]:= (z-z0bar)^ord/Factorial[ord] bt[n+ord,z0bar];


addAntiHoloDerivatives[ct[n_,z_], ord_, z0bar_]:= (z-z0bar)^ord/Factorial[ord]ct[n+ord,z0bar];


(* ::Subsection::Closed:: *)
(*Define Polar*)


Polar[f_,z_,z0_]:=Block[{x},(Series[(f/.{z->z0+x}),{x,0,-1}]//Normal)/.{x->z-z0}]


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
