(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Taylor`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`Wick`"];
Needs["StringCode`NormalOrdering`"];


(* ::Section:: *)
(*Declare public variables and methods*)


TaylorAtOrder::usage = "Taylor expands a normal ordered product at a given order";
TaylorAtOrderHolo::usage = "Taylor expands a holomorphic normal ordered product at a given order";
TaylorAtOrderAntiHolo::usage = "Taylor expands an antiholomorphic normal ordered product at a given order";


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Define TaylorAtOrder*)


TaylorAtOrderHolo[Ra_/;RTest[Ra], ord_, z0_]:= Module[{holoLengthR = holomorphicLength[Ra, z0],RLength = Length[Ra], RList = List @@ Ra, 
resultForGivenPartition, result = 0, partitions, i=1}, 
resultForGivenPartition = ConstantArray[None, RLength];

(*Partition the order of Taylor into the number of fields that can be Taylored*)
partitions = computePartition[ord, holoLengthR];

(*For each partition perform Taylor expansion*)
Scan[Function[partition, 

(*Each element of a partition gives the order of differentiation of a given field in a normal-ordered product*)
Scan[Function[partitionNumber,

(*Go through normal-ordered product until you find a field you can Taylor*)
While[i <= RLength && (!isHolomorphic[Head[RList[[i]]]] || isAtPointHolo[RList[[i]], z0]), resultForGivenPartition[[i]] = RList[[i]]; i++];

(*When you have found a field you can Taylor, add the required number of derivatives as determined by the partition*)
resultForGivenPartition[[i]] = addHoloDerivatives[RList[[i]], partitionNumber, z0];
i++;],
partition];

(*Take the Taylored fields, join them with possibly non-Taylored fields at the tail of input, and make them into a normal-ordered product*)
result = result + R @@ Join[resultForGivenPartition[[;; i - 1]], RList[[i;;]]];

i = 1;
resultForGivenPartition = ConstantArray[None, RLength];
], partitions];
result]


TaylorAtOrderAntiHolo[Ra_/;RTest[Ra], ord_, z0bar_]:= Module[{antiHoloLengthR = antiHolomorphicLength[Ra, z0bar],RLength = Length[Ra], RList = List @@ Ra, 
resultForGivenPartition, result = 0, partitions, i=1}, 
resultForGivenPartition = ConstantArray[None, RLength];

(*Partition the order of Taylor into the number of fields that can be Taylored*)
partitions = computePartition[ord, antiHoloLengthR];

(*For each partition perform Taylor expansion*)
Scan[Function[partition, 

(*Each element of a partition gives the order of differentiation of a given field in a normal-ordered product*)
Scan[Function[partitionNumber,

(*Go through normal-ordered product until you find a field you can Taylor*)
While[i <= RLength && (!isAntiHolomorphic[Head[RList[[i]]]] || isAtPointAntiHolo[RList[[i]], z0bar]), resultForGivenPartition[[i]] = RList[[i]]; i++];

(*When you have found a field you can Taylor, add the required number of derivatives as determined by the partition*)
resultForGivenPartition[[i]] = addAntiHoloDerivatives[RList[[i]], partitionNumber, z0bar];
i++;
],
partition];

(*Take the Taylored fields, join them with possibly non-Taylored fields at the tail of input, and make them into a normal-ordered product*)
result = result + R @@ Join[resultForGivenPartition[[;; i - 1]], RList[[i;;]]];

i = 1;
resultForGivenPartition = ConstantArray[None, RLength];
], partitions];
result]


(*Taylor at a given order is a composition of Tayloring the holomorphic and antiholomorphic parts*)
TaylorAtOrder[Ra_/;RTest[Ra], ordHolo_,ordAntiHolo_, z0_,z0bar_]:= TaylorAtOrderAntiHolo[TaylorAtOrderHolo[Ra, ordHolo, z0], ordAntiHolo, z0bar];


(*Implement multilinearity of Taylor*)

TaylorAtOrder[a_+b_,c_,d_,e_,f_]:=TaylorAtOrder[a,c,d,e,f]+TaylorAtOrder[b,c,d,e,f]
TaylorAtOrder[a_ b_,c_,d_,e_,f_]:=a TaylorAtOrder[b,c,d,e,f]/;isScalarFactorQ[a]

TaylorAtOrderHolo[a_+b_,c_,d_]:=TaylorAtOrderHolo[a,c,d]+TaylorAtOrderHolo[b,c,d]
TaylorAtOrderHolo[a_ b_,c_,d_]:=a TaylorAtOrderHolo[b,c,d]/;isScalarFactorQ[a]

TaylorAtOrderAntiHolo[a_+b_,c_,d_]:=TaylorAtOrderAntiHolo[a,c,d]+TaylorAtOrderAntiHolo[b,c,d]
TaylorAtOrderAntiHolo[a_ b_,c_,d_]:=a TaylorAtOrderAntiHolo[b,c,d]/;isScalarFactorQ[a]

TaylorAtOrder[0, ord1_, ord2_, z0_, z0bar_]:= 0;
TaylorAtOrderHolo[0, ord_, z0_]:= 0;
TaylorAtOrderAntiHolo[0, ord_, z0bar_]:= 0;

(* Scalars (no local fields) are constant under Taylor expansion. *)
TaylorAtOrderHolo[a_, 0, z0_] := a /; isScalarFactorQ[a];
TaylorAtOrderHolo[a_, ord_ /; ord > 0, z0_] := 0 /; isScalarFactorQ[a];
TaylorAtOrderAntiHolo[a_, 0, z0bar_] := a /; isScalarFactorQ[a];
TaylorAtOrderAntiHolo[a_, ord_ /; ord > 0, z0bar_] := 0 /; isScalarFactorQ[a];
TaylorAtOrder[a_, 0, 0, z0_, z0bar_] := a /; isScalarFactorQ[a];
TaylorAtOrder[a_, ordHolo_, ordAntiHolo_, z0_, z0bar_] := 0 /; ((ordHolo > 0 || ordAntiHolo > 0) && isScalarFactorQ[a]);


(*Taylor to zeroth order preserves the input*)
TaylorAtOrderHolo[Ra_/;RTest[Ra], 0, z0_]:= R @@ Map[addHoloDerivatives[#, 0, z0] &, Ra];
TaylorAtOrderAntiHolo[Ra_/;RTest[Ra], 0, z0bar_]:= R @@ Map[addAntiHoloDerivatives[#, 0, z0bar] &, Ra];


(* ::Subsubsection:: *)
(*Compute partitions*)


holomorphicLength::usage = "Computes how many holomorphic fields are in a normal-ordered product";
holomorphicLength[Ra_/; RTest[Ra], z0_]:= Module[{length = 0}, 
Scan[Function[Relem, If[isHolomorphic[Head[Relem]] && !isAtPointHolo[Relem,z0],length = length + 1]],Ra];
length
];


antiHolomorphicLength::usage = "Computes how many antiholomorphic fields are in a normal-ordered product";
antiHolomorphicLength[Ra_/; RTest[Ra], z0bar_]:= Module[{length = 0}, 
Scan[Function[Relem, If[isAntiHolomorphic[Head[Relem]] && !isAtPointAntiHolo[Relem,z0bar], length = length + 1]],Ra];
length
];


computePartition::usage = "Computes partitions, including zeros: for example partition of 1 into 2 gives both {1,0} and {0,1}";
computePartition[order_, length_]:= computePartition[order, length] =
DeleteDuplicates@Flatten[Permutations/@(Select[IntegerPartitions[order,{length},Range[0,order]],Length[#]==length&]),1];


(* ::Subsubsection:: *)
(*Check if field needs expanding*)


isAtPointHolo::usage = "Check if holomorphic field is at a point";
isAtPointAntiHolo::usage = "Check if antiholomorphic field is at a point";


isAtPointHolo[b[n_, z_], z0_] := SameQ[z,z0];
isAtPointHolo[c[n_, z_], z0_] := SameQ[z,z0];
isAtPointAntiHolo[bt[n_, zbar_], z0bar_] := SameQ[zbar,z0bar];
isAtPointAntiHolo[ct[n_, zbar_], z0bar_] := SameQ[zbar,z0bar];


(* ::Subsubsection:: *)
(*Define adding derivatives*)


addHoloDerivatives::usage = "Adds holomorphic derivatives to a holomorphic field";
addAntiHoloDerivatives::usage = "Adds holomorphic derivatives to an antiholomorphic field";


addHoloDerivatives[b[n_,z_], ord_,z0_]:= (z-z0)^ord/Factorial[ord] b[n+ord,z0];


addHoloDerivatives[c[n_,z_], ord_, z0_]:= (z-z0)^ord/Factorial[ord]c[n+ord,z0];


addAntiHoloDerivatives[bt[n_,z_], ord_,z0bar_]:= (z-z0bar)^ord/Factorial[ord] bt[n+ord,z0bar];


addAntiHoloDerivatives[ct[n_,z_], ord_, z0bar_]:= (z-z0bar)^ord/Factorial[ord]ct[n+ord,z0bar];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
