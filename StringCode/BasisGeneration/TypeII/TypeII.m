(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`BasisGeneration`TypeII`"];


Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`TypeII`"];


(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


(* ::Input::Initialization:: *)
Begin["Private`"];


(* ::Subsection:: *)
(*Get allowed values for background charges of the \[Phi] linear dilaton*)


backgroundCharges[maxWeight_, {minPicture_, maxPicture_}, {minGhostNumber_, maxGhostNumber_}]:= Module[{result, gh, pic, q, qSolution},
qSolution = Reduce[Or @@ Flatten[Table[backgroundChargesAtGhPic[maxWeight, pic, gh, q], {gh, minGhostNumber, maxGhostNumber}, {pic, minPicture, maxPicture}]],q,Reals];
If[qSolution === False, result = {}, result = generateIntegersInIntervals[Map[inequalityToInterval, If[Head[qSolution]===Or, qSolution/.{Or -> List}, {qSolution}]]]];
result] 


backgroundCharges[maxWeight_, minPicture_, maxGhostNumber_]:= 
backgroundCharges[maxWeight, {minPicture, -1}, {1, maxGhostNumber}]


backgroundChargesAtGhPic[maxWeight_, pic_, gh_, q_]:= Module[{result, boundPositiveCharge, boundNegativeCharge, boundCharge},
(*for each q, find whether there exists at least one state of a given picture, ghost number below some weight*)
(*one simply computes the lowest possible weight of a state with given q and picture, ghost number and compares to maxWeight*)
boundPositiveCharge = Reduce[{-1/2 q (q+2) + 1/2 (q+pic)(q+pic+1) + 1/2 (q+pic+gh)(q+pic+gh+3) <= maxWeight, q+pic >= 0, q+pic+gh >= 0, q >=0}, q,Reals];
boundNegativeCharge = Reduce[{-1/2 (-q) (-q-2) + 1/2 (-q+pic)(-q+pic+1) + 1/2 (-q+pic+gh)(-q+pic+gh-3) <= maxWeight, (-q+pic)>= 0,(-q+pic+gh)>=0, q <=0},q,Reals];
boundCharge = Reduce[boundPositiveCharge || boundNegativeCharge, q, Reals];
result = boundCharge;
result]


inequalityToInterval[Inequality[a_, q___, b_]] := {a,b}


generateIntegersInIntervals[intervals__]:= Module[{result}, 
result = Flatten[Map[generateIntegersInInterval, intervals]];
result]


generateIntegersInInterval[interval__]:= Module[{result, low, high},
low = Ceiling[interval[[1]]];
high = Floor[interval[[2]]];
If[high >= low, result = Range[low, high], result = {}];
result]


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
