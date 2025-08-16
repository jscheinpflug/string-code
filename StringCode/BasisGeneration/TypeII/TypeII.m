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
(*Generate basis*)


generateBasisHolo[maxWeight_, {minPicture_, maxPicture_}, {minGhostNumber_, maxGhostNumber_}, {minBackgroundCharge_, maxBackgroundCharge_}]:= 
Module[{backgroundCharges = 
Select[getBackgroundCharges[maxWeight, {minPicture, maxPicture}, {minGhostNumber, maxGhostNumber}],(minBackgroundCharge <= # <= maxBackgroundCharge)&],
backgroundWeights, basisUpToWeightHolo, result},
backgroundWeights = Map[weightOfBackgroundCharge, backgroundCharges];

(*generate basis of negative mode actions - note that the modes are always (half-)integer because of superconformal algebra*)
basisUpToWeightHolo = generateNegativeModesHoloUpToWeight[Max[(Plus[maxWeight, -#]&) @ backgroundWeights] + 1];
Print[basisUpToWeightHolo];

(*join the negative mode actions with ground states expphi, and c_1, c_0, c_1 c_0*)

(*select appropriate pictures and ghost numbers from all states up to the required weight*)

result];


generateBasisHolo[maxWeight_, {minPicture_, maxPicture_}, {minGhostNumber_, maxGhostNumber_}]:= 
generateBasisHolo[maxWeight, {minPicture, maxPicture}, {minGhostNumber, maxGhostNumber}, {-Infinity, Infinity}];
generateBasisHolo[maxWeight_, minPicture_, maxGhostNumber_]:= generateBasisHolo[maxWeight, {minPicture, -1}, {1, maxGhostNumber}, {-Infinity, Infinity}]
generateBasisHolo[maxWeight_, minPicture_, maxGhostNumber_, {minBackgroundCharge_, maxBackgroundCharge_}]:= 
generateBasisHolo[maxWeight, {minPicture, -1}, {1, maxGhostNumber}, {minBackgroundCharge, maxBackgroundCharge}]


(* ::Subsubsection:: *)
(*Generate excited modes*)


integerPartitions[partitionNumber_]:= integerPartitions[partitionNumber] = IntegerPartitions[partitionNumber];


integerPartitionsInto[partitionNumber_, into_] := computePartition[partitionNumber, into]


integerPartitionsIntoTwo[partitionNumber_] := integerPartitionsIntoTwo[partitionNumber] = Module[{n = Floor[partitionNumber]},
  Table[{k, partitionNumber - k}, {k, 0, n}]
]


fermionicIntegerPartitions[partitionNumber_]:= fermionicIntegerPartitions[partitionNumber] = Select[integerPartitions[partitionNumber], DuplicateFreeQ];


getIntegerPartitionsForField[field_/;(isBoson[field] || (isFermion[field] && isIndexed[field])), fieldWeight_, partitionNumber_] := getIntegerPartitionsForField[field, fieldWeight, partitionNumber] = 
If[IntegerQ[fieldWeight],
Select[integerPartitions[partitionNumber], AllTrue[#, (# >= fieldWeight) &]&],
Select[fieldWeight integerPartitions[1/fieldWeight partitionNumber], AllTrue[#, (# >= fieldWeight) &]&]
]

getIntegerPartitionsForField[field_/;isFermion[field], fieldWeight_, partitionNumber_]:= getIntegerPartitionsForField[field, fieldWeight, partitionNumber] = 
If[IntegerQ[fieldWeight],
Select[fermionicIntegerPartitions[partitionNumber], AllTrue[#, (# >= fieldWeight) &]&],
Select[fieldWeight fermionicIntegerPartitions[1/fieldWeight partitionNumber], AllTrue[#, (# >= fieldWeight) &]&]
]


generateNegativeModesHoloUpToWeight[maxWeight_]:= generateNegativeModesHoloUpToWeight[maxWeight] = 
Module[{result, simpleFields = Select[simplefields,isHolomorphic], negativeModesSeparate, modeAssoc, assocToField, simpleFieldWeight, weightAssoc}, 

(*for each simple field build a tower of negative modes with modding up to maxWeight*)
modeAssoc = Association[];
negativeModesSeparate = Map[
Function[simpleField,
assocToField = Association[];
simpleFieldWeight = weightSymbolHolo[simpleField];
If[IntegerQ[simpleFieldWeight],
Do[
AssociateTo[assocToField, 
weight -> generateNegativeModesForField[simpleField, simpleFieldWeight, getIntegerPartitionsForField[simpleField, simpleFieldWeight, weight]]],
{weight, 1, maxWeight}],
Do[
AssociateTo[assocToField, 
simpleFieldWeight weight -> generateNegativeModesForField[simpleField, simpleFieldWeight, getIntegerPartitionsForField[simpleField, simpleFieldWeight, simpleFieldWeight weight]]],
{weight, 1, 1/simpleFieldWeight maxWeight}]];
AssociateTo[modeAssoc, simpleField -> assocToField]],
 simpleFields];
 
weightAssoc = Association[];
(*combine the negative modes of each simple field - assume (half-)integer modding*)
Scan[AssociateTo[weightAssoc, # -> combineNegativeModesToWeight[#, modeAssoc, simpleFields]] &, Range[0, maxWeight, 1/2]];

result = weightAssoc;

result]


combineNegativeModesToWeight[weight_, modesAssoc_, simpleFields_]:= combineNegativeModesToWeight[weight, modesAssoc, simpleFields] = 
Module[{result, simpleFieldsIntegerWeight, simpleFieldsIntegerWeightLength, simpleFieldsHalfIntegerWeight, simpleFieldsHalfIntegerWeightLength, 
simpleFieldsIntegerWeightPartitions, simpleFieldsHalfIntegerWeightPartitions, modesAssocInteger, modesAssocHalfInteger, modesAssocIntegerValues,
modesAssocHalfIntegerValues, integerValues, halfIntegerValues},

(*split the required modding into integer and (half-)integer parts*)
simpleFieldsIntegerWeight = Select[simpleFields, IntegerQ[weightSymbolHolo[#]] &];
simpleFieldsIntegerWeightLength = Length[simpleFieldsIntegerWeight];
simpleFieldsHalfIntegerWeight = Select[simpleFields, (IntegerQ[2 weightSymbolHolo[#]] && OddQ[2 weightSymbolHolo[#]]) &];
simpleFieldsHalfIntegerWeightLength = Length[simpleFieldsHalfIntegerWeight];

modesAssocInteger = KeySelect[modesAssoc, IntegerQ[weightSymbolHolo[#]] &];
modesAssocIntegerValues = Values[modesAssocInteger];
modesAssocHalfInteger = KeySelect[modesAssoc, (IntegerQ[2 weightSymbolHolo[#]] && OddQ[2 weightSymbolHolo[#]]) &];
modesAssocHalfIntegerValues = Values[modesAssocHalfInteger];

(*for each partition combine negative modes*)
result = Flatten[Function[{partitionWeightInteger, partitionWeightHalfInteger}, 
simpleFieldsIntegerWeightPartitions = integerPartitionsInto[partitionWeightInteger, simpleFieldsIntegerWeightLength];
simpleFieldsHalfIntegerWeightPartitions = 1/2 integerPartitionsInto[2 partitionWeightHalfInteger, simpleFieldsHalfIntegerWeightLength];
Select[Function[{simpleFieldsIntegerWeightPartition, simpleFieldsHalfIntegerWeightPartition},

integerValues = MapThread[Lookup[#1, #2, {}] &, {modesAssocIntegerValues, simpleFieldsIntegerWeightPartition}];
halfIntegerValues = MapThread[Lookup[#1, #2, {}] &, {modesAssocHalfIntegerValues, simpleFieldsHalfIntegerWeightPartition}];

If[AnyTrue[integerValues, (# =!= {}) &] && AnyTrue[halfIntegerValues, (# =!= {}) &],
Join[
Flatten[integerValues, 1],
Flatten[halfIntegerValues, 1]
],
If[AnyTrue[integerValues, (# =!= {}) &] && partitionWeightHalfInteger === 0,
Flatten[integerValues, 1],
If[AnyTrue[halfIntegerValues, (# =!= {}) &] && partitionWeightInteger === 0,
Flatten[halfIntegerValues, 1], {}
]
]]
] @@@ Tuples[{simpleFieldsIntegerWeightPartitions, simpleFieldsHalfIntegerWeightPartitions}], (# =!= {})&]
] @@@ integerPartitionsIntoTwo[weight],1];

If[result =!= {},
FlattenAt[result,1], {}]
]


generateNegativeModesForField[field_/; (isSimple[field] && isIndexed[field]), fieldWeight_, partitions_]:= generateNegativeModesForField[field, fieldWeight, partitions] = 
Module[{result, modesForPartition, index, counter = 1}, 
result = Select[Map[Function[partition,
modesForPartition =
If[AllTrue[partition, IntegerQ[# - fieldWeight] &],
Map[Function[modeNumber,
index = "normalizedIndex" <> ToString[counter];
counter ++;
getMode[field, fieldWeight, modeNumber, index]
], partition], {}
];
counter = 1;
modesForPartition], partitions], !(# === {})&];
result]


generateNegativeModesForField[field_/; isSimple[field], fieldWeight_, partitions_]:= generateNegativeModesForField[field, fieldWeight, partitions] = 
Module[{result}, 
result = Map[Function[partition,
Map[Function[modeNumber,
getMode[field, fieldWeight, modeNumber]
], partition]], partitions];
result]


(* ::Subsubsection:: *)
(*Get modes of simple fields*)


getMode[field_/;(isSimple[field] && isIndexed[field]), fieldWeight_, modeNumber_, index_]:= field[index, modeNumber-fieldWeight, 0];
getMode[field_/;isSimple[field], fieldWeight_, modeNumber_]:= field[modeNumber-fieldWeight,0];


(* ::Subsubsection:: *)
(*Compute weight of exp\[Phi]*)


weightOfBackgroundCharge[q_]:= -1/2 q (q+2);


(* ::Subsection:: *)
(*Get allowed values for background charges of the \[Phi] linear dilaton*)


getBackgroundCharges[maxWeight_, {minPicture_, maxPicture_}, {minGhostNumber_, maxGhostNumber_}]:= Module[{result, gh, pic, q, qSolution},
qSolution = Reduce[Or @@ Flatten[Table[getBackgroundChargesAtGhPic[maxWeight, pic, gh, q], {gh, minGhostNumber, maxGhostNumber}, {pic, minPicture, maxPicture}]],q,Reals];
If[qSolution === False, result = {}, result = generateIntegersInIntervals[Map[inequalityToInterval, If[Head[qSolution]===Or, qSolution/.{Or -> List}, {qSolution}]]]];
result] 


getBackgroundCharges[maxWeight_, minPicture_, maxGhostNumber_]:= 
getBackgroundCharges[maxWeight, {minPicture, -1}, {1, maxGhostNumber}]


getBackgroundChargesAtGhPic[maxWeight_, pic_, gh_, q_]:= Module[{result, boundPositiveCharge, boundNegativeCharge, boundCharge},
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
