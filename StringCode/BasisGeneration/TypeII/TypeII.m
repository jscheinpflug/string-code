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


generateBasisHolo::usage = "Generates basis in the holomorphic sector";
generateBasisHolo[maxWeight_, {minPicture_, maxPicture_}, {minGhostNumber_, maxGhostNumber_}, {minBackgroundCharge_, maxBackgroundCharge_}]:= 
Module[{backgroundCharges = 
Select[getBackgroundCharges[maxWeight, {minPicture, maxPicture}, {minGhostNumber, maxGhostNumber}],(minBackgroundCharge <= # <= maxBackgroundCharge)&],
backgroundWeights, basisUpToWeight, groundStates, gradedBasisUpToWeight, result},

(*Get weights of possible \[Phi] background charge insertions*)
backgroundWeights = Map[weightOfBackgroundCharge, backgroundCharges];

(*Generate basis of negative modes- note that the modes are always (half-)integer because of superconformal algebra*)
basisUpToWeight = generateNegativeModesHoloUpToWeight[Max[(Plus[maxWeight, -#]&) @ backgroundWeights] + 1];

(*Grade the above basis by picture and ghost number*)
gradedBasisUpToWeight = gradeBasisUpToWeightHolo[basisUpToWeight];

(*Join the negative mode actions with ground states expphi, and c_1, c_0, c_1 c_0, then filter by picture and ghost numbers*)
groundStates = generateGroundStates[backgroundCharges];

result = joinModesWithGroundStates[groundStates, gradedBasisUpToWeight, maxWeight, {minPicture, maxPicture}, {minGhostNumber, maxGhostNumber}];

result];


(*Give some default values to holomorphic basis generation*)
generateBasisHolo[maxWeight_, {minPicture_, maxPicture_}, {minGhostNumber_, maxGhostNumber_}]:= 
generateBasisHolo[maxWeight, {minPicture, maxPicture}, {minGhostNumber, maxGhostNumber}, {-Infinity, Infinity}];
generateBasisHolo[maxWeight_, minPicture_, maxGhostNumber_]:= generateBasisHolo[maxWeight, {minPicture, -1}, {1, maxGhostNumber}, {-Infinity, Infinity}]
generateBasisHolo[maxWeight_, minPicture_, maxGhostNumber_, {minBackgroundCharge_, maxBackgroundCharge_}]:= 
generateBasisHolo[maxWeight, {minPicture, -1}, {1, maxGhostNumber}, {minBackgroundCharge, maxBackgroundCharge}]


(* ::Subsubsection::Closed:: *)
(*Generate excited modes*)


integerPartitions::usage = "Integer partitions of a given number";
integerPartitions[partitionNumber_]:= integerPartitions[partitionNumber] = IntegerPartitions[partitionNumber];


integerPartitionsInto::usage = "Integer partitions of a given number into another number, including zeros: for example partition of 1 into 2 is {1,0}, {0,1}";
integerPartitionsInto[partitionNumber_, into_] := computePartition[partitionNumber, into]


integerPartitionsIntoTwo::usage = "Integer partitions into two - automatically works for partitioning half-integer";
integerPartitionsIntoTwo[partitionNumber_] := integerPartitionsIntoTwo[partitionNumber] = Module[{n = Floor[partitionNumber]},
  Table[{k, partitionNumber - k}, {k, 0, n}]
]


fermionicIntegerPartitions::usage = "Non-repeating integer partitions of a given number";
fermionicIntegerPartitions[partitionNumber_]:= fermionicIntegerPartitions[partitionNumber] = Select[integerPartitions[partitionNumber], DuplicateFreeQ];


getIntegerPartitionsForField::usage = "Given a field, determine which integer partitions one should take [fermionic or bosonic]";

getIntegerPartitionsForField[field_/;(isBoson[field] || (isFermion[field] && isIndexed[field])), fieldWeight_, partitionNumber_] := getIntegerPartitionsForField[field, fieldWeight, partitionNumber] = 

(*If weight of field is non-integer, create a partition with increments given by that field weight, otherwise the increments are 1*)
If[IntegerQ[fieldWeight],
Select[integerPartitions[partitionNumber], AllTrue[#, (# >= fieldWeight) &]&],
Select[fieldWeight integerPartitions[1/fieldWeight partitionNumber], AllTrue[#, (# >= fieldWeight) &]&]
]

getIntegerPartitionsForField[field_/;isFermion[field], fieldWeight_, partitionNumber_]:= getIntegerPartitionsForField[field, fieldWeight, partitionNumber] = 
(*If weight of field is non-integer, create a partition with increments given by that field weight, otherwise the increments are 1*)
If[IntegerQ[fieldWeight],
Select[fermionicIntegerPartitions[partitionNumber], AllTrue[#, (# >= fieldWeight) &]&],
Select[fieldWeight fermionicIntegerPartitions[1/fieldWeight partitionNumber], AllTrue[#, (# >= fieldWeight) &]&]

]


generateNegativeModesHoloUpToWeight::usage = "Generates negative modes up to a given weight, in the holomorphic sector";
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
(*For each weight [with integer increments] up to maxWeight, generate negative modes for that weight*)
AssociateTo[assocToField, 
weight -> generateNegativeModesForField[simpleField, simpleFieldWeight, getIntegerPartitionsForField[simpleField, simpleFieldWeight, weight]]],
{weight, 1, maxWeight}],
Do[
(*For each weight [with non-integer increments] up to maxWeight, generate negative modes for that weight*)
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


combineNegativeModesToWeight::usage = "Given a set of negative modes for each field, combine them up to a given weight";
combineNegativeModesToWeight[weight_, modesAssoc_, simpleFields_]:= combineNegativeModesToWeight[weight, modesAssoc, simpleFields] = 
Module[{result, simpleFieldsIntegerWeight, simpleFieldsIntegerWeightLength, simpleFieldsHalfIntegerWeight, simpleFieldsHalfIntegerWeightLength, 
simpleFieldsIntegerWeightPartitions, simpleFieldsHalfIntegerWeightPartitions, modesAssocInteger, modesAssocHalfInteger, modesAssocIntegerValues,
modesAssocHalfIntegerValues, integerValues, halfIntegerValues, allValues, numberOfIntegerSectors, numberOfHalfIntegerSectors},

(*Split the required modding into integer and (half-)integer parts*)
simpleFieldsIntegerWeight = Select[simpleFields, IntegerQ[weightSymbolHolo[#]] &];
simpleFieldsIntegerWeightLength = Length[simpleFieldsIntegerWeight];
simpleFieldsHalfIntegerWeight = Select[simpleFields, (IntegerQ[2 weightSymbolHolo[#]] && OddQ[2 weightSymbolHolo[#]]) &];
simpleFieldsHalfIntegerWeightLength = Length[simpleFieldsHalfIntegerWeight];

(*Split modes into integer and half-integer*)
modesAssocInteger = KeySelect[modesAssoc, IntegerQ[weightSymbolHolo[#]] &];
modesAssocIntegerValues = Values[modesAssocInteger];
modesAssocHalfInteger = KeySelect[modesAssoc, (IntegerQ[2 weightSymbolHolo[#]] && OddQ[2 weightSymbolHolo[#]]) &];
modesAssocHalfIntegerValues = Values[modesAssocHalfInteger];

result = 
(*Partition weight between integer and half-integer modes*)
Function[{partitionWeightInteger, partitionWeightHalfInteger}, 

simpleFieldsIntegerWeightPartitions = integerPartitionsInto[partitionWeightInteger, simpleFieldsIntegerWeightLength];
simpleFieldsHalfIntegerWeightPartitions = 1/2 integerPartitionsInto[2 partitionWeightHalfInteger, simpleFieldsHalfIntegerWeightLength];

(*Compute subpartitions of the above two partitions*)
Select[
Function[{simpleFieldsIntegerWeightPartition, simpleFieldsHalfIntegerWeightPartition},

(*Get both integer and half-integer modes at weights given by the above two subpartitions*)
integerValues = Select[MapThread[Lookup[#1, #2, {}] &, {modesAssocIntegerValues, simpleFieldsIntegerWeightPartition}], (# =!= {})&];
halfIntegerValues = Select[MapThread[Lookup[#1, #2, {}] &, {modesAssocHalfIntegerValues, simpleFieldsHalfIntegerWeightPartition}], (#=!={})&];

(*Combine the above integer and half-integer modes into a single set of modes*)
allValues = Join[integerValues, halfIntegerValues];

(*Return all combinations of each of the mode sectors*)
If[allValues =!= {},
combineSectors[allValues],
Nothing]

] @@@ Tuples[{simpleFieldsIntegerWeightPartitions, simpleFieldsHalfIntegerWeightPartitions}], 
(# =!= {})&]
] @@@ integerPartitionsIntoTwo[weight];

If[result =!= {{{{}}}},
Flatten[result,2],
{}]
]


combineSectors::usage = "Combines all of the mode sectors";
combineSectors[allValues_]:= combineSectors[allValues] = Join @@@ Tuples[allValues]


generateNegativeModesForField::usage = "Generate negative modes for a given simple field";

(*Generate negative modes for a given indexed simple field*)
generateNegativeModesForField[field_/; (isSimple[field] && isIndexed[field]), fieldWeight_, partitions_]:= generateNegativeModesForField[field, fieldWeight, partitions] = 
Module[{result, modesForPartition, index, counter = 1}, 

result = 
Select[Map[Function[partition,
modesForPartition =
(*Only keep partitions, which are of integer increments on top the weight of input simple field*)
If[AllTrue[partition, IntegerQ[# - fieldWeight] &],

(*For each partition in input partitions extract modes numbers*)
Map[Function[modeNumber,

(*Keep track of indices of modes*)
index = "normalizedIndex" <> ToString[counter];
counter ++;

(*Get a mode for each in the above set of mode numbers*)
getMode[field, fieldWeight, modeNumber, index]
], partition], {}
];
counter = 1;
modesForPartition], partitions], !(# === {})&];

result]

(*Generate negative modes for a given non-indexed simple field*)
generateNegativeModesForField[field_/; isSimple[field], fieldWeight_, partitions_]:= generateNegativeModesForField[field, fieldWeight, partitions] = 
Module[{result}, 

result = 
Map[Function[partition,
(*For each partition in input partitions extract modes numbers*)
Map[Function[modeNumber,
(*Get a mode for each in the above set of mode numbers*)
getMode[field, fieldWeight, modeNumber]
], partition]], partitions];

result]


(* ::Subsubsection::Closed:: *)
(*Grade basis*)


gradeBasisUpToWeightHolo::usage = "Grade basis of simple fields up to a given weight by picture and ghost number";
gradeBasisUpToWeightHolo[basisUpToWeight_]:= gradeBasisUpToWeightHolo[basisUpToWeight] = gradeBasisAtWeightHolo /@ basisUpToWeight


gradeBasisAtWeightHolo::usage = "Grade basis of simple fields at a given weight by picture and ghost number";
gradeBasisAtWeightHolo[basisAtWeight_]:= gradeBasisAtWeightHolo[basisAtWeight] =  
GroupBy[basisAtWeight, Through[{totalHolPictureOfList, totalHolGhostNumberOfList}[#]] &];


totalHolPictureOfList::usage = "Computes total holomorphic picture of a list of fields";
totalHolPictureOfList[list_]:= Map[pictureHol, list]//Total;

totalHolPictureOfList::usage = "Computes total holomorphic picture of a list of fields";
totalHolGhostNumberOfList[list_]:= Map[ghostNumberHolo, list]//Total;


(* ::Subsubsection:: *)
(*Generate ground states*)


generateGroundStates::usage = "Generate ground states given a set of background charges of \[Phi]";
generateGroundStates[backgroundCharges_]:= Module[{exp\[Phi]SymbolChoice, exp\[Phi]Background, backgroundChargeWeight},
Association @ Catenate @ Map[Function[backgroundCharge, 
backgroundChargeWeight = weightOfBackgroundCharge[backgroundCharge];
If[backgroundCharge != 0,
If[IntegerQ[backgroundChargeWeight],
exp\[Phi]SymbolChoice = exp\[Phi]b, exp\[Phi]SymbolChoice = exp\[Phi]f];
exp\[Phi]Background = exp\[Phi]SymbolChoice[backgroundCharge,0],
exp\[Phi]Background = 1];
{
{backgroundCharge, 1, backgroundChargeWeight - 1} -> R[c[0,0], exp\[Phi]Background],
{backgroundCharge, 1, backgroundChargeWeight} -> R[c[1,0], exp\[Phi]Background],
{backgroundCharge, 2, backgroundChargeWeight - 1} -> R[c[0,0], c[1,0], exp\[Phi]Background]
}], backgroundCharges]];


(* ::Subsubsection:: *)
(*Join modes with ground states and filter by picture/ghost number*)


joinModesWithGroundStates::usage = "Joins modes up to a given weight with ground states, and filters by picture/ghost numbers";
joinModesWithGroundStates[groundStates_, modesUpToWeight_, maxWeight_, {minPicture_, maxPicture_},{minGhostNumber_, maxGhostNumber_}] := 
Module[{modePicture, modeGhostNumber, basisPicture, basisGhostNumber, basisWeight, combinedPicture, combinedGhostNumber}, 
Reap[
KeyValueMap[Function[{weight, modesAtWeight},
KeyValueMap[
Function[{modeKey, modeValues},
{modePicture, modeGhostNumber} = modeKey;
KeyValueMap[
Function[{basisKey, basisValue},
{basisPicture, basisGhostNumber, basisWeight} = basisKey;
combinedPicture = modePicture + basisPicture;
combinedGhostNumber = modeGhostNumber + basisGhostNumber;
If[minPicture <= combinedPicture <= maxPicture && minGhostNumber <= combinedGhostNumber <= maxGhostNumber && 0<= basisWeight + weight <= maxWeight,
Scan[
Function[modeValue,
Sow[R[R @@ modeValue, basisValue]]
],modeValues]
]], groundStates
]
], modesAtWeight]
], modesUpToWeight]][[2,1]]
]


(* ::Subsubsection::Closed:: *)
(*Get modes of simple fields*)


getMode::usage = "Creates a mode of a given simple field";

getMode[field_/;(isSimple[field] && isIndexed[field]), fieldWeight_, modeNumber_, index_]:= field[index, modeNumber-fieldWeight, 0];
getMode[field_/;isSimple[field], fieldWeight_, modeNumber_]:= field[modeNumber-fieldWeight,0];


(* ::Subsubsection::Closed:: *)
(*Compute weight of exp\[Phi]*)


weightOfBackgroundCharge::usage = "Computes weight of exp\[Phi] at a given background charge";
weightOfBackgroundCharge[q_]:= -1/2 q (q+2);


(* ::Subsection:: *)
(*Get allowed values for background charges of the \[Phi] linear dilaton*)


getBackgroundCharges::usage = "Get possible background charges at a given range of pictures, ghost numbers up to a given weight";
getBackgroundCharges[maxWeight_, {minPicture_, maxPicture_}, {minGhostNumber_, maxGhostNumber_}]:= Module[{result, gh, pic, q, qSolution},
qSolution = Reduce[Or @@ Flatten[Table[getBackgroundChargesAtGhPic[maxWeight, pic, gh, q], {gh, minGhostNumber, maxGhostNumber}, {pic, minPicture, maxPicture}]],q,Reals];
If[qSolution === False, result = {}, result = generateIntegersInIntervals[Map[inequalityToInterval, If[Head[qSolution]===Or, qSolution/.{Or -> List}, {qSolution}]]]];
result] 

(*Default maximal picture is -1 and minimal ghost number is 1*)
getBackgroundCharges[maxWeight_, minPicture_, maxGhostNumber_]:= 
getBackgroundCharges[maxWeight, {minPicture, -1}, {1, maxGhostNumber}]


getBackgroundChargesAtGhPic::usage = "Get possible background charges at a given picture, ghost number up to a given weight";
getBackgroundChargesAtGhPic[maxWeight_, pic_, gh_, q_]:= Module[{result, boundPositiveCharge, boundNegativeCharge, boundCharge},

(*for each q, find whether there exists at least one state of a given picture, ghost number below some weight*)
(*one simply computes the lowest possible weight of a state with given q and picture, ghost number and compares to maxWeight*)
boundPositiveCharge = Reduce[{-1/2 q (q+2) + 1/2 (q+pic)(q+pic+1) + 1/2 (q+pic+gh)(q+pic+gh+3) <= maxWeight, q+pic >= 0, q+pic+gh >= 0, q >=0}, q,Reals];
boundNegativeCharge = Reduce[{-1/2 (-q) (-q-2) + 1/2 (-q+pic)(-q+pic+1) + 1/2 (-q+pic+gh)(-q+pic+gh-3) <= maxWeight, (-q+pic)>= 0,(-q+pic+gh)>=0, q <=0},q,Reals];
boundCharge = Reduce[boundPositiveCharge || boundNegativeCharge, q, Reals];
result = boundCharge;

result]


inequalityToInterval::usage = "Converts an inequality to an interval";
inequalityToInterval[Inequality[a_, q___, b_]] := {a,b}
inequalityToInterval[Equal[q___,a_]]:= {a,a};


generateIntegersInIntervals::usage = "Given a set of intervals, generate integers in them";
generateIntegersInIntervals[intervals__]:= Module[{result}, 
result = Flatten[Map[generateIntegersInInterval, intervals]];
result]


generateIntegersInIntervals::usage = "Given an interval, generate integers in it";
generateIntegersInInterval[interval__]:= Module[{result, low, high},

low = Ceiling[interval[[1]]];
high = Floor[interval[[2]]];
If[high >= low, result = Range[low, high], result = {}];

result]


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
