(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Brackets`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`StringFields`"];
Needs["StringCode`Operators`"];
Needs["StringCode`OPE`"];
Needs["StringCode`Taylor`"];


(* ::Section:: *)
(*Declare public variables and methods*)


Bracket::usage = "Computes the string bracket";
BracketProjected::usage = "Computes a projection of the string bracket";
actBRST::usage = "Acts with the BRST charge (computes 1-bracket)";


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection::Closed:: *)
(*Define 1-bracket (action of BRST charge)*)


(*Action of BRST charge splits into holomorphic and antiholomorphic parts*)
actBRST[SFa_/; SFtest[SFa]]:= actBRSTHolo[SFa] + actBRSTAntiHolo[SFa];

(*Linearity of BRST charge action*)

actBRST[a_+b_]:=actBRST[a] + actBRST[b];
actBRST[a_ b_]:=a actBRST[b]/;(And @@(FreeQ[a,#]&/@ allfields))
actBRST[0] := 0;

actBRSTAntiHolo[a_+b_]:= actBRSTAntiHolo[a] + actBRSTAntiHolo[b];
actBRSTAntiHolo[a_ b_]:= a actBRSTAntiHolo[b]/;(And @@(FreeQ[a,#]&/@ allfields))
actBRSTAntiHolo[0] := 0;

actBRSTHolo[a_+b_]:= actBRSTHolo[a] +actBRSTHolo[b];
actBRSTHolo[a_ b_]:=a actBRSTHolo[b]/;(And @@(FreeQ[a,#]&/@ allfields))
actBRSTHolo[0] := 0;


(* ::Subsection:: *)
(*Define bracket*)


(*Multilinearity of Bracket*)
Bracket[args___, a_ + b_, rest___] := Bracket[args, a, rest] + Bracket[args, b, rest]

Bracket[args___, a_ b_, rest___] := a Bracket[args, b, rest] /; And @@ (FreeQ[a, #] & /@ Join[allfields,{WedgeProduct}])

(*Join wedge products, give no sign: assuming that we wedge even number of differential as in closed string*)
Bracket[args___, WedgeProduct[a__]b___, rest___]:= WedgeProduct[a, Bracket[args, b, rest]]; 

BracketBosonic::usage = "Defines bosonic part of the bracket, which is shared among string theories";
BracketBosonic[toBracket__/;AllTrue[{toBracket}, SFtest]]:= Module[{result = 0, SFsAtPos, localCoordinateFunctionsHol, localCoordinateFunctionsAntiHol, localCoordinateReplacement, 
moduli, bracketOrder, bracketList = {toBracket}, w, wbar, curlyB, curlyBs, minCGhostModdings, minCbarGhostModdings, SFList, moduliLength, afterApplyingBghosts, afterHeldActionOfPCOs, prefac},
bracketOrder = Length[bracketList];

(*Conformally transform the string field insertions*)
{localCoordinateFunctionsHol, localCoordinateFunctionsAntiHol, w, wbar, moduli, localCoordinateReplacement} = getLocalCoordinateData[bracketOrder];
SFList = placeSFAtPosGivenLocalCoordinates[localCoordinateFunctionsHol, localCoordinateFunctionsAntiHol, bracketList];

(*Create and apply the curly B-ghost insertions, one B-ghost action on the insertions for each modulus*)
moduliLength = Length[moduli];

If[moduliLength > 0,

(*Create the curly B-ghost insertions, one for each modulus*)
curlyB = createCurlyB[SFList, localCoordinateFunctionsHol, localCoordinateFunctionsAntiHol, bracketOrder, moduli, w, wbar];
curlyBs = createCurlyBs[curlyB, moduliLength];

(*Apply the curly B-ghost insertions*)
afterApplyingBghosts = applyCurlyBs[SFList, curlyBs, moduliLength],
afterApplyingBghosts = MultiOp @@ SFList];
result = 1/(-2Pi I)^(1/2 moduliLength) afterApplyingBghosts;
result]


(* ::Subsubsection:: *)
(*Place string fields at positions given by local coordinates*)


placeSFAtPosGivenLocalCoordinates::usage = "Places string fields at positions given by local coordinates of a given bracket";
placeSFAtPosGivenLocalCoordinates[localCoordinateFunctionsHol__, localCoordinateFunctionsAntiHol__, SFs__]:= 
Table[SFAtPos[SFs[[i]], localCoordinateFunctionsHol[[i]], localCoordinateFunctionsAntiHol[[i]]],{i,1,Length[SFs]}]


(* ::Subsubsection:: *)
(*Factorize MultiOp times constant*)


extractPrefacFromMultiOpTimesConstant::usage = "Extracts constant prefactor from possible constant multiplied by multi-local operator";
extractPrefacFromMultiOpTimesConstant[Times[a_, Ma_/;MultiOptest[Ma]]] := a;
extractPrefacFromMultiOpTimesConstant[Ma_/;MultiOptest[Ma]] := 1;
extractPrefacFromMultiOpTimesConstant[1] := 1;

extractListFromMultiOpTimesConstant::usage = "Extracts the list of operators inside a multi-local operator product possibly multiplied by a constant prefactor";
extractListFromMultiOpTimesConstant[Times[a_, Ma_/;MultiOptest[Ma]]] := List @@ Ma;
extractListFromMultiOpTimesConstant[Ma_/;MultiOptest[Ma]] := List @@ Ma;


(* ::Subsection:: *)
(*Define projected bracket*)


(*Projected bracket is Bracket composed with a projection*)
BracketProjected[toBracket__/; AllTrue[{toBracket}, SFtest], weightHolo_, weightAntiHolo_]:=
b0mHold[BracketProjection[(Bracket[toBracket]/.{b0mHold[a__]:>a}), weightHolo, weightAntiHolo]];

(*Multilinearity of projected Bracket*)
BracketProjected[args___, a_ + b_, rest___,  weightHolo_, weightAntiHolo_] := BracketProjected[args, a, rest,  weightHolo, weightAntiHolo] + BracketProjected[args, b, rest, weightHolo, weightAntiHolo]
BracketProjected[args___, a_ b_, rest___, weightHolo_, weightAntiHolo_] := a BracketProjected[args, b, rest, weightHolo, weightAntiHolo] /; And @@ (FreeQ[a, #] & /@ Join[allOperators,{WedgeProduct}])

(*Join wedge products, give no sign: assuming that we wedge even number of differential as in closed string*)
BracketProjected[args___, WedgeProduct[a__] b___, rest___, weightHolo_, weightAntiHolo_] := WedgeProduct[a, BracketProjected[args, b, rest, weightHolo, weightAntiHolo]]

(*Multilinearity of Bracket projection*)
BracketProjection[a_ + b_, weightHolo_, weightAntiHolo_] :=
 BracketProjection[a, weightHolo, weightAntiHolo] + BracketProjection[b, weightHolo, weightAntiHolo]
 
BracketProjection[a_ b_, weightHolo_, weightAntiHolo_] := 
a BracketProjection[b, weightHolo, weightAntiHolo] /; And @@ (FreeQ[a, #] & /@ Join[allOperators,{WedgeProduct}])

(*Join wedge products, give no sign: assuming that we wedge even number of differential as in closed string*)
BracketProjection[WedgeProduct[a__] b___, weightHolo_, weightAntiHolo_] := WedgeProduct[a, BracketProjection[b, weightHolo, weightAntiHolo]]


(* ::Subsection:: *)
(*Collapse multi-local operator via OPE*)


CollapseFree::usage = "Collapse multi-local of free fields operator via OPE";
CollapseFree[multiOpHolo_/;MultiOptest[multiOpHolo], multiOpAntiHolo_/;MultiOptest[multiOpAntiHolo], \[Epsilon]Holo_, \[Epsilon]AntiHolo_]:= 
Module[{OPEHolo, OPEAntiHolo},

(*Rescale positions of operators in the bracket by a common \[Epsilon]Holo/\[Epsilon]AntiHolo to ease weight projection, and then perform OPE*)
{OPEHolo, OPEAntiHolo} = {OPE @@ rescaleMultiOp[multiOpHolo, \[Epsilon]Holo], OPE @@ rescaleMultiOp[multiOpAntiHolo, \[Epsilon]AntiHolo]};
{OPEHolo, OPEAntiHolo}
]

CollapseInteracting::usage = "Collapse multi-local of free fields operator via OPE, keep only singular parts";
CollapseInteracting[interactingOPE_, \[Epsilon]Holo_, \[Epsilon]AntiHolo_, weightHolo_, weightAntiHolo_]:= 
Module[{result, weight = weightHolo + weightAntiHolo, weightRange},
(*Assume that operators of weights from 0 to weight can appear, consider weights by steps of 2 to preserve level-matching condition*)
weightRange = Range[0, weight, 2];
(*Write down the singular part of OPE, with operators in a given weight range*)
Total @ Map[1/(\[Epsilon]Holo \[Epsilon]AntiHolo)^((weight - #)/2) InteractingProjection[interactingOPE, #] &, weightRange]
]


(* ::Subsection:: *)
(*Factorize operators into holomorphic and anti-holomorphic parts*)


(* ::Subsubsection:: *)
(*Factorize multi-local operators*)


factorizeMultiOp::usage = "Factorize multi-local operator into holomorphic and antiholomorphic multi-local operators";
factorizeMultiOp[multiOp_/;MultiOptest[multiOp]]:=
Module[{multiOpReplaced = multiOp/.factorizationReplacement, localOpFactorized, localOpFree, localOpInteracting, localOpPrefac, localOpList,
localOpHolo, localOpAntiHolo, localOpsHolo, localOpsAntiHolo,localOpsHoloAntiHolo, localOpsInteracting, prefac = 1},
{localOpsHolo, localOpsAntiHolo, localOpsInteracting, localOpsHoloAntiHolo} = 
Reap[Scan[Function[localOp,
If[OpTest[localOp],
localOpFree = localOp[[1]];
localOpInteracting = localOp[[2]],
If[Rtest[localOp],
localOpFree = localOp;
localOpInteracting = 1,
localOpFree = 1;
localOpInteracting = localOp;]
];
localOpPrefac = extractPrefacFromRTimesConstant[localOpFree]/.{WedgeProduct[a___]->1};
localOpList = extractListFromRTimesConstant[localOpFree];
localOpFactorized = splitOperators[localOpList, isHolomorphic, isAntiHolomorphic];
prefac = prefac * localOpPrefac;
{localOpHolo, localOpAntiHolo} = {R @@ localOpFactorized[[1]], R @@ localOpFactorized[[2]]};
Sow[localOpHolo, "Holo"];
Sow[localOpAntiHolo, "AntiHolo"];
Sow[localOpInteracting, "Interacting"];
Sow[localOpList, "Holo and AntiHolo"];
], List @@ multiOpReplaced]][[2]];
{MultiOp @@ localOpsHolo, MultiOp @@ localOpsAntiHolo, MultiOp @@ localOpsInteracting, factorizationSign[Flatten[localOpsHoloAntiHolo], isHolomorphic, isAntiHolomorphic]}]


(* ::Subsubsection:: *)
(*Factorize normal-ordered product utils*)


extractPrefacFromRTimesConstant::usage = "Extracts constant prefactor from possible constant multiplied by normal-ordered product";
extractPrefacFromRTimesConstant[Times[a_, Ra_/;Rtest[Ra]]] := a;
extractPrefacFromRTimesConstant[Ra_/;Rtest[Ra]] := 1;
extractPrefacFromRTimesConstant[1] := 1;

extractListFromRTimesConstant::usage = "Extracts the list of operators inside a normal-ordered product possibly multiplied by a constant prefactor";
extractListFromRTimesConstant[Times[a_, Ra_/;Rtest[Ra]]] := List @@ Ra;
extractListFromRTimesConstant[Ra_/;Rtest[Ra]] := List @@ Ra;


(* ::Subsubsection:: *)
(*Rescale all chiral local operators [position is their last argument] inside a factorized MultiOp*)


rescaleMultiOp::usage = "Rescale all chiral [after factorization] local operators [position is their last argument] inside a MultiOp";
rescaleMultiOp[multiOp_/;MultiOptest[multiOp], rescalingFactor_]:= Module[{multiOpList = List @@ multiOp}, 
MultiOp @@ Map[rescaleOp[rescalingFactor], multiOpList]]


rescaleOp::usage = "Rescales a normal-ordered product";
rescaleOp[rescalingFactor_][op_]:= Module[{opList = List @@ op}, 
R @@ Map[rescalePositionBy[rescalingFactor], opList]]


rescalePositionBy::usage = "Rescales a chiral local operator";
rescalePositionBy[rescalingFactor_][op_]:= op/.{symbol_[args__, pos_]:> symbol[args, rescalingFactor pos]};


(* ::Subsection:: *)
(*Project OPE onto a given weight*)


projectOPE::usage = "Project OPE of local operators onto a given holomorphic, antiholomorphic weight";
projectOPE[OPEHolo_, OPEAntiHolo_, weightHolo_, weightCountingParameterHolo_, weightAntiHolo_, weightCountingParameterAntiHolo_, interactingWeight_, OPEInteracting_, OPEInteractingSingular_]:= 
Module[{result = 0, powerHolo,  powerAntiHolo, expansionOrderHolo, OPEExpandedHolo = Expand[OPEHolo], OPETermsHolo, OPETermsInteractingSingular, OPETermsInteractingPossiblyNonSingular,
expansionOrderAntiHolo, interactingOrder, OPEExpandedAntiHolo = Expand[OPEAntiHolo], OPETermsAntiHolo},

OPETermsHolo = If[Head[OPEExpandedHolo] === Plus, List @@ OPEExpandedHolo, {OPEExpandedHolo}];
OPETermsAntiHolo = If[Head[OPEExpandedHolo] === Plus, List @@ OPEExpandedAntiHolo, {OPEExpandedAntiHolo}];
OPETermsInteractingSingular = If[Head[OPEInteractingSingular] === Plus, List @@ OPEInteractingSingular, {OPEInteractingSingular}];

Scan[Function[OPETermHolo,
Scan[Function[OPETermAntiHolo,

(*Extract powers of singularities in the free field OPE*)
powerHolo = extractWeightCountingParameterPower[OPETermHolo, weightCountingParameterHolo];
powerAntiHolo = extractWeightCountingParameterPower[OPETermAntiHolo, weightCountingParameterAntiHolo];

(*Check if level-matching condition is preserved*)
If[powerHolo === powerAntiHolo,

If[powerHolo >=1, 
(*If there are nontrivial singular parts in the free field OPE, keep also the appropriate non-singular parts of the interacting OPE*)
OPETermsInteractingPossiblyNonSingular = OPETermsInteractingSingular + 
Total[Map[(weightCountingParameterHolo weightCountingParameterAntiHolo)^# InteractingProjection[OPEInteracting, 2#] &, Range[1, -powerHolo]]],
OPETermsInteractingPossiblyNonSingular = OPETermsInteractingSingular];

Scan[Function[OPETermInteracting,
(*Compute to what orders should one Taylor expand the free field OPE*)
interactingOrder = extractWeightCountingParameterPower[OPETermInteracting, weightCountingParameterHolo];
expansionOrderHolo = weightHolo - powerHolo - interactingOrder;
expansionOrderAntiHolo = weightAntiHolo - powerAntiHolo - interactingOrder;


If[expansionOrderHolo >= 0 && expansionOrderAntiHolo >= 0,
(*Taylor expand and project the interacting OPE, so that the total weight is (weightHolo, weightAntiHolo)*)
result = result +
Op[
R[TaylorAtOrderHolo[OPETermHolo, expansionOrderHolo, 0], TaylorAtOrderAntiHolo[OPETermAntiHolo, expansionOrderAntiHolo, 0]], 
InteractingProjection[OPEInteracting, 2interactingOrder + interactingWeight]
];
];
], OPETermsInteractingPossiblyNonSingular]
];
], OPETermsAntiHolo]
], OPETermsHolo];

result/.{weightCountingParameterHolo -> 1, weightCountingParameterAntiHolo -> 1}]


projectHolo::usage = "Project OPE onto a given holomorphic weight";
projectHolo[OPE_, weight_, weightCountingParameter_]:= Module[{result = 0, power, expansionOrder, OPEexpanded = Expand[OPE], OPEterms},
OPEterms = If[Head[OPEexpanded] === Plus, List @@ OPEexpanded, {OPEexpanded}];
Scan[Function[OPEterm,

(*Compute to what orders should one Taylor expand the OPE*)
power = extractWeightCountingParameterPower[OPEterm, weightCountingParameter];
expansionOrder = -power + weight;

If[expansionOrder >= 0,
result = result + TaylorAtOrderHolo[OPEterm, expansionOrder, 0]];
],
OPEterms];
result/.{weightCountingParameter -> 1}]


projectAntiHolo::usage = "Project OPE onto a given antiholomorphic weight";
projectAntiHolo[OPE_, weight_, weightCountingParameter_]:= Module[{result = 0, power, expansionOrder, OPEexpanded = Expand[OPE], OPEterms},
OPEterms = If[Head[OPEexpanded] === Plus, List @@ OPEexpanded, {OPEexpanded}];
Scan[Function[OPEterm,

(*Compute to what orders should one Taylor expand the OPE*)
power = extractWeightCountingParameterPower[OPEterm, weightCountingParameter];
expansionOrder = -power + weight;

If[expansionOrder >= 0,
result = result + TaylorAtOrderAntiHolo[OPEterm, expansionOrder, 0]];
],
OPEterms];
result/.{weightCountingParameter -> 1}]


(* ::Subsubsection::Closed:: *)
(*Extract weight-counting parameter power*)


extractWeightCountingParameterPower::usage = "Extract weight-counting parameter power";
extractWeightCountingParameterPower[OPEterm_, weightCountingParameter_] := (Exponent[Together[OPEterm], weightCountingParameter])


(* ::Subsubsection::Closed:: *)
(*Set factorization replacement*)


(*This replacement rule is called on multi-local operator every time factorization into holomorphic/antiholomorphic parts is performed, defaults to no rule*)
(*It is useful for example for splitting expX into holomorphic and antiholomorphic parts in the case of free boson CFT*)
factorizationReplacement =  {};


(* ::Subsection:: *)
(*Define action of b0^-*)


(*Define holomorphic b-ghost mode actions, generally at different points*)
bmodeHolo[mode_][Ra_/;Rtest[Ra]] := Module[{pos, result = 0, cAssoc = Association[], fermionNumber = 0, position = 1},
Scan[Function[Relem,
If[Head[Relem ]=== c, If[mode >= Relem[[1]]-1, 
If[Relem[[2]]=!=0,
AssociateTo[cAssoc, position -> {Relem -> (-1)^fermionNumber 1/Factorial[mode-(Relem[[1]]-1)] (Relem[[2]])^(mode-(Relem[[1]]-1))}],
If[mode === Relem[[1]]-1,
AssociateTo[cAssoc, position -> {Relem -> (-1)^fermionNumber}]]];
]];
If[MemberQ[fermions, Head[Relem]], fermionNumber = fermionNumber + 1];
position = position + 1;
],Ra];

KeyValueMap[Function[{pos, replacement}, 
result = result + ReplaceAt[Ra, replacement, pos];
], cAssoc];
result];

(*Define antiholomorphic b-ghost mode actions at the same point*)
bmodeAntiHolo[mode_][Ra_/;Rtest[Ra]] := Module[{pos, result = 0, cAssoc = Association[], fermionNumber = 0, position = 1},
Scan[Function[Relem,
If[Head[Relem ]=== ct, If[mode >= Relem[[1]]-1, 
If[Relem[[2]]=!=0,
AssociateTo[cAssoc, position -> {Relem -> (-1)^fermionNumber 1/Factorial[mode-(Relem[[1]]-1)] (Relem[[2]])^(mode-(Relem[[1]]-1))}],
If[mode === Relem[[1]]-1,
AssociateTo[cAssoc, position -> {Relem -> (-1)^fermionNumber}]]];
]];
If[MemberQ[fermions, Head[Relem]], fermionNumber = fermionNumber + 1];
position = position + 1;
],Ra];

KeyValueMap[Function[{pos, replacement}, 
result = result + ReplaceAt[Ra, replacement, pos];
], cAssoc];
result];


(*Multilinearity of b-ghost mode actions*)
bmodeHolo[mode_][a_+b_]:=bmodeHolo[mode][a] + bmodeHolo[mode][b];
bmodeHolo[mode_][a_ b_]:=a bmodeHolo[mode][b]/;(And @@(FreeQ[a,#]&/@ allfields))
bmodeHolo[mode_][0] := 0;

bmodeAntiHolo[mode_][a_+b_]:=bmodeAntiHolo[mode][a] + bmodeAntiHolo[mode][b];
bmodeAntiHolo[mode_][a_ b_]:=a bmodeAntiHolo[mode][b]/;(And @@(FreeQ[a,#]&/@ allfields))
bmodeAntiHolo[mode_][0] := 0;


(* ::Subsection:: *)
(*Create B-ghost insertion*)


createCurlyB::usage = "Create curlyB insertion given local coordinate functions, moduli and number of bracket insertions"
createCurlyB[SFList__, localCoordinateFunctionsHol__, localCoordinateFunctionsAntiHol__,  bracketOrder_, moduli_,  w_, wbar_]:= 
Module[{i,j, minCGhostModdings,minCbarGhostModdings, result = 0},

(*Get maximum possible b-ghost mode that does not vanish upon action*)
minCGhostModdings = Map[getMinCGhostModding, SFList];
minCbarGhostModdings = Map[getMinCbarGhostModding, SFList];

(*For each modulus and insertion, create the relevant b-ghost insertions*)
Do[
result = result + createBs[SFList[[i]], localCoordinateFunctionsHol[[i]], localCoordinateFunctionsAntiHol[[i]], i, moduli, w, wbar], 
{i,1,bracketOrder}];
result
]


scalarQ[x_] := FreeQ[x, _MultiOp | _Op | _R | _Interacting]


getMinCGhostModding::usage = "Get minimum c-ghost modding inside a local operator";

getMinCGhostModding[z0_][expr_Times] := getMinCGhostModding[z0][SelectFirst[List @@ expr, !scalarQ[#] &]]

getMinCGhostModding[z0_][Ma_/; MultiOptest[Ma]]:=  Module[{moddingList = Select[getMinCGhostModding[z0] /@ List @@ Ma, # != "None" &]},
If[moddingList =!= {}, Min[moddingList], "None"]
];

getMinCGhostModding[z0_][Opa_/; OpTest[Opa]]:=  getMinCGhostModding[z0][Opa[[1]]];

getMinCGhostModding[z0_][Ra_/; Rtest[Ra]]:= Module[{RList = List @@ Ra, maxOrder = "None", currentOrder},
Scan[Function[Relem,
If[Head[Relem] == c,
(*If the c-ghost is not at zero, use the minimal b-ghost modding for the flat vertex i.e. 0*)
currentOrder = (Relem/.{c[der_,z_]:>c[der,z-z0]})/.{c[der_, 0]:> 1 - der, c[der_, z_]:> 0};
If[maxOrder == "None" || currentOrder < maxOrder, maxOrder = currentOrder]
]
], RList];
maxOrder
]

getMinCGhostModding[z0_][a_]:= "None";


getMinCbarGhostModding::usage = "Get minimum cbar-ghost modding inside a local operator";

getMinCbarGhostModding[z0bar_][expr_Times] := getMinCGhostModding[z0bar][SelectFirst[List @@ expr, !scalarQ[#] &]]

getMinCbarGhostModding[z0bar_][Ma_/; MultiOptest[Ma]]:=  Module[{moddingList = Select[getMinCbarGhostModding[z0bar] /@ List @@ Ma,# != "None" &]},
If[moddingList =!= {}, Min[moddingList], "None"]
];

getMinCbarGhostModding[z0bar_][Opa_/; OpTest[Opa]]:=  getMinCbarGhostModding[z0bar][Opa[[1]]];

getMinCbarGhostModding[z0bar_][Ra_/; Rtest[Ra]]:= Module[{RList = List @@ Ra, maxOrder = "None", currentOrder},
Scan[Function[Relem,
If[Head[Relem] == ct,
(*If the c-ghost is not at zero, use the minimal b-ghost modding for the flat vertex i.e. 0*)
currentOrder = (Relem/.{ct[der_,zbar_]:> ct[der, zbar - z0bar]})/.{ct[der_, 0]:> 1 - der, ct[der_,zbar_]:>0};
If[maxOrder == "None" || currentOrder < maxOrder, maxOrder = currentOrder]
]
], RList];
maxOrder
]

getMinCbarGhostModding[z0bar_][a_]:= "None";


getInverseSeriesAtOrder::usage = "Get series of inverse function to a given order";
getInverseSeriesAtOrder[toInvert_, coord_, inversionCoord_, order_]:= 
(InverseSeries[Series[toInvert,{coord,0,order}]]//Normal)/.{coord->inversionCoord};


createBs::usage = "Creates b-ghost insertions for a given modulus and set of local coordinates, given an upper bound on b-ghost modding"
createBs[insertion_, localCoordinateHol_, localCoordinateAntiHol_, insertionLabel_, moduli_, w_, wbar_]:= 
Module[{result, expandedBGhostIntegrandHol,expandedBGhostIntegrandAntiHol, BGhostIntegrandHolo, BGhostIntegrandAntiHolo, wInTermsOfZ, wbarInTermsOfZbar, 
z, zbar, z0 = localCoordinateHol[0], z0bar = localCoordinateAntiHol[0], maxOrderHolo, maxOrderAntiHolo, minCGhostModding, minCbarGhostModding},

minCGhostModding = getMinCGhostModding[z0][insertion];

If[minCGhostModding != "None",
maxOrderHolo = -minCGhostModding + 1;

If[maxOrderHolo > 0,
(*Obtain a disc coordinate w in terms of sphere coordinate z*)
wInTermsOfZ = getInverseSeriesAtOrder[localCoordinateHol[w], w,z, maxOrderHolo];

(*Differentiate local coordinates as a function of w with respect to the modulus, substituting the sphere coordinate z in the end*)
expandedBGhostIntegrandHol = (Series[-(Differential[localCoordinateHol[w], moduli]/.{w->wInTermsOfZ}), {z,z0,maxOrderHolo}]//Normal);

(*Replace terms in the above series with b-ghost modes*)
BGhostIntegrandHolo = Total[(#/.{Times[rest___,(z-z0)^p_?NumericQ]:> rest bmodeHolo[p-1][insertionLabel],Times[rest___,diff_/;diff===(z-z0)]:> rest bmodeHolo[0][insertionLabel],Times[rest___,1]:> rest bmodeHolo[-1][insertionLabel]}) & /@ (List@@(expandedBGhostIntegrandHol))],
(*If no derivatives of c-ghost appear, then return dz(w)/d(modulus)_{w=0} b_{-1}*)
BGhostIntegrandHolo = -Differential[localCoordinateHol[0], moduli] bmodeHolo[-1][insertionLabel];
], 
BGhostIntegrandHolo = 0;
];

minCbarGhostModding = getMinCbarGhostModding[z0bar][insertion];

If[minCbarGhostModding != "None",
maxOrderAntiHolo = -minCbarGhostModding + 1;
If[maxOrderAntiHolo > 0,
(*Obtain a disc coordinate wbar in terms of local coordinate zbar*)
wbarInTermsOfZbar = getInverseSeriesAtOrder[localCoordinateAntiHol[wbar], wbar, zbar, maxOrderAntiHolo];

(*Differentiate local coordinates as a function of wbar with respect to the modulus, substituting the sphere coordinate zbar in the end*)
expandedBGhostIntegrandAntiHol = (Series[-(Differential[localCoordinateAntiHol[wbar], moduli]/.{wbar->wbarInTermsOfZbar}), {zbar,z0bar,maxOrderAntiHolo}]//Normal);

(*Replace terms in the above series with bt-ghost modes*)
BGhostIntegrandAntiHolo = Total[(#/.{Times[rest___,(zbar-z0bar)^p_?NumericQ]:> rest bmodeAntiHolo[p-1][insertionLabel],Times[rest___,diff_/;diff===(zbar-z0bar)]:> rest bmodeAntiHolo[0][insertionLabel],Times[rest___,1]:> rest bmodeAntiHolo[-1][insertionLabel]})& /@ (List@@(expandedBGhostIntegrandAntiHol))],

(*If no derivatives of c-ghost appear, then return dzbar(wbar)/d(modulus)_{wbar=0} bt_{-1}*)
BGhostIntegrandAntiHolo = -Differential[localCoordinateAntiHol[0], moduli] bmodeAntiHolo[-1][insertionLabel];
],
BGhostIntegrandAntiHolo = 0;
];
result = BGhostIntegrandHolo + BGhostIntegrandAntiHolo;
result]


(* ::Subsubsection:: *)
(*Define differential of a local coordinate map*)


Differential::usage = "Differential of a function of moduli";
Differential[expr_, moduli_] /; !DependentQ[expr, moduli] := 0;

(* 0 if the whole thing is independent of the moduli *)
Differential[expr_, moduli_] /; !DependentQ[expr, moduli] := 0;

(*Multilinearity*)
Differential[a_ + b_, moduli_] := Differential[a, moduli] + Differential[b, moduli];
Differential[c_ b_, moduli_] /; !DependentQ[c, moduli] := c Differential[b, moduli];

(* Product rule over all dependent factors *)
Differential[Times[args__]/;(Length[{args}] > 1), moduli_] := Module[{f = {args}},
  Total @ Table[
    If[DependentQ[f[[i]], moduli],
      Differential[f[[i]], moduli] * Times @@ Delete[f, i],
      0
    ]
  , {i, Length[f]}]
];

DependentQ::usage = "Checks if expression is dependent on moduli";
DependentQ[expr_, moduli_List] := moduli =!= {} && !FreeQ[expr, Alternatives @@ moduli];


(* ::Subsection:: *)
(*Create B-ghost insertions*)


combineCurlyBs::usage = "Takes two curly B's and combines them";
combineCurlyBs[a_+b_, c___]:= combineCurlyBs[a, c] + combineCurlyBs[b, c];
combineCurlyBs[a___, b_+c_]:= combineCurlyBs[a, b] + combineCurlyBs[a, c];
combineCurlyBs[a_ f_,d___]:= a combineCurlyBs[f,d]/;(And @@(FreeQ[a,#]&/@ {Differential, WedgeProduct, bmodeHolo, bmodeAntiHolo}))
combineCurlyBs[f___, a_ d_]:= a combineCurlyBs[f,d]/;(And @@(FreeQ[a,#]&/@ {Differential, WedgeProduct, bmodeHolo, bmodeAntiHolo}))
combineCurlyBs[a_ b___, c_ d___]:= WedgeProduct[a, c] combineCurlyBs[b,d]/; (MemberQ[{Differential, WedgeProduct}, Head[a]] && MemberQ[{Differential, WedgeProduct}, Head[c]]);
combineCurlyBs[combineCurlyBs[a___],b___]:= combineCurlyBs[a,b];
combineCurlyBs[a___, combineCurlyBs[b___]]:= combineCurlyBs[a,b];


createCurlyBs::usage = "Takes in a single curlyB object, and creates a joined action of all required curlyB insertions"
createCurlyBs[curlyB_, numberOfModuli_]:= Module[{result = curlyB}, 
If[numberOfModuli > 1,
(*Combine curlyBs by iterating the combination on two curlyBs, and then sort b-ghost modes into canonical ordering*)
result = (Nest[combineCurlyBs[curlyB, #] &, result, numberOfModuli - 1] /.{combineCurlyBs[a__]:>Signature[{a}] combinedCurlyBs[Sort[{a}]]});
];
result]


(* ::Subsubsection:: *)
(*Sort b-ghosts according to on which position they act*)


(* ::Subsubsection:: *)
(*Define wedge product*)


WedgeProduct::usage = "A wedge product between Differentials";
WedgeProduct[ c___,a_,a_,d___]:=0
WedgeProduct[c___,a_+b_,d___]:=WedgeProduct[c,a,d]+WedgeProduct[c,b,d]
WedgeProduct[c___, s_?nonDifferentialQ f_, d___] := s WedgeProduct[c, f, d];
WedgeProduct[c___, s_?nonDifferentialQ,   d___] := s WedgeProduct[c, d];
WedgeProduct[]:=1;
WedgeProduct[a___,WedgeProduct[b___],c___]:=WedgeProduct[a,b,c]
WedgeProduct[c___,b_,a_,d___]:=-WedgeProduct[c,a,b,d]/;(!OrderedQ[{b,a}])

nonDifferentialQ::usage = "Checks if does not contain Differential";
nonDifferentialQ[expr_] := FreeQ[expr, Differential];


(* ::Subsection:: *)
(*Apply B-ghost insertions to multi-op*)


applyCurlyBs::usage = "Apply a curlyB [sum over b-ghost modes attached to positions] to a multi-local operator"
applyCurlyBs[SFList_, curlyBs_, moduliLength_]:= 
Module[{result = 0, prefac, bGhostModes, curlyBOnPosition,
curlyBList = curlyBs/.{Plus->List}},

If[Head[curlyBList] === List,
Scan[Function[curlyB,
(*Action of a curlyB is application of its b-ghost modes on each local operator in the input multilocal operator*)
 result = result + applyBghostModes[curlyB, SFList];
], curlyBList],
 result = result + applyBghostModes[curlyBs, SFList];
 ];

(*The overall sign is for anticommutation of coordinate functions and b-ghosts*)
(-1)^(moduliLength/2)/Factorial[moduliLength] result
];


applyBghostModes::usage = "Apply a set of b-ghost modes to a local operator";
applyBghostModes[a_ b_, SFList_]:= a applyBghostModes[b, SFList]/;Head[b]==combinedCurlyBs;
applyBghostModes[BghostModes_, SFList_] := Module[{result, bGhostPosition, currentResultAtPosition, SFParities = Map[parityOp, SFList], currentSFList},
currentSFList = SFList;
Scan[Function[BghostMode,
(*Act the b-ghost mode*)
bGhostPosition = getBGhostPosition[BghostMode];
currentResultAtPosition =  currentSFList[[bGhostPosition]];
currentSFList[[bGhostPosition]] = (-1)^(Total[Take[SFParities, bGhostPosition - 1]]) actBGhostMode[BghostMode, currentResultAtPosition];
SFParities[[bGhostPosition]] = Mod[SFParities[[bGhostPosition]] + 1,2];
], Reverse @@ BghostModes];
result = MultiOp @@ currentSFList;
result]

applyBghostModes[][a_] := a;


getBGhostPosition::usage = "Obtain the position at which a b-ghost mode acts";
getBGhostPosition[bmodeHolo[a_][b_]]:= b;
getBGhostPosition[bmodeAntiHolo[a_][b_]]:= b;


actBGhostMode::usage = "Acts a b-ghost mode on a local operator";
actBGhostMode[a_, op1_ + op2_]:= actBGhostMode[a, op1] + actBGhostMode[a, op2];
actBGhostMode[a_, b_ c_]:= b actBGhostMode[a,c]/;(And @@(FreeQ[b,#]&/@ allfields));

actBGhostMode[bmodeHolo[a_], MultiOpa_/;MultiOptest[MultiOpa]]:= Module[{result = 0, sign = 1, OpList = List @@ MultiOpa, parities},
parities = Map[parityOp, OpList];
Do[result = result + (-1)^(Total[Take[parities, i-1]]) MultiOp @@ MapAt[actBGhostMode[bmodeHolo[a], #] &, OpList, i],
{i, 1, Length[OpList]}];
result
];

actBGhostMode[bmodeHolo[a_][b_], MultiOpa_/;MultiOptest[MultiOpa]]:= Module[{result = 0, sign = 1, OpList = List @@ MultiOpa, parities},
parities = Map[parityOp, OpList];
Do[result = result + (-1)^(Total[Take[parities, i-1]]) MultiOp @@ MapAt[actBGhostMode[bmodeHolo[a], #] &, OpList, i],
{i, 1, Length[OpList]}];
result
];

actBGhostMode[bmodeAntiHolo[a_], MultiOpa_/;MultiOptest[MultiOpa]]:= Module[{result = 0, sign = 1, OpList = List @@ MultiOpa, parities},
parities = Map[parityOp, OpList];
Do[result = result + (-1)^(Total[Take[parities, i-1]]) MultiOp @@ MapAt[actBGhostMode[bmodeAntiHolo[a], #] &, OpList, i],
{i, 1, Length[OpList]}];
result
];

actBGhostMode[bmodeAntiHolo[a_][b_], MultiOpa_/;MultiOptest[MultiOpa]]:= Module[{result = 0, sign = 1, OpList = List @@ MultiOpa, parities},
parities = Map[parityOp, OpList];
Do[result = result + (-1)^(Total[Take[parities, i-1]]) MultiOp @@ MapAt[actBGhostMode[bmodeAntiHolo[a], #] &, OpList, i],
{i, 1, Length[OpList]}];
result
];

actBGhostMode[bmodeHolo[a_][b_], Opa_/;OpTest[Opa]]:= Op[bmodeHolo[a][Opa[[1]]], Opa[[2]]];
actBGhostMode[bmodeAntiHolo[a_][b_], Opa_/;OpTest[Opa]]:= Op[bmodeAntiHolo[a][Opa[[1]]], Opa[[2]]];
actBGhostMode[bmodeHolo[a_], Opa_/;OpTest[Opa]]:= Op[bmodeHolo[a][Opa[[1]]], Opa[[2]]];
actBGhostMode[bmodeAntiHolo[a_], Opa_/;OpTest[Opa]]:= Op[bmodeAntiHolo[a][Opa[[1]]], Opa[[2]]];

actBGhostMode[bmodeHolo[a_][b_], Ra_/;Rtest[Ra]]:= bmodeHolo[a][Ra];
actBGhostMode[bmodeAntiHolo[a_][b_], Ra_/;Rtest[Ra]]:= bmodeAntiHolo[a][Ra];
actBGhostMode[bmodeHolo[a_], Ra_/;Rtest[Ra]]:= bmodeHolo[a][Ra];
actBGhostMode[bmodeAntiHolo[a_], Ra_/;Rtest[Ra]]:= bmodeAntiHolo[a][Ra];

actBGhostMode[b_, Ia_/;InteractingTest[Ia]]:= 0;


(* ::Subsection:: *)
(*Collapse b0m*)


CollapseB0m::usage = "Collapses b0m, which was being held unevaluated";

CollapseB0m[a_ + b_]:= CollapseB0m[a] + CollapseB0m[b]
CollapseB0m[a_ b_]:= a CollapseB0m[b]/;(And @@(FreeQ[a,#]&/@ allfields))
CollapseB0m[b0mHold[a_]]:= actBGhostMode[bmodeHolo[0], a] - actBGhostMode[bmodeAntiHolo[0],a]


(* ::Subsection:: *)
(*Apply propagator*)


ApplyPropagator::usage = "Applies the propagator b0+/L0+ on a level-projected bracket";

ApplyPropagator[q_][a_ + b_]:= ApplyPropagator[q][a] + ApplyPropagator[q][b]
ApplyPropagator[q_][a_ b_]:= a ApplyPropagator[q][b]/;(And @@(FreeQ[a,#]&/@ allfields));

ApplyPropagator[q_][MultiOpa_/;MultiOptest[MultiOpa]]:= Module[{rescaledMultiOp},
rescaledMultiOp =  1/(-4 Pi I) 1/(q Conjugate[q]) mapOp[rescaling[q], rescaling[Conjugate[q]]][MultiOpa];
actBGhostMode[bmodeHolo[0], rescaledMultiOp] + actBGhostMode[bmodeAntiHolo[0],rescaledMultiOp]]

ApplyPropagator[q_][Opa_/;OpTest[Opa]]:= Module[{rescaledOp},
rescaledOp = 1/(-4 Pi I) 1/(q Conjugate[q]) mapOp[rescaling[q], rescaling[Conjugate[q]]][Opa];
actBGhostMode[bmodeHolo[0], rescaledOp] + actBGhostMode[bmodeAntiHolo[0],rescaledOp]]

ApplyPropagator[q_][Ra_/;Rtest[Ra]]:= Module[{rescaledR},
rescaledR = 1/(-4 Pi I) 1/(q Conjugate[q]) mapOp[rescaling[q], rescaling[Conjugate[q]]][Ra];
actBGhostMode[bmodeHolo[0], rescaledR] + actBGhostMode[bmodeAntiHolo[0],rescaledR]]

ApplyPropagator[q_][Ia_/;InteractingTest[Ia]]:= Module[{rescaledI},
rescaledI = 1/(-4 Pi I)1/(q Conjugate[q]) mapOp[rescaling[q], rescaling[Conjugate[q]]][Ia];
actBGhostMode[bmodeHolo[0], rescaledI] + actBGhostMode[bmodeAntiHolo[0],rescaledI]]

rescaling[factor_][z_]:= factor z //Expand;


(* ::Subsection:: *)
(*Determine whether OPE should be computed*)


singularity::usage = "Compute order of singularity of Wick contraction"
singularity[b[n_,z_],c[m_,w_]]:= 1 + m + n;
singularity[c[m_,w_],b[n_,z_]]:= 1 + m + n;
singularity[bt[n_,z_],ct[m_,w_]]:= 1 + m + n;
singularity[ct[m_,w_],bt[n_,z_]]:= 1 + m + n;


singularityMatrix::usage = "Compute a matrix of orders of singularities in the OPE of two operators"
singularityMatrix[Ra_/;Rtest[Ra], Rb_/; Rtest[Rb]]:= Table[singularity[Ra[[i]], Rb[[j]]], {i, 1, Length[Ra]}, {j, 1, Length[Rb]}];
singularityMatrix[a_ b_, c_]:= singularityMatrix[b,c]/;(And @@(FreeQ[a,#]&/@ allfields));
singularityMatrix[a_, b_ c_]:= singularityMatrix[a,c]/;(And @@(FreeQ[b,#]&/@ allfields));


(* Upper-bounds singularity given singularityMatrix, gets the position of the exp\[Phi] in PCO, on the corresponding row sums up all its entries
since an exponential can contract multiple times (importantly sums up even the negative value) and then adds the maximum from each other row. 
If there are no two operators in the string field contracting with the same operator in the PCO at the same (maximal) singularity order, the upper bound is saturated. *)
upperBoundSingularity[singularityMatrix_?MatrixQ, compositeRowNumber_] := Module[
  {n = Length[singularityMatrix], total = 0, row, negs},
  Do[
    row = singularityMatrix[[i]];
    negs = Select[row, # < 0 &];
    If[i != compositeRowNumber, total = total + Max[row], total = total + Total[row]],
    {i, n}
  ];
  total
];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
