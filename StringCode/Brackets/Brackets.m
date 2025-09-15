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
Bracket[args___, a_ b_, rest___] := a Bracket[args, b, rest] /; And @@ (FreeQ[a, #] & /@ allfields)

BracketBosonic::usage = "Defines bosonic part of the bracket, which is shared among string theories";
BracketBosonic[toBracket__/;AllTrue[{toBracket}, SFtest]]:= Module[{result = 0, SFsAtPos, localCoordinateFunctionsHol, localCoordinateFunctionsAntiHol, localCoordinateReplacement, 
moduli, bracketOrder, bracketList = {toBracket}, w, wbar, curlyB, curlyBs, minCGhostModdings, minCbarGhostModdings, SFList, moduliLength, afterApplyingBghosts, afterHeldActionOfPCOs},
bracketOrder = Length[bracketList];

(*Conformally transform the string field insertions*)
{localCoordinateFunctionsHol, localCoordinateFunctionsAntiHol, w, wbar, moduli, localCoordinateReplacement} = getLocalCoordinateData[bracketOrder];
SFsAtPos = placeSFAtPosGivenLocalCoordinates[localCoordinateFunctionsHol, localCoordinateFunctionsAntiHol, bracketList, w, wbar];
SFList = List @@ SFsAtPos;

(*Create and apply the curly B-ghost insertions, one B-ghost action on the insertions for each modulus*)
moduliLength = Length[moduli];
If[moduliLength > 0,

(*Create the curly B-ghost insertions, one for each modulus*)
curlyB = createCurlyB[SFList, localCoordinateFunctionsHol, localCoordinateFunctionsAntiHol, bracketOrder, moduli, w, wbar];
curlyBs = createCurlyBs[curlyB, bracketOrder, moduliLength];

(*Apply the curly B-ghost insertions*)
afterApplyingBghosts = applyCurlyBs[SFList, curlyBs, moduliLength],
afterApplyingBghosts = SFsAtPos];

result = {afterApplyingBghosts, localCoordinateReplacement, SFList};
result]


(* ::Subsubsection::Closed:: *)
(*Place string fields at positions given by local coordinates*)


placeSFAtPosGivenLocalCoordinates::usage = "Places string fields at positions given by local coordinates of a given bracket";
placeSFAtPosGivenLocalCoordinates[localCoordinateFunctionsHol__, localCoordinateFunctionsAntiHol__, SFs__, w_, wbar_]:= 
Module[{i, length = Length[SFs]},
MultiOp @@ Table[SFAtPos[SFs[[i]], localCoordinateFunctionsHol[[i]]/.{w->0}, localCoordinateFunctionsAntiHol[[i]]/.{wbar->0}],{i,1,length}]
]


(* ::Subsection::Closed:: *)
(*Define projected bracket*)


(*Projected bracket is Bracket composed with a projection*)
BracketProjected[toBracket__/; AllTrue[{toBracket}, SFtest], weightHolo_, weightAntiHolo_]:=
BracketProjection[Bracket[toBracket], weightHolo, weightAntiHolo];

(*Multilinearity of projected Bracket*)
BracketProjected[args___, a_ + b_, rest___,  weightHolo_, weightAntiHolo_] := BracketProjected[args, a, rest,  weightHolo, weightAntiHolo] + BracketProjected[args, b, rest]
BracketProjected[args___, a_ b_, rest___, weightHolo_, weightAntiHolo_] := a BracketProjected[args, b, rest, weightHolo, weightAntiHolo] /; And @@ (FreeQ[a, #] & /@ allfields)

(*Multilinearity of Bracket projection*)
BracketProjection[{args___, a_ + b_, rest___, localCoordinateReplacement_}, weightHolo_, weightAntiHolo_] :=
 BracketProjection[{args, a, rest, localCoordinateReplacement}, weightHolo, weightAntiHolo] + BracketProjection[{args, b, rest, localCoordinateReplacement}, weightHolo, weightAntiHolo]
BracketProjection[{args___, a_ b_, rest___, localCoordinateReplacement_}, weightHolo_, weightAntiHolo_] := 
a BracketProjection[{args, b, rest, localCoordinateReplacement}, weightHolo, weightAntiHolo] /; And @@ (FreeQ[a, #] & /@ allfields)


(* ::Subsection::Closed:: *)
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


(* ::Subsection::Closed:: *)
(*Factorize operators into holomorphic and anti-holomorphic parts*)


(* ::Subsubsection:: *)
(*Factorize multi-local operators*)


factorizeMultiOp::usage = "Factorize multi-local operator into holomorphic and antiholomorphic multi-local operators";
factorizeMultiOp[multiOp_/;MultiOptest[multiOp]]:=
Module[{multiOpReplaced = multiOp/.factorizationReplacement, localOpFactorized, localOpFree, localOpInteracting, localOpPrefac, localOpList,
localOpHolo, localOpAntiHolo, localOpsHolo, localOpsAntiHolo, localOpsInteracting, prefac = 1},
{localOpsHolo, localOpsAntiHolo, localOpsInteracting} = 
Reap[Scan[Function[localOp,
localOpFree = localOp[[1]];
localOpInteracting = localOp[[2]];
localOpPrefac = extractPrefacFromRTimesConstant[localOpFree];
localOpList = extractListFromRTimesConstant[localOpFree];
localOpFactorized = splitOperators[localOpList, isHolomorphic, isAntiHolomorphic];
prefac = prefac * localOpPrefac * factorizationSign[localOpList, isHolomorphic, isAntiHolomorphic];
{localOpHolo, localOpAntiHolo} = {R @@ localOpFactorized[[1]], R @@ localOpFactorized[[2]]};
Sow[localOpHolo, "Holo"];
Sow[localOpAntiHolo, "AntiHolo"];
Sow[localOpInteracting, "Interacting"]
], List @@ multiOpReplaced]][[2]];
{MultiOp @@ localOpsHolo, MultiOp @@ localOpsAntiHolo, MultiOp @@ localOpsInteracting, prefac}]


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


(* ::Subsection::Closed:: *)
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


(* ::Subsection::Closed:: *)
(*Define action of b0^-*)


(*Define holomorphic b-ghost mode actions at the same point*)
bmodeHolo[mode_][Ra_/;Rtest[Ra]] := Module[{pos, result = 0, cAssoc = Association[], fermionNumber = 0, position = 1, der},
Scan[Function[Relem,
If[Head[Relem] == c, 
der = Relem/.{c[der_,_]:> der};
AssociateTo[cAssoc, position -> If[der -1 == mode, {Relem -> (-1)^fermionNumber Factorial[der]}, {Relem ->0}]]];
If[MemberQ[fermions, Head[Relem]], fermionNumber = fermionNumber + 1];
position = position + 1;
],Ra];

KeyValueMap[Function[{pos, replacement}, 
result = result + ReplaceAt[Ra, replacement, pos];
], cAssoc];
result];

(*Define antiholomorphic b-ghost mode actions at the same point*)
bmodeAntiHolo[mode_][Ra_/;Rtest[Ra]] := Module[{pos, result = 0, cAssoc = Association[], fermionNumber = 0, position = 1, der},
Scan[Function[Relem,
If[Head[Relem]== ct, 
der = Relem/.{ct[der_,_]:> der};
AssociateTo[cAssoc, position -> If[der - 1 == mode, {Relem -> (-1)^fermionNumber Factorial[der]}, {Relem ->0}]]];
If[MemberQ[fermions, Head[Relem]], fermionNumber = fermionNumber + 1];
position = position + 1;
],Ra];

KeyValueMap[Function[{pos, replacement}, 
result = result + ReplaceAt[Ra, replacement, pos];
], cAssoc];
result];

(*Define action of holomorphic b-ghost zero mode, generally at different points*)
b0mHolo[Ra_/;Rtest[Ra]] := Module[{pos, result = 0, cAssoc = Association[], fermionNumber = 0, position = 1},
Scan[Function[Relem,
If[MatchQ[Relem, c[0, _]], AssociateTo[cAssoc, position -> {Relem -> (-1)^fermionNumber Relem[[2]]}], 
If[MatchQ[Relem, c[1, _]],  AssociateTo[cAssoc, position -> {Relem -> (-1)^fermionNumber}]]];
If[MemberQ[fermions, Head[Relem]], fermionNumber = fermionNumber + 1];
position = position + 1;
],Ra];

KeyValueMap[Function[{pos, replacement}, 
result = result + ReplaceAt[Ra, replacement, pos];
], cAssoc];
result];

(*Define action of antiholomorphic b-ghost zero mode, generally at different points*)
b0mAntiHolo[Ra_/;Rtest[Ra]] := Module[{pos, result = 0, cAssoc = Association[], fermionNumber = 0, position = 1},
Scan[Function[Relem,
If[MatchQ[Relem, ct[0, _]], AssociateTo[cAssoc, position -> {Relem -> (-1)^fermionNumber Relem[[2]]}], 
If[MatchQ[Relem, ct[1, _]],  AssociateTo[cAssoc, position -> {Relem -> (-1)^fermionNumber}]]];
If[MemberQ[fermions, Head[Relem]], fermionNumber = fermionNumber + 1];
position = position + 1;
],Ra];

KeyValueMap[Function[{pos, replacement}, 
result = result + ReplaceAt[Ra, replacement, pos];
], cAssoc];
result];


(*Multilinearity of b-ghost mode actions*)
b0m[Ra_/;Rtest[Ra]] := b0mHolo[Ra] - b0mAntiHolo[Ra];
b0m[a_+b_]:=b0m[a] + b0m[b];
b0m[a_ b_]:=a b0m[b]/;(And @@(FreeQ[a,#]&/@ allfields))
b0m[0] := 0;

bmodeHolo[mode_][a_+b_]:=bmodeHolo[mode][a] + bmodeHolo[mode][b];
bmodeHolo[mode_][a_ b_]:=a bmodeHolo[mode][b]/;(And @@(FreeQ[a,#]&/@ allfields))
bmodeHolo[mode_][0] := 0;

bmodeAntiHolo[mode_][a_+b_]:=bmodeAntiHolo[mode][a] + bmodeAntiHolo[mode][b];
bmodeAntiHolo[mode_][a_ b_]:=a bmodeAntiHolo[mode][b]/;(And @@(FreeQ[a,#]&/@ allfields))
bmodeAntiHolo[mode_][0] := 0;


(* ::Subsection::Closed:: *)
(*Create B-ghost insertion*)


createCurlyB::usage = "Create curlyB insertion given local coordinate functions, moduli and number of bracket insertions"
createCurlyB[SFList__, localCoordinateFunctionsHol__, localCoordinateFunctionsAntiHol__,  bracketOrder_, moduli_,  w_, wbar_]:= 
Module[{i,j, minCGhostModdings,minCbarGhostModdings},

(*Get maximum possible b-ghost mode that does not vanish upon action*)
minCGhostModdings = Map[getMinCGhostModding[#[[1]]] &, SFList];
minCbarGhostModdings = Map[getMinCbarGhostModding[#[[1]]] &, SFList];

(*For each modulus and insertion, create the relevant b-ghost insertions*)
Table[
createBs[localCoordinateFunctionsHol[[i]], localCoordinateFunctionsAntiHol[[i]], moduli, w, wbar, minCGhostModdings[[i]], minCbarGhostModdings[[i]]], 
{i,1,bracketOrder}]
]


getMinCGhostModding::usage = "Get minimum c-ghost modding inside a local operator";
getMinCGhostModding[Ra_/; Rtest[Ra]]:= Module[{RList = List @@ Ra, maxOrder = "None", currentOrder},
Scan[Function[Relem,
If[Head[Relem] == c,
currentOrder = Relem/.{c[der_, z_]:> 1 - der};
If[maxOrder == "None" || currentOrder < maxOrder, maxOrder = currentOrder]
]
], RList];
maxOrder
]


getMinCbarGhostModding::usage = "Get minimum cbar-ghost modding inside a local operator";
getMinCbarGhostModding[Ra_/; Rtest[Ra]]:= Module[{RList = List @@ Ra, maxOrder = "None", currentOrder},
Scan[Function[Relem,
If[Head[Relem] == ct,
currentOrder = Relem/.{ct[der_, z_]:> 1 - der};
If[maxOrder == "None" || currentOrder < maxOrder, maxOrder = currentOrder]
]
], RList];
maxOrder
]


getInverseSeriesAtOrder::usage = "Get series of inverse function to a given order";
getInverseSeriesAtOrder[toInvert_, coord_, inversionCoord_, order_]:= 
(InverseSeries[Series[toInvert,{coord,0,order}]]//Normal)/.{coord->inversionCoord};


createBs::usage = "Creates b-ghost insertions for a given modulus and set of local coordinates, given an upper bound on b-ghost modding"
createBs[localCoordinateHol_, localCoordinateAntiHol_, moduli_, w_, wbar_, minCGhostModding_, minCbarGhostModding_]:= 
Module[{result, expandedBGhostIntegrandHol,expandedBGhostIntegrandAntiHol, BGhostIntegrandListHol = {},BGhostIntegrandListAntiHol = {}, wInTermsOfZ, wbarInTermsOfZbar, 
z, zbar, z0 = localCoordinateHol/.{w->0}, z0bar = localCoordinateAntiHol/.{wbar->0}, maxOrderHolo, maxOrderAntiHolo},

If[minCGhostModding != "None",
maxOrderHolo = -minCGhostModding + 1;
If[maxOrderHolo > 0,
(*Obtain a disc coordinate w in terms of sphere coordinate z*)
wInTermsOfZ = getInverseSeriesAtOrder[localCoordinateHol, w,z, maxOrderHolo];

(*Differentiate local coordinates as a function of w with respect to the modulus, substituting the sphere coordinate z in the end*)
expandedBGhostIntegrandHol = Series[-(Differential[localCoordinateHol, moduli])/.{w->wInTermsOfZ}, {z,z0,maxOrderHolo}]//Normal;

(*Replace terms in the above series with b-ghost modes*)
BGhostIntegrandListHol = (#/.{Times[rest___,(z-z0)^p_?NumericQ]:>{Times @@ {rest}, bmodeHolo[p-1]},Times[rest___,diff_/;diff===(z-z0)]:>{Times @@ {rest}, bmodeHolo[0]},Times[rest___,1]:>{Times @@ {rest}, bmodeHolo[-1]}}) & /@ (List@@(expandedBGhostIntegrandHol)),
(*If no derivatives of c-ghost appear, then return dz(w)/d(modulus)_{w=0} b_{-1}*)
BGhostIntegrandListHol = {{-Differential[localCoordinateHol/.{w->0}, moduli], bmodeHolo[-1]}};
]
];

If[minCbarGhostModding != "None",
maxOrderAntiHolo = -minCbarGhostModding + 1;
If[maxOrderAntiHolo > 0,
(*Obtain a disc coordinate wbar in terms of local coordinate zbar*)
wbarInTermsOfZbar = getInverseSeriesAtOrder[localCoordinateAntiHol, wbar, zbar, maxOrderAntiHolo];

(*Differentiate local coordinates as a function of wbar with respect to the modulus, substituting the sphere coordinate zbar in the end*)
expandedBGhostIntegrandAntiHol = Series[-Differential[localCoordinateAntiHol, moduli]/.{wbar->wbarInTermsOfZbar}, {zbar,z0bar,maxOrderAntiHolo}]//Normal;

(*Replace terms in the above series with bt-ghost modes*)
BGhostIntegrandListAntiHol =(#/.{Times[rest___,(zbar-z0bar)^p_?NumericQ]:>{Times @@ {rest}, bmodeAntiHolo[p-1]},Times[rest___,diff_/;diff===(zbar-z0bar)]:>{Times @@ {rest}, bmodeAntiHolo[0]},Times[rest___,1]:>{Times @@ {rest}, bmodeAntiHolo[-1]}})& /@ (List@@(expandedBGhostIntegrandAntiHol)),

(*If no derivatives of c-ghost appear, then return dzbar(wbar)/d(modulus)_{wbar=0} bt_{-1}*)
BGhostIntegrandListAntiHol = {{-Differential[localCoordinateAntiHol/.{wbar->0}, moduli],bmodeAntiHolo[-1]}};
]
];
result = Join[BGhostIntegrandListHol,BGhostIntegrandListAntiHol];
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


(* ::Subsection::Closed:: *)
(*Create B-ghost insertions*)


createCurlyBs::usage = "Takes in a single curlyB object, and creates a joined action of all required curlyB insertions";
createCurlyBs[curlyB_, numberOfPositions_, numberOfCurlyBs_]:= Module[{result = {{1, ConstantArray[{}, numberOfPositions]}}, prefac, bGhostMode},
Do[
(*For each, possibly composite, curlyB action in result, add another curlyB action*)
result = Flatten[Map[addCurlyB[curlyB, numberOfPositions, #] &, result],2],
numberOfCurlyBs];
result/.{WedgeProductNoSign->WedgeProduct}]


addCurlyB::usage = "Adds a curlyB to an interemediate object that tracks already added curlyBs)";
addCurlyB[curlyB_, numberOfPositions_, curlyBAction_] := 
Module[{result = {}, initialPrefac = curlyBAction[[1]], initialBModes = curlyBAction[[2]], curlyBOnPosition, prefac, bGhostMode, initialBGhostModesAtPosition}, 
result = Reap[
(*For each position, go through all the various b-ghost modes, and add them to the initial b-ghost modes at that position, keeping track of prefactors*)
Do[
curlyBOnPosition = curlyB[[i]];
initialBGhostModesAtPosition = initialBModes[[i]];
Scan[Function[BGhostOnPosition,
{prefac, bGhostMode} = BGhostOnPosition;
If[!MemberQ[initialBGhostModesAtPosition, bGhostMode],

(*Sow updated prefactor and updated b-ghost modes*)
(*Treat coordinate function prefactors as anticommuting*)
Sow[{WedgeProductNoSign[initialPrefac, prefac], ReplacePart[initialBModes, i -> Append[initialBGhostModesAtPosition, bGhostMode]]}];
];
], curlyBOnPosition],
{i, 1, numberOfPositions}]][[2]];
result]


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

WedgeProductNoSign::usage = "A wedge product between Differentials, with no sign for swaps (treat coordinates as anticommuting)";
WedgeProductNoSign[ c___,a_,a_,d___]:=0
WedgeProductNoSign[c___,a_+b_,d___]:=WedgeProductNoSign[c,a,d]+WedgeProductNoSign[c,b,d]
WedgeProductNoSign[c___, s_?nonDifferentialQ f_, d___] := s WedgeProductNoSign[c, f, d];
WedgeProductNoSign[c___, s_?nonDifferentialQ,   d___] := s WedgeProductNoSign[c, d];
WedgeProductNoSign[]:=1;
WedgeProductNoSign[a___,WedgeProductNoSign[b___],c___]:=WedgeProductNoSign[a,b,c]
WedgeProductNoSign[c___,b_,a_,d___]:=WedgeProductNoSign[c,a,b,d]/;(!OrderedQ[{b,a}])

nonDifferentialQ::usage = "Checks if does not contain Differential";
nonDifferentialQ[expr_] := FreeQ[expr, Differential];


(* ::Subsection:: *)
(*Apply B-ghost insertions to multi-op*)


applyCurlyBs::usage = "Apply a curlyB [sum over b-ghost modes attached to positions] to a multi-local operator"
applyCurlyBs[SFList_, curlyBs__, moduliLength_]:= 
Module[{result = 0, prefac, bGhostModes, curlyBOnPosition, SFParities = Map[parityOp, SFList], SFParitiesAccumulated, SFListWithAccumulatedSigns},

(*Create auxiliary list that makes sure that b-ghosts get a minus sign when they pass through a fermionic string field*)
(*The signs assume that the b-ghosts will first be applied to the "furthermost" string field*)
SFParitiesAccumulated = Mod[Accumulate[SFParities] - SFParities[[1]],2];
SFListWithAccumulatedSigns = MapThread[(Times[(-1)^#1, #2]) &, {SFParitiesAccumulated, SFList}];

Scan[Function[curlyB,
{prefac, bGhostModes} = curlyB;
 
(*Action of a curlyB is application of its b-ghost modes on each local operator in the input multilocal operator*)
 result = result + prefac MultiOp @@ MapThread[#1 @ #2 &, {applyBghostModes @@@ bGhostModes, SFListWithAccumulatedSigns}];
],
 curlyBs];
(*The overall sign is for anticommutation of coordinate functions and b-ghosts*)
(-1)^(moduliLength-1) /Factorial[moduliLength] result
];


applyBghostModes::usage = "Apply a set of b-ghost modes to a local operator";
applyBghostModes[BghostModes__][operator_] := Module[{result, normalOrderedPartOfResult = operator[[1]], interactingPartOfResult = operator[[2]]},
Scan[Function[BghostMode,
(*Act a b-ghost mode*)
normalOrderedPartOfResult = (BghostMode/.{bmodeHolo[a_]:> bmodeHolo[a][normalOrderedPartOfResult], bmodeAntiHolo[a_]:> bmodeAntiHolo[a][normalOrderedPartOfResult]});
], {BghostModes}];
result = normalOrderedPartOfResult/.{R[a_]:> Op[R[a],interactingPartOfResult]};
result]

applyBghostModes[][a_] := a;


(* ::Subsection::Closed:: *)
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
