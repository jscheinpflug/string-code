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
EffectiveBracket::usage = "Computes the effective bracket summing over tree diagrams";
EffectiveBracketHold::usage = "Computes the combinatorics of the effective bracket summing over tree diagrams";
DrawTree::usage = "DrawTree[expr] draws tree diagrams for EffectiveBracketHold output";
Differential::usage = "Differential of a function of moduli";

(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection::Closed:: *)
(*Define 1-bracket (action of BRST charge)*)


(*Action of BRST charge splits into holomorphic and antiholomorphic parts*)
actBRST[SFa_/; SFTest[SFa]]:= actBRSTHolo[SFa] + actBRSTAntiHolo[SFa];

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

Bracket[args___, a_ b_, rest___] := a Bracket[args, b, rest] /; And @@ (FreeQ[a, #] & /@ Join[allfields,{Wedge}])

(*Join wedge products, give no sign: assuming that we wedge even number of differential as in closed string*)
Bracket[args___, Wedge[a__]b___, rest___]:= Wedge[a, Bracket[args, b, rest]]; 

BracketBosonic::usage = "Defines bosonic part of the bracket, which is shared among string theories";
BracketBosonic[toBracket__/;AllTrue[{toBracket}, SFTest]]:= Module[{result = 0, SFsAtPos, localCoordinateFunctionsHol, localCoordinateFunctionsAntiHol, localCoordinateReplacement, 
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
extractPrefacFromMultiOpTimesConstant[Times[a_, Ma_/;MultiOpTest[Ma]]] := a;
extractPrefacFromMultiOpTimesConstant[Ma_/;MultiOpTest[Ma]] := 1;
extractPrefacFromMultiOpTimesConstant[1] := 1;

extractListFromMultiOpTimesConstant::usage = "Extracts the list of operators inside a multi-local operator product possibly multiplied by a constant prefactor";
extractListFromMultiOpTimesConstant[Times[a_, Ma_/;MultiOpTest[Ma]]] := List @@ Ma;
extractListFromMultiOpTimesConstant[Ma_/;MultiOpTest[Ma]] := List @@ Ma;


(* ::Subsection:: *)
(*Define projected bracket*)


(*Projected bracket is Bracket composed with a projection*)
BracketProjected[toBracket__/; AllTrue[{toBracket}, SFTest], weightHolo_, weightAntiHolo_]:=
b0mHold[BracketProjection[(Bracket[toBracket]/.{b0mHold[a__]:>a}), weightHolo, weightAntiHolo]];

(*Multilinearity of projected Bracket*)
BracketProjected[args___, a_ + b_, rest___,  weightHolo_, weightAntiHolo_] := BracketProjected[args, a, rest,  weightHolo, weightAntiHolo] + BracketProjected[args, b, rest, weightHolo, weightAntiHolo]
BracketProjected[args___, a_ b_, rest___, weightHolo_, weightAntiHolo_] := a BracketProjected[args, b, rest, weightHolo, weightAntiHolo] /; And @@ (FreeQ[a, #] & /@ Join[allfields,{Wedge}])
BracketProjected[args___, 0, rest___, weightHolo_, weightAntiHolo_]:=0;

(*Join wedge products, give no sign: assuming that we wedge even number of differential as in closed string*)
BracketProjected[args___, Wedge[a__] b___, rest___, weightHolo_, weightAntiHolo_] := Wedge[a, BracketProjected[args, b, rest, weightHolo, weightAntiHolo]]


(*Multilinearity of Bracket projection*)
BracketProjection[a_ + b_, weightHolo_, weightAntiHolo_] :=
 BracketProjection[a, weightHolo, weightAntiHolo] + BracketProjection[b, weightHolo, weightAntiHolo]
 
BracketProjection[a_ b_, weightHolo_, weightAntiHolo_] := 
a BracketProjection[b, weightHolo, weightAntiHolo] /; And @@ (FreeQ[a, #] & /@ Join[allfields,{Wedge}])

(*Join wedge products, give no sign: assuming that we wedge even number of differential as in closed string*)
BracketProjection[Wedge[a__] b___, weightHolo_, weightAntiHolo_] := Wedge[a, BracketProjection[b, weightHolo, weightAntiHolo]]


(* ::Subsection:: *)
(*Factorize operators into holomorphic and anti-holomorphic parts*)


(* ::Subsubsection:: *)
(*Factorize multi-local operators*)


factorizeMultiOp::usage = "Factorize multi-local operator into holomorphic and antiholomorphic multi-local operators";
factorizeMultiOp[multiOp_/;MultiOpTest[multiOp]]:=
Module[{multiOpReplaced = multiOp, localOpFactorized, localOpPrefac, localOpList,
localOpHolo, localOpAntiHolo, localOpsHolo, localOpsAntiHolo,localOpsHoloAntiHolo, prefac = 1,
scalarQ, parseLocalOp},
scalarQ[expr_] := And @@ (FreeQ[expr, #] & /@ allfields);
parseLocalOp[localOp_] := Module[{factors},
If[RTestUpToConstant[localOp],
{
extractPrefacFromRTimesConstant[localOp] /. {Wedge[a___] -> 1},
extractListFromRTimesConstant[localOp]
},
If[Head[localOp] === Times,
factors = List @@ localOp;
{
Times @@ ((Select[factors, scalarQ]) /. {Wedge[a___] -> 1}),
Select[factors, !scalarQ[#] &]
},
If[scalarQ[localOp],
{localOp /. {Wedge[a___] -> 1}, {}},
{1, {localOp}}
]
]
]
];
{localOpsHolo, localOpsAntiHolo, localOpsHoloAntiHolo} =
Reap[Scan[Function[localOp,
{localOpPrefac, localOpList} = parseLocalOp[localOp];
localOpList = factorizeOperator /@ localOpList;
localOpList = Flatten[
  (localOpList /. {
    {holoPart_, antiHoloPart_} :> {holoPart, antiHoloPart},
    Ra_ /; RTest[Ra] :> List @@ Ra
  }),
  1
];
localOpFactorized = splitOperators[localOpList, isHolomorphic, isAntiHolomorphic];
prefac = prefac * localOpPrefac;
{localOpHolo, localOpAntiHolo} = {R @@ localOpFactorized[[1]], R @@ localOpFactorized[[2]]};
Sow[localOpHolo, "Holo"];
Sow[localOpAntiHolo, "AntiHolo"];
Sow[localOpList, "Holo and AntiHolo"];
], List @@ multiOpReplaced]][[2]];
{MultiOp @@ localOpsHolo, MultiOp @@ localOpsAntiHolo, prefac factorizationSign[Flatten[localOpsHoloAntiHolo], isHolomorphic, isAntiHolomorphic]}]


(* ::Subsubsection:: *)
(*Factorize normal-ordered product utils*)


extractPrefacFromRTimesConstant::usage = "Extracts constant prefactor from possible constant multiplied by normal-ordered product";
extractPrefacFromRTimesConstant[Times[a_, Ra_/;RTest[Ra]]] := a;
extractPrefacFromRTimesConstant[Ra_/;RTest[Ra]] := 1;
extractPrefacFromRTimesConstant[1] := 1;

extractListFromRTimesConstant::usage = "Extracts the list of operators inside a normal-ordered product possibly multiplied by a constant prefactor";
extractListFromRTimesConstant[Times[a_, Ra_/;RTest[Ra]]] := List @@ Ra;
extractListFromRTimesConstant[Ra_/;RTest[Ra]] := List @@ Ra;


(* ::Subsubsection::Closed:: *)
(*Set factorization replacement*)


(* ::Subsection:: *)
(*Define action of b0^-*)


(*Define holomorphic b-ghost mode actions, generally at different points*)
bmodeHolo[contourCenter_][mode_][Ra_/;RTest[Ra]] := Module[{pos, result = 0, cAssoc = Association[], fermionNumber = 0, position = 1},
Scan[Function[Relem,
If[Head[Relem ]=== c, If[mode >= Relem[[1]]-1, 
If[Relem[[2]] - contourCenter =!=0,
AssociateTo[cAssoc, position -> {Relem -> (-1)^fermionNumber 1/Factorial[mode-(Relem[[1]]-1)] (Relem[[2]]-contourCenter)^(mode-(Relem[[1]]-1))}],
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
bmodeAntiHolo[contourCenter_][mode_][Ra_/;RTest[Ra]] := Module[{pos, result = 0, cAssoc = Association[], fermionNumber = 0, position = 1},
Scan[Function[Relem,
If[Head[Relem ]=== ct, If[mode >= Relem[[1]]-1, 
If[Relem[[2]]-contourCenter=!=0,
AssociateTo[cAssoc, position -> {Relem -> (-1)^fermionNumber 1/Factorial[mode-(Relem[[1]]-1)] (Relem[[2]]-contourCenter)^(mode-(Relem[[1]]-1))}],
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
bmodeHolo[contourCenter_][mode_][a_+b_]:=bmodeHolo[contourCenter][mode][a] + bmodeHolo[contourCenter][mode][b];
bmodeHolo[contourCenter_][mode_][a_ b_]:=a bmodeHolo[contourCenter][mode][b]/;(And @@(FreeQ[a,#]&/@ allfields))
bmodeHolo[contourCenter_][mode_][0] := 0;

bmodeAntiHolo[contourCenter_][mode_][a_+b_]:=bmodeAntiHolo[contourCenter][mode][a] + bmodeAntiHolo[contourCenter][mode][b];
bmodeAntiHolo[contourCenter_][mode_][a_ b_]:=a bmodeAntiHolo[contourCenter][mode][b]/;(And @@(FreeQ[a,#]&/@ allfields))
bmodeAntiHolo[contourCenter_][mode_][0] := 0;


(* ::Subsection:: *)
(*Create B-ghost insertion*)


createCurlyB::usage = "Create curlyB insertion given local coordinate functions, moduli and number of bracket insertions"
createCurlyB[SFList__, localCoordinateFunctionsHol__, localCoordinateFunctionsAntiHol__,  bracketOrder_, moduli_,  w_, wbar_]:= 
Module[{i,result = 0},

(*For each modulus and insertion, create the relevant b-ghost insertions*)
Do[
result = result + createBs[SFList[[i]], localCoordinateFunctionsHol[[i]], localCoordinateFunctionsAntiHol[[i]], i, moduli, w, wbar], 
{i,1,bracketOrder}];
result
]


scalarQ[x_] := FreeQ[x, _MultiOp | _R]


getMinCGhostModding::usage = "Get minimum c-ghost modding inside a local operator";

getMinCGhostModding[z0_][expr_Times] := getMinCGhostModding[z0][SelectFirst[List @@ expr, !scalarQ[#] &]]

getMinCGhostModding[z0_][Ma_/; MultiOpTest[Ma]]:=  Module[{moddingList = Select[getMinCGhostModding[z0] /@ List @@ Ma, # != "None" &]},
If[moddingList =!= {}, Min[moddingList], "None"]
];

getMinCGhostModding[z0_][Ra_/; RTest[Ra]]:= Module[{RList = List @@ Ra, maxOrder = "None", currentOrder},
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

getMinCbarGhostModding[z0bar_][Ma_/; MultiOpTest[Ma]]:=  Module[{moddingList = Select[getMinCbarGhostModding[z0bar] /@ List @@ Ma,# != "None" &]},
If[moddingList =!= {}, Min[moddingList], "None"]
];

getMinCbarGhostModding[z0bar_][Ra_/; RTest[Ra]]:= Module[{RList = List @@ Ra, maxOrder = "None", currentOrder},
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
BGhostIntegrandHolo = Total[(#/.{Times[rest___,(z-z0)^p_?NumericQ]:> rest bmodeHolo[z0][p-1][insertionLabel],Times[rest___,diff_/;diff===(z-z0)]:> rest bmodeHolo[z0][0][insertionLabel],Times[rest___,1]:> rest bmodeHolo[z0][-1][insertionLabel]}) & /@ (List@@(expandedBGhostIntegrandHol))],
(*If no derivatives of c-ghost appear, then return dz(w)/d(modulus)_{w=0} b_{-1}*)
BGhostIntegrandHolo = -Differential[localCoordinateHol[0], moduli] bmodeHolo[z0][-1][insertionLabel];
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
BGhostIntegrandAntiHolo = Total[(#/.{Times[rest___,(zbar-z0bar)^p_?NumericQ]:> rest bmodeAntiHolo[z0bar][p-1][insertionLabel],Times[rest___,diff_/;diff===(zbar-z0bar)]:> rest bmodeAntiHolo[z0bar][0][insertionLabel],Times[rest___,1]:> rest bmodeAntiHolo[z0bar][-1][insertionLabel]})& /@ (List@@(expandedBGhostIntegrandAntiHol))],

(*If no derivatives of c-ghost appear, then return dzbar(wbar)/d(modulus)_{wbar=0} bt_{-1}*)
BGhostIntegrandAntiHolo = -Differential[localCoordinateAntiHol[0], moduli] bmodeAntiHolo[z0bar][-1][insertionLabel];
],
BGhostIntegrandAntiHolo = 0;
];
result = BGhostIntegrandHolo + BGhostIntegrandAntiHolo;
result]


(* ::Subsubsection:: *)
(*Define differential of a local coordinate map*)

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
combineCurlyBs[a_ f_,d___]:= a combineCurlyBs[f,d]/;(And @@(FreeQ[a,#]&/@ {Differential, Wedge, bmodeHolo, bmodeAntiHolo}))
combineCurlyBs[f___, a_ d_]:= a combineCurlyBs[f,d]/;(And @@(FreeQ[a,#]&/@ {Differential, Wedge, bmodeHolo, bmodeAntiHolo}))
combineCurlyBs[a_ b___, c_ d___]:= Wedge[a, c] combineCurlyBs[b,d]/; (MemberQ[{Differential, Wedge}, Head[a]] && MemberQ[{Differential, Wedge}, Head[c]]);
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


Wedge::usage = "A wedge product between Differentials";
Wedge[ c___,a_,a_,d___]:=0
Wedge[c___,a_+b_,d___]:=Wedge[c,a,d]+Wedge[c,b,d]
Wedge[c___, s_?nonDifferentialQ f_, d___] := s Wedge[c, f, d];
Wedge[c___, s_?nonDifferentialQ,   d___] := s Wedge[c, d];
Wedge[]:=1;
Wedge[a___,Wedge[b___],c___]:=Wedge[a,b,c]
Wedge[c___,b_,a_,d___]:=-Wedge[c,a,b,d]/;(!OrderedQ[{b,a}])

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
getBGhostPosition[bmodeHolo[contourCenter_][a_][b_]]:= b;
getBGhostPosition[bmodeAntiHolo[contourCenter_][a_][b_]]:= b;


actBGhostMode::usage = "Acts a b-ghost mode on a local operator";
actBGhostMode[a_, op1_ + op2_]:= actBGhostMode[a, op1] + actBGhostMode[a, op2];
actBGhostMode[a_, b_ c_]:= b actBGhostMode[a,c]/;(And @@(FreeQ[b,#]&/@ allfields));

actBGhostMode[bmodeHolo[contourCenter_][a_], MultiOpa_/;MultiOpTest[MultiOpa]]:= Module[{result = 0, sign = 1, OpList = List @@ MultiOpa, parities},
parities = Map[parityOp, OpList];
Do[result = result + (-1)^(Total[Take[parities, i-1]]) MultiOp @@ MapAt[actBGhostMode[bmodeHolo[contourCenter][a], #] &, OpList, i],
{i, 1, Length[OpList]}];
result
];

actBGhostMode[bmodeHolo[contourCenter_][a_][b_], MultiOpa_/;MultiOpTest[MultiOpa]]:= Module[{result = 0, sign = 1, OpList = List @@ MultiOpa, parities},
parities = Map[parityOp, OpList];
Do[result = result + (-1)^(Total[Take[parities, i-1]]) MultiOp @@ MapAt[actBGhostMode[bmodeHolo[contourCenter][a], #] &, OpList, i],
{i, 1, Length[OpList]}];
result
];

actBGhostMode[bmodeAntiHolo[contourCenter_][a_], MultiOpa_/;MultiOpTest[MultiOpa]]:= Module[{result = 0, sign = 1, OpList = List @@ MultiOpa, parities},
parities = Map[parityOp, OpList];
Do[result = result + (-1)^(Total[Take[parities, i-1]]) MultiOp @@ MapAt[actBGhostMode[bmodeAntiHolo[contourCenter][a], #] &, OpList, i],
{i, 1, Length[OpList]}];
result
];

actBGhostMode[bmodeAntiHolo[contourCenter_][a_][b_], MultiOpa_/;MultiOpTest[MultiOpa]]:= Module[{result = 0, sign = 1, OpList = List @@ MultiOpa, parities},
parities = Map[parityOp, OpList];
Do[result = result + (-1)^(Total[Take[parities, i-1]]) MultiOp @@ MapAt[actBGhostMode[bmodeAntiHolo[contourCenter][a], #] &, OpList, i],
{i, 1, Length[OpList]}];
result
];

actBGhostMode[bmodeHolo[contourCenter_][a_][b_], Ra_/;RTest[Ra]]:= bmodeHolo[contourCenter][a][Ra];
actBGhostMode[bmodeAntiHolo[contourCenter_][a_][b_], Ra_/;RTest[Ra]]:= bmodeAntiHolo[contourCenter][a][Ra];
actBGhostMode[bmodeHolo[contourCenter_][a_], Ra_/;RTest[Ra]]:= bmodeHolo[contourCenter][a][Ra];
actBGhostMode[bmodeAntiHolo[contourCenter_][a_], Ra_/;RTest[Ra]]:= bmodeAntiHolo[contourCenter][a][Ra];
actBGhostMode[b_, a_/;NumericQ[a]]:= 0;


(* ::Subsection:: *)
(*Collapse b0m*)


CollapseB0m::usage = "Collapses b0m, which was being held unevaluated";

CollapseB0m[a_ + b_]:= CollapseB0m[a] + CollapseB0m[b]
CollapseB0m[a_ b_]:= a CollapseB0m[b]/;(And @@(FreeQ[a,#]&/@ allfields))
CollapseB0m[b0mHold[a_]]:= actBGhostMode[bmodeHolo[0][0], a] - actBGhostMode[bmodeAntiHolo[0][0],a]
CollapseB0m[0]:=0


(* ::Subsection:: *)
(*Apply propagator*)


ApplyPropagator::usage = "Applies the propagator b0+/L0+ on a level-projected bracket";

ApplyPropagator[q_][a_ + b_]:= ApplyPropagator[q][a] + ApplyPropagator[q][b]
ApplyPropagator[q_][a_ b_]:= a ApplyPropagator[q][b]/;(And @@(FreeQ[a,#]&/@ allfields));

ApplyPropagator[q_][MultiOpa_/;MultiOpTest[MultiOpa]]:= Module[{rescaledMultiOp},
rescaledMultiOp =  1/(-4 Pi I) 1/(q Conjugate[q]) MultiOp[(mapOp[rescaling[q], rescaling[Conjugate[q]]][MultiOpa])];
actBGhostMode[bmodeHolo[0][0], rescaledMultiOp] + actBGhostMode[bmodeAntiHolo[0][0],rescaledMultiOp]]

ApplyPropagator[q_][Ra_/;RTest[Ra]]:= Module[{rescaledR},
rescaledR = 1/(-4 Pi I) 1/(q Conjugate[q]) mapOp[rescaling[q], rescaling[Conjugate[q]]][Ra];
actBGhostMode[bmodeHolo[0][0], rescaledR] + actBGhostMode[bmodeAntiHolo[0][0],rescaledR]]

ApplyPropagator[q_][SFa_/;SFTest[SFa]]:= SF[ApplyPropagator[q] @@ SFa]

ApplyPropagator[q_][0]:=0;

rescaling[factor_][z_]:= factor z //Expand;


(* ::Subsection:: *)
(*Determine whether OPE should be computed*)


singularity::usage = "Compute order of singularity of Wick contraction"
singularity[b[n_,z_],c[m_,w_]]:= 1 + m + n;
singularity[c[m_,w_],b[n_,z_]]:= 1 + m + n;
singularity[bt[n_,z_],ct[m_,w_]]:= 1 + m + n;
singularity[ct[m_,w_],bt[n_,z_]]:= 1 + m + n;


singularityMatrix::usage = "Compute a matrix of orders of singularities in the OPE of two operators"
singularityMatrix[Ra_/;RTest[Ra], Rb_/; RTest[Rb]]:= Table[singularity[Ra[[i]], Rb[[j]]], {i, 1, Length[Ra]}, {j, 1, Length[Rb]}];
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


(* ::Subsection:: *)
(*Effective bracket*)


(* Hold symbols for deferred evaluation *)
BracketHold::usage = "Placeholder for Bracket during EffectiveBracketHold computation";
PropagatorHold::usage = "Placeholder for ApplyPropagator during EffectiveBracketHold computation";
ProjectorHold::usage = "Placeholder for BracketProjected during EffectiveBracketHold computation";

(* Multilinearity for BracketHold *)
BracketHold[args___, a_ + b_, rest___] := BracketHold[args, a, rest] + BracketHold[args, b, rest]
BracketHold[args___, c_ d_, rest___] := c BracketHold[args, d, rest] /; And @@ (FreeQ[c, #] & /@ allfields)
BracketHold[] := 1;

(* Multilinearity for PropagatorHold *)
PropagatorHold[q_][a_ + b_] := PropagatorHold[q][a] + PropagatorHold[q][b]
PropagatorHold[q_][c_ a_] := c PropagatorHold[q][a] /; And @@ (FreeQ[c, #] & /@ allfields)
PropagatorHold[q_][0] := 0;

(* Multilinearity for ProjectorHold *)
ProjectorHold[wH_, wA_][a_ + b_] := ProjectorHold[wH,wA][a] + ProjectorHold[wH,wA][b]
ProjectorHold[wH_,wA_][c_ a_] := c ProjectorHold[wH,wA][a] /; And @@ (FreeQ[c, #] & /@ allfields)
ProjectorHold[wH_,wA_][0] := 0;

(* ProjectorBarHold - placeholder for (1-P) structure applied to inner brackets *)
ProjectorBarHold::usage = "Placeholder for ProjectorBar (1-P) during EffectiveBracketHold computation";
ProjectorBarHold[wH_, wA_][a_ + b_] := ProjectorBarHold[wH,wA][a] + ProjectorBarHold[wH,wA][b]
ProjectorBarHold[wH_, wA_][c_ a_] := c ProjectorBarHold[wH,wA][a] /; And @@ (FreeQ[c, #] & /@ allfields)
ProjectorBarHold[wH_, wA_][0] := 0;


(* Get partitions excluding all-1s *)
getPartitions::usage = "Get integer partitions excluding the all-1s partition";
getPartitions[n_] := DeleteCases[IntegerPartitions[n], {1 ..}]


(* Generate all ways to assign n items to groups of given sizes *)
(* Works with positional indices to handle duplicate elements correctly *)
assignToGroups::usage = "Generate all index-based assignments of n positions to groups of given sizes";
assignToGroups[n_Integer, sizes_List] := Module[{indices = Range[n], result = {},
  sortedSizes = Sort[sizes, Greater], helper},

  (* Recursive helper to build assignments using indices *)
  helper[remaining_, {}, acc_] := AppendTo[result, acc];
  helper[remaining_, {size_, rest___}, acc_] := Module[{subsets},
    subsets = Subsets[remaining, {size}];
    Scan[helper[Complement[remaining, #], {rest}, Append[acc, #]] &, subsets]
  ];

  helper[indices, sortedSizes, {}];

  (* Remove duplicates from repeated partition sizes *)
  DeleteDuplicatesBy[result, Sort]
]


(* Generate all valid orderings of groups for the linear chain *)
(* Returns list of ordered groups from outer to inner *)
(* Constraint: innermost (last) group must have size >= 2 *)
generateNestings::usage = "Generate all valid orderings of groups (innermost must have >=2 elements)";
generateNestings[groups_List] := Module[{perms},
  perms = Permutations[groups];
  (* Filter: innermost (last) group must have size >= 2 *)
  Select[perms, Length[Last[#]] >= 2 &]
]


(* Build the chain recursively from innermost outward *)
buildChain::usage = "Build nested bracket chain from ordered groups";
buildChain[{innermost_}, {}, wH_, wA_] := BracketHold[Sequence @@ innermost];
buildChain[{outer_, rest__}, {q_, qrest___}, wH_, wA_] :=
  BracketHold[Sequence @@ outer, PropagatorHold[q][ProjectorBarHold[wH,wA][buildChain[{rest}, {qrest}, wH, wA]]]];


(* Build a single Hold term from an ordered list of index groups *)
buildHoldTerm::usage = "Build a ProjectorHold[BracketHold[...]] term from ordered index groups";
buildHoldTerm[orderedIndexGroups_List, fieldList_List, wH_, wA_] := Module[
  {orderedGroups = Map[fieldList[[#]] &, orderedIndexGroups, {1}],
   qs = Table[ToExpression["q" <> ToString[i]], {i, Length[orderedIndexGroups] - 1}]},
  ProjectorHold[wH,wA][buildChain[orderedGroups, qs, wH, wA]]
]


(* Main EffectiveBracketHold function *)
(* Returns symbolic expression using BracketHold, PropagatorHold, ProjectorHold, ProjectorBarHold *)
EffectiveBracketHold[fields__, wH_, wA_] := Module[
  {n = Length[{fields}], partitions, allTerms = 0, fieldList = {fields}},

  partitions = getPartitions[n];

  (* Sum over all partitions *)
  Scan[Function[partition,
    (* Sum over all index-based assignments *)
    Scan[Function[indexAssignment,
      (* Sum over all valid orderings *)
      Scan[Function[ordering,
        allTerms = allTerms + buildHoldTerm[ordering, fieldList, wH, wA]
      ], generateNestings[indexAssignment]]
    ], assignToGroups[n, partition]]
  ], partitions];

  allTerms
]

(* Multilinearity of EffectiveBracketHold *)
EffectiveBracketHold[args___, a_ + b_, rest___] :=
  EffectiveBracketHold[args, a, rest] + EffectiveBracketHold[args, b, rest]
EffectiveBracketHold[args___, c_ d_, rest___] :=
  c EffectiveBracketHold[args, d, rest] /; And @@ (FreeQ[c, #] & /@ allfields)

(* Multilinearity of EffectiveBracket*)
EffectiveBracket[args___, a_ + b_, rest___, wH_, wA_] :=
  EffectiveBracket[args, a, rest, wH, wA] + EffectiveBracket[args, b, rest, wH, wA]
EffectiveBracket[args___, c_ d_, rest___, wH_, wA_] :=
  c EffectiveBracket[args, d, rest, wH, wA] /; And @@ (FreeQ[c, #] & /@ allfields)

(*Define EffectiveBracket as a substitution of EffectiveBracketHold*)
projectorBarSub = {ProjectorBarHold[wH_,wA_][a_] -> a - ProjectorHold[wH,wA][a]};
projectorOfBracketSub = {ProjectorHold[wH_,wA_][BracketHold[a__]]-> CollapseB0m[BracketProjected[a,wH,wA]]}
propagatorSub = {PropagatorHold[q_][a___]:>-ApplyPropagator[q][SF[a]]}
bracketSub = {BracketHold[a__]->SF[CollapseB0m[Bracket[a]]]}
EffectiveBracket[fields__, wH_, wA_]:= (((EffectiveBracketHold[fields, wH, wA]/.projectorBarSub)//.projectorOfBracketSub)/.bracketSub)/.propagatorSub;

(* ::Subsection:: *)
(*Draw tree diagrams*)


(* --- Tree representation --- *)
(* tNode["root" | "junction", {children}] for internal nodes *)
(* tLeaf[field] for external legs *)

(* --- Parsing --- *)

(* Collect all field leaves in left-to-right order *)
collectFields[BracketHold[args__]] := Flatten[collectFields /@ {args}]
collectFields[expr_ /; MatchQ[Head[expr], _PropagatorHold]] := collectFields[expr[[1]]]
collectFields[ProjectorBarHold[wH_,wA_][inner_]] := collectFields[inner]
collectFields[field_] := {field}

(* Parse EffectiveBracketHold output into lightweight tree *)
parseToTree[ProjectorHold[wH_,wA_][inner_]] := tNode["root", {parseBracket[inner]}]
parseBracket[BracketHold[args__]] := tNode["junction", parseArg /@ {args}]
parseArg[arg_ /; MatchQ[Head[arg], _PropagatorHold]] := parseBracket[arg[[1, 1]]]
parseArg[field_] := tLeaf[field]


(* --- Layout and rendering via Graphics primitives --- *)

leafColor[n_] := ColorData[97][n]

(* drawNode returns {graphicsPrimitives, xCenter, nextAvailableX} *)
(* Leaves are placed at integer x-positions; internal nodes centered over children *)
drawNode[tLeaf[field_], x0_, depth_, fieldMap_] := Module[
  {idx = fieldMap[field], col},
  col = leafColor[idx];
  {
    {col, EdgeForm[Darker[col, 0.3]], Disk[{x0, -depth}, 0.22],
     White, Text[Style[ToString[idx], Bold, 9], {x0, -depth}]},
    x0,
    x0 + 1
  }
]

drawNode[tNode[type_, children_List], x0_, depth_, fieldMap_] := Module[
  {nextX = x0, childResults = {}, myX, edgePrims, nodePrim, allPrims},

  Scan[Function[child,
    Module[{r = drawNode[child, nextX, depth + 1, fieldMap]},
      AppendTo[childResults, r];
      nextX = r[[3]];
    ]
  ], children];

  myX = Mean[#[[2]] & /@ childResults];

  (* Edges: drawn behind everything *)
  edgePrims = {GrayLevel[0.3], AbsoluteThickness[1.5],
    Sequence @@ (Line[{{myX, -depth}, {#[[2]], -(depth + 1)}}] & /@ childResults)};

  (* Node marker *)
  nodePrim = Switch[type,
    "root", {GrayLevel[0.3], EdgeForm[GrayLevel[0.3]], Disk[{myX, -depth}, 0.16],
             White, Text[Style["P", Bold, 7], {myX, -depth}]},
    "junction", {GrayLevel[0.3], EdgeForm[GrayLevel[0.3]], Disk[{myX, -depth}, 0.08]}
  ];

  (* Assemble: edges, then children, then this node on top *)
  allPrims = Join[{edgePrims}, #[[1]] & /@ childResults, {nodePrim}];
  {allPrims, myX, nextX}
]


(* --- Helpers --- *)

splitTerms[expr_Plus] := List @@ expr
splitTerms[expr_] := {expr}

extractProjectorHold[c_ ProjectorHold[wH_, wA_][expr_]] := {c, ProjectorHold[wH, wA][expr]}
extractProjectorHold[ProjectorHold[wH_, wA_][expr_]] := {1, ProjectorHold[wH, wA][expr]}

numberFields[terms_List] := Module[
  {allFields, uniqueFields},
  allFields = Flatten[collectFields[#[[2, 1]]] & /@ terms];
  uniqueFields = DeleteDuplicates[allFields];
  Association @ MapIndexed[#1 -> #2[[1]] &, uniqueFields]
]

makeLegend[fieldMap_Association] := Module[{entries},
  entries = KeyValueMap[
    Function[{field, idx},
      Row[{
        Graphics[{leafColor[idx], EdgeForm[Darker[leafColor[idx], 0.3]], Disk[{0, 0}, 1],
          White, Text[Style[ToString[idx], Bold, 10], {0, 0}]},
          ImageSize -> 18],
        " = ",
        field
      }]
    ], fieldMap];
  Column[entries, Spacings -> 0.3, Frame -> True, FrameStyle -> GrayLevel[0.8],
    Background -> GrayLevel[0.98], RoundingRadius -> 5]
]


(* --- Draw a single tree as a lightweight Graphics object --- *)

drawSingleTree[term_, fieldMap_] := Module[{coeff, proj, tree, result},
  {coeff, proj} = extractProjectorHold[term];
  tree = parseToTree[proj];
  result = drawNode[tree, 0, 0, fieldMap];
  Graphics[result[[1]], ImageSize -> {Automatic, 120}, ImagePadding -> 15]
]


(* --- Main DrawTree entry points --- *)

Options[DrawTree] = {"Legend" -> True};

DrawTree[0, OptionsPattern[]] := Style["No diagrams", Italic, GrayLevel[0.5]]

DrawTree[expr_Plus, opts : OptionsPattern[]] := Module[
  {terms, fieldMap, trees, nCols = 4, grid, legend},
  terms = extractProjectorHold /@ splitTerms[expr];
  fieldMap = numberFields[terms];
  trees = MapIndexed[
    Labeled[drawSingleTree[#1, fieldMap], Style["Term " <> ToString[#2[[1]]], GrayLevel[0.5], 8], Bottom] &,
    (#[[1]] #[[2]] & /@ terms)
  ];
  grid = Grid[Partition[trees, UpTo[nCols]], Spacings -> {2, 2}, Alignment -> Center];
  If[OptionValue["Legend"],
    legend = makeLegend[fieldMap];
    Column[{grid, legend}, Spacings -> 1.5, Alignment -> Center],
    grid
  ]
]

DrawTree[expr_ProjectorHold, opts : OptionsPattern[]] := Module[
  {terms, fieldMap, tree, legend},
  terms = {extractProjectorHold[expr]};
  fieldMap = numberFields[terms];
  tree = drawSingleTree[expr, fieldMap];
  If[OptionValue["Legend"],
    legend = makeLegend[fieldMap];
    Column[{tree, legend}, Spacings -> 1.5, Alignment -> Center],
    tree
  ]
]

DrawTree[c_ expr_ProjectorHold, opts : OptionsPattern[]] := Module[
  {terms, fieldMap, tree, legend},
  terms = {extractProjectorHold[c expr]};
  fieldMap = numberFields[terms];
  tree = drawSingleTree[c expr, fieldMap];
  If[OptionValue["Legend"],
    legend = makeLegend[fieldMap];
    Column[{tree, legend}, Spacings -> 1.5, Alignment -> Center],
    tree
  ]
]


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
