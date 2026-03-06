(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Brackets`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`Operators`"];
Needs["StringCode`BasisGeneration`"];
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
BracketInputTest::usage = "Predicate used by bracket routines to recognize acceptable operator inputs (normal-ordered R[...] or MultiOp[...]).";
BracketInputTest[x_] := RTest[x] || MultiOpTest[x];
actBRST[op_/;RTest[op]]:= actBRSTHolo[op] + actBRSTAntiHolo[op];

(*Linearity of BRST charge action*)

actBRST[a_+b_]:=actBRST[a] + actBRST[b];
actBRST[a_ b_]:=a actBRST[b]/;(isScalarFactorQ[a])
actBRST[0] := 0;

actBRSTAntiHolo[a_+b_]:= actBRSTAntiHolo[a] + actBRSTAntiHolo[b];
actBRSTAntiHolo[a_ b_]:= a actBRSTAntiHolo[b]/;(isScalarFactorQ[a])
actBRSTAntiHolo[0] := 0;

actBRSTHolo[a_+b_]:= actBRSTHolo[a] +actBRSTHolo[b];
actBRSTHolo[a_ b_]:=a actBRSTHolo[b]/;(isScalarFactorQ[a])
actBRSTHolo[0] := 0;


(* ::Subsection:: *)
(*Define bracket*)


(*Multilinearity of Bracket*)
Bracket[args___, a_ + b_, rest___] := Bracket[args, a, rest] + Bracket[args, b, rest]

Bracket[args___, a_ b_, rest___] := a Bracket[args, b, rest] /; (isScalarFactorQ[a] && FreeQ[a, Wedge])

(*Join wedge products, give no sign: assuming that we wedge even number of differential as in closed string*)
Bracket[args___, Wedge[a__]b___, rest___]:= Wedge[a, Bracket[args, b, rest]]; 

BracketBosonic::usage = "Defines bosonic part of the bracket, which is shared among string theories";
BracketBosonic[toBracket__/;AllTrue[{toBracket}, BracketInputTest]]:= Module[{result = 0, localCoordinateFunctionsHol, localCoordinateFunctionsAntiHol, localCoordinateReplacement,
moduli, bracketOrder, bracketList = {toBracket}, w, wbar, curlyB, curlyBs, minCGhostModdings, minCbarGhostModdings, opList, moduliLength, afterApplyingBghosts, afterHeldActionOfPCOs, prefac},
bracketOrder = Length[bracketList];

(*Conformally transform the string field insertions*)
{localCoordinateFunctionsHol, localCoordinateFunctionsAntiHol, w, wbar, moduli, localCoordinateReplacement} = getLocalCoordinateData[bracketOrder];
opList = placeOpAtPosGivenLocalCoordinates[localCoordinateFunctionsHol, localCoordinateFunctionsAntiHol, bracketList];

(*Create and apply the curly B-ghost insertions, one B-ghost action on the insertions for each modulus*)
moduliLength = Length[moduli];

If[moduliLength > 0,

(*Create the curly B-ghost insertions, one for each modulus*)
curlyB = createCurlyB[opList, localCoordinateFunctionsHol, localCoordinateFunctionsAntiHol, bracketOrder, moduli, w, wbar];
curlyBs = createCurlyBs[curlyB, moduliLength];

(*Apply the curly B-ghost insertions*)
afterApplyingBghosts = applyCurlyBs[opList, curlyBs, moduliLength],
afterApplyingBghosts = MultiOp @@ opList];
result = 1/(-2Pi I)^(1/2 moduliLength) afterApplyingBghosts;
result]


(* ::Subsubsection:: *)
(*Place string fields at positions given by local coordinates*)


placeOpAtPosGivenLocalCoordinates::usage = "Places a list of string fields at positions specified by corresponding holomorphic/antiholomorphic local coordinate maps.";
placeOpAtPosGivenLocalCoordinates[localCoordinateFunctionsHol__, localCoordinateFunctionsAntiHol__, ops__]:= 
Table[OpAtPos[ops[[i]], localCoordinateFunctionsHol[[i]], localCoordinateFunctionsAntiHol[[i]]], {i, 1, Length[ops]}]


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
BracketProjected[toBracket__/; AllTrue[{toBracket}, BracketInputTest], weightHolo_, weightAntiHolo_]:=
b0mHold[BracketProjection[(Bracket[toBracket]/.{b0mHold[a__]:>a}), weightHolo, weightAntiHolo]];

(*Multilinearity of projected Bracket*)
BracketProjected[args___, a_ + b_, rest___,  weightHolo_, weightAntiHolo_] := BracketProjected[args, a, rest,  weightHolo, weightAntiHolo] + BracketProjected[args, b, rest, weightHolo, weightAntiHolo]
BracketProjected[args___, a_ b_, rest___, weightHolo_, weightAntiHolo_] := a BracketProjected[args, b, rest, weightHolo, weightAntiHolo] /; (isScalarFactorQ[a] && FreeQ[a, Wedge])
BracketProjected[args___, 0, rest___, weightHolo_, weightAntiHolo_]:=0;

(*Join wedge products, give no sign: assuming that we wedge even number of differential as in closed string*)
BracketProjected[args___, Wedge[a__] b___, rest___, weightHolo_, weightAntiHolo_] := Wedge[a, BracketProjected[args, b, rest, weightHolo, weightAntiHolo]]


(*Multilinearity of Bracket projection*)
BracketProjection[a_ + b_, weightHolo_, weightAntiHolo_] :=
 BracketProjection[a, weightHolo, weightAntiHolo] + BracketProjection[b, weightHolo, weightAntiHolo]
 
BracketProjection[a_ b_, weightHolo_, weightAntiHolo_] := 
a BracketProjection[b, weightHolo, weightAntiHolo] /; (isScalarFactorQ[a] && FreeQ[a, Wedge])

(*Join wedge products, give no sign: assuming that we wedge even number of differential as in closed string*)
BracketProjection[Wedge[a__] b___, weightHolo_, weightAntiHolo_] := Wedge[a, BracketProjection[b, weightHolo, weightAntiHolo]]


(* ::Subsection:: *)
(*Shared projected bracket helpers*)


combineProjectedBracketChiral::usage = "Combines holomorphic and antiholomorphic projected bracket pieces into a single normal-ordered factor, simplifying identities for 0 and 1.";
combineProjectedBracketChiral[projectedHolo_, projectedAntiHolo_] := Which[
  projectedHolo === 0 || projectedAntiHolo === 0, 0,
  projectedHolo === 1, projectedAntiHolo,
  projectedAntiHolo === 1, projectedHolo,
  True, R[projectedHolo, projectedAntiHolo]
];

projectBracketLocalOps::usage = "Projects a list of local operators to fixed chiral weights, using a factorized path when possible and falling back to generic OPE projection otherwise.";
projectBracketLocalOps[localOps_List, weightHolo_, weightAntiHolo_] := Module[
  {
    dualChiralOps, factorizationPrefac, bracketHolo, bracketAntiHolo,
    holoLocalOps, antiLocalOps, projectedHolo, projectedAntiHolo, projectedOPE
  },

  dualChiralOps = Flatten[(extractListFromRTimesConstant /@ Select[localOps, RTestUpToConstant]), 1];
  dualChiralOps = Select[dualChiralOps, isHolomorphic[Head[#]] && isAntiHolomorphic[Head[#]] &];

  (* Prefer factorized projection; only skip it when mixed-chirality fields exist but some are not factorizable. *)
  If[dualChiralOps === {} || AllTrue[dualChiralOps, isFactorizable[Head[#]] &],
    {bracketHolo, bracketAntiHolo, factorizationPrefac} = factorizeMultiOp[MultiOp @@ localOps];
    holoLocalOps = Select[List @@ bracketHolo, RTest];
    antiLocalOps = Select[List @@ bracketAntiHolo, RTest];

    (* In factorized mode, OPEProjected* receives the requested chiral weights directly. *)
    projectedHolo = If[
      holoLocalOps === {},
      If[weightHolo === 0, 1, 0],
      OPEProjectedHolo[weightHolo] @@ holoLocalOps
    ];
    projectedAntiHolo = If[
      antiLocalOps === {},
      If[weightAntiHolo === 0, 1, 0],
      OPEProjectedAntiHolo[weightAntiHolo] @@ antiLocalOps
    ];
    {"Factorized", factorizationPrefac, projectedHolo, projectedAntiHolo},

    (* Fallback path for non-factorizable mixed-chirality operators. *)
    projectedOPE = OPEProjected[weightHolo, weightAntiHolo] @@ localOps;
    {"Generic", projectedOPE}
  ]
];


(* ::Subsection:: *)
(*Factorize operators into holomorphic and anti-holomorphic parts*)


(* ::Subsubsection:: *)
(*Factorize multi-local operators*)


factorizeMultiOp::usage = "Factorize multi-local operator into holomorphic and antiholomorphic multi-local operators";
factorizeMultiOp[multiOp_/;MultiOpTest[multiOp]]:=
Module[{multiOpReplaced = multiOp, localOpFactorized, localOpPrefac, localOpList,
localOpHolo, localOpAntiHolo, localOpsHolo, localOpsAntiHolo,localOpsHoloAntiHolo, prefac = 1,
scalarQ, parseLocalOp},
scalarQ[expr_] := isScalarFactorQ[expr];
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
(*Create B-ghost insertion*)


createCurlyB::usage = "Create curlyB insertion given local coordinate functions, moduli and number of bracket insertions"
createCurlyB[SFList__, localCoordinateFunctionsHol__, localCoordinateFunctionsAntiHol__,  bracketOrder_, moduli_,  w_, wbar_]:= 
Module[{i,result = <||>},

(*For each modulus and insertion, create the relevant b-ghost insertions*)
Do[
result = mergeCurlyBAssociations[result, createBs[SFList[[i]], localCoordinateFunctionsHol[[i]], localCoordinateFunctionsAntiHol[[i]], i, moduli, w, wbar]],
{i,1,bracketOrder}];
result
]


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

getMinCbarGhostModding[z0bar_][expr_Times] := getMinCbarGhostModding[z0bar][SelectFirst[List @@ expr, !scalarQ[#] &]]

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
  getInverseSeriesAtOrder[toInvert, coord, inversionCoord, order] =
    (InverseSeries[Series[toInvert,{coord,0,order}]]//Normal)/.{coord->inversionCoord};

canonicalCurlyBKey::usage = "Sort a b-ghost mode list into canonical order and return the induced fermionic sign plus held key.";
canonicalCurlyBKey[modes_List] := Module[{sign = Signature[modes]},
  If[sign === 0,
    {0, HoldComplete[{}]},
    With[{sortedModes = Sort[modes]},
      (*Store the evaluated canonical ordering so equivalent mode pairs really merge*)
      {sign, HoldComplete[sortedModes]}
    ]
  ]
];

mergeCurlyBAssociations::usage = "Merge curly-B associations, summing coefficients for identical canonical mode lists.";
mergeCurlyBAssociations[] := <||>;
mergeCurlyBAssociations[data__Association] := Select[Merge[{data}, Total], # =!= 0 &];

bgGhostModeCoefficients::usage = "Compute memoized b-ghost mode coefficients for a local coordinate map.";
bgGhostModeCoefficients[localCoordinate_, moduli_, maxOrder_Integer] :=
  bgGhostModeCoefficients[localCoordinate, moduli, maxOrder] = Module[
    {localCoord, sphereCoord, center, inverseSeries, shift, shiftedIntegrand},
    localCoord = Unique["curlyBW"];
    sphereCoord = Unique["curlyBZ"];
    center = localCoordinate[0];
    inverseSeries = getInverseSeriesAtOrder[localCoordinate[localCoord], localCoord, sphereCoord, maxOrder];
    shift = Unique["curlyBShift"];
    (*Expand the differentiated inverse map around the insertion point and read off mode coefficients by powers of the shifted sphere coordinate*)
    shiftedIntegrand = Expand[
      (Series[-(Differential[localCoordinate[localCoord], moduli] /. localCoord -> inverseSeries), {sphereCoord, center, maxOrder}] // Normal) /. sphereCoord -> shift + center
    ];
    Association @ Cases[
      Table[(power - 1) -> Coefficient[shiftedIntegrand, shift, power], {power, 0, maxOrder}],
      (_ -> coeff_) /; coeff =!= 0
    ]
  ];

createBsChiralData::usage = "Construct a single-chirality b-ghost insertion as an association keyed by held mode lists.";
createBsChiralData[insertion_, localCoordinate_, insertionLabel_, moduli_, contourCenter_, minGhostModdingFn_, modeHead_] := Module[
  {minGhostModding, maxOrder},
  minGhostModding = minGhostModdingFn[contourCenter][insertion];
  If[minGhostModding === "None", Return[<||>]];
  maxOrder = -minGhostModding + 1;
  If[maxOrder <= 0,
    (*If no derivatives of the c-ghost appear, only the b_{-1} mode survives*)
    Return[<|HoldComplete[{modeHead[contourCenter][-1][insertionLabel]}] -> -Differential[contourCenter, moduli]|>]
  ];
  (*Otherwise attach the coefficient of each shifted power to the corresponding b-mode*)
  Association @ KeyValueMap[
    HoldComplete[{modeHead[contourCenter][#1][insertionLabel]}] -> #2 &,
    bgGhostModeCoefficients[localCoordinate, moduli, maxOrder]
  ]
];


createBs::usage = "Creates b-ghost insertions for a given modulus and set of local coordinates, given an upper bound on b-ghost modding"
createBs[insertion_, localCoordinateHol_, localCoordinateAntiHol_, insertionLabel_, moduli_, w_, wbar_]:=
Module[{z0 = localCoordinateHol[0], z0bar = localCoordinateAntiHol[0]},
(*Combine the holomorphic and antiholomorphic contributions for this insertion*)
mergeCurlyBAssociations[
  createBsChiralData[insertion, localCoordinateHol, insertionLabel, moduli, z0, getMinCGhostModding, bmodeHolo],
  createBsChiralData[insertion, localCoordinateAntiHol, insertionLabel, moduli, z0bar, getMinCbarGhostModding, bmodeAntiHolo]
]]


(* ::Subsubsection:: *)
(*Define differential of a local coordinate map*)

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

combineCurlyBAssociations::usage = "Combine two curly-B associations using wedge products and canonicalized mode tuples.";
combineCurlyBAssociations[left_Association, right_Association] := Module[{result = <||>, coeff, sign, key},
  (*Combine every left/right term, wedge the differential prefactors, and merge by the canonical mode tuple*)
  KeyValueMap[
    Function[{leftModes, leftCoeff},
      KeyValueMap[
        Function[{rightModes, rightCoeff},
          coeff = Wedge[leftCoeff, rightCoeff];
          If[coeff =!= 0,
            {sign, key} = canonicalCurlyBKey[Join[ReleaseHold[leftModes], ReleaseHold[rightModes]]];
            If[sign =!= 0, result[key] = Lookup[result, key, 0] + sign coeff]
          ]
        ],
        right
      ]
    ],
    left
  ];
  Select[result, # =!= 0 &]
];

createCurlyBs::usage = "Takes in a single curlyB object, and creates a joined action of all required curlyB insertions"
createCurlyBs[curlyB_Association, numberOfModuli_]:= Module[{result = curlyB},
If[numberOfModuli > 1,
(*Combine one single-modulus curlyB for each modulus in the integration measure*)
result = Nest[combineCurlyBAssociations[curlyB, #] &, result, numberOfModuli - 1];
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
applyCurlyBs[SFList_, curlyBs_Association, moduliLength_]:=
(*The overall sign is for anticommutation of coordinate functions and b-ghosts*)
(-1)^(moduliLength/2)/Factorial[moduliLength] Total[
  KeyValueMap[#2 applyBghostModes[ReleaseHold[#1], SFList] &, curlyBs]
];


applyBghostModes::usage = "Apply an ordered list of b-ghost modes to a list of local operators.";
applyBghostModes[modes_List, SFList_] := Module[{result, bGhostPosition, currentResultAtPosition, SFParities = Map[parityOp, SFList], currentSFList},
currentSFList = SFList;
Scan[Function[BghostMode,
(*Act the b-ghost mode*)
bGhostPosition = getBGhostPosition[BghostMode];
currentResultAtPosition =  currentSFList[[bGhostPosition]];
currentSFList[[bGhostPosition]] = (-1)^(Total[Take[SFParities, bGhostPosition - 1]]) actBGhostMode[BghostMode, currentResultAtPosition];
SFParities[[bGhostPosition]] = Mod[SFParities[[bGhostPosition]] + 1,2];
], Reverse[modes]];
result = MultiOp @@ currentSFList;
result]


getBGhostPosition::usage = "Obtain the position at which a b-ghost mode acts";
getBGhostPosition[bmodeHolo[contourCenter_][a_][b_]]:= b;
getBGhostPosition[bmodeAntiHolo[contourCenter_][a_][b_]]:= b;


(* ::Subsection:: *)
(*Collapse b0m*)


CollapseB0m::usage = "Collapses b0m, which was being held unevaluated";

CollapseB0m[a_ + b_]:= CollapseB0m[a] + CollapseB0m[b]
CollapseB0m[a_ b_]:= a CollapseB0m[b]/;(isScalarFactorQ[a])
CollapseB0m[b0mHold[a_]]:= actBGhostMode[bmodeHolo[0][0], a] - actBGhostMode[bmodeAntiHolo[0][0],a]
CollapseB0m[0]:=0


(* ::Subsection:: *)
(*Apply propagator*)


ApplyPropagator::usage = "Applies the propagator b0+/L0+ on a level-projected bracket";

ApplyPropagator[q_][a_ + b_]:= ApplyPropagator[q][a] + ApplyPropagator[q][b]
ApplyPropagator[q_][a_ b_]:= a ApplyPropagator[q][b]/;(isScalarFactorQ[a]);

ApplyPropagator[q_][MultiOpa_/;MultiOpTest[MultiOpa]]:= Module[{rescaledMultiOp},
rescaledMultiOp =  1/(-4 Pi I) 1/(q Conjugate[q]) MultiOp[(mapOp[rescaling[q], rescaling[Conjugate[q]]][MultiOpa])];
actBGhostMode[bmodeHolo[0][0], rescaledMultiOp] + actBGhostMode[bmodeAntiHolo[0][0],rescaledMultiOp]]

ApplyPropagator[q_][Ra_/;RTest[Ra]]:= Module[{rescaledR},
rescaledR = 1/(-4 Pi I) 1/(q Conjugate[q]) mapOp[rescaling[q], rescaling[Conjugate[q]]][Ra];
actBGhostMode[bmodeHolo[0][0], rescaledR] + actBGhostMode[bmodeAntiHolo[0][0],rescaledR]]

ApplyPropagator[q_][0]:=0;

rescaling::usage = "Returns a coordinate rescaling map z |-> factor z (expanded).";
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
singularityMatrix[a_ b_, c_]:= singularityMatrix[b,c]/;(isScalarFactorQ[a]);
singularityMatrix[a_, b_ c_]:= singularityMatrix[a,c]/;(isScalarFactorQ[b]);


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
BracketHold[args___, c_ d_, rest___] := c BracketHold[args, d, rest] /; isScalarFactorQ[c]
BracketHold[] := 1;

(* Multilinearity for PropagatorHold *)
PropagatorHold[q_][a_ + b_] := PropagatorHold[q][a] + PropagatorHold[q][b]
PropagatorHold[q_][c_ a_] := c PropagatorHold[q][a] /; isScalarFactorQ[c]
PropagatorHold[q_][0] := 0;

(* Multilinearity for ProjectorHold *)
ProjectorHold[wH_, wA_][a_ + b_] := ProjectorHold[wH,wA][a] + ProjectorHold[wH,wA][b]
ProjectorHold[wH_,wA_][c_ a_] := c ProjectorHold[wH,wA][a] /; isScalarFactorQ[c]
ProjectorHold[wH_,wA_][0] := 0;

(* ProjectorBarHold - placeholder for (1-P) structure applied to inner brackets *)
ProjectorBarHold::usage = "Placeholder for ProjectorBar (1-P) during EffectiveBracketHold computation";
ProjectorBarHold[wH_, wA_][a_ + b_] := ProjectorBarHold[wH,wA][a] + ProjectorBarHold[wH,wA][b]
ProjectorBarHold[wH_, wA_][c_ a_] := c ProjectorBarHold[wH,wA][a] /; isScalarFactorQ[c]
ProjectorBarHold[wH_, wA_][0] := 0;

effectiveBracketTrees::usage = "Enumerate effective-bracket trees as nested index lists.";
effectiveBracketTrees[indices_List] := effectiveBracketTrees[indices] =
  If[Length[indices] < 2,
    {},
    Join[
      {indices},
      (*Choose an outer subset and recurse on the complementary inner subtree*)
      Flatten[
        Table[
          With[{innerIndices = Complement[indices, outerIndices]},
            If[Length[innerIndices] < 2, Nothing, {outerIndices, #} & /@ effectiveBracketTrees[innerIndices]]
          ],
          {outerSize, 1, Length[indices] - 2},
          {outerIndices, Subsets[indices, {outerSize}]}
        ],
        2
      ]
    ]
  ];

effectiveBracketTreeToHold::usage = "Convert a nested index-list tree into BracketHold/PropagatorHold/ProjectorBarHold expressions.";
effectiveBracketTreeToHold[indices_List /; VectorQ[indices, IntegerQ], fieldList_List, wH_, wA_, nextQ_Integer] :=
  {BracketHold[Sequence @@ fieldList[[indices]]], nextQ};
effectiveBracketTreeToHold[{outerIndices_List, innerTree_}, fieldList_List, wH_, wA_, nextQ_Integer] := Module[
  {innerHold, finalQ, q},
  (*Build the inner subtree first so q1, q2, ... follow the nesting depth deterministically*)
  {innerHold, finalQ} = effectiveBracketTreeToHold[innerTree, fieldList, wH, wA, nextQ + 1];
  q = ToExpression["q" <> ToString[nextQ]];
  {
    BracketHold[
      Sequence @@ fieldList[[outerIndices]],
      PropagatorHold[q][ProjectorBarHold[wH, wA][innerHold]]
    ],
    finalQ
  }
];


(* Main EffectiveBracketHold function *)
(* Returns symbolic expression using BracketHold, PropagatorHold, ProjectorHold, ProjectorBarHold *)
EffectiveBracketHold[fields__, wH_, wA_] := Module[
  {n = Length[{fields}], fieldList = {fields}, trees},
  (*Enumerate all tree skeletons once, then convert each skeleton into the held bracket expression*)
  trees = effectiveBracketTrees[Range[n]];
  Total[
    ProjectorHold[wH, wA][First[effectiveBracketTreeToHold[#, fieldList, wH, wA, 1]]] & /@ trees
  ]
]

(* Multilinearity of EffectiveBracketHold *)
EffectiveBracketHold[args___, a_ + b_, rest___] :=
  EffectiveBracketHold[args, a, rest] + EffectiveBracketHold[args, b, rest]
EffectiveBracketHold[args___, c_ d_, rest___] :=
  c EffectiveBracketHold[args, d, rest] /; isScalarFactorQ[c]

(* Multilinearity of EffectiveBracket*)
EffectiveBracket[args___, a_ + b_, rest___, wH_, wA_] :=
  EffectiveBracket[args, a, rest, wH, wA] + EffectiveBracket[args, b, rest, wH, wA]
EffectiveBracket[args___, c_ d_, rest___, wH_, wA_] :=
  c EffectiveBracket[args, d, rest, wH, wA] /; isScalarFactorQ[c]

(*Define EffectiveBracket as a substitution of EffectiveBracketHold*)
projectorBarSub = {ProjectorBarHold[wH_,wA_][a_] -> a - ProjectorHold[wH,wA][a]};
projectorOfBracketSub = {ProjectorHold[wH_,wA_][BracketHold[a__]]-> CollapseB0m[BracketProjected[a,wH,wA]]}
propagatorSub = {PropagatorHold[q_][a___]:>-ApplyPropagator[q][a]}
bracketSub = {BracketHold[a__]->CollapseB0m[Bracket[a]]}
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
  {nextX = x0, childResults, reaped, myX, edgePrims, nodePrim, allPrims},

  reaped = Last @ Reap[
    nextX = Fold[
      Function[{x, child},
        Module[{r = drawNode[child, x, depth + 1, fieldMap]},
          Sow[r];
          r[[3]]
        ]
      ],
      x0,
      children
    ]
  ];
  childResults = If[reaped === {}, {}, First[reaped]];

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
