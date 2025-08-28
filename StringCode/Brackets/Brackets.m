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


(* ::Subsection::Closed:: *)
(*Define bracket*)


(*Multilinearity of Bracket*)
Bracket[args___, a_ + b_, rest___] := Bracket[args, a, rest] + Bracket[args, b, rest]
Bracket[args___, a_ b_, rest___] := a Bracket[args, b, rest] /; And @@ (FreeQ[a, #] & /@ allfields)


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
(*Create B-ghost insertions*)


createCurlyBs::usage = "Create curlyB insertions given local coordinate functions, moduli and number of bracket insertions"
createCurlyBs[SFList__, localCoordinateFunctionsHol__, localCoordinateFunctionsAntiHol__, moduli__, bracketOrder_, w_, wbar_]:= 
Module[{i,j, minCGhostModdings,minCbarGhostModdings},
(*Get maximum possible b-ghost mode that does not vanish upon action*)
minCGhostModdings = Map[getMinCGhostModding, SFList];
minCbarGhostModdings = Map[getMinCbarGhostModding, SFList];
(*For each modulus and insertion, create the relevant b-ghost insertions*)
Table[
createBs[localCoordinateFunctionsHol[[j]], localCoordinateFunctionsAntiHol[[j]], w, wbar, moduli[[i]], minCGhostModdings[[j]], minCbarGhostModdings[[j]]],
{i,1,Length[moduli]}, {j,1,bracketOrder}]
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
createBs[localCoordinateHol_, localCoordinateAntiHol_, w_, wbar_, modulus_, minCGhostModding_, minCbarGhostModding_]:= 
Module[{result, expandedBGhostIntegrandHol,expandedBGhostIntegrandAntiHol, BGhostIntegrandListHol = {},BGhostIntegrandListAntiHol = {}, wInTermsOfZ, wbarInTermsOfZbar, 
z, zbar, z0 = localCoordinateHol/.{w->0}, z0bar = localCoordinateAntiHol/.{wbar->0}, maxOrderHolo, maxOrderAntiHolo},

If[minCGhostModding != "None",
maxOrderHolo = -minCGhostModding + 1;
If[maxOrderHolo > 0,
(*Obtain a disc coordinate w in terms of sphere coordinate z*)
wInTermsOfZ = getInverseSeriesAtOrder[localCoordinateHol, w,z, maxOrderHolo];

(*Differentiate local coordinates as a function of w with respect to the modulus, substituting the sphere coordinate z in the end*)
expandedBGhostIntegrandHol = Series[(D[localCoordinateHol, modulus])/.{w->wInTermsOfZ}, {z,z0,maxOrderHolo}]//Normal;

(*Replace terms in the above series with b-ghost modes*)
BGhostIntegrandListHol = (#/.{Times[rest___,(z-z0)^p_?NumericQ]:>bmodeHolo[p-1]*rest,Times[rest___,diff_/;diff===(z-z0)]:>bmodeHolo[0]*rest,Times[rest___,1]:>bmodeHolo[-1]*rest}) & /@ (List@@(expandedBGhostIntegrandHol)),

(*If no derivatives of c-ghost appear, then return dz(w)/d(modulus)_{w=0} b_{-1}*)
BGhostIntegrandListHol = {D[localCoordinateHol/.{w->0}, modulus] bmodeHolo[-1]};
]
];

If[minCbarGhostModding != "None",
maxOrderAntiHolo = -minCbarGhostModding + 1;
If[maxOrderAntiHolo > 0,
(*Obtain a disc coordinate wbar in terms of local coordinate zbar*)
wbarInTermsOfZbar = getInverseSeriesAtOrder[localCoordinateAntiHol, wbar, zbar, maxOrderAntiHolo];

(*Differentiate local coordinates as a function of wbar with respect to the modulus, substituting the sphere coordinate zbar in the end*)
expandedBGhostIntegrandAntiHol = Series[(D[localCoordinateAntiHol, modulus])/.{wbar->wbarInTermsOfZbar}, {zbar,z0bar,maxOrderAntiHolo}]//Normal;

(*Replace terms in the above series with bt-ghost modes*)
BGhostIntegrandListAntiHol =(#/.{Times[rest___,(zbar-z0bar)^p_?NumericQ]:>bmodeAntiHolo[p-1]*rest,Times[rest___,diff_/;diff===(zbar-z0bar)]:>bmodeAntiHolo[0]*rest,Times[rest___,1]:>bmodeBar[-1]*rest})& /@ (List@@(expandedBGhostIntegrandAntiHol)),

(*If no derivatives of c-ghost appear, then return dzbar(wbar)/d(modulus)_{wbar=0} bt_{-1}*)
BGhostIntegrandListAntiHol = {D[localCoordinateAntiHol/.{wbar->0}, modulus]bmodeAntiHolo[-1]};
]
];
result = Join[BGhostIntegrandListHol,BGhostIntegrandListAntiHol];
result]


(* ::Subsection:: *)
(*Apply B-ghost insertions to multi-op*)


applyCurlyBs::usage = "Apply a curlyB [sum over b-ghost modes attached to positions] to a multi-local operator"
applyCurlyBs[SFsAtPos_/;MultiOptest[SFsAtPos], curlyBs__]:= Module[{result = 0, intermediateResult = SFsAtPos, i, curlyBOnPosition},
Scan[Function[curlyB,
(*Apply each curlyB operator*)
Do[
 curlyBOnPosition = curlyB[[i]];
(*Action of a curlyB is application of its b-ghost modes on each local operator in the input multilocal operator*)
 result = result + replaceInMultiOpAtPosition[intermediateResult, i, applyBghostModes[curlyBOnPosition]],
 {i,1,Length[curlyB]}];
 intermediateResult = result;],
 curlyBs];
result
];


applyBghostModes::usage = "Apply a set of b-ghost modes to a local operator";
applyBghostModes[BghostModes__][Ra_/;RtestUpToConstant[Ra]] := Module[{result = 0},
Scan[Function[BghostMode,
(*Act a b-ghost mode*)
result = result + (BghostMode/.{bmodeHolo[a_]:> bmodeHolo[a][Ra], bmodeAntiHolo[a_]:> bmodeAntiHolo[a][Ra]});
], BghostModes];
result]
applyBghostModes[BghostModes__][a_] := 0;


replaceInMultiOpAtPosition::usage = "Replace a local operator inside multi-local operator";
replaceInMultiOpAtPosition[multiOp_/;MultiOptest[multiOp], position_, toApply_]:= Module[{multiOpList = List @@ multiOp},
MultiOp @@ ReplacePart[multiOpList, position -> toApply[multiOpList[[position]]]]];

(*Multilinearity in multi-local operators of the replacement*)
replaceInMultiOpAtPosition[a_+b_, position_, toReplace_]:= replaceInMultiOpAtPosition[a,position,toReplace] + replaceInMultiOpAtPosition[b, position, toReplace];
replaceInMultiOpAtPosition[a_ b_, position_, toReplace_]:= a replaceInMultiOpAtPosition[b, position, toReplace]/;(Head[b] == MultiOp)


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
