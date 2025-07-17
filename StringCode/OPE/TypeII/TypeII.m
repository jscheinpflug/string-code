(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`OPE`TypeII`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`TypeII`"];
Needs["StringCode`Wick`"];
Needs["StringCode`Wick`TypeII`"];
Needs["StringCode`OPE`"];


(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Define OPE with ProfileX*)


extractKDummyExponentials[expr_]:=
  Cases[expr, 
    Power[_, exp_] /; 
      !FreeQ[exp, 
        dot[lhs_, rhs_] /; 
          (StringContainsQ[ToString[lhs], "kdummy$"] && 
          StringContainsQ[ToString[rhs], "kdummy$"])
      ]
  ]
  
replaceExpWickByOne = 
   { Power[_, exp_] /; 
      !FreeQ[exp, 
        dot[lhs_, rhs_] /; 
          (StringContainsQ[ToString[lhs], "kdummy$"] && 
          StringContainsQ[ToString[rhs], "kdummy$"])
      ] -> 1 };
    
  
expandExponentialAtOrder[base_^(a___ dot[k1_, k2_]), ord_] := Module[{i},(a Log[base])^ord/Factorial[ord] Product[Module[{\[Mu]}, k1[\[Mu]] k2[\[Mu]]], {i, 1, ord}]]
  
replaceExpWithExpansions[expr_, exponentials_, replacementList_]:= Module[{replacementRule = {}, i},
replacementRule = Table[exponentials[[i]] -> replacementList[[i]], {i,1,Length[exponentials]}];
expr/.replacementRule
]  
  
getPartitionsAtOrder[ord_, lengthInto_]:= 
DeleteDuplicates@Flatten[Permutations/@(Select[IntegerPartitions[ord,{lengthInto},Range[0,ord]],Length[#]==lengthInto&]),1];  
  
expandExponentials[expr_, maxExpansionOrder_]:= Module[{result = 0, partitions,expLength, exponentials, i = 1},
exponentials = extractKDummyExponentials[expr];
expLength = Length[exponentials];
partitions = Flatten[Table[getPartitionsAtOrder[i, expLength], {i,1,maxExpansionOrder}],1];
Scan[Function[partition, 
result = result + replaceExpWithExpansions[expr, exponentials, Table[expandExponentialAtOrder[exponentials[[i]], partition[[i]]], {i,1, Length[partition]}]];
], partitions];
result]  
   
OPEWithProfileX[toOPE__, \[Alpha]pOrder_] :=
 Module[{resultingToOPE = {}, replacedAndProfiles, performedOPE, performedOPEList, derivativeOrder, expMaxExpansionOrder, expandedOPEPieces = {}, allProfiles = {}},
   {resultingToOPE, allProfiles} = replaceProfilesWithExpAndCollectProfilesInListOfR[{toOPE}];
   performedOPE = ((OPE @@ resultingToOPE) // Expand) /. {R[a__] :> R @@ Join[Flatten[allProfiles], {a}]};
   performedOPEList = If[(Head[performedOPE] === Times || Head[performedOPE] === R), List[performedOPE],List @@ performedOPE];
   Scan[Function[OPEpiece,
     derivativeOrder = Exponent[OPEpiece, \[Alpha]p];
     If[derivativeOrder < \[Alpha]pOrder,
      expMaxExpansionOrder = Floor[(\[Alpha]pOrder - derivativeOrder)/2];
      If[expMaxExpansionOrder > 0,
       AppendTo[expandedOPEPieces, expandExponentials[OPEpiece, expMaxExpansionOrder]]
       ];
      AppendTo[expandedOPEPieces, OPEpiece /. replaceExpWickByOne],
      If[derivativeOrder == \[Alpha]pOrder, AppendTo[expandedOPEPieces, OPEpiece /. replaceExpWickByOne]]];
     ], performedOPEList];
  (Plus @@ expandedOPEPieces)
    /. replaceProductWithMomentumByDerivativeRule /. {cleanIntermediateExp, cleanIntermediateMomenta}]


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
