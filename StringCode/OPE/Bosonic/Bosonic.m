(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`OPE`Bosonic`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`Bosonic`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`Bosonic`"];
Needs["StringCode`Wick`"];
Needs["StringCode`Wick`Bosonic`"];
Needs["StringCode`OPE`"];


(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*OPE with ProfileX*)


replaceProductWithMomentumByDerivativeRule := expr_ :> Module[
  {momenta, rest, result},

  momenta = Join[
    Cases[List @@ expr, s_Symbol[arg_] /; StringContainsQ[SymbolName[s], "kdummy$"]],
    Cases[List @@ expr, Power[s_Symbol[arg_], n_] /; StringContainsQ[SymbolName[s], "kdummy$"]]
  ];

  rest = Times @@ DeleteCases[List @@ expr, s_ /; MemberQ[momenta, s]];

  result = Fold[
    Function[{inRest, momentum},
      Module[{sym, index, power = 1},
        If[MatchQ[momentum, Power[_, _]],
          sym = Head[momentum[[1]]];
          index = momentum[[1, 1]];
          power = momentum[[2]],
          sym = Head[momentum];
          index = momentum[[1]]
        ];
        inRest /. ProfileX[pol_, args_, z___, profileSym_Symbol] /;
          profileSym === sym :>
          (-I)^power ProfileX[pol, Join[args, ConstantArray[index, power]], z, profileSym]
      ]
    ],
    rest,
    momenta
  ];

  result
] /; MatchQ[expr, Times[__Symbol | Power[__], __]]


cleanIntermediateExp =
  expX[s_Symbol, w_, wbar_] /;
    StringMatchQ[SymbolName[s], "kdummy$" ~~ __] :> 1;

cleanIntermediateMomenta =
  ProfileX[profile_, ders_List, z_, zbar_, k_Symbol] /;
    StringMatchQ[SymbolName[k], "kdummy$" ~~ __] :>
   ProfileX[profile, ders, z, zbar];   
   
countKDummy[expr_] := Count[expr, s_[__] /; StringContainsQ[SymbolName[s], "kdummy$"]];
  
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
   
OPEWithReplacedProfileX[toOPE__, maxDerivativeOrder_] :=
 Module[{resultingToOPE = {}, replacedAndProfiles, performedOPE, performedOPEList, derivativeOrder, expMaxExpansionOrder, expandedOPEPieces = {}, allProfiles = {}},
   {resultingToOPE, allProfiles} = replaceProfilesWithExpAndCollectProfilesInListOfR[{toOPE}];
   performedOPE = ((OPE @@ resultingToOPE) // Expand) /. {R[a__] :> R @@ Join[Flatten[allProfiles], {a}]};
   performedOPEList = If[Head[performedOPE] === Times, List[performedOPE],List @@ performedOPE];
   Scan[Function[OPEpiece,
     derivativeOrder = countKDummy[OPEpiece];
     If[derivativeOrder < maxDerivativeOrder,
      expMaxExpansionOrder = Floor[(maxDerivativeOrder - derivativeOrder)/2];
      If[expMaxExpansionOrder > 0,
       AppendTo[expandedOPEPieces, expandExponentials[OPEpiece, expMaxExpansionOrder]]
       ];
      AppendTo[expandedOPEPieces, OPEpiece /. replaceExpWickByOne],
      If[derivativeOrder == maxDerivativeOrder, AppendTo[expandedOPEPieces, OPEpiece /. replaceExpWickByOne]]];
     ], performedOPEList];
  (Plus @@ expandedOPEPieces)
    /. replaceProductWithMomentumByDerivativeRule /. {cleanIntermediateExp, cleanIntermediateMomenta}]


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
