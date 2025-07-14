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
(*Define OPE with Profiles*)


isProfile[expr_] := MatchQ[expr, R[__]] && MemberQ[List @@ expr, _ProfileX]


createProfileExp[ProfileX[polX_,degree_, ders_List,z_,zbar_],momentum_]:= expX[momentum,z,zbar]


extractProfile[ProfileX[polX_,degree_, ders_List,z_,zbar_],momentum_]:= ProfileX[polX,degree, ders,momentum]


replaceProductWithMomentumByDerivativeRule = 
{Times[p_Symbol[args___],ProfileX[pol_,degree_, polargs_,p_]]:>
If[degree > Length[polargs],-I ProfileX[pol,degree,Append[polargs,args],p],0]}


OPEWithReplacedProfileX[toOPE__]:= Module[{prefac = 1, normalOrderingListed = {}, replacedNormalOrderedList = {}, resultingToOPE = {}, uniqueK=0},
 Scan[
    Function[normalOrderedProduct,
      If[isProfile[normalOrderedProduct],
        (
          normalOrderingListed = List @@ normalOrderedProduct;
          Scan[Function[arg,
          If[MatchQ[arg,_ProfileX],
          (
          uniqueK = Module[{k},k];
          prefac = prefac * extractProfile[arg, uniqueK];
          AppendTo[replacedNormalOrderedList, createProfileExp[arg, uniqueK]]
          ),
          AppendTo[replacedNormalOrderedList, arg];
          ];
          ], normalOrderingListed];
          AppendTo[resultingToOPE, R @@ replacedNormalOrderedList];
          replacedNormalOrderedList = {};
          normalOrderingListed = {};
        ),
        AppendTo[resultingToOPE, normalOrderedProduct]
      ];
    ],
    {toOPE}
  ];
((prefac OPE @@ resultingToOPE)//Expand)//.replaceProductWithMomentumByDerivativeRule]


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
