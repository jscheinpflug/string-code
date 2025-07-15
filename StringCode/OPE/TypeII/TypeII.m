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
(*Define OPE with Profiles*)


isProfile[expr_] := MatchQ[expr, R[__]] && MemberQ[List @@ expr, _ProfileX];


extractProfileData[ProfileX[profile_, degree_, z_,zbar_]]:= {profile,degree,z,zbar};


createDerivativeIndicesAndXs[degree_, z_, zbar_]:= 
Module[{derivativeIndices = {}, Xs = {}}, Table[Module[{\[Mu]}, AppendTo[derivativeIndices, \[Mu]]; AppendTo[Xs, X[\[Mu],z,zbar]]], {i,1,degree}]; {derivativeIndices, Xs}];


OPEWithReplacedProfileX[toOPE__]:= Module[{prefac = 1, profileName, derivativeIndices, Xs, degree,z,zbar,normalOrderingListed = {}, replacedNormalOrderedList = {}, resultingToOPE = {}},
 Scan[
    Function[normalOrderedProduct,
      If[isProfile[normalOrderedProduct],
        (
          normalOrderingListed = List @@ normalOrderedProduct;
          Scan[Function[profile,
          If[MatchQ[profile,_ProfileX],
          (
          {profileName, degree, z, zbar} = extractProfileData[profile];
          {derivativeIndices, Xs} = createDerivativeIndicesAndXs[degree, z, zbar];
          prefac = prefac *  1/Factorial[degree] * profileName[derivativeIndices];
          replacedNormalOrderedList = Join[replacedNormalOrderedList, Xs];
          ),
          AppendTo[replacedNormalOrderedList, profile];
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
((prefac OPE @@ resultingToOPE)//Expand)]


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
