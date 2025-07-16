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


replaceProductWithMomentumByDerivativeRule = Times[dummyMomentum_[index_],Ra_R] :> 
(Ra /. ProfileX[pol_, args_, z___, profileDummyMomentum_Symbol] /; profileDummyMomentum === dummyMomentum
 :> ProfileX[pol, Append[args, index], z, profileDummyMomentum]
);

cleanIntermediateExp =
  expX[s_Symbol, w_, wbar_] /;
    StringMatchQ[SymbolName[s], "kdummy$" ~~ __] :> 1;

cleanIntermediateMomenta =
  ProfileX[profile_, ders_List, z_, zbar_, k_Symbol] /;
    StringMatchQ[SymbolName[k], "kdummy$" ~~ __] :>
   ProfileX[profile, ders, z, zbar];   
   
OPEWithReplacedProfileX[toOPE__, maxDerivativeOrder_]:= Module[{resultingToOPE = {}, replacedAndProfiles, allProfiles = {}},
 {resultingToOPE, allProfiles} = replaceProfilesWithExpAndCollectProfilesInListOfR[{toOPE}];
((OPE @@ resultingToOPE)//Expand)/.{R[a__]:> R @@ Join[Flatten[allProfiles], {a}]}
//.replaceProductWithMomentumByDerivativeRule/.{cleanIntermediateExp, cleanIntermediateMomenta}]


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
