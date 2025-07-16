(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`NormalOrdering`Bosonic`"];


Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`Bosonic`"];
Needs["StringCode`NormalOrdering`"]


(* ::Section:: *)
(*Declare public variables and methods*)


replaceProfilesWithExpAndCollectProfilesInR::usage = "Replaces all profiles with exponentials and collects profiles in a normal ordered product";
replaceProfilesWithExpAndCollectProfilesInListOfR::usage = "Replaces all profiles with exponentials and collects profiles in a list of normal ordered products";
countDerivativesInR::usage = "Counts total number of spacetime derivatives in normal ordered product";
countDerivativesInListOfR::usage = "Counts total number of spacetime derivatives in a list of normal ordered products";


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Define utilities for ProfileX*)


RcontainsProfile[expr_] := MatchQ[expr, R[__]] && MemberQ[List @@ expr, _ProfileX];

createProfileExp[ProfileX[profile_,ders_List,z_,zbar_],momentum_]:= expX[momentum,z,zbar];

appendMomentumToProfile[ProfileX[profile_,ders_List,z_,zbar_],momentum_]:= ProfileX[profile, ders, z, zbar, momentum];

replaceProfilesWithExpAndCollectProfilesInR[Ra_/;Rtest[Ra]]:= Module[{normalOrderingListed = {}, replacedNormalOrderedList = {}, profiles = {}, uniqueK},
          normalOrderingListed = List @@ Ra;
          Scan[Function[Relem,
          If[MatchQ[Relem,_ProfileX],
          (
          uniqueK = Module[{kdummy},kdummy];
          AppendTo[profiles, appendMomentumToProfile[Relem, uniqueK]];
          AppendTo[replacedNormalOrderedList, createProfileExp[Relem, uniqueK]]
          ),
          AppendTo[replacedNormalOrderedList, Relem];
          ];
          ], normalOrderingListed];
          {R @@ replacedNormalOrderedList, profiles}
]; 
replaceProfilesWithExpAndCollectProfilesInR[a_ b_]:=a replaceProfilesWithExpAndCollectProfilesInR[b]/;(And @@(FreeQ[a,#]&/@ allfields))

replaceProfilesWithExpAndCollectProfilesInListOfR[RList_]:= Module[{replacedAndProfiles = {}, replacedList = {}, allProfiles = {}},
          Scan[Function[Ra, 
          replacedAndProfiles = replaceProfilesWithExpAndCollectProfilesInR[Ra];  
          AppendTo[replacedList, replacedAndProfiles[[1]]];
          AppendTo[allProfiles, replacedAndProfiles[[2]]];
          ], RList];
          {replacedList, allProfiles}
]; 

extractDerivativeOrder[ProfileX[profile_,ders_List,z_,zbar_]]:= Length[ders];

countDerivativesInR[Ra_/;Rtest[Ra]]:= Module[{RList = List @@ Ra, derivativeOrder = 0}, 
Scan[Function[Relem,  If[Head[Relem] == ProfileX, derivativeOrder = derivativeOrder + extractDerivativeOrder[Relem]], RList]];
derivativeOrder];

countDerivativesInListOfR[listOfR_]:= Module[{derivativeOrder = 0},
Scan[Function[listElem, derivativeOrder = derivativeOrder + countDerivativesInR[listElem];], listOfR];
derivativeOrder];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
