(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`NormalOrdering`TypeII`"];


Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];
Needs["StringCode`NormalOrdering`"]


(* ::Section:: *)
(*Declare public variables and methods*)


exp\[Phi]parity::usage = "Define Grassmann parity for holomorphic exponentials of \[Phi]";
exp\[Phi]tparity::usage = "Define Grassmann parity for antiholomorphic exponentials of \[Phi]";
replaceProfilesWithExpAndCollectProfilesInR::usage = "Replaces all profiles with exponentials and collects profiles in a normal ordered product";
replaceProfilesWithExpAndCollectProfilesInListOfR::usage = "Replaces all profiles with exponentials and collects profiles in a list of normal ordered products";
countDerivativesInR::usage = "Counts total number of spacetime derivatives in normal ordered product";
countDerivativesInListOfR::usage = "Counts total number of spacetime derivatives in a list of normal ordered products";


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection::Closed:: *)
(*Define Grassmann parity*)


regcomm[f_,g_]:=(-1)^(parity[f] parity[g])(-1)^(exp\[Phi]parity[f] exp\[Phi]parity[g])(-1)^(exp\[Phi]tparity[f] exp\[Phi]tparity[g])


exp\[Phi]parity[f_]:=0/;(And @@(FreeQ[f,#]&/@ exp\[Phi]fermions))
exp\[Phi]parity[f_]:=1/;(!(And @@(FreeQ[f,#]&/@ exp\[Phi]fermions)))
exp\[Phi]parity[R[f__,g__]]:=Mod[exp\[Phi]parity[R[f]]+exp\[Phi]parity[R[g]],2]
exp\[Phi]parity[R[f_]]:=exp\[Phi]parity[f]


exp\[Phi]tparity[f_]:=0/;(And @@(FreeQ[f,#]&/@ exp\[Phi]tfermions))
exp\[Phi]tparity[f_]:=1/;(!(And @@(FreeQ[f,#]&/@ exp\[Phi]tfermions)))
exp\[Phi]tparity[R[f__,g__]]:=Mod[exp\[Phi]tparity[R[f]]+exp\[Phi]tparity[R[g]],2]
exp\[Phi]tparity[R[f_]]:=exp\[Phi]tparity[f]


(* ::Subsection::Closed:: *)
(*Define normal-ordered product*)


R[ c___,a_,a_,d___]:=R[c,exp\[Phi]b[2a[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]f)
R[ c___,a_,a_,d___]:=R[c,exp\[Phi]tb[2a[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]tf)
R[ c___,a_,b_,d___]:=R[c,exp\[Phi]b[a[[1]]+b[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]b && Head[b]==exp\[Phi]b && a[[2]]==b[[2]])
R[ c___,a_,b_,d___]:=R[c,exp\[Phi]tb[a[[1]]+b[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]tb && Head[b]==exp\[Phi]tb && a[[2]]==b[[2]])
R[ c___,a_,b_,d___]:=R[c,exp\[Phi]b[a[[1]]+b[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]f && Head[b]==exp\[Phi]f && a[[2]]==b[[2]])
R[ c___,a_,b_,d___]:=R[c,exp\[Phi]tb[a[[1]]+b[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]tf && Head[b]==exp\[Phi]tf && a[[2]]==b[[2]])
R[ c___,a_,b_,d___]:=R[c,exp\[Phi]f[a[[1]]+b[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]b && Head[b]==exp\[Phi]f && a[[2]]==b[[2]])
R[ c___,a_,b_,d___]:=R[c,exp\[Phi]tf[a[[1]]+b[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]tb && Head[b]==exp\[Phi]tf && a[[2]]==b[[2]])


(* ::Subsection::Closed:: *)
(*Define CR*)


CR[ c___,a_,a_,d___]:=CR[c,exp\[Phi]b[2a[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]f)
CR[ c___,a_,a_,d___]:=CR[c,exp\[Phi]tb[2a[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]tf)
CR[ c___,a_,b_,d___]:=CR[c,exp\[Phi]b[a[[1]]+b[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]f && Head[b]==exp\[Phi]f && a[[2]]==b[[2]])
CR[ c___,a_,b_,d___]:=CR[c,exp\[Phi]tb[a[[1]]+b[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]tf && Head[b]==exp\[Phi]tf && a[[2]]==b[[2]])
CR[ c___,a_,b_,d___]:=CR[c,exp\[Phi]f[a[[1]]+b[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]b && Head[b]==exp\[Phi]f && a[[2]]==b[[2]])
CR[ c___,a_,b_,d___]:=CR[c,exp\[Phi]tf[a[[1]]+b[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]tb && Head[b]==exp\[Phi]tf && a[[2]]==b[[2]])


(* ::Subsection:: *)
(*Define utilities for ProfileX*)


containsProfile[expr_] := MatchQ[expr, R[__]] && MemberQ[List @@ expr, _ProfileX];

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
