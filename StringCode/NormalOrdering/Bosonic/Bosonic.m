(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`NormalOrdering`Bosonic`"];


Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`Bosonic`"];
Needs["StringCode`NormalOrdering`"]


(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


replaceProfilesWithExpAndCollectProfilesInR::usage = "Replaces all profiles with exponentials and collects profiles in a normal ordered product";
replaceProfilesWithExpAndCollectProfilesInListOfR::usage = "Replaces all profiles with exponentials and collects profiles in a list of normal ordered products";
countDerivativesInR::usage = "Counts total number of spacetime derivatives in normal ordered product";
countDerivativesInListOfR::usage = "Counts total number of spacetime derivatives in a list of normal ordered products";
replaceProductWithMomentumByDerivativeRule::usage = "Defines a rule that replaces products of profiles with momenta by the appropriate derivatives";
cleanIntermediateExp::usage = "Replaces exponentials with dummy momenta by one";
cleanIntermediateMomenta::usage = "Erases dummy momenta attached to ProfileX";


(* ::Subsection:: *)
(*Define utilities for ProfileX*)


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
] /; MatchQ[expr, Times[__Symbol | Power[__], __]];

cleanIntermediateExp =
  expX[s_Symbol, w_, wbar_] /;
    StringMatchQ[SymbolName[s], "kdummy$" ~~ __] :> 1;

cleanIntermediateMomenta =
  ProfileX[profile_, ders_List, z_, zbar_, k_Symbol] /;
    StringMatchQ[SymbolName[k], "kdummy$" ~~ __] :>
   ProfileX[profile, ders, z, zbar];   

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
