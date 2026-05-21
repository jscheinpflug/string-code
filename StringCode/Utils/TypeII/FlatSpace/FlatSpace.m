(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Utils`TypeII`FlatSpace`"];
Needs["StringCode`Utils`"];
Needs["StringCode`Utils`TypeII`"];
Needs["StringCode`Symbols`TypeII`FlatSpace`"];


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


ContractDelta[expr_] := expr //. {
  g_ \[Delta][\[Mu]_, \[Mu]1_] :> (g /. {\[Mu] -> \[Mu]1}) /; !FreeQ[g, \[Mu]],
  g_ \[Delta][\[Mu]1_, \[Mu]_] :> (g /. {\[Mu] -> \[Mu]1}) /; !FreeQ[g, \[Mu]]
};


coefficientCarrierFieldQ0[field_] := MemberQ[
  {ProfileX, ProfileXHolo, ProfileXAntiHolo, expX, expXHolo, expXAntiHolo},
  Head[field]
];


matchingProfileDerivativeAppendList0::usage =
  "matchingProfileDerivativeAppendList0[derExpr, field] returns the derivative-list suffix that one TypeII FlatSpace profile field can absorb.";
matchingProfileDerivativeAppendList0[derExpr_, ProfileX[profile_, ders_List, _, _]] :=
  matchingProfileDerivativeAppendListFromData0[derExpr, profile, ders];
matchingProfileDerivativeAppendList0[derExpr_, ProfileXHolo[profile_, ders_List, _]] :=
  matchingProfileDerivativeAppendListFromData0[derExpr, profile, ders];
matchingProfileDerivativeAppendList0[derExpr_, ProfileXAntiHolo[profile_, ders_List, _]] :=
  matchingProfileDerivativeAppendListFromData0[derExpr, profile, ders];


appendProfileDerivativeIndices0::usage =
  "appendProfileDerivativeIndices0[field, indices] appends absorbed derivative indices to one TypeII FlatSpace profile field.";
appendProfileDerivativeIndices0[ProfileX[profile_, ders_List, z_, zb_], indices_List] :=
  ProfileX[profile, Join[ders, indices], z, zb];
appendProfileDerivativeIndices0[ProfileXHolo[profile_, ders_List, z_], indices_List] :=
  ProfileXHolo[profile, Join[ders, indices], z];
appendProfileDerivativeIndices0[ProfileXAntiHolo[profile_, ders_List, zb_], indices_List] :=
  ProfileXAntiHolo[profile, Join[ders, indices], zb];


flatSpaceProfileArgumentSymbols0::usage =
  "flatSpaceProfileArgumentSymbols0[profile] extracts renamable non-head symbols from the profile tensor/function arguments carried by ProfileX-like fields.";
flatSpaceProfileArgumentSymbols0[profile_] := If[
  AtomQ[profile],
  {},
  Cases[List @@ profile, sym_Symbol :> sym, Infinity, Heads -> False]
];


flatSpaceProfileDerivativeSymbols0::usage =
  "flatSpaceProfileDerivativeSymbols0[field] extracts derivative-list symbols carried by one TypeII FlatSpace profile field.";
flatSpaceProfileDerivativeSymbols0[ProfileX[_, ders_List, _, _]] := Cases[ders, sym_Symbol :> sym, Infinity];
flatSpaceProfileDerivativeSymbols0[ProfileXHolo[_, ders_List, _]] := Cases[ders, sym_Symbol :> sym, Infinity];
flatSpaceProfileDerivativeSymbols0[ProfileXAntiHolo[_, ders_List, _]] := Cases[ders, sym_Symbol :> sym, Infinity];
flatSpaceProfileDerivativeSymbols0[_] := {};


flatSpaceModeSymbols0::usage =
  "flatSpaceModeSymbols0[modes] extracts renamable mode-label symbols from TypeII spin-field mode tuples.";
flatSpaceModeSymbols0[modes_List] := Flatten @ Replace[
  modes,
  {
    {sym_Symbol, _} :> {sym},
    {_, sym_Symbol} :> {sym},
    _ :> {}
  },
  {1}
];


flatSpaceDummyIndexData0::usage =
  "flatSpaceDummyIndexData0[sym, class] builds one typed dummy-index record for TypeII FlatSpace canonicalization.";
flatSpaceDummyIndexData0[sym_Symbol, class_] := <|"Symbol" -> sym, "Class" -> class|>;


flatSpaceSpinorClass0::usage =
  "flatSpaceSpinorClass0[chirality] returns the canonical dummy-index class for one TypeII spinor chirality label.";
flatSpaceSpinorClass0["chiral"] := "SpinorChiral";
flatSpaceSpinorClass0["antichiral"] := "SpinorAntiChiral";
flatSpaceSpinorClass0[_] := "SpinorChiral";


flatSpaceGammaVectorLinkQ0::usage =
  "flatSpaceGammaVectorLinkQ0[link] is True when link is one explicit GammaUDHold or GammaDUHold vector link.";
flatSpaceGammaVectorLinkQ0[link_] := MatchQ[link, GammaUDHold[_] | GammaDUHold[_]];


flatSpaceToggleSpinorChirality0::usage =
  "flatSpaceToggleSpinorChirality0[chirality] toggles between chiral and antichiral labels.";
flatSpaceToggleSpinorChirality0["chiral"] := "antichiral";
flatSpaceToggleSpinorChirality0["antichiral"] := "chiral";
flatSpaceToggleSpinorChirality0[other_] := other;


flatSpaceGammaSpinorChiralities0::usage =
  "flatSpaceGammaSpinorChiralities0[links] infers the endpoint chirality labels carried by one GammaAntisymmetricProductHold link list.";
flatSpaceGammaSpinorChiralities0[links_List] := Module[{cTag, coreLinks, vectorLinks, tailLinks, left},
  cTag = If[links =!= {} && MatchQ[First[links], CUDHold | CDUHold], First[links], None];
  coreLinks = If[cTag === None, links, Rest[links]];
  vectorLinks = Select[coreLinks, flatSpaceGammaVectorLinkQ0];
  tailLinks = Select[coreLinks, !flatSpaceGammaVectorLinkQ0[#] &];
  If[cTag === CUDHold,
    Return[{"chiral", Nest[flatSpaceToggleSpinorChirality0, "antichiral", Length[vectorLinks]]}]
  ];
  If[cTag === CDUHold,
    Return[{"antichiral", Nest[flatSpaceToggleSpinorChirality0, "chiral", Length[vectorLinks]]}]
  ];
  If[vectorLinks === {} && tailLinks =!= {} && AllTrue[tailLinks, # === Gamma11UUHold[] &], Return[{"chiral", "chiral"}]];
  If[vectorLinks === {} && tailLinks =!= {} && AllTrue[tailLinks, # === Gamma11DDHold[] &], Return[{"antichiral", "antichiral"}]];
  If[vectorLinks === {}, Return[{"chiral", "antichiral"}]];
  left = Which[
    Head[First[vectorLinks]] === GammaUDHold, "chiral",
    Head[First[vectorLinks]] === GammaDUHold, "antichiral",
    True, "chiral"
  ];
  {left, Nest[flatSpaceToggleSpinorChirality0, left, Length[vectorLinks]]}
];


flatSpaceGammaFactorSpinorEndpointData0::usage =
  "flatSpaceGammaFactorSpinorEndpointData0[factor] extracts typed spinor endpoint records from one GammaAntisymmetricProductHold factor.";
flatSpaceGammaFactorSpinorEndpointData0[GammaAntisymmetricProductHold[links_List, s1_, s2_]] := Module[{pair},
  pair = flatSpaceGammaSpinorChiralities0[links];
  Join[
    Cases[{s1}, sym_Symbol :> flatSpaceDummyIndexData0[sym, flatSpaceSpinorClass0[pair[[1]]]]],
    Cases[{s2}, sym_Symbol :> flatSpaceDummyIndexData0[sym, flatSpaceSpinorClass0[pair[[2]]]]]
  ]
];
flatSpaceGammaFactorSpinorEndpointData0[_] := {};


flatSpaceGammaFactorVectorData0::usage =
  "flatSpaceGammaFactorVectorData0[factor] extracts typed vector-index records from one GammaAntisymmetricProductHold factor.";
flatSpaceGammaFactorVectorData0[GammaAntisymmetricProductHold[links_List, _, _]] :=
  (flatSpaceDummyIndexData0[#, "Vector"] &) /@ Cases[links, GammaUDHold[idx_Symbol] | GammaDUHold[idx_Symbol] :> idx, {1}];
flatSpaceGammaFactorVectorData0[_] := {};


flatSpaceGammaSpinorEndpointData0::usage =
  "flatSpaceGammaSpinorEndpointData0[expr] extracts typed gamma spinor endpoint records from expr.";
flatSpaceGammaSpinorEndpointData0[expr_] := Flatten @ Cases[
  expr,
  factor_GammaAntisymmetricProductHold :> flatSpaceGammaFactorSpinorEndpointData0[factor],
  Infinity
];


flatSpaceGammaVectorData0::usage =
  "flatSpaceGammaVectorData0[expr] extracts typed gamma vector-link records from expr.";
flatSpaceGammaVectorData0[expr_] := Flatten @ Cases[
  expr,
  factor_GammaAntisymmetricProductHold :> flatSpaceGammaFactorVectorData0[factor],
  Infinity
];


flatSpaceVectorNonGammaCandidateSymbols0::usage =
  "flatSpaceVectorNonGammaCandidateSymbols0[expr] extracts vector symbols that are dummy candidates outside gamma-link slots.";
flatSpaceVectorNonGammaCandidateSymbols0[expr_] := DeleteDuplicates @ Join[
  Flatten @ Cases[
    expr,
    derExpr_?derivativeApplicationQ0 :> Cases[Last[extractDerivativeBaseAndIndices0[derExpr]], sym_Symbol :> sym, Infinity],
    Infinity
  ],
  Flatten @ Cases[
    expr,
    field_ :> flatSpaceProfileDerivativeSymbols0[field],
    Infinity
  ],
  Flatten @ Cases[
    expr,
    \[Delta][lhs_Symbol, rhs_Symbol] :> {lhs, rhs},
    Infinity
  ]
];


flatSpaceProtectedFieldData0::usage =
  "flatSpaceProtectedFieldData0[field] extracts typed non-dummy TypeII FlatSpace symbols that must stay fixed during dummy-index canonicalization.";
flatSpaceProtectedFieldData0[dX[idx_Symbol, _, _]] := {flatSpaceDummyIndexData0[idx, "Vector"]};
flatSpaceProtectedFieldData0[dXt[idx_Symbol, _, _]] := {flatSpaceDummyIndexData0[idx, "Vector"]};
flatSpaceProtectedFieldData0[\[Psi][idx_Symbol, _, _]] := {flatSpaceDummyIndexData0[idx, "Vector"]};
flatSpaceProtectedFieldData0[\[Psi]t[idx_Symbol, _, _]] := {flatSpaceDummyIndexData0[idx, "Vector"]};
flatSpaceProtectedFieldData0[ProfileX[profile_, _, _, _]] := (flatSpaceDummyIndexData0[#, "Vector"] &) /@ flatSpaceProfileArgumentSymbols0[profile];
flatSpaceProtectedFieldData0[ProfileXHolo[profile_, _, _]] := (flatSpaceDummyIndexData0[#, "Vector"] &) /@ flatSpaceProfileArgumentSymbols0[profile];
flatSpaceProtectedFieldData0[ProfileXAntiHolo[profile_, _, _]] := (flatSpaceDummyIndexData0[#, "Vector"] &) /@ flatSpaceProfileArgumentSymbols0[profile];
flatSpaceProtectedFieldData0[S[{alpha_Symbol, chirality_}, _, modes_List, _, _]] := Join[
  {flatSpaceDummyIndexData0[alpha, flatSpaceSpinorClass0[chirality]]},
  (flatSpaceDummyIndexData0[#, "Vector"] &) /@ flatSpaceModeSymbols0[modes]
];
flatSpaceProtectedFieldData0[St[{alpha_Symbol, chirality_}, _, modes_List, _, _]] := Join[
  {flatSpaceDummyIndexData0[alpha, flatSpaceSpinorClass0[chirality]]},
  (flatSpaceDummyIndexData0[#, "Vector"] &) /@ flatSpaceModeSymbols0[modes]
];
flatSpaceProtectedFieldData0[_] := {};


flatSpaceProtectedFieldSymbols0::usage =
  "flatSpaceProtectedFieldSymbols0[field] extracts non-dummy TypeII FlatSpace symbols that must stay fixed during dummy-index canonicalization.";
flatSpaceProtectedFieldSymbols0[dX[idx_Symbol, _, _]] := {idx};
flatSpaceProtectedFieldSymbols0[dXt[idx_Symbol, _, _]] := {idx};
flatSpaceProtectedFieldSymbols0[\[Psi][idx_Symbol, _, _]] := {idx};
flatSpaceProtectedFieldSymbols0[\[Psi]t[idx_Symbol, _, _]] := {idx};
flatSpaceProtectedFieldSymbols0[ProfileX[profile_, _, _, _]] := flatSpaceProfileArgumentSymbols0[profile];
flatSpaceProtectedFieldSymbols0[ProfileXHolo[profile_, _, _]] := flatSpaceProfileArgumentSymbols0[profile];
flatSpaceProtectedFieldSymbols0[ProfileXAntiHolo[profile_, _, _]] := flatSpaceProfileArgumentSymbols0[profile];
flatSpaceProtectedFieldSymbols0[S[{alpha_Symbol, _}, _, modes_List, _, _]] := Join[{alpha}, flatSpaceModeSymbols0[modes]];
flatSpaceProtectedFieldSymbols0[St[{alpha_Symbol, _}, _, modes_List, _, _]] := Join[{alpha}, flatSpaceModeSymbols0[modes]];
flatSpaceProtectedFieldSymbols0[_] := {};


flatSpaceSingletonGammaSpinorProtectedData0::usage =
  "flatSpaceSingletonGammaSpinorProtectedData0[expr] returns gamma spinor endpoint records that occur exactly once and are therefore treated as external/protected.";
flatSpaceSingletonGammaSpinorProtectedData0[expr_] := Module[{endpointData, counts},
  endpointData = flatSpaceGammaSpinorEndpointData0[expr];
  counts = CountsBy[endpointData, dummyIndexDataKey0];
  Select[
    DeleteDuplicatesBy[endpointData, dummyIndexDataKey0],
    counts[dummyIndexDataKey0[#]] === 1 &
  ]
];


flatSpaceSingletonGammaVectorProtectedData0::usage =
  "flatSpaceSingletonGammaVectorProtectedData0[expr] returns gamma vector-link records that occur only once and have no non-gamma dummy-support occurrence.";
flatSpaceSingletonGammaVectorProtectedData0[expr_] := Module[{vectorData, counts, nonGammaSupportSymbols},
  vectorData = flatSpaceGammaVectorData0[expr];
  counts = CountsBy[vectorData, dummyIndexDataKey0];
  nonGammaSupportSymbols = flatSpaceVectorNonGammaCandidateSymbols0[expr];
  Select[
    DeleteDuplicatesBy[vectorData, dummyIndexDataKey0],
    counts[dummyIndexDataKey0[#]] === 1 && !MemberQ[nonGammaSupportSymbols, #["Symbol"]] &
  ]
];


dummyIndexCandidateData0::usage =
  "dummyIndexCandidateData0[expr] returns typed TypeII FlatSpace dummy-index candidates across profile derivatives, gamma vector links, and gamma spinor contractions.";
dummyIndexCandidateData0[expr_] := DeleteDuplicatesBy[
  Join[
    (flatSpaceDummyIndexData0[#, "Vector"] &) /@ flatSpaceVectorNonGammaCandidateSymbols0[expr],
    flatSpaceGammaVectorData0[expr],
    flatSpaceGammaSpinorEndpointData0[expr]
  ],
  dummyIndexDataKey0
];


dummyIndexProtectedData0::usage =
  "dummyIndexProtectedData0[expr] returns typed TypeII FlatSpace protected/free indices that must stay fixed during dummy-index canonicalization.";
dummyIndexProtectedData0[expr_] := DeleteDuplicatesBy[
  Join[
    Flatten @ Cases[expr, field_ :> flatSpaceProtectedFieldData0[field], Infinity],
    flatSpaceSingletonGammaSpinorProtectedData0[expr],
    flatSpaceSingletonGammaVectorProtectedData0[expr]
  ],
  dummyIndexDataKey0
];


dummyIndexCandidateSymbols0::usage =
  "dummyIndexCandidateSymbols0[expr] returns TypeII FlatSpace dummy-index candidates from derivative factors and ProfileX derivative lists.";
dummyIndexCandidateSymbols0[expr_] := dummyIndexCandidateData0[expr][[All, "Symbol"]];


dummyIndexProtectedSymbols0::usage =
  "dummyIndexProtectedSymbols0[expr] returns TypeII FlatSpace non-dummy symbols that must not be renamed during dummy-index canonicalization.";
dummyIndexProtectedSymbols0[expr_] := dummyIndexProtectedData0[expr][[All, "Symbol"]];


canonicalDummyIndexStem0::usage =
  "canonicalDummyIndexStem0[class, expr] returns the canonical stem used for one TypeII FlatSpace dummy-index class.";
canonicalDummyIndexStem0["Vector", _] := "\[Mu]";
canonicalDummyIndexStem0["SpinorChiral", _] := "\[Alpha]";
canonicalDummyIndexStem0["SpinorAntiChiral", _] := "\[Alpha]";


flatSpaceRenamableFieldSymbols0::usage =
  "flatSpaceRenamableFieldSymbols0[field] extracts the renamable symbols contributed by one TypeII FlatSpace field occurrence.";
flatSpaceRenamableFieldSymbols0[dX[idx_Symbol, _, _]] := {idx};
flatSpaceRenamableFieldSymbols0[dXt[idx_Symbol, _, _]] := {idx};
flatSpaceRenamableFieldSymbols0[\[Psi][idx_Symbol, _, _]] := {idx};
flatSpaceRenamableFieldSymbols0[\[Psi]t[idx_Symbol, _, _]] := {idx};
flatSpaceRenamableFieldSymbols0[ProfileX[profile_, ders_List, _, _]] := Join[
  flatSpaceProfileArgumentSymbols0[profile],
  Cases[ders, sym_Symbol :> sym, Infinity]
];
flatSpaceRenamableFieldSymbols0[ProfileXHolo[profile_, ders_List, _]] := Join[
  flatSpaceProfileArgumentSymbols0[profile],
  Cases[ders, sym_Symbol :> sym, Infinity]
];
flatSpaceRenamableFieldSymbols0[ProfileXAntiHolo[profile_, ders_List, _]] := Join[
  flatSpaceProfileArgumentSymbols0[profile],
  Cases[ders, sym_Symbol :> sym, Infinity]
];
flatSpaceRenamableFieldSymbols0[S[{alpha_Symbol, _}, _, modes_List, _, _]] := Join[{alpha}, flatSpaceModeSymbols0[modes]];
flatSpaceRenamableFieldSymbols0[St[{alpha_Symbol, _}, _, modes_List, _, _]] := Join[{alpha}, flatSpaceModeSymbols0[modes]];
flatSpaceRenamableFieldSymbols0[_] := {};


renamableOperatorSymbols0::usage =
  "renamableOperatorSymbols0[expr] lists TypeII FlatSpace vector, spinor, profile, and mode-index symbols that may be renamed during operator matching.";
renamableOperatorSymbols0[expr_] := DeleteDuplicates @ Flatten @ Cases[
  expr,
  field_ :> flatSpaceRenamableFieldSymbols0[field],
  Infinity
];


postProcessMatchedCoefficient0::usage =
  "postProcessMatchedCoefficient0[expr] expands and delta-contracts one TypeII FlatSpace extracted coefficient.";
postProcessMatchedCoefficient0[expr_] := Expand[ContractDelta[expr]];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
