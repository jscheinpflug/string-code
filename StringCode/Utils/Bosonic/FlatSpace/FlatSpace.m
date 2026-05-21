(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Utils`Bosonic`FlatSpace`"];
Needs["StringCode`Utils`"];
Needs["StringCode`Utils`Bosonic`"];
Needs["StringCode`Symbols`Bosonic`FlatSpace`"];


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
  "matchingProfileDerivativeAppendList0[derExpr, field] returns the derivative-list suffix that one bosonic FlatSpace profile field can absorb.";
matchingProfileDerivativeAppendList0[derExpr_, ProfileX[profile_, ders_List, _, _]] :=
  matchingProfileDerivativeAppendListFromData0[derExpr, profile, ders];
matchingProfileDerivativeAppendList0[derExpr_, ProfileXHolo[profile_, ders_List, _]] :=
  matchingProfileDerivativeAppendListFromData0[derExpr, profile, ders];
matchingProfileDerivativeAppendList0[derExpr_, ProfileXAntiHolo[profile_, ders_List, _]] :=
  matchingProfileDerivativeAppendListFromData0[derExpr, profile, ders];


appendProfileDerivativeIndices0::usage =
  "appendProfileDerivativeIndices0[field, indices] appends absorbed derivative indices to one bosonic FlatSpace profile field.";
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
  "flatSpaceProfileDerivativeSymbols0[field] extracts derivative-list symbols carried by one bosonic FlatSpace profile field.";
flatSpaceProfileDerivativeSymbols0[ProfileX[_, ders_List, _, _]] := Cases[ders, sym_Symbol :> sym, Infinity];
flatSpaceProfileDerivativeSymbols0[ProfileXHolo[_, ders_List, _]] := Cases[ders, sym_Symbol :> sym, Infinity];
flatSpaceProfileDerivativeSymbols0[ProfileXAntiHolo[_, ders_List, _]] := Cases[ders, sym_Symbol :> sym, Infinity];
flatSpaceProfileDerivativeSymbols0[_] := {};


flatSpaceProtectedFieldSymbols0::usage =
  "flatSpaceProtectedFieldSymbols0[field] extracts non-dummy bosonic FlatSpace symbols that must stay fixed during dummy-index canonicalization.";
flatSpaceProtectedFieldSymbols0[dX[idx_Symbol, _, _]] := {idx};
flatSpaceProtectedFieldSymbols0[dXt[idx_Symbol, _, _]] := {idx};
flatSpaceProtectedFieldSymbols0[ProfileX[profile_, _, _, _]] := flatSpaceProfileArgumentSymbols0[profile];
flatSpaceProtectedFieldSymbols0[ProfileXHolo[profile_, _, _]] := flatSpaceProfileArgumentSymbols0[profile];
flatSpaceProtectedFieldSymbols0[ProfileXAntiHolo[profile_, _, _]] := flatSpaceProfileArgumentSymbols0[profile];
flatSpaceProtectedFieldSymbols0[_] := {};


dummyIndexCandidateSymbols0::usage =
  "dummyIndexCandidateSymbols0[expr] returns bosonic FlatSpace dummy-index candidates from derivative factors and ProfileX derivative lists.";
dummyIndexCandidateSymbols0[expr_] := DeleteDuplicates @ Join[
  Flatten @ Cases[
    expr,
    derExpr_?derivativeApplicationQ0 :> Cases[Last[extractDerivativeBaseAndIndices0[derExpr]], sym_Symbol :> sym, Infinity],
    Infinity
  ],
  Flatten @ Cases[
    expr,
    field_ :> flatSpaceProfileDerivativeSymbols0[field],
    Infinity
  ]
];


dummyIndexProtectedSymbols0::usage =
  "dummyIndexProtectedSymbols0[expr] returns bosonic FlatSpace non-dummy symbols that must not be renamed during dummy-index canonicalization.";
dummyIndexProtectedSymbols0[expr_] := DeleteDuplicates @ Flatten @ Cases[
  expr,
  field_ :> flatSpaceProtectedFieldSymbols0[field],
  Infinity
];


flatSpaceRenamableFieldSymbols0::usage =
  "flatSpaceRenamableFieldSymbols0[field] extracts the renamable symbols contributed by one bosonic FlatSpace field occurrence.";
flatSpaceRenamableFieldSymbols0[dX[idx_Symbol, _, _]] := {idx};
flatSpaceRenamableFieldSymbols0[dXt[idx_Symbol, _, _]] := {idx};
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
flatSpaceRenamableFieldSymbols0[_] := {};


renamableOperatorSymbols0::usage =
  "renamableOperatorSymbols0[expr] lists bosonic FlatSpace vector/profile-index symbols that may be renamed during operator matching.";
renamableOperatorSymbols0[expr_] := DeleteDuplicates @ Flatten @ Cases[
  expr,
  field_ :> flatSpaceRenamableFieldSymbols0[field],
  Infinity
];


postProcessMatchedCoefficient0::usage =
  "postProcessMatchedCoefficient0[expr] expands and delta-contracts one bosonic FlatSpace extracted coefficient.";
postProcessMatchedCoefficient0[expr_] := Expand[ContractDelta[expr]];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
