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


flatSpaceProfileArgumentSymbols0::usage =
  "flatSpaceProfileArgumentSymbols0[profile] extracts renamable non-head symbols from the profile tensor/function arguments carried by ProfileX-like fields.";
flatSpaceProfileArgumentSymbols0[profile_] := If[
  AtomQ[profile],
  {},
  Cases[List @@ profile, sym_Symbol :> sym, Infinity, Heads -> False]
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
