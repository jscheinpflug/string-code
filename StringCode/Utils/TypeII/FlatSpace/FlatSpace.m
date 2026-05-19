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


flatSpaceProfileArgumentSymbols0::usage =
  "flatSpaceProfileArgumentSymbols0[profile] extracts renamable non-head symbols from the profile tensor/function arguments carried by ProfileX-like fields.";
flatSpaceProfileArgumentSymbols0[profile_] := If[
  AtomQ[profile],
  {},
  Cases[List @@ profile, sym_Symbol :> sym, Infinity, Heads -> False]
];


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
