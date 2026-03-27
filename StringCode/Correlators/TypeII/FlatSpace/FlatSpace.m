(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Correlators`TypeII`FlatSpace`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];
Needs["StringCode`Symbols`TypeII`FlatSpace`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`TypeII`"];
Needs["StringCode`Operators`"];
Needs["StringCode`Correlators`"];
Needs["StringCode`Correlators`TypeII`"];
Needs["StringCode`Wick`TypeII`FlatSpace`"];
Needs["StringCode`OPE`TypeII`FlatSpace`"];


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


typeIIPurePsiExpPhiHeads::usage = "typeIIPurePsiExpPhiHeads is the list of supported raw TypeII free-field heads handled by the dedicated correlator Wick path.";
typeIIPurePsiExpPhiHeads = {
  \[Psi], \[Psi]t,
  d\[Phi], d\[Phi]t,
  exp\[Phi]b, exp\[Phi]f, exp\[Phi]tb, exp\[Phi]tf
};


purePsiExpPhiCorrQ::usage = "purePsiExpPhiCorrQ[Ra] is True when a local operator lies entirely in the supported raw TypeII free-field sector handled by CorrWickList.";
purePsiExpPhiCorrQ[Ra_ /; RTest[Ra]] := AllTrue[List @@ Ra, MemberQ[typeIIPurePsiExpPhiHeads, Head[#]] &];


corrEvaluableRListQ[rList_List] := True /; (rList =!= {} && AllTrue[rList, purePsiExpPhiCorrQ]);


corrEntirelyFreeQ::usage = "corrEntirelyFreeQ[rList] is extended in TypeII FlatSpace so the pure raw psi/phi free sector goes straight to CorrWickList.";
corrEntirelyFreeQ[rList_List] := True /; (rList =!= {} && AllTrue[rList, purePsiExpPhiCorrQ]);


registerChargeVevSector[
  "typeii-holo-h",
  {expH},
  {-2, 0, 0, 0, 0, 0},
  {expH, dH, exp\[Phi]b, exp\[Phi]f, d\[Phi], \[Eta], \[Xi], \[Beta], \[Gamma]},
  {dH, \[Eta], \[Xi], \[Beta], \[Gamma]},
  Bosonize,
  (#[[1]] &),
  1
];

registerChargeVevSector[
  "typeii-anti-h",
  {expHt},
  {-2, 0, 0, 0, 0, 0},
  {expHt, dHt, exp\[Phi]tb, exp\[Phi]tf, d\[Phi]t, \[Eta]t, \[Xi]t, \[Beta]t, \[Gamma]t},
  {dHt, \[Eta]t, \[Xi]t, \[Beta]t, \[Gamma]t},
  Bosonize,
  (#[[1]] &),
  1
];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
