(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`OPE`TypeII`FlatSpace`IndependentTensorStructures`"];
Needs["StringCode`OPE`TypeII`FlatSpace`CountSinglet`"];
Needs["StringCode`OPE`TypeII`FlatSpace`GammaProductGrammar`"];
Needs["StringCode`OPE`TypeII`FlatSpace`IndependentTensorStructuresSelector`"];
Needs["StringCode`OPE`TypeII`FlatSpace`TensorStructures`"];


(* ::Section:: *)
(*Declare public variables and methods*)


findIndependentTensorStructures::usage =
  "findIndependentTensorStructures[incoming, outgoing, opts] returns a verified independent subset of TypeII flat-space tensor structures; with candidate-list input it scans the supplied concrete candidates in order.";

findIndependentTensorStructures::badarg =
  "Arguments are not in a supported form for independent tensor-structure selection.";
findIndependentTensorStructures::badtarget =
  "\"TargetRank\" must be Automatic or a nonnegative integer; received `1`.";
findIndependentTensorStructures::badopt =
  "Unsupported option `1` supplied to findIndependentTensorStructures.";
findIndependentTensorStructures::toomanyout =
  "Outgoing input may contain at most one spinor index for automatic target-rank computation.";
findIndependentTensorStructures::targetunmet =
  "Requested target rank `1` could not be reached; the maximal verified rank found was `2`.";

Options[findIndependentTensorStructures] = {
  "TargetRank" -> Automatic,
  "ProbeCount" -> 5,
  "VerificationProbeCount" -> 3,
  "RandomSeed" -> Automatic,
  "ReturnStatistics" -> False
};


(* ::Section:: *)
(*Logic*)


Begin["Private`"];

validTargetRankOptionQ::usage = "validTargetRankOptionQ[target] checks whether the target-rank option is Automatic or a nonnegative integer.";
validTargetRankOptionQ[Automatic] := True;
validTargetRankOptionQ[target_Integer?NonNegative] := True;
validTargetRankOptionQ[_] := False;

parseSelectorOptions::usage = "parseSelectorOptions[opts] validates selector options and returns an option association or $Failed.";
parseSelectorOptions[opts_List] := Module[{assoc, targetRank, invalidOptions},
  invalidOptions = Complement[First /@ opts, First /@ Options[findIndependentTensorStructures]];
  If[invalidOptions =!= {}, Message[findIndependentTensorStructures::badopt, First[invalidOptions]]; Return[$Failed]];
  assoc = Association[Join[Options[findIndependentTensorStructures], opts]];
  targetRank = Lookup[assoc, "TargetRank", Automatic];
  If[!validTargetRankOptionQ[targetRank], Message[findIndependentTensorStructures::badtarget, targetRank]; Return[$Failed]];
  assoc
];

normalizeCandidateInput::usage =
  "normalizeCandidateInput[candidates] normalizes selector input to a list of candidate groups, preserving generator-provided abstract grouping.";
normalizeCandidateInput[candidates_List] := Which[
  candidates === {}, {},
  AllTrue[candidates, ListQ], Select[candidates, # =!= {} &],
  True, {candidates}
];

candidateInputCount::usage =
  "candidateInputCount[candidates] returns the flat candidate count represented by grouped or ungrouped selector input.";
candidateInputCount[candidates_List] := Total[Length /@ normalizeCandidateInput[candidates]];

selectorResult::usage = "selectorResult[basis, targetRank, visitedCandidates, optsAssoc] formats the selector return value according to ReturnStatistics.";
selectorResult[basis_List, targetRank_, visitedCandidates_Integer?NonNegative, optsAssoc_Association] := If[
  TrueQ[Lookup[optsAssoc, "ReturnStatistics", False]],
  <|"Basis" -> basis, "TargetRank" -> targetRank, "VisitedCandidates" -> visitedCandidates|>,
  basis
];

associationSelectionData::usage = "associationSelectionData[incoming, outgoing] validates association input and returns normalized search metadata.";
associationSelectionData[incoming_Association, outgoing_Association] := Module[
  {inNorm, outNorm, inVec, outVec, inSpin, outSpin, allIndexSymbols, outSpinor},
  inNorm = normalizeIndexAssociation[incoming];
  outNorm = normalizeIndexAssociation[outgoing];
  inVec = inNorm["vector"];
  outVec = outNorm["vector"];
  inSpin = inNorm["spinor"];
  outSpin = outNorm["spinor"];
  If[!(validVectorIndexListQ[inVec] && validVectorIndexListQ[outVec] && validSpinorIndexListQ[inSpin] && validSpinorIndexListQ[outSpin]),
    Message[findIndependentTensorStructures::badarg];
    Return[$Failed];
  ];
  If[Length[outSpin] > 1, Message[findIndependentTensorStructures::toomanyout]; Return[$Failed]];
  allIndexSymbols = Join[inVec, outVec, inSpin[[All, 1]], outSpin[[All, 1]]];
  (* Repeated symbols or odd spinor count imply malformed index bookkeeping for tensor generation/selection. *)
  If[!DuplicateFreeQ[allIndexSymbols] || OddQ[Length[inSpin] + Length[outSpin]],
    Message[findIndependentTensorStructures::badarg];
    Return[$Failed];
  ];
  outSpinor = If[outSpin === {}, None, First[outSpin]];
  <|
    "Incoming" -> inNorm,
    "Outgoing" -> outNorm,
    "OutSpinor" -> outSpinor,
    "ExternalVectors" -> Join[inVec, outVec]
  |>
];

automaticAssociationTargetRank::usage = "automaticAssociationTargetRank[data] computes the exact automatic target rank from incoming and outgoing representation content.";
automaticAssociationTargetRank[data_Association] := Module[{nChiral, nAnti},
  nChiral = Count[data["Incoming"]["spinor"][[All, 2]], "chiral"];
  nAnti = Count[data["Incoming"]["spinor"][[All, 2]], "antichiral"];
  If[data["OutSpinor"] =!= None,
    If[data["OutSpinor"][[2]] === "chiral", nAnti++, nChiral++];
  ];
  countSinglets[nChiral, nAnti, Length[data["ExternalVectors"]]]
];

scanCandidatesOrFail::usage = "scanCandidatesOrFail[candidates, targetRank, optsAssoc] runs the exact selector and emits badarg on compile failure.";
scanCandidatesOrFail[candidates_List, targetRank_, optsAssoc_Association] := Module[{result = scanCandidateList[candidates, targetRank, optsAssoc]},
  If[result === $Failed, Message[findIndependentTensorStructures::badarg]; $Failed, result]
];

findIndependentTensorStructures[incoming_Association, outgoing_Association, opts___Rule] := Module[
  {optsAssoc, searchData, targetRank, candidates, candidateCount, scanResult},
  optsAssoc = parseSelectorOptions[{opts}];
  If[optsAssoc === $Failed, Return[$Failed]];
  searchData = associationSelectionData[incoming, outgoing];
  If[searchData === $Failed, Return[$Failed]];
  targetRank = Lookup[optsAssoc, "TargetRank", Automatic];
  targetRank = If[targetRank === Automatic, automaticAssociationTargetRank[searchData], targetRank];
  If[targetRank === 0, Return[selectorResult[{}, 0, 0, optsAssoc]]];
  (* Association mode preserves generator grouping so the selector can compile and scan abstract families lazily. *)
  candidates = normalizeCandidateInput @ generateTensorStructures[searchData["Incoming"], searchData["Outgoing"]];
  candidateCount = candidateInputCount[candidates];
  If[targetRank > candidateCount,
    Message[findIndependentTensorStructures::targetunmet, targetRank, candidateCount];
    Return[$Failed];
  ];
  scanResult = scanCandidatesOrFail[candidates, targetRank, optsAssoc];
  If[scanResult === $Failed, Return[$Failed]];
  If[Length[scanResult["Basis"]] < targetRank,
    Message[findIndependentTensorStructures::targetunmet, targetRank, Length[scanResult["Basis"]]];
    Return[$Failed];
  ];
  selectorResult[scanResult["Basis"], scanResult["TargetRank"], scanResult["VisitedCandidates"], optsAssoc]
];

findIndependentTensorStructures[candidates_List, opts___Rule] := Module[
  {optsAssoc, normalizedCandidates, targetRank, candidateCount, scanResult},
  optsAssoc = parseSelectorOptions[{opts}];
  If[optsAssoc === $Failed, Return[$Failed]];
  normalizedCandidates = normalizeCandidateInput[candidates];
  candidateCount = candidateInputCount[normalizedCandidates];
  targetRank = Lookup[optsAssoc, "TargetRank", Automatic];
  If[normalizedCandidates === {},
    targetRank = Replace[targetRank, Automatic -> 0];
    If[targetRank =!= 0, Message[findIndependentTensorStructures::targetunmet, targetRank, 0]; Return[$Failed]];
    Return[selectorResult[{}, 0, 0, optsAssoc]];
  ];
  If[targetRank =!= Automatic && targetRank > candidateCount,
    Message[findIndependentTensorStructures::targetunmet, targetRank, candidateCount];
    Return[$Failed];
  ];
  (* List mode accepts flat or grouped candidates and scans them lazily in the supplied flat order. *)
  scanResult = scanCandidatesOrFail[normalizedCandidates, targetRank, optsAssoc];
  If[scanResult === $Failed, Return[$Failed]];
  If[targetRank =!= Automatic && Length[scanResult["Basis"]] < targetRank,
    Message[findIndependentTensorStructures::targetunmet, targetRank, Length[scanResult["Basis"]]];
    Return[$Failed];
  ];
  selectorResult[scanResult["Basis"], scanResult["TargetRank"], scanResult["VisitedCandidates"], optsAssoc]
];

findIndependentTensorStructures[___] := Module[{},
  Message[findIndependentTensorStructures::badarg];
  $Failed
];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
