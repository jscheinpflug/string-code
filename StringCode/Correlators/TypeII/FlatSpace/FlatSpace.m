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
Needs["StringCode`OPE`TypeII`FlatSpace`GammaMatrices`"];
Needs["StringCode`OPE`TypeII`FlatSpace`GammaMatrices`GammaProductGrammar`"];
Needs["StringCode`OPE`TypeII`FlatSpace`SpinProjection`Solve`"];
Needs["StringCode`OPE`TypeII`FlatSpace`TensorStructures`IndependentTensorStructures`"];


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


corrSpinFieldHeads::usage = "corrSpinFieldHeads lists the raw TypeII Ramond spin-field heads handled by the correlator bosonization pre-pass.";
corrSpinFieldHeads = {S, St};


corrHasSpinFieldQ0::usage = "corrHasSpinFieldQ0[Ra] is True when a local operator contains a raw TypeII Ramond spin field S or St.";
corrHasSpinFieldQ0[Ra_ /; RTest[Ra]] := AnyTrue[List @@ Ra, MemberQ[corrSpinFieldHeads, Head[#]] &];


corrValidSpinDescendantModeQ0::usage = "corrValidSpinDescendantModeQ0[mode, maxIdx] is True when mode is a bosonizable descendant spin mode {vectorIndex, modding} (either order) with vector index in 1..maxIdx and nonpositive modding. Self-contained mirror of the spin-mode grammar so the correlator module does not depend on Symbols`Private helpers.";
corrValidSpinDescendantModeQ0[mode_, maxIdx_Integer] :=
  MatchQ[mode, {i_Integer?Positive, _Integer?NonPositive} /; i <= maxIdx] ||
  MatchQ[mode, {_Integer?NonPositive, i_Integer?Positive} /; i <= maxIdx];


corrBosonizableSpinFieldQ0::usage = "corrBosonizableSpinFieldQ0[field] is True when field is a Ramond spin field that Bosonize fully reduces to bosonized expH/dH content: a ground state, a valid descendant-mode excited state, or a derivative thereof.";
corrBosonizableSpinFieldQ0[(S | St)[{spinVec_List, ("chiral" | "antichiral")}, q_ /; NumericQ[q], modes_List, der_Integer?NonNegative, _]] :=
  modes === {} || AllTrue[modes, corrValidSpinDescendantModeQ0[#, Length[spinVec]] &];
corrBosonizableSpinFieldQ0[_] := False;


corrOperatorSpinBosonizableQ0::usage = "corrOperatorSpinBosonizableQ0[Ra] is True when every spin field in a local operator is Bosonize-reducible, so the bosonization pre-pass fully eliminates all raw spin fields and the recursion into Corr terminates.";
corrOperatorSpinBosonizableQ0[Ra_ /; RTest[Ra]] := AllTrue[
  List @@ Ra,
  (!MemberQ[corrSpinFieldHeads, Head[#]] || corrBosonizableSpinFieldQ0[#]) &
];


(* Defer generic dispatch for ANY raw spin field so spin fields that Bosonize
   cannot reduce (unsupported mode grammar) stay symbolic rather than being
   shunted to an inert residual. *)
corrDeferToSpecializedQ[rList_List] := True /; (rList =!= {} && AnyTrue[rList, corrHasSpinFieldQ0]);


(* R-sector pre-pass: bosonize S/St to expH/dH/expHt in place and recurse into
   Corr, which then evaluates the pure bosonized free+charge sector. Triggers
   only when every spin field is Bosonize-reducible, so the bosonized operators
   are spin-free and the recursion always makes progress and terminates. *)
Corr[ops__ /; (AllTrue[{ops}, RTest] && AnyTrue[{ops}, corrHasSpinFieldQ0] && AllTrue[{ops}, corrOperatorSpinBosonizableQ0])] :=
  Corr @@ (Bosonize /@ {ops});


(* ============================================================================
   Symbolic-index R-sector correlators (hybrid: numeric z-oracle x tensor-oracle
   fit). A spin field with a SYMBOLIC spinor index cannot be bosonized to a
   concrete expH, so it is not handled by the pre-pass above. Instead we compute
   the correlator's Lorentz-tensor decomposition <O_1...O_n> = Sum_k T^(k) f_k(z):
   the tensor basis {T^(k)} comes from findIndependentTensorStructures, and the
   scalar z-functions f_k are fit from the numeric bosonized correlator evaluated
   at random concrete index assignments (M.f = g). Any failure leaves Corr inert.
   ============================================================================ *)

corrChiralSpinWeights0::usage = "corrChiralSpinWeights0 is the ordered list of 16 chiral SO(10) spin weights, reconstructed from source so the correlator module does not depend on the Symbols`Private ordering symbol.";
corrChiralSpinWeights0 = Join[{{1/2, 1/2, 1/2, 1/2, 1/2}}, Permutations[{1/2, 1/2, 1/2, -1/2, -1/2}], Permutations[{1/2, -1/2, -1/2, -1/2, -1/2}]];

corrAntiSpinWeights0::usage = "corrAntiSpinWeights0 is the ordered list of 16 antichiral SO(10) spin weights (= -corrChiralSpinWeights0).";
corrAntiSpinWeights0 = -corrChiralSpinWeights0;

corrSpinWeightAt0::usage = "corrSpinWeightAt0[chirality, index] returns the explicit spin weight vector of the given chirality at basis index 1..16.";
corrSpinWeightAt0["chiral", i_Integer] := corrChiralSpinWeights0[[i]];
corrSpinWeightAt0["antichiral", i_Integer] := corrAntiSpinWeights0[[i]];

corrSpinChiralityMap0::usage = "corrSpinChiralityMap0[spinExternals] maps each external spin label to its physical chirality. One global chirality per label is what keeps every tensor structure describing the same physical configuration during the fit.";
corrSpinChiralityMap0[spinExternals_List] := Association[(#["Label"] -> #["Chirality"]) & /@ spinExternals];

corrSymbolicSpinIndexQ0::usage = "corrSymbolicSpinIndexQ0[field] is True when field is a Ramond spin field whose spinor index is symbolic (not an explicit numeric weight vector).";
corrSymbolicSpinIndexQ0[field_] := MatchQ[field, (S | St)[{alpha_, ("chiral" | "antichiral")}, _, _, _, _] /; ! VectorQ[alpha, NumericQ]];

corrHasSymbolicSpinQ0::usage = "corrHasSymbolicSpinQ0[Ra] is True when a local operator contains a symbolic-index spin field.";
corrHasSymbolicSpinQ0[Ra_ /; RTest[Ra]] := AnyTrue[List @@ Ra, corrSymbolicSpinIndexQ0];

corrSpinExternals0::usage = "corrSpinExternals0[ops] returns the ordered list of external symbolic-index spin-field slots {<|Label,Chirality|>,...}, one per symbolic S/St field across the operator list.";
corrSpinExternals0[ops_List] := Flatten[
  Function[Ra, Cases[List @@ Ra, (S | St)[{alpha_ /; ! VectorQ[alpha, NumericQ], chir : ("chiral" | "antichiral")}, __] :> <|"Label" -> alpha, "Chirality" -> chir|>]] /@ ops,
  1
];

corrVectorExternals0::usage = "corrVectorExternals0[ops] returns the ordered list of symbolic external vector indices carried by psi/psit fields across the operator list.";
corrVectorExternals0[ops_List] := DeleteDuplicates @ Flatten[
  Function[Ra, Cases[List @@ Ra, (\[Psi] | \[Psi]t)[mu_, _, _] /; ! IntegerQ[mu] :> mu]] /@ ops,
  1
];

corrInternalVectorDummies0::usage = "corrInternalVectorDummies0[struct, externalVectors] returns the contracted internal vector dummy symbols of a tensor structure (all gamma-link indices minus the external ones).";
corrInternalVectorDummies0[struct_, externalVectors_List] := Complement[
  DeleteDuplicates @ Cases[struct, (GammaUDHold | GammaDUHold)[v_] :> v, Infinity],
  externalVectors
];

corrFeedFactorChiralities0::usage = "corrFeedFactorChiralities0[struct, spinAssignment, chiralityMap] substitutes each spinor label in a tensor structure by an explicit weight vector of the label's PHYSICAL chirality, at the label's assigned basis index. Using one global chirality per label (rather than the per-factor slot chirality from gammaProductSpinorChiralities) keeps every structure describing the same physical configuration; a rigid factor whose links disagree with the physical chirality then simply fails to resolve, which the driver treats as a deferral.";
corrFeedFactorChiralities0[struct_, spinAssignment_Association, chiralityMap_Association] := struct /. GammaAntisymmetricProductHold[links_List, s1_, s2_] :> GammaAntisymmetricProductHold[
  links,
  If[KeyExistsQ[spinAssignment, s1], corrSpinWeightAt0[chiralityMap[s1], spinAssignment[s1]], s1],
  If[KeyExistsQ[spinAssignment, s2], corrSpinWeightAt0[chiralityMap[s2], spinAssignment[s2]], s2]
];

corrResolveStructure0::usage = "corrResolveStructure0[struct, spinAssignment, vectorAssignment, externalVectors, chiralityMap] evaluates one tensor structure to a scalar at a concrete index assignment: feeds each spinor label its physical chirality, substitutes external vector labels, and sums the contracted internal vector dummies over 1..10.";
corrResolveStructure0[struct_, spinAssignment_Association, vectorAssignment_Association, externalVectors_List, chiralityMap_Association] := Module[
  {fed, dummies, withExternal},
  fed = corrFeedFactorChiralities0[struct, spinAssignment, chiralityMap];
  (* Internal dummies are the contracted vector indices, i.e. all gamma-link
     indices minus the external (open) vector labels. Compute them BEFORE
     substituting the external labels, so a concrete external index is not
     mistaken for a dummy and summed over. *)
  dummies = corrInternalVectorDummies0[fed, externalVectors];
  withExternal = fed /. KeyValueMap[Rule, vectorAssignment];
  If[dummies === {},
    spinProjectionEvaluateTensorScalars[withExternal],
    Total[spinProjectionEvaluateTensorScalars[withExternal /. Thread[dummies -> #]] & /@ Tuples[Range[10], Length[dummies]]]
  ]
];

corrNumericCorrelatorAt0::usage = "corrNumericCorrelatorAt0[ops, spinExternals, spinAssignment, vectorAssignment] evaluates the numeric bosonized correlator (the z-oracle) with the external symbolic indices replaced by concrete weights (physical chirality) and vector integers.";
corrNumericCorrelatorAt0[ops_List, spinExternals_List, spinAssignment_Association, vectorAssignment_Association] := Module[
  {spinRules},
  spinRules = Function[slot, slot["Label"] -> corrSpinWeightAt0[slot["Chirality"], spinAssignment[slot["Label"]]]] /@ spinExternals;
  Corr @@ (ops /. Join[spinRules, KeyValueMap[Rule, vectorAssignment]])
];

corrRandomSpinAssignment0::usage = "corrRandomSpinAssignment0[spinExternals] draws a random basis index 1..16 for each external spin label.";
corrRandomSpinAssignment0[spinExternals_List] := Association[(#["Label"] -> RandomInteger[{1, 16}]) & /@ spinExternals];

corrRandomVectorAssignment0::usage = "corrRandomVectorAssignment0[vectorExternals] draws a random vector index 1..10 for each external vector label.";
corrRandomVectorAssignment0[vectorExternals_List] := Association[(# -> RandomInteger[{1, 10}]) & /@ vectorExternals];

corrTensorStructures0::usage = "corrTensorStructures0[spinExternals, vectorExternals] builds the independent Lorentz tensor structure basis for the correlator. This is purely a tensor-basis framing: every external spin and vector index is handed to findIndependentTensorStructures as incoming, carrying its PHYSICAL chirality, with an empty outgoing slot. It has nothing to do with the physical BPZ conjugate (an Infinity coordinate, handled downstream by corrWithInfinity in the numeric z-oracle); no chirality is flipped here.";
corrTensorStructures0[spinExternals_List, vectorExternals_List] := Module[
  {incoming},
  If[spinExternals === {}, Return[$Failed]];
  incoming = <|"vector" -> vectorExternals, "spinor" -> ({#["Label"], #["Chirality"]} & /@ spinExternals)|>;
  Quiet @ findIndependentTensorStructures[
    incoming,
    <|"vector" -> {}, "spinor" -> {}|>,
    "TargetRank" -> Automatic,
    "RandomSeed" -> 1234
  ]
];

corrSymbolicSpinFailed0::usage = "corrSymbolicSpinFailed0 is the private sentinel returned by corrSymbolicSpinDriver0 when the symbolic-index correlator cannot be computed, so the dispatch leaves Corr inert.";


corrSymbolicSpinDriver0::usage = "corrSymbolicSpinDriver0[ops] computes a symbolic-index R-sector correlator as Sum_k T^(k) f_k(z): fit the scalar z-functions of the independent tensor structures against the numeric bosonized correlator at random concrete index assignments. Returns an inert Corr[...] on any failure (unresolved structure, rank deficiency, or empty basis).";
corrSymbolicSpinDriver0[ops_List] := Module[
  {spinExternals, vectorExternals, chiralityMap, structs, kDim, rows = {}, gvals = {},
   extraRows = {}, extraG = {}, rank = 0, attempts = 0, maxAttempts = 4000,
   sa, va, row, g, fvec, verified = True, verifyTarget = 4},
  spinExternals = corrSpinExternals0[ops];
  If[Length[spinExternals] < 2, Return[corrSymbolicSpinFailed0]];
  vectorExternals = corrVectorExternals0[ops];
  chiralityMap = corrSpinChiralityMap0[spinExternals];
  structs = corrTensorStructures0[spinExternals, vectorExternals];
  If[! ListQ[structs] || structs === {}, Return[corrSymbolicSpinFailed0]];
  kDim = Length[structs];
  (* Charge-saturating assignments are rare (a percent or so of random draws), so
     gather ONE pool of usable probes and split it: the first rank-increasing rows
     fit the z-functions, the surplus rows verify them. Two independent sampling
     passes would each risk starving. *)
  While[(rank < kDim || Length[extraRows] < verifyTarget) && attempts < maxAttempts,
    attempts++;
    sa = corrRandomSpinAssignment0[spinExternals];
    va = corrRandomVectorAssignment0[vectorExternals];
    g = corrNumericCorrelatorAt0[ops, spinExternals, sa, va];
    If[g === 0 || ! FreeQ[g, Corr] || ! FreeQ[g, R], Continue[]];
    row = Table[corrResolveStructure0[structs[[k]], sa, va, vectorExternals, chiralityMap], {k, kDim}];
    If[! FreeQ[row, GammaAntisymmetricProductHold], Return[corrSymbolicSpinFailed0]];  (* structure did not resolve *)
    If[rank < kDim && MatrixRank[Append[rows, row]] > rank,
      AppendTo[rows, row]; AppendTo[gvals, g]; rank++,
      If[rank >= kDim, AppendTo[extraRows, row]; AppendTo[extraG, g]]
    ]
  ];
  If[rank < kDim || Length[extraRows] < verifyTarget, Return[corrSymbolicSpinFailed0]];
  fvec = Quiet @ LinearSolve[rows, gvals];
  If[! FreeQ[fvec, LinearSolve] || Length[fvec] =!= kDim, Return[corrSymbolicSpinFailed0]];
  (* Held-out self-consistency: the fitted structures must reproduce the numeric
     correlator on the surplus probes, which took no part in the fit. Catches cases
     whose structures resolve to numbers but not the physically-correct ones (e.g.
     the mixed-chirality two-gamma, deferred to a later pass). *)
  verified = True;
  Do[
    If[Simplify[extraG[[i]] - extraRows[[i]] . fvec] =!= 0, verified = False],
    {i, verifyTarget}
  ];
  If[! TrueQ[verified], Return[corrSymbolicSpinFailed0]];
  Total[Table[structs[[k]] Simplify[fvec[[k]]], {k, kDim}]]
];


(* Symbolic-index R-sector correlator dispatch (mutually exclusive with the
   concrete bosonization pre-pass, which requires numeric spinor weights). *)
Corr[ops__ /; (AllTrue[{ops}, RTest] && AnyTrue[{ops}, corrHasSymbolicSpinQ0])] :=
  With[{corrSymbolicResult0 = corrSymbolicSpinDriver0[{ops}]}, corrSymbolicResult0 /; corrSymbolicResult0 =!= corrSymbolicSpinFailed0];


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
