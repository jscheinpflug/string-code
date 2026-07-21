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

corrSpinExternalsFromFields0::usage = "corrSpinExternalsFromFields0[fields] returns the ordered external symbolic-index spin-field slots {<|Label,Chirality|>,...} of one flat field list.";
corrSpinExternalsFromFields0[fields_List] := Cases[
  fields,
  (S | St)[{alpha_ /; ! VectorQ[alpha, NumericQ], chir : ("chiral" | "antichiral")}, __] :> <|"Label" -> alpha, "Chirality" -> chir|>
];

corrVectorExternalsFromFields0::usage = "corrVectorExternalsFromFields0[fields] returns the ordered symbolic external vector indices carried by psi/psit fields of one flat field list.";
corrVectorExternalsFromFields0[fields_List] := DeleteDuplicates @ Cases[
  fields,
  (\[Psi] | \[Psi]t)[mu_, _, _] /; ! IntegerQ[mu] :> mu
];

corrSpinExternals0::usage = "corrSpinExternals0[ops] returns the ordered list of external symbolic-index spin-field slots {<|Label,Chirality|>,...}, one per symbolic S/St field across the operator list.";
corrSpinExternals0[ops_List] := Flatten[
  Function[Ra, corrSpinExternalsFromFields0[List @@ Ra]] /@ ops,
  1
];

corrVectorExternals0::usage = "corrVectorExternals0[ops] returns the ordered list of symbolic external vector indices carried by psi/psit fields across the operator list.";
corrVectorExternals0[ops_List] := DeleteDuplicates @ Flatten[
  Function[Ra, corrVectorExternalsFromFields0[List @@ Ra]] /@ ops,
  1
];

corrSectorFields0::usage = "corrSectorFields0[ops] splits the operator list into holomorphic and antiholomorphic flat field lists, reusing the package factorization helpers rather than a bespoke classification: factorizeOperator first resolves both-chiral factorizable fields (ProfileX -> ProfileXHolo * ProfileXAntiHolo), then splitOperators partitions on isHolomorphic/isAntiHolomorphic. Returns <|\"Holo\" -> fields, \"Anti\" -> fields|>.";
corrSectorFields0[ops_List] := Module[{fields, split},
  fields = Join @@ (Function[Ra, Flatten[factorizeOperator /@ (List @@ Ra), 1]] /@ ops);
  split = splitOperators[fields, isHolomorphic, isAntiHolomorphic];
  <|"Holo" -> split[[1]], "Anti" -> split[[2]]|>
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

corrAntiDummySymbol0::usage = "corrAntiDummySymbol0[i] is the i-th antiholomorphic contracted-dummy symbol (nu-tilde i), used to keep the antiholomorphic sector's internal indices distinct from the holomorphic sector's.";
corrAntiDummySymbol0[i_Integer] := ToExpression["\[Nu]t" <> ToString[i]];

corrRenameAntiDummies0::usage = "corrRenameAntiDummies0[struct, antiVectors] renames the contracted internal dummies of one antiholomorphic tensor structure to nu-tilde symbols. Both sectors' bases come from findIndependentTensorStructures and therefore both emit nu1, nu2, ...; multiplying them without renaming would wrongly identify a holomorphic dummy with an antiholomorphic one and co-sum them.";
corrRenameAntiDummies0[struct_, antiVectors_List] := Module[{dummies},
  dummies = corrInternalVectorDummies0[struct, antiVectors];
  If[dummies === {},
    struct,
    struct /. Thread[dummies -> (corrAntiDummySymbol0 /@ Range[Length[dummies]])]
  ]
];

corrSectorTensorStructures0::usage = "corrSectorTensorStructures0[holoSpin, holoVec, antiSpin, antiVec] builds the tensor-structure basis as the OUTER PRODUCT of the two chiral sectors' independent bases. Holomorphic and antiholomorphic spinor indices live in independent Lorentz spinor spaces, so a single merged query would invent structures contracting a left-mover with a right-mover and inflate the basis (e.g. 11 structures where the factorized answer has 1). An empty sector contributes the trivial factor 1, so single-sector inputs reproduce the unfactorized basis exactly.";
corrSectorTensorStructures0[holoSpin_List, holoVec_List, antiSpin_List, antiVec_List] := Module[
  {holoStructs, antiStructs},
  holoStructs = If[holoSpin === {}, {1}, corrTensorStructures0[holoSpin, holoVec]];
  antiStructs = If[antiSpin === {}, {1}, corrTensorStructures0[antiSpin, antiVec]];
  If[! ListQ[holoStructs] || ! ListQ[antiStructs] || holoStructs === {} || antiStructs === {},
    Return[$Failed]
  ];
  antiStructs = corrRenameAntiDummies0[#, antiVec] & /@ antiStructs;
  Flatten[Outer[Times, holoStructs, antiStructs], 1]
];

corrSymbolicSpinFailed0::usage = "corrSymbolicSpinFailed0 is the private sentinel returned by corrSymbolicSpinDriver0 when the symbolic-index correlator cannot be computed, so the dispatch leaves Corr inert.";


(* Every deferral leaves Corr inert, but the reasons are very different: a genuine
   representation-theory obstruction, a vanishing correlator, and a merely
   exhausted sampling budget all used to look identical. These messages separate
   them so an inert result can be diagnosed. *)

Corr::spinbasis =
  "Symbolic spin correlator: no independent tensor-structure basis exists for the given external indices (`1` spin, `2` vector), so the correlator has no Lorentz invariants and may vanish identically. Leaving Corr inert.";

Corr::spinstruct =
  "Symbolic spin correlator: tensor structure `1` of `2` could not be evaluated at the physical chiralities -- a rigid gamma factor's link chirality disagrees with the external chirality assignment (e.g. an opposite-chirality two-gamma, which this link grammar cannot express). This is a representation-theory obstruction, not a sampling problem. Leaving Corr inert.";

Corr::spinprobes =
  "Symbolic spin correlator: exhausted `1` sampling attempts having found only `2` charge-saturating probes (reached rank `3` of `4` structures, with `5` of the `6` verification rows needed). Charge-saturating index assignments are rare, so this is most likely an insufficient sampling budget rather than a physics obstruction; if the rank is stuck below `4` the structures may instead be degenerate on the saturating set. Leaving Corr inert.";

Corr::spinsolve =
  "Symbolic spin correlator: the linear solve for the `1` z-functions failed on a full-rank system. Leaving Corr inert.";

Corr::spinverify =
  "Symbolic spin correlator: the fitted z-functions failed held-out verification on `1` of `2` surplus probes -- the tensor basis resolves to numbers but does not reproduce the numeric correlator. Leaving Corr inert.";


corrSymbolicSpinDriver0::usage = "corrSymbolicSpinDriver0[ops] computes a symbolic-index R-sector correlator as Sum_k T^(k) f_k(z): fit the scalar z-functions of the independent tensor structures against the numeric bosonized correlator at random concrete index assignments. Returns the corrSymbolicSpinFailed0 sentinel (leaving Corr inert) on failure, emitting one of Corr::spinbasis, Corr::spinstruct, Corr::spinprobes, Corr::spinsolve or Corr::spinverify to identify which kind of deferral occurred.";
corrSymbolicSpinDriver0[ops_List] := Module[
  {sectors, holoSpin, antiSpin, holoVec, antiVec,
   spinExternals, vectorExternals, chiralityMap, structs, kDim, rows = {}, gvals = {},
   extraRows = {}, extraG = {}, rank = 0, attempts = 0, maxAttempts = 4000, usable = 0,
   sa, va, row, g, fvec, badStruct, badCount, verified = True, verifyTarget = 4},
  (* Split into chiral sectors first: S/psi and St/psit carry indices of independent
     Lorentz spinor spaces, so their tensor bases must be built separately and
     multiplied. Classification reuses the package factorization helpers so that
     both-chiral fields (ProfileX) are resolved the same way BracketProjected does.

     On the fermionic reordering sign: splitOperators has a companion,
     factorizationSign, which BracketProjected applies because it actually computes
     the two sectors separately and multiplies them. This driver does NOT, and must
     not, apply it. The z-oracle here is the FULL correlator (Corr on the original
     operators), so every Grassmann sign is already present in g; the fitted f_k
     absorb it. The sector split is used only to classify indices and to build the
     basis as a product. Applying factorizationSign on top would double-count it. *)
  sectors = corrSectorFields0[ops];
  holoSpin = corrSpinExternalsFromFields0[sectors["Holo"]];
  antiSpin = corrSpinExternalsFromFields0[sectors["Anti"]];
  holoVec = corrVectorExternalsFromFields0[sectors["Holo"]];
  antiVec = corrVectorExternalsFromFields0[sectors["Anti"]];
  spinExternals = Join[holoSpin, antiSpin];
  (* Fewer than two symbolic spin fields: this driver simply does not apply, so
     defer silently rather than reporting a failure. *)
  If[Length[spinExternals] < 2, Return[corrSymbolicSpinFailed0]];
  vectorExternals = Join[holoVec, antiVec];
  chiralityMap = corrSpinChiralityMap0[spinExternals];
  structs = corrSectorTensorStructures0[holoSpin, holoVec, antiSpin, antiVec];
  If[! ListQ[structs] || structs === {},
    Message[Corr::spinbasis, Length[spinExternals], Length[vectorExternals]];
    Return[corrSymbolicSpinFailed0]
  ];
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
    usable++;
    row = Table[corrResolveStructure0[structs[[k]], sa, va, vectorExternals, chiralityMap], {k, kDim}];
    (* A structure that will not resolve is a representation-theory obstruction and
       will not resolve at any other assignment either, so bail immediately. *)
    If[! FreeQ[row, GammaAntisymmetricProductHold],
      badStruct = FirstPosition[row, _GammaAntisymmetricProductHold, {0}, Infinity][[1]];
      Message[Corr::spinstruct, badStruct, kDim];
      Return[corrSymbolicSpinFailed0]
    ];
    If[rank < kDim && MatrixRank[Append[rows, row]] > rank,
      AppendTo[rows, row]; AppendTo[gvals, g]; rank++,
      If[rank >= kDim, AppendTo[extraRows, row]; AppendTo[extraG, g]]
    ]
  ];
  If[rank < kDim || Length[extraRows] < verifyTarget,
    Message[Corr::spinprobes, attempts, usable, rank, kDim, Length[extraRows], verifyTarget];
    Return[corrSymbolicSpinFailed0]
  ];
  fvec = Quiet @ LinearSolve[rows, gvals];
  If[! FreeQ[fvec, LinearSolve] || Length[fvec] =!= kDim,
    Message[Corr::spinsolve, kDim];
    Return[corrSymbolicSpinFailed0]
  ];
  (* Held-out self-consistency: the fitted structures must reproduce the numeric
     correlator on the surplus probes, which took no part in the fit. Catches cases
     whose structures resolve to numbers but not the physically-correct ones (e.g.
     the mixed-chirality two-gamma, deferred to a later pass). *)
  verified = True;
  badCount = 0;
  Do[
    If[Simplify[extraG[[i]] - extraRows[[i]] . fvec] =!= 0, verified = False; badCount++],
    {i, verifyTarget}
  ];
  If[! TrueQ[verified],
    Message[Corr::spinverify, badCount, verifyTarget];
    Return[corrSymbolicSpinFailed0]
  ];
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
