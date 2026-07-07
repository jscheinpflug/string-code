(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`OPE`TypeII`FlatSpace`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];
Needs["StringCode`Symbols`TypeII`FlatSpace`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`TypeII`"];
Needs["StringCode`Operators`"];
Needs["StringCode`OPE`"];
Needs["StringCode`Taylor`"];
Needs["StringCode`BasisGeneration`TypeII`"];
Needs["StringCode`BasisGeneration`TypeII`FlatSpace`"];
Needs["StringCode`OPE`TypeII`FlatSpace`TensorStructures`CountSinglet`"];
Needs["StringCode`OPE`TypeII`FlatSpace`GammaMatrices`GammaKernelEngine`"];
Needs["StringCode`OPE`TypeII`FlatSpace`GammaMatrices`"];
Needs["StringCode`OPE`TypeII`FlatSpace`GammaMatrices`GammaProductGrammar`"];
Needs["StringCode`OPE`TypeII`FlatSpace`SpinProjection`Compile`"];
Needs["StringCode`OPE`TypeII`FlatSpace`SpinProjection`Solve`"];
Needs["StringCode`OPE`TypeII`FlatSpace`TensorStructures`IndependentTensorStructures`"];
Needs["StringCode`OPE`TypeII`FlatSpace`TensorStructures`"];
Needs["StringCode`OPE`TypeII`FlatSpace`TensorStructures`TensorStructuresVisualize`"];


(* ::Section:: *)
(*Declare public variables and methods*)

(* ::Section:: *)
(*Logic*)


Begin["Private`"];

projectionExponentReplacement = {\[Alpha]p -> 0};
If[FreeQ[Options[OPEProjected], "RandomSeed" -> _], Options[OPEProjected] = Append[Options[OPEProjected], "RandomSeed" -> Automatic]];
OPEProjected::spinsolve =
  "Could not determine a unique spin-field projection in the `1` sector after `2` probe attempts.";
OPEProjected::incomplete =
  "Could not determine a complete spin-field projection in the `1` sector after `2` candidate probes (`3`/`4` pivots).";

hasSpinFieldQ::usage = "Checks whether a normal-ordered operator contains TypeII spin fields S or St.";
hasSpinFieldQ[Ra_ /; RTest[Ra]] := AnyTrue[List @@ Ra, MemberQ[{S, St}, Head[#]] &];

sectorHasSpinFieldQ0::usage =
  "sectorHasSpinFieldQ0[sector, ops] is True iff the selected TypeII chiral sector contains at least one spin field after splitting.";
sectorHasSpinFieldQ0[sector : ("Holo" | "Anti"), ops_List] :=
  AnyTrue[spinProjectionSectorOps0[ops, spinProjectionSectorSpec[sector]], hasSpinFieldQ];

typeIIRamondOutputHoloQ::usage =
  "typeIIRamondOutputHoloQ[restR] is True iff the holomorphic remainder has Ramond output parity.";
typeIIRamondOutputHoloQ[restR_List] := OddQ[Count[Flatten[List @@ # & /@ restR], _S]];

typeIIRamondOutputAntiHoloQ::usage =
  "typeIIRamondOutputAntiHoloQ[restR] is True iff the antiholomorphic remainder has Ramond output parity.";
typeIIRamondOutputAntiHoloQ[restR_List] := OddQ[Count[Flatten[List @@ # & /@ restR], _St]];

typeIITotalPictureHolo0::usage =
  "typeIITotalPictureHolo0[restR] sums the holomorphic picture contributions of the non-collapsable remainder field-by-field.";
typeIITotalPictureHolo0[restR_List] := Total[pictureContributionHolo /@ Flatten[List @@ # & /@ restR]];

typeIITotalPictureAntiHolo0::usage =
  "typeIITotalPictureAntiHolo0[restR] sums the antiholomorphic picture contributions of the non-collapsable remainder field-by-field.";
typeIITotalPictureAntiHolo0[restR_List] := Total[pictureContributionAntiHolo /@ Flatten[List @@ # & /@ restR]];

minTypeIINonCollapsableWeightFromPicture::usage =
  "minTypeIINonCollapsableWeightFromPicture[qTotal, ramondQ] returns the TypeII lower bound from picture and NS/R sector.";
minTypeIINonCollapsableWeightFromPicture[qTotal_, ramondQ_] := With[
  {base = -qTotal (qTotal + 2)/2},
  Which[IntegerQ[qTotal], base, TrueQ[ramondQ], base + 5/8, True, base + 1/2]
];

minNonCollapsableWeightHolo::usage =
  "minNonCollapsableWeightHolo[restR] returns the TypeII holomorphic lower bound for non-collapsable remainder projections derived from picture number and Ramond parity.";
minNonCollapsableWeightHolo[restR_List] := minTypeIINonCollapsableWeightFromPicture[
  typeIITotalPictureHolo0[restR],
  typeIIRamondOutputHoloQ[restR]
];

minNonCollapsableWeightAntiHolo::usage =
  "minNonCollapsableWeightAntiHolo[restR] returns the TypeII antiholomorphic lower bound for non-collapsable remainder projections derived from picture number and Ramond parity.";
minNonCollapsableWeightAntiHolo[restR_List] := minTypeIINonCollapsableWeightFromPicture[
  typeIITotalPictureAntiHolo0[restR],
  typeIIRamondOutputAntiHoloQ[restR]
];

recombineProjectedFlatSpaceROps0::usage =
  "recombineProjectedFlatSpaceROps0[ops] recombines factorized FlatSpace profile and plane-wave operator pairs inside one normal-ordered operator list.";
recombineProjectedFlatSpaceROps0[ops_List] := FixedPoint[
  Replace[#, {
    {left___, ProfileXHolo[profile_, ders_, z_], middle___, ProfileXAntiHolo[profile_, ders_, zbar_], right___} :>
      {left, ProfileX[profile, ders, z, zbar], middle, right},
    {left___, ProfileXAntiHolo[profile_, ders_, zbar_], middle___, ProfileXHolo[profile_, ders_, z_], right___} :>
      {left, ProfileX[profile, ders, z, zbar], middle, right},
    {left___, expXHolo[p_, z_], middle___, expXAntiHolo[p_, zbar_], right___} :>
      {left, expX[p, z, zbar], middle, right},
    {left___, expXAntiHolo[p_, zbar_], middle___, expXHolo[p_, z_], right___} :>
      {left, expX[p, z, zbar], middle, right}
  }] &,
  ops
];

recombineProjectedFlatSpaceR0::usage =
  "recombineProjectedFlatSpaceR0[ra] recombines factorized FlatSpace profile and plane-wave pairs inside one projected normal-ordered product.";
recombineProjectedFlatSpaceR0[ra_ /; RTest[ra]] := With[
  {ops = recombineProjectedFlatSpaceROps0[List @@ ra]},
  R @@ ops
];

postProcessProjectedOPE0::usage =
  "postProcessProjectedOPE0[expr] recombines factorized FlatSpace profile and plane-wave fields in projected OPE outputs. Module-generated dummy indices, Kronecker delta contractions, and der[F][\[Mu]] folding into ProfileX are all deferred to the outermost BracketProjection boundary for performance reasons.";
postProcessProjectedOPE0[expr_] := FixedPoint[
  Expand[# /. ra_ /; RTest[ra] :> recombineProjectedFlatSpaceR0[ra]] &,
  Expand[expr]
];


OPEWickList::usage = "OPEWickList[rList] folds OPEWick over a list of normal-ordered products.";
OPEWickList[rList_List] := Which[
  rList === {}, 1,
  Length[rList] === 1, First[rList],
  True, OPEWick[First[rList], OPEWickList[Rest[rList]]]
];

psiExpPhiHeads = {\[Psi], \[Psi]t, d\[Phi], d\[Phi]t, exp\[Phi]b, exp\[Phi]f, exp\[Phi]tb, exp\[Phi]tf};
purePsiExpPhiQ::usage = "purePsiExpPhiQ[Ra] is True when Ra contains only \:03c8/\:2202\:03d5/exp\:03d5 TypeII fields handled by the bosonized free-field OPE path.";
purePsiExpPhiQ[Ra_ /; RTest[Ra]] := AllTrue[List @@ Ra, MemberQ[psiExpPhiHeads, Head[#]] &];

OPE[Ra_, Rb_] := OPEWick[Ra, Rb] /; (
  RTest[Ra] && RTest[Rb] &&
  purePsiExpPhiQ[Ra] && purePsiExpPhiQ[Rb]
);

combineChiral::usage = "combineChiral[a, b] rejoins holomorphic and antiholomorphic projected factors into one normal-ordered expression.";
combineChiral[a_, b_] := Which[
  a === 0 || b === 0, 0,
  a === 1, b,
  b === 1, a,
  True, R[a, b]
];

spinProjectionCompiledSeed::usage =
  "spinProjectionCompiledSeed is the canonical deterministic seed used by the compiled supported spin-field solver.";
spinProjectionCompiledSeed = 1234;

spinProjectedCoefficient::usage = "spinProjectedCoefficient[i] is an internal placeholder for one unresolved spin-field OPE coefficient.";


sectorExprFromArtifact0::usage =
  "sectorExprFromArtifact0[artifact, seed] resolves one projected sector artifact to its expression using exact compiled solving when needed.";
sectorExprFromArtifact0[artifact_, seed_] := Which[
  artifact === None, 0,
  artifact["Mode"] === "ClosedForm", artifact["Expr"],
  artifact["Mode"] === "SpinProjectionFailure",
    (
      Message[OPEProjected::incomplete, artifact["Sector"], 0, 0, 0];
      $Failed
    ),
  artifact["Mode"] === "SpinProjection",
    Module[{result, expr},
      result = solveSectorArtifact[artifact, seed];
      If[!TrueQ[result["CompleteQ"]],
        Message[
          OPEProjected::incomplete,
          artifact["Sector"],
          Lookup[result, "VisitedCandidates", 0],
          Lookup[result, "PivotCount", Length[Lookup[result, "Pivots", {}]]],
          Lookup[result, "VarCount", artifact["VarCount"]]
        ];
        Return[$Failed]
      ];
      expr = If[
        artifact["Columns"] === {},
        artifact["Expr"],
        Total @ Table[
          If[
            result["CoeffVector"][[i]] === 0,
            Nothing,
            result["CoeffVector"][[i]] artifact["Columns"][[i, "RepresentativeExpr"]]
          ],
          {i, Length[artifact["Columns"]]}
        ]
      ];
      expr
    ],
  True, 0
];

spinProjectionSectorExpr0::usage =
  "spinProjectionSectorExpr0[sector, ops, weight, seed] resolves one chiral spin-projection artifact to its projected expression or $Failed.";
spinProjectionSectorExpr0[sector : ("Holo" | "Anti"), ops_List, weight_, seed_] :=
  sectorExprFromArtifact0[buildSectorArtifact[sector, ops, weight, seed], seed];

spinProjectionSpectatorExpr0::usage =
  "spinProjectionSpectatorExpr0[sector, ops] returns the unprojected spectator expression in the opposite chirality for chiral projected OPEs.";
spinProjectionSpectatorExpr0[sector : ("Holo" | "Anti"), ops_List] :=
  opeOfRList[spinProjectionSectorOps0[ops, spinProjectionSectorSpec[sector]]];

OPEProjectedHolo[wH_][Ra__ /; (And @@ (RTest /@ {Ra}) && !AnyTrue[{Ra}, hasCollapsable] && sectorHasSpinFieldQ0["Holo", {Ra}]), opts___Rule] := Module[
  {seed, ops = {Ra}, projectedHolo, spectatorAnti},
  seed = Replace[Lookup[Association[Join[Options[OPEProjected], {opts}]], "RandomSeed", Automatic], Automatic -> spinProjectionCompiledSeed];
  projectedHolo = spinProjectionSectorExpr0["Holo", ops, wH, seed];
  If[projectedHolo === $Failed, Return[Unevaluated[OPEProjectedHolo[wH][Ra, opts]]]];
  spectatorAnti = spinProjectionSpectatorExpr0["Anti", ops];
  postProcessProjectedOPE0[spinProjectionOverallSign0[ops] multiplyFactors[projectedHolo, spectatorAnti]]
];

OPEProjectedAntiHolo[wA_][Ra__ /; (And @@ (RTest /@ {Ra}) && !AnyTrue[{Ra}, hasCollapsable] && sectorHasSpinFieldQ0["Anti", {Ra}]), opts___Rule] := Module[
  {seed, ops = {Ra}, spectatorHolo, projectedAnti},
  seed = Replace[Lookup[Association[Join[Options[OPEProjected], {opts}]], "RandomSeed", Automatic], Automatic -> spinProjectionCompiledSeed];
  projectedAnti = spinProjectionSectorExpr0["Anti", ops, wA, seed];
  If[projectedAnti === $Failed, Return[Unevaluated[OPEProjectedAntiHolo[wA][Ra, opts]]]];
  spectatorHolo = spinProjectionSpectatorExpr0["Holo", ops];
  postProcessProjectedOPE0[spinProjectionOverallSign0[ops] multiplyFactors[spectatorHolo, projectedAnti]]
];

OPEProjected[wH_, wA_][Ra__ /; (And @@ (RTest /@ {Ra}) && AnyTrue[{Ra}, hasSpinFieldQ]), opts___Rule] := Module[
  {seed, artifacts, hExpr, aExpr},
  seed = Replace[Lookup[Association[Join[Options[OPEProjected], {opts}]], "RandomSeed", Automatic], Automatic -> spinProjectionCompiledSeed];
  artifacts = buildProjectedArtifacts[{Ra}, wH, wA, seed];
  hExpr = sectorExprFromArtifact0[artifacts["Holo"], seed];
  If[hExpr === $Failed, Return[Unevaluated[OPEProjected[wH, wA][Ra]]]];
  aExpr = sectorExprFromArtifact0[artifacts["Anti"], seed];
  If[aExpr === $Failed, Return[Unevaluated[OPEProjected[wH, wA][Ra]]]];
  postProcessProjectedOPE0[artifacts["Sign"] combineChiral[hExpr, aExpr]]
];

OPEProjected[wH_, wA_][Ra__ /; (And @@ (RTest /@ {Ra}) && !AnyTrue[{Ra}, hasCollapsable] && !AnyTrue[{Ra}, hasSpinFieldQ])] := Module[
  {
    \[Epsilon]Holo, \[Epsilon]AntiHolo, localLists, splitLists, sign, holoOps, antiOps,
    insertionWeightHolo, insertionWeightAntiHolo, targetWeightHolo, targetWeightAntiHolo,
    projectedHolo, projectedAntiHolo
  },
  localLists = List @@ # & /@ {Ra};
  splitLists = splitOperators[#, isHolomorphic, isAntiHolomorphic] & /@ localLists;
  insertionWeightHolo = Total[totalWeightHolo /@ {Ra}];
  insertionWeightAntiHolo = Total[totalWeightAntiHolo /@ {Ra}];
  targetWeightHolo = wH - insertionWeightHolo;
  targetWeightAntiHolo = wA - insertionWeightAntiHolo;

  sign = If[Flatten[localLists] === {}, 1, factorizationSign[Flatten[localLists], isHolomorphic, isAntiHolomorphic]];

  holoOps = Select[R @@@ (splitLists[[All, 1]]), RTest];
  antiOps = Select[R @@@ (splitLists[[All, 2]]), RTest];

  projectedHolo = projectHolo[
    OPEWickList[rescaleR[\[Epsilon]Holo] /@ holoOps],
    targetWeightHolo, \[Epsilon]Holo
  ];
  projectedAntiHolo = projectAntiHolo[
    OPEWickList[rescaleR[\[Epsilon]AntiHolo] /@ antiOps],
    targetWeightAntiHolo, \[Epsilon]AntiHolo
  ];

  postProcessProjectedOPE0[sign combineChiral[projectedHolo, projectedAntiHolo]]
];


(* ::Section:: *)
(*End*)


End[];
EndPackage[];
