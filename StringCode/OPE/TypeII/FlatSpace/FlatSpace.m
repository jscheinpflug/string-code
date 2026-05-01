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


OPEWickList::usage = "OPEWickList[rList] folds OPEWick over a list of normal-ordered products.";
OPEWickList[rList_List] := Which[
  rList === {}, 1,
  Length[rList] === 1, First[rList],
  True, OPEWick[First[rList], OPEWickList[Rest[rList]]]
];

psiExpPhiHeads = {\[Psi], \[Psi]t, d\[Phi], d\[Phi]t, exp\[Phi]b, exp\[Phi]f, exp\[Phi]tb, exp\[Phi]tf};
purePsiExpPhiQ::usage = "purePsiExpPhiQ[Ra] is True when Ra contains only ψ/∂ϕ/expϕ TypeII fields handled by the bosonized free-field OPE path.";
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

(* OPEProjected for mixed collapsable + spin fields *)
(* Handles cases where operators contain both ghosts (c, b) and spin fields (S, St) *)
OPEProjected[wH_, wA_][Ra__ /; (And @@ (RTest /@ {Ra}) && AnyTrue[{Ra}, hasSpinFieldQ] && AnyTrue[{Ra}, hasCollapsable]), opts___Rule] := Module[
  {
    seed, collPieces, collR, restR,
    collLists, splitLists, sign, holoOps, antiOps,
    restLists, restSplitLists, signRest, restHoloOps, restAntiOps,
    insertionWeightHolo, insertionWeightAntiHolo, targetWeightHolo, targetWeightAntiHolo,
    totalCollWeightHolo, totalCollWeightAntiHolo,
    \[Epsilon]Holo, \[Epsilon]AntiHolo,
    opeCollResultHolo, opeCollResultAntiHolo,
    minCollWeightHolo, minCollWeightAntiHolo,
    memoRestHolo, memoRestAntiHolo,
    validCollWeightsHolo, validCollWeightsAntiHolo,
    tableHolo, tableAntiHolo, holoProjected, antiHoloProjected
  },

  seed = Replace[Lookup[Association[Join[Options[OPEProjected], {opts}]], "RandomSeed", Automatic], Automatic -> spinProjectionCompiledSeed];

  (* Compute target weights *)
  insertionWeightHolo = Total[totalWeightHolo /@ {Ra}];
  insertionWeightAntiHolo = Total[totalWeightAntiHolo /@ {Ra}];
  targetWeightHolo = (wH - insertionWeightHolo) /. (h_Symbol)[__] /; MemberQ[{"dot", "der"}, SymbolName[h]] :> 0;
  targetWeightAntiHolo = (wA - insertionWeightAntiHolo) /. (h_Symbol)[__] /; MemberQ[{"dot", "der"}, SymbolName[h]] :> 0;

  (* Split operators into collapsable (ghosts) and rest (spin + matter) *)
  collPieces = splitCollapsable /@ {Ra};
  collR = Select[collPieces[[All, 1]], # =!= 1 &];
  restR = Select[collPieces[[All, 2]], # =!= 1 &];

  (* Split collapsable fields into holo/antiholo *)
  collLists = factorizeForChiralSplit /@ (List @@ # & /@ collR);
  splitLists = splitOperators[#, isHolomorphic, isAntiHolomorphic] & /@ collLists;
  sign = If[Flatten[collLists] === {}, 1,
    factorizationSign[Flatten[collLists], isHolomorphic, isAntiHolomorphic]
  ];
  holoOps = Select[R @@@ (splitLists[[All, 1]]), RTest];
  antiOps = Select[R @@@ (splitLists[[All, 2]]), RTest];

  (* Split rest fields into holo/antiholo *)
  restLists = factorizeForChiralSplit /@ (List @@ # & /@ restR);
  restSplitLists = splitOperators[#, isHolomorphic, isAntiHolomorphic] & /@ restLists;
  signRest = If[Flatten[restLists] === {}, 1,
    factorizationSign[Flatten[restLists], isHolomorphic, isAntiHolomorphic]
  ];
  restHoloOps = Select[R @@@ (restSplitLists[[All, 1]]), RTest];
  restAntiOps = Select[R @@@ (restSplitLists[[All, 2]]), RTest];

  (* Holomorphic sector *)
  totalCollWeightHolo = Total[totalWeightHolo /@ holoOps];
  opeCollResultHolo = opeOfRList[rescaleR[\[Epsilon]Holo] /@ holoOps];
  minCollWeightHolo = totalCollWeightHolo + Exponent[opeCollResultHolo // Together, \[Epsilon]Holo, Min];

  (* Memoized spin solver for holomorphic rest fields *)
  memoRestHolo[restWt_] := memoRestHolo[restWt] = Module[{artifact},
    If[restHoloOps === {},
      If[restWt == 0, 1, 0],
      If[restWt < 0,
        0,
        artifact = buildSectorArtifact["Holo", restHoloOps, restWt, seed];
        If[ToString[artifact["Mode"]] === "SpinProjectionFailure" && ToString[artifact["Reason"]] === "NoCandidates",
          0,
          sectorExprFromArtifact0[artifact, seed]
        ]
      ]
    ]
  ];

  (* Pre-filter valid collapsable weights: must yield non-negative rest weights *)
  validCollWeightsHolo = Select[
    Range[minCollWeightHolo, targetWeightHolo],
    targetWeightHolo - # >= 0 &
  ];

  tableHolo = Table[
    Module[{collRes = projectHolo[opeCollResultHolo, collWt - totalCollWeightHolo, \[Epsilon]Holo]},
      If[collRes === 0, 0, multiplyFactors[collRes, memoRestHolo[targetWeightHolo - collWt]]]
    ],
    {collWt, validCollWeightsHolo}
  ];
  holoProjected = Total[tableHolo];

  (* Antiholomorphic sector *)
  totalCollWeightAntiHolo = Total[totalWeightAntiHolo /@ antiOps];
  opeCollResultAntiHolo = opeOfRList[rescaleR[\[Epsilon]AntiHolo] /@ antiOps];
  minCollWeightAntiHolo = totalCollWeightAntiHolo + Exponent[opeCollResultAntiHolo // Together, \[Epsilon]AntiHolo, Min];

  (* Memoized spin solver for antiholomorphic rest fields *)
  memoRestAntiHolo[restWt_] := memoRestAntiHolo[restWt] = Module[{artifact},
    If[restAntiOps === {},
      If[restWt == 0, 1, 0],
      If[restWt < 0,
        0,
        artifact = buildSectorArtifact["Anti", restAntiOps, restWt, seed];
        If[ToString[artifact["Mode"]] === "SpinProjectionFailure" && ToString[artifact["Reason"]] === "NoCandidates",
          0,
          sectorExprFromArtifact0[artifact, seed]
        ]
      ]
    ]
  ];

  (* Pre-filter valid collapsable weights: must yield non-negative rest weights *)
  validCollWeightsAntiHolo = Select[
    Range[minCollWeightAntiHolo, targetWeightAntiHolo],
    targetWeightAntiHolo - # >= 0 &
  ];

  tableAntiHolo = Table[
    Module[{collRes = projectAntiHolo[opeCollResultAntiHolo, collWt - totalCollWeightAntiHolo, \[Epsilon]AntiHolo]},
      If[collRes === 0, 0, multiplyFactors[collRes, memoRestAntiHolo[targetWeightAntiHolo - collWt]]]
    ],
    {collWt, validCollWeightsAntiHolo}
  ];
  antiHoloProjected = Total[tableAntiHolo];

  sign signRest combineChiral[holoProjected, antiHoloProjected]
];

(* OPEProjected for pure spin fields (no collapsable) *)
OPEProjected[wH_, wA_][Ra__ /; (And @@ (RTest /@ {Ra}) && AnyTrue[{Ra}, hasSpinFieldQ] && !AnyTrue[{Ra},hasCollapsable]), opts___Rule] := Module[
  {seed, artifacts, hExpr, aExpr},
  seed = Replace[Lookup[Association[Join[Options[OPEProjected], {opts}]], "RandomSeed", Automatic], Automatic -> spinProjectionCompiledSeed];
  artifacts = buildProjectedArtifacts[{Ra}, wH, wA, seed];
  hExpr = sectorExprFromArtifact0[artifacts["Holo"], seed];
  If[hExpr === $Failed, Return[Unevaluated[OPEProjected[wH, wA][Ra]]]];
  aExpr = sectorExprFromArtifact0[artifacts["Anti"], seed];
  If[aExpr === $Failed, Return[Unevaluated[OPEProjected[wH, wA][Ra]]]];
  artifacts["Sign"] combineChiral[hExpr, aExpr]
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

  sign combineChiral[projectedHolo, projectedAntiHolo]
];

(* OPEProjectedHolo for mixed collapsable + spin fields *)
(* Handles holomorphic operators containing both ghosts (c, b) and spin fields (S) *)
OPEProjectedHolo[wH_][Ra__ /; (And @@ (RTest /@ {Ra}) && AnyTrue[{Ra}, hasSpinFieldQ] && AnyTrue[{Ra}, hasCollapsable]), opts___Rule] := Module[
  {
    seed, collPieces, collR, restR,
    insertionWeightHolo, targetWeightHolo,
    totalCollWeightHolo, \[Epsilon]Holo,
    opeCollResultHolo, minCollWeightHolo,
    memoRestHolo, validCollWeightsHolo,
    tableHolo
  },

  seed = Replace[Lookup[Association[Join[Options[OPEProjected], {opts}]], "RandomSeed", Automatic], Automatic -> spinProjectionCompiledSeed];

  (* Compute target weight *)
  insertionWeightHolo = Total[totalWeightHolo /@ {Ra}];
  targetWeightHolo = (wH - insertionWeightHolo) /. (h_Symbol)[__] /; MemberQ[{"dot", "der"}, SymbolName[h]] :> 0;

  (* Split operators into collapsable (ghosts) and rest (spin fields) *)
  collPieces = splitCollapsable /@ {Ra};
  collR = Select[collPieces[[All, 1]], # =!= 1 &];
  restR = Select[collPieces[[All, 2]], # =!= 1 &];

  (* Holomorphic collapsable OPE *)
  totalCollWeightHolo = Total[totalWeightHolo /@ collR];
  opeCollResultHolo = opeOfRList[rescaleR[\[Epsilon]Holo] /@ collR];
  minCollWeightHolo = totalCollWeightHolo + Exponent[opeCollResultHolo // Together, \[Epsilon]Holo, Min];

  (* Memoized spin solver for rest fields *)
  memoRestHolo[restWt_] := memoRestHolo[restWt] = Module[{artifact},
    If[restR === {},
      If[restWt == 0, 1, 0],
      If[restWt < 0,
        0,
        artifact = buildSectorArtifact["Holo", restR, restWt, seed];
        If[ToString[artifact["Mode"]] === "SpinProjectionFailure" && ToString[artifact["Reason"]] === "NoCandidates",
          0,
          sectorExprFromArtifact0[artifact, seed]
        ]
      ]
    ]
  ];

  (* Pre-filter valid collapsable weights *)
  validCollWeightsHolo = Select[
    Range[minCollWeightHolo, targetWeightHolo],
    targetWeightHolo - # >= 0 &
  ];

  tableHolo = Table[
    Module[{collRes = projectHolo[opeCollResultHolo, collWt - totalCollWeightHolo, \[Epsilon]Holo]},
      If[collRes === 0, 0, multiplyFactors[collRes, memoRestHolo[targetWeightHolo - collWt]]]
    ],
    {collWt, validCollWeightsHolo}
  ];
  Total[tableHolo]
];

(* OPEProjectedAntiHolo for mixed collapsable + spin fields *)
(* Handles antiholomorphic operators containing both ghosts (ct, bt) and spin fields (St) *)
OPEProjectedAntiHolo[wA_][Ra__ /; (And @@ (RTest /@ {Ra}) && AnyTrue[{Ra}, hasSpinFieldQ] && AnyTrue[{Ra}, hasCollapsable]), opts___Rule] := Module[
  {
    seed, collPieces, collR, restR,
    insertionWeightAntiHolo, targetWeightAntiHolo,
    totalCollWeightAntiHolo, \[Epsilon]AntiHolo,
    opeCollResultAntiHolo, minCollWeightAntiHolo,
    memoRestAntiHolo, validCollWeightsAntiHolo,
    tableAntiHolo
  },

  seed = Replace[Lookup[Association[Join[Options[OPEProjected], {opts}]], "RandomSeed", Automatic], Automatic -> spinProjectionCompiledSeed];

  (* Compute target weight *)
  insertionWeightAntiHolo = Total[totalWeightAntiHolo /@ {Ra}];
  targetWeightAntiHolo = (wA - insertionWeightAntiHolo) /. (h_Symbol)[__] /; MemberQ[{"dot", "der"}, SymbolName[h]] :> 0;

  (* Split operators into collapsable (ghosts) and rest (spin fields) *)
  collPieces = splitCollapsable /@ {Ra};
  collR = Select[collPieces[[All, 1]], # =!= 1 &];
  restR = Select[collPieces[[All, 2]], # =!= 1 &];

  (* Antiholomorphic collapsable OPE *)
  totalCollWeightAntiHolo = Total[totalWeightAntiHolo /@ collR];
  opeCollResultAntiHolo = opeOfRList[rescaleR[\[Epsilon]AntiHolo] /@ collR];
  minCollWeightAntiHolo = totalCollWeightAntiHolo + Exponent[opeCollResultAntiHolo // Together, \[Epsilon]AntiHolo, Min];

  (* Memoized spin solver for rest fields *)
  memoRestAntiHolo[restWt_] := memoRestAntiHolo[restWt] = Module[{artifact},
    If[restR === {},
      If[restWt == 0, 1, 0],
      If[restWt < 0,
        0,
        artifact = buildSectorArtifact["Anti", restR, restWt, seed];
        If[ToString[artifact["Mode"]] === "SpinProjectionFailure" && ToString[artifact["Reason"]] === "NoCandidates",
          0,
          sectorExprFromArtifact0[artifact, seed]
        ]
      ]
    ]
  ];

  (* Pre-filter valid collapsable weights *)
  validCollWeightsAntiHolo = Select[
    Range[minCollWeightAntiHolo, targetWeightAntiHolo],
    targetWeightAntiHolo - # >= 0 &
  ];

  tableAntiHolo = Table[
    Module[{collRes = projectAntiHolo[opeCollResultAntiHolo, collWt - totalCollWeightAntiHolo, \[Epsilon]AntiHolo]},
      If[collRes === 0, 0, multiplyFactors[collRes, memoRestAntiHolo[targetWeightAntiHolo - collWt]]]
    ],
    {collWt, validCollWeightsAntiHolo}
  ];
  Total[tableAntiHolo]
];


(* ::Section:: *)
(*End*)


End[];
EndPackage[];
