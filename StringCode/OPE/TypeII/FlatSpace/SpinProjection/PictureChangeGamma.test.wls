PrependTo[$Path, Nest[DirectoryName, $InputFileName, 6]];
Needs["StringCode`"];
InitStringCode[<|"theory" -> "TypeII", "CFT" -> "FlatSpace",
  "conventions" -> "TypeII-Ashoke", "bracket" -> "Flat"|>];

pictureGammaChecks = {};
pictureGammaCheck::usage = "pictureGammaCheck records a Boolean check for the antichiral picture-change OPE.";
pictureGammaCheck[label_, result_] := (
  AppendTo[pictureGammaChecks, TrueQ[result]];
  Print[label, ": ", TrueQ[result]]
);

pictureGammaDressedFermion = R[exp\[Phi]tf[1, zz], \[Psi]t[mu, 0, zz]];
pictureGammaGroundSpin = R[St[{beta, "antichiral"}, -1/2, {}, 0, 0]];
pictureGammaOps = {pictureGammaDressedFermion, pictureGammaGroundSpin};
pictureGammaResult = OPEProjectedAntiHolo[0] @@ pictureGammaOps;
pictureGammaSolve = Private`spinProjectionLastSolveResult;
pictureGammaArtifact = StringCode`OPE`TypeII`FlatSpace`SpinProjection`Compile`buildSectorArtifact[
  "Anti", pictureGammaOps, 0, Private`spinProjectionCompiledSeed
];

pictureGammaCheck["The projected OPE emits the picture-change gamma block and passes validation",
  !FreeQ[pictureGammaResult, GammaRamondPictureHold[]] && TrueQ[pictureGammaSolve["ValidationPassedQ"]]];

pictureGammaCheck["All 160 components agree with the directly bosonized OPE",
  TrueQ[pictureGammaSolve["ValidationPassedQ"]] && And @@ Flatten[Table[
    With[{assignment = {{spin}, {vec}}},
      Expand[
        Private`spinProjectionSectorEvaluation["Anti", 0,
          Private`spinProjectionConcreteInputs[pictureGammaArtifact, assignment]] -
        Private`spinProjectionValidationPrediction0[
          pictureGammaArtifact, pictureGammaSolve["CoeffVector"], assignment]
      ] === 0
    ],
    {spin, 16}, {vec, 10}
  ]]];

pictureGammaLegacy = OPEProjectedAntiHolo[0][
  R[exp\[Phi]tf[-1, zz], \[Psi]t[mu, 0, zz]],
  R[St[{beta, "antichiral"}, -3/2, {}, 0, 0]]
];
pictureGammaCheck["The reference picture pair uses the original GammaUD",
  !FreeQ[pictureGammaLegacy, GammaUDHold[mu]] && FreeQ[pictureGammaLegacy, GammaRamondPictureHold[]] &&
    TrueQ[Private`spinProjectionLastSolveResult["ValidationPassedQ"]]];

pictureGammaAfterNS = OPEProjectedAntiHolo[1][
  R[St[{beta, "antichiral"}, -1/2, {}, 0, zz]],
  R[exp\[Phi]tf[-1, 0], \[Psi]t[mu, 0, 0]]
];
pictureGammaCheck["The reversed picture -1 fermion OPE uses the adjusted GammaUD",
  !FreeQ[pictureGammaAfterNS, {GammaUDHold[mu], GammaRamondPictureHold[]}] &&
    TrueQ[Private`spinProjectionLastSolveResult["ValidationPassedQ"]]];

pictureGammaAfterRaise = OPEProjectedAntiHolo[1][
  pictureGammaDressedFermion,
  R[St[{beta, "chiral"}, -3/2, {}, 0, 0]]
];
pictureGammaCheck["Picture raising the intermediate state uses the adjusted GammaDU",
  !FreeQ[pictureGammaAfterRaise, {GammaDUHold[mu], GammaRamondPictureHold[]}] &&
    TrueQ[Private`spinProjectionLastSolveResult["ValidationPassedQ"]]];

pictureGammaPair = OPEProjectedAntiHolo[1][
  pictureGammaGroundSpin,
  R[St[{alpha, "antichiral"}, -1/2, {}, 0, zz]]
];
pictureGammaCheck["The pair of antichiral picture -1/2 spin fields uses the adjusted rank-one chain",
  !FreeQ[pictureGammaPair, {CDUHold, _GammaUDHold, GammaAntichiralPairPictureHold[]}] &&
    TrueQ[Private`spinProjectionLastSolveResult["ValidationPassedQ"]]];

pictureGammaPairWithGhost = OPEProjectedAntiHolo[0][
  pictureGammaGroundSpin,
  R[St[{alpha, "antichiral"}, -1/2, {}, 0, zz]],
  R[exp\[Phi]tb[-2, 1]]
];
pictureGammaCheck["The pair with a ghost insertion uses the adjusted rank-three chain",
  !FreeQ[pictureGammaPairWithGhost, {CDUHold, _GammaUDHold, _GammaDUHold, _GammaUDHold,
      GammaAntichiralPairPictureHold[]}] && TrueQ[Private`spinProjectionLastSolveResult["ValidationPassedQ"]]];

pictureGammaFlux = R[ProfileX[F[alpha, beta], {}, 0, 0], c[0, 0], ct[0, 0],
  S[{alpha, "chiral"}, -1/2, {}, 0, 0], St[{beta, "antichiral"}, -1/2, {}, 0, 0]];
pictureGammaBRST = actBRST[pictureGammaFlux];
pictureGammaCheck["The profiled opposite-chirality RR vertex has a valid BRST image",
  FreeQ[pictureGammaBRST, $Failed | $Aborted] && !FreeQ[pictureGammaBRST, GammaRamondPictureHold[]]];

pictureGammaPCO = Private`actPCOAntiHoloAtPos[pictureGammaFlux];
pictureGammaCheck["Antiholomorphic picture raising uses the same table",
  FreeQ[pictureGammaPCO, $Failed | $Aborted] && !FreeQ[pictureGammaPCO, GammaRamondPictureHold[]]];

Exit[If[And @@ pictureGammaChecks, 0, 1]];
