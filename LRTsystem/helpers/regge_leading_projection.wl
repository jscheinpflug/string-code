(* Load after InitStringCode in the notebook's existing kernel.
   This computes one supplied gauge half, with no scalar/heat substitutions. *)
BeginPackage["KonishiReggeProjection`", {
  "StringCode`NormalOrdering`", "StringCode`Symbols`",
  "StringCode`Symbols`TypeII`", "StringCode`Symbols`TypeII`FlatSpace`",
  "StringCode`Brackets`"
}];

ReggeLeadingHalf::usage = "ReggeLeadingHalf[gaugeHalf, seed, n] computes the leading psi (dX)^n times barred-psi (barred-dX)^n component of EffectiveBracket[gaugeHalf, seed, n, n]. seed must be a single leading Regge vertex with 2 n + 2 profile slots. Both pre-b0-minus ghost representatives are retained after picture changing. Scalar factors and derivative orders are unchanged; the package hook is restored even on abort. This does not compute auxiliary output components or add the other gauge half.";
ReggeLeadingHalf::init = "Initialize StringCode before loading and using this helper.";
ReggeLeadingHalf::seed = "The seed must be a single leading Regge vertex at level `1`, with one ProfileX carrying `2` tensor slots.";

Begin["`Private`"];

reggeSignature::usage = "reggeSignature records non-profile oscillator heads and derivative orders, ignoring only matter Lorentz labels.";
reggeSignature[reggeWord_R] := Sort[
  (If[MatchQ[#, (dX | dXt | \[Psi] | \[Psi]t)[_, _, _]],
      {Head[#], #[[2]], #[[3]]}, #] &) /@
    Select[List @@ reggeWord,
      !StringStartsQ[SymbolName[Head[#]], "ProfileX"] &]
];

reggeChiralTargets::usage = "reggeChiralTargets gives the leading chiral family with and without the derivative-c ghost needed before b0-minus.";
reggeChiralTargets[reggeLevel_Integer, reggeAnti_] := Module[
  {reggeCore, reggeGhost},
  {reggeCore, reggeGhost} = If[TrueQ[reggeAnti],
    {Join[{ct[0, 0], exp\[Phi]tf[-1, 0], \[Psi]t[reggeSlot, 0, 0]},
      Table[dXt[reggeSlot, 0, 0], {reggeLevel}]], ct[1, 0]},
    {Join[{c[0, 0], exp\[Phi]f[-1, 0], \[Psi][reggeSlot, 0, 0]},
      Table[dX[reggeSlot, 0, 0], {reggeLevel}]], c[1, 0]}
  ];
  (* Build signatures from lists: repeated placeholder indices must never
     be evaluated as an R vertex and trigger tensor contractions. *)
  Sort[(If[MatchQ[#, (dX | dXt | \[Psi] | \[Psi]t)[_, _, _]],
       {Head[#], #[[2]], #[[3]]}, #] &) /@ #] & /@
    {reggeCore, Append[reggeCore, reggeGhost]}
];

reggeKeep::usage = "reggeKeep projects only oscillator words, leaving all scalar coefficients and profile derivatives intact.";
reggeKeep[reggeExpr_, reggeTargets_List] := reggeExpr /.
  (reggeWord_R /; !MemberQ[reggeTargets, reggeSignature[reggeWord]]) :> 0;

ReggeLeadingHalf[reggeGauge_, reggeSeed_, reggeLevel_Integer?Positive] := Module[
  {reggeHolo, reggeAnti, reggeFinal, reggeSeedWords, reggeProfiles,
   reggeSaved, reggeOriginal, reggeResult},
  If[DownValues[Private`combineProjectedBracketChiral] === {},
    Message[ReggeLeadingHalf::init]; Return[$Failed]];
  reggeHolo = reggeChiralTargets[reggeLevel, False];
  reggeAnti = reggeChiralTargets[reggeLevel, True];
  reggeFinal = Sort[Join[First[reggeHolo], First[reggeAnti]]];
  reggeSeedWords = Cases[reggeSeed, _R, {0, Infinity}];
  If[Length[reggeSeedWords] =!= 1 ||
      reggeSignature[First[reggeSeedWords]] =!= reggeFinal,
    Message[ReggeLeadingHalf::seed, reggeLevel, 2 reggeLevel + 2];
    Return[$Failed]];
  reggeProfiles = Cases[List @@ First[reggeSeedWords], _ProfileX];
  If[Length[reggeProfiles] =!= 1 ||
      AtomQ[reggeProfiles[[1, 1]]] ||
      Length[reggeProfiles[[1, 1]]] =!= 2 reggeLevel + 2,
    Message[ReggeLeadingHalf::seed, reggeLevel, 2 reggeLevel + 2];
    Return[$Failed]];
  reggeSaved = DownValues[Private`combineProjectedBracketChiral];
  DownValues[reggeOriginal] = reggeSaved /.
    Private`combineProjectedBracketChiral -> reggeOriginal;
  Internal`WithLocalSettings[
    (Private`combineProjectedBracketChiral[reggeH_, reggeA_] :=
       reggeOriginal[reggeKeep[reggeH, reggeHolo],
                     reggeKeep[reggeA, reggeAnti]]),
    (reggeResult = EffectiveBracket[reggeGauge, reggeSeed,
                                    reggeLevel, reggeLevel];
     If[reggeResult === $Failed, $Failed,
       reggeKeep[reggeResult, {reggeFinal}]]),
    (DownValues[Private`combineProjectedBracketChiral] = reggeSaved;
     Clear[reggeOriginal])
  ]
];

End[];
EndPackage[];
