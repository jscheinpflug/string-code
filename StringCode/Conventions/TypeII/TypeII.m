(* ::Package:: *)

BeginPackage["StringCode`Conventions`TypeII`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`TypeII`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];

\[Alpha]pValue::usage="Value of \[Alpha] prime";
fermionToBosonWickRatio::usage ="Defines the ratio of coefficients in  partial X partial X and psi psi OPEs";
psiSCoefficient::usage = "Defines the coefficient multiplying the mixed gamma matrix in the bosonized e^-phi psi with e^-phi/2 S OPE.";
psiSdotCoefficient::usage = "psiSdotCoefficient is the derived coefficient multiplying the mixed gamma matrix in the bosonized e^-phi psi with e^-3phi/2 Sdot OPE.";
SSdotCoefficient::usage = "SSdotCoefficient is the derived coefficient multiplying the chiral-antichiral pairing matrix in the bosonized e^-phi/2 S with e^-3phi/2 Sdot OPE.";

\[Beta]ghost::usage = "Defines the holomorphic \[Beta]-ghost";
\[Gamma]ghost::usage = "Defines the holomorphic \[Gamma]-ghost";
\[Delta]\[Beta]ghost::usage = "Defines the holomorphic delta distribution of the \[Beta]-ghost";
\[Delta]\[Gamma]ghost::usage = "Defines the holomorphic delta distribution of the \[Gamma]-ghost";

\[Beta]ghostbar::usage = "Defines the antiholomorphic \[Beta]-ghost";
\[Gamma]ghostbar::usage = "Defines the antiholomorphic \[Gamma]-ghost";
\[Delta]\[Beta]ghostbar::usage = "Defines the antiholomorphic delta distribution of the \[Beta]-ghost";
\[Delta]\[Gamma]ghostbar::usage = "Defines the antiholomorphic delta distribution of the \[Gamma]-ghost";

Tmatter::usage = "Defines the holomorphic matter CFT stress tensor";
Gmatter::usage = "Defines the holomorphic matter CFT supercurrent";
Tghost::usage = "Defines the holomorphic ghost CFT stress tensor";
Gghost::usage = "Defines the holomorphic ghost CFT supercurrent";
Ttotal::usage = "Defines the total holomorphic CFT stress tensor";
Gtotal::usage = "Defines the total holomorphic CFT supercurrent";

Tmatterbar::usage = "Defines the antiholomorphic matter CFT stress tensor";
Gmatterbar::usage = "Defines the antiholomorphic matter CFT supercurrent";
Tghostbar::usage = "Defines the antiholomorphic ghost CFT stress tensor";
Gghostbar::usage = "Defines the antiholomorphic ghost CFT supercurrent";
Ttotalbar::usage = "Defines the total antiholomorphic CFT stress tensor";
Gtotalbar::usage = "Defines the total antiholomorphic CFT supercurrent";
jBRST::usage = "Defines the string theory BRST current";
jBRSTNoTD::usage = "Defines the string theory BRST current without total derivative term";
jBRSTbar::usage = "Defines the string antiholomorphic theory BRST current";
jBRSTbarNoTD::usage = "Defines the string antiholomorphic theory BRST current without total derivative term";
PCO::usage = "Defines the holomorphic PCO";
PCObar::usage = "Defines the antiholomorphic PCO";


Begin["Private`"]

rawBosonizedFermionToBosonWickRatio::usage =
  "rawBosonizedFermionToBosonWickRatio is the psi-psi coefficient in the convention-blind raw TypeII bosonization basis.";
rawBosonizedFermionToBosonWickRatio = 1;

rawBosonizedPsiSCoefficient::usage =
  "rawBosonizedPsiSCoefficient is the coefficient of the bosonized e^-phi psi with e^-phi/2 S OPE in the convention-blind raw TypeII bosonization basis.";
rawBosonizedPsiSCoefficient = 1/Sqrt[2];

rawBosonizedPsiSdotCoefficient::usage =
  "rawBosonizedPsiSdotCoefficient is the coefficient of the bosonized e^-phi psi with e^-3phi/2 Sdot OPE in the convention-blind raw TypeII bosonization basis.";
rawBosonizedPsiSdotCoefficient = -I/Sqrt[2];

rawBosonizedSSdotCoefficient::usage =
  "rawBosonizedSSdotCoefficient is the coefficient of the bosonized e^-phi/2 S with e^-3phi/2 Sdot OPE in the convention-blind raw TypeII bosonization basis.";
rawBosonizedSSdotCoefficient = 1;

exactConventionEqualityQ::usage =
  "exactConventionEqualityQ[left, right] is True when the two convention expressions agree exactly after exact simplification.";
exactConventionEqualityQ[left_, right_] := TrueQ[Simplify[left == right]];

typeIIBosonizationScaleData::usage =
  "typeIIBosonizationScaleData[fermionRatio, psiS] returns the exact bosonized TypeII state-normalization scales implied by the declared convention coefficients, or $Failed if the data are inconsistent.";
typeIIBosonizationScaleData[
  fermionRatio_,
  psiS_
] := typeIIBosonizationScaleData[fermionRatio, psiS] = Module[
  {
    psiScaleSquared,
    psiScale,
    chiralSpinScale,
    antichiralSpinScale,
    reconstructedFermionRatio,
    reconstructedPsiS,
    reconstructedPsiSdot
  },
  psiScaleSquared = fermionRatio/rawBosonizedFermionToBosonWickRatio;
  psiScale = Sqrt[psiScaleSquared];
  chiralSpinScale = 1;
  antichiralSpinScale = rawBosonizedPsiSCoefficient psiScale/psiS;
  reconstructedFermionRatio = rawBosonizedFermionToBosonWickRatio psiScale^2;
  reconstructedPsiS = rawBosonizedPsiSCoefficient psiScale chiralSpinScale/antichiralSpinScale;
  reconstructedPsiSdot = rawBosonizedPsiSdotCoefficient psiScale antichiralSpinScale/chiralSpinScale;
  If[
    !And[
      exactConventionEqualityQ[reconstructedFermionRatio, fermionRatio],
      exactConventionEqualityQ[reconstructedPsiS, psiS]
    ],
    Message[
      typeIIBosonizationScaleData::reconstruction,
      fermionRatio,
      psiS,
      reconstructedFermionRatio,
      reconstructedPsiS
    ];
    Return[$Failed]
  ];
  <|
    "Psi" -> psiScale,
    "ChiralSpin" -> chiralSpinScale,
    "AntichiralSpin" -> antichiralSpinScale,
    "PsiSdotCoefficient" -> reconstructedPsiSdot,
    "SSdotCoefficient" -> rawBosonizedSSdotCoefficient chiralSpinScale antichiralSpinScale
  |>
];

typeIIBosonizationScaleData::inconsistent =
  "The TypeII bosonization convention data are inconsistent.";

typeIIBosonizationScaleData::reconstruction =
  "The TypeII bosonization convention data could not be reconstructed exactly from the solved bosonization scales. Requested {fermionToBosonWickRatio, psiSCoefficient} = {`1`, `2`} but reconstructed {`3`, `4`}."; 

currentTypeIIBosonizationScaleData::usage =
  "currentTypeIIBosonizationScaleData[] returns the exact bosonized TypeII state-normalization scales implied by the currently loaded convention module.";
currentTypeIIBosonizationScaleData[] :=
  typeIIBosonizationScaleData[
    fermionToBosonWickRatio,
    psiSCoefficient
  ];

psiBosonizationScale::usage =
  "psiBosonizationScale[] returns the exact normalization multiplier applied to bosonized psi and psit states in the current TypeII convention.";
psiBosonizationScale[] := Module[{scaleData = currentTypeIIBosonizationScaleData[]},
  If[scaleData === $Failed, Return[$Failed]];
  scaleData["Psi"]
];

chiralSpinBosonizationScale::usage =
  "chiralSpinBosonizationScale[] returns the exact normalization multiplier applied to bosonized chiral Ramond ground states in the current TypeII convention.";
chiralSpinBosonizationScale[] := Module[{scaleData = currentTypeIIBosonizationScaleData[]},
  If[scaleData === $Failed, Return[$Failed]];
  scaleData["ChiralSpin"]
];

antichiralSpinBosonizationScale::usage =
  "antichiralSpinBosonizationScale[] returns the exact normalization multiplier applied to bosonized antichiral Ramond ground states in the current TypeII convention.";
antichiralSpinBosonizationScale[] := Module[{scaleData = currentTypeIIBosonizationScaleData[]},
  If[scaleData === $Failed, Return[$Failed]];
  scaleData["AntichiralSpin"]
];

psiSdotCoefficient := Module[{scaleData = currentTypeIIBosonizationScaleData[]},
  If[scaleData === $Failed, Return[$Failed]];
  scaleData["PsiSdotCoefficient"]
];

SSdotCoefficient := Module[{scaleData = currentTypeIIBosonizationScaleData[]},
  If[scaleData === $Failed, Return[$Failed]];
  scaleData["SSdotCoefficient"]
];

spinBosonizationScale::usage =
  "spinBosonizationScale[chirality] returns the exact normalization multiplier applied to bosonized Ramond ground states of the requested chirality.";
spinBosonizationScale["chiral"] := chiralSpinBosonizationScale[];
spinBosonizationScale["antichiral"] := antichiralSpinBosonizationScale[];
spinBosonizationScale[_] := $Failed;


End[];
EndPackage[];
