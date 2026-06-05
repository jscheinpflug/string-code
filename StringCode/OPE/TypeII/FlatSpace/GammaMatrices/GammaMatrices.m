(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`OPE`TypeII`FlatSpace`GammaMatrices`"];
Needs["StringCode`Symbols`TypeII`FlatSpace`"];


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


gammaSpinorDimension::usage =
  "gammaSpinorDimension is the canonical 16-component SO(10) spinor dimension used by the frozen TypeII flat-space gamma matrices.";
gammaSpinorDimension = 16;


gammaVectorDimension::usage =
  "gammaVectorDimension is the canonical 10-component vector dimension used by the frozen TypeII flat-space gamma matrices.";
gammaVectorDimension = 10;


validGammaIndexQ::usage =
  "validGammaIndexQ[mu] checks whether mu is a valid concrete vector index in the active TypeII FlatSpace signature.";
validGammaIndexQ[mu_Integer] := validFlatSpaceVectorIndexQ[mu];
validGammaIndexQ[_] := False;


validGammaSpinorIndexQ::usage =
  "validGammaSpinorIndexQ[alpha] checks whether alpha is a valid canonical flat-space spinor basis index between 1 and 16.";
validGammaSpinorIndexQ[alpha_Integer] := 1 <= alpha <= gammaSpinorDimension;
validGammaSpinorIndexQ[_] := False;


sparseGammaMatrixFromRules::usage =
  "sparseGammaMatrixFromRules[rules] converts a sparse 16x16 rule list into an exact SparseArray matrix.";
sparseGammaMatrixFromRules[rules_List] := SparseArray[rules, {gammaSpinorDimension, gammaSpinorDimension}];


denseGammaMatrixFromSparse::usage =
  "denseGammaMatrixFromSparse[matrix] converts one exact sparse gamma matrix into its dense Normal form.";
denseGammaMatrixFromSparse[matrix_SparseArray] := Normal[matrix];


denseGammaMatrixFromRules::usage =
  "denseGammaMatrixFromRules[rules] converts a sparse 16x16 rule list into an exact dense matrix.";
denseGammaMatrixFromRules[rules_List] := denseGammaMatrixFromSparse[sparseGammaMatrixFromRules[rules]];


gammaSparseIdentityMatrix::usage =
  "gammaSparseIdentityMatrix[dim] returns the exact dim x dim sparse identity matrix used by the frozen gamma conventions.";
gammaSparseIdentityMatrix[dim_Integer?Positive] := SparseArray[Band[{1, 1}] -> 1, {dim, dim}];

sparseGammaMatrixInverse::usage =
  "sparseGammaMatrixInverse[matrix] returns the exact sparse inverse of one frozen spinor matrix.";
sparseGammaMatrixInverse[matrix_SparseArray] := SparseArray[Inverse[Normal[matrix]]];


Get[FileNameJoin[{DirectoryName[$InputFileName], "SpinFieldConventionData.m"}]];


CUDSparseData::usage =
  "CUDSparseData is the exact sparse chiral-antichiral spinor pairing matrix extracted from the picture-dressed e^-phi/2 S with e^-3 phi/2 Sdot OPE coefficient.";
CUDSparseData = sparseGammaMatrixFromRules[CUDOPEDataRules];


CUDData::usage =
  "CUDData is the exact chiral-antichiral spinor pairing matrix extracted from the picture-dressed e^-phi/2 S with e^-3 phi/2 Sdot OPE coefficient.";
CUDData = denseGammaMatrixFromSparse[CUDSparseData];


CDUSparseData::usage =
  "CDUSparseData is the exact sparse antichiral-chiral spinor pairing matrix extracted from the picture-dressed e^-3 phi/2 Sdot with e^-phi/2 S OPE coefficient.";
CDUSparseData = sparseGammaMatrixFromRules[CDUOPEDataRules];


CUDInverseSparseData::usage =
  "CUDInverseSparseData is the exact sparse inverse of the chiral-antichiral pairing matrix.";
CUDInverseSparseData = sparseGammaMatrixInverse[CUDSparseData];


CDUInverseSparseData::usage =
  "CDUInverseSparseData is the exact sparse inverse of the antichiral-chiral pairing matrix.";
CDUInverseSparseData = sparseGammaMatrixInverse[CDUSparseData];


CDUData::usage =
  "CDUData is the exact antichiral-chiral spinor pairing matrix extracted from the picture-dressed e^-3 phi/2 Sdot with e^-phi/2 S OPE coefficient.";
CDUData = denseGammaMatrixFromSparse[CDUSparseData];


gammaUDSparseData::usage =
  "gammaUDSparseData is the exact list of ten sparse mixed chiral-to-antichiral gamma matrices extracted from the picture-dressed e^-phi psi with e^-3 phi/2 Sdot OPE coefficient.";
gammaUDSparseData = sparseGammaMatrixFromRules /@ GammaUDOPEDataRules;


gammaUDData::usage =
  "gammaUDData is the exact list of ten mixed chiral-to-antichiral gamma matrices extracted from the picture-dressed e^-phi psi with e^-3 phi/2 Sdot OPE coefficient.";
gammaUDData = denseGammaMatrixFromSparse /@ gammaUDSparseData;


gammaDUSparseData::usage =
  "gammaDUSparseData is the exact list of ten sparse mixed antichiral-to-chiral gamma matrices extracted from the picture-dressed e^-phi psi with e^-phi/2 S OPE coefficient.";
gammaDUSparseData = sparseGammaMatrixFromRules /@ GammaDUOPEDataRules;


gammaDUData::usage =
  "gammaDUData is the exact list of ten mixed antichiral-to-chiral gamma matrices extracted from the picture-dressed e^-phi psi with e^-phi/2 S OPE coefficient.";
gammaDUData = denseGammaMatrixFromSparse /@ gammaDUSparseData;


CGammaSparseData::usage =
  "CGammaSparseData is the exact list of ten sparse chiral-chiral charge-conjugated gamma matrices derived from CUD . GammaDU.";
CGammaSparseData = Table[CUDSparseData . gammaDUSparseData[[i]], {i, 1, gammaVectorDimension}];


CGammaData::usage =
  "CGammaData is the exact list of ten chiral-chiral charge-conjugated gamma matrices derived from CUD . GammaDU.";
CGammaData = denseGammaMatrixFromSparse /@ CGammaSparseData;


CIGammaSparseData::usage =
  "CIGammaSparseData is the exact list of ten sparse antichiral-antichiral charge-conjugated gamma matrices derived from CDU . GammaUD.";
CIGammaSparseData = Table[CDUSparseData . gammaUDSparseData[[i]], {i, 1, gammaVectorDimension}];


CIGammaData::usage =
  "CIGammaData is the exact list of ten antichiral-antichiral charge-conjugated gamma matrices derived from CDU . GammaUD.";
CIGammaData = denseGammaMatrixFromSparse /@ CIGammaSparseData;


gammaSparseMatrixAtActiveIndex::usage =
  "gammaSparseMatrixAtActiveIndex[data, mu] returns a stored sparse gamma matrix at active vector index mu.";
gammaSparseMatrixAtActiveIndex[data_List, mu_Integer] := Module[{pos = flatSpaceVectorIndexPosition[mu]},
  If[pos === $Failed, Return[$Failed]];
  data[[pos]]
];


gammaDenseMatrixAtActiveIndex::usage =
  "gammaDenseMatrixAtActiveIndex[data, mu] returns a stored dense gamma matrix at active vector index mu.";
gammaDenseMatrixAtActiveIndex[data_List, mu_Integer] := Module[{pos = flatSpaceVectorIndexPosition[mu]},
  If[pos === $Failed, Return[$Failed]];
  data[[pos]]
];


gammaScaledSparseMatrixAtActiveIndex::usage =
  "gammaScaledSparseMatrixAtActiveIndex[data, scale, mu] returns a signature-scaled sparse gamma matrix at active vector index mu.";
gammaScaledSparseMatrixAtActiveIndex[data_List, scale_, mu_Integer] := Module[{matrix = gammaSparseMatrixAtActiveIndex[data, mu]},
  If[matrix === $Failed || scale === $Failed, Return[$Failed]];
  scale matrix
];


gammaScaledDenseMatrixAtActiveIndex::usage =
  "gammaScaledDenseMatrixAtActiveIndex[data, scale, mu] returns a signature-scaled dense gamma matrix at active vector index mu.";
gammaScaledDenseMatrixAtActiveIndex[data_List, scale_, mu_Integer] := Module[{matrix = gammaDenseMatrixAtActiveIndex[data, mu]},
  If[matrix === $Failed || scale === $Failed, Return[$Failed]];
  scale matrix
];


GammaUDUpSparse[mu_Integer] := gammaScaledSparseMatrixAtActiveIndex[gammaUDSparseData, flatSpaceUpperGammaScale[mu], mu] /; validGammaIndexQ[mu];


GammaUDUp[mu_Integer] := gammaScaledDenseMatrixAtActiveIndex[gammaUDData, flatSpaceUpperGammaScale[mu], mu] /; validGammaIndexQ[mu];


GammaUDDownSparse[mu_Integer] := gammaScaledSparseMatrixAtActiveIndex[gammaUDSparseData, flatSpaceLowerGammaScale[mu], mu] /; validGammaIndexQ[mu];


GammaUDDown[mu_Integer] := gammaScaledDenseMatrixAtActiveIndex[gammaUDData, flatSpaceLowerGammaScale[mu], mu] /; validGammaIndexQ[mu];


GammaDUUpSparse[mu_Integer] := gammaScaledSparseMatrixAtActiveIndex[gammaDUSparseData, flatSpaceUpperGammaScale[mu], mu] /; validGammaIndexQ[mu];


GammaDUUp[mu_Integer] := gammaScaledDenseMatrixAtActiveIndex[gammaDUData, flatSpaceUpperGammaScale[mu], mu] /; validGammaIndexQ[mu];


GammaDUDownSparse[mu_Integer] := gammaScaledSparseMatrixAtActiveIndex[gammaDUSparseData, flatSpaceLowerGammaScale[mu], mu] /; validGammaIndexQ[mu];


GammaDUDown[mu_Integer] := gammaScaledDenseMatrixAtActiveIndex[gammaDUData, flatSpaceLowerGammaScale[mu], mu] /; validGammaIndexQ[mu];


CGammaUpSparse[mu_Integer] := gammaScaledSparseMatrixAtActiveIndex[CGammaSparseData, flatSpaceUpperGammaScale[mu], mu] /; validGammaIndexQ[mu];


CGammaUp[mu_Integer] := gammaScaledDenseMatrixAtActiveIndex[CGammaData, flatSpaceUpperGammaScale[mu], mu] /; validGammaIndexQ[mu];


CGammaDownSparse[mu_Integer] := gammaScaledSparseMatrixAtActiveIndex[CGammaSparseData, flatSpaceLowerGammaScale[mu], mu] /; validGammaIndexQ[mu];


CGammaDown[mu_Integer] := gammaScaledDenseMatrixAtActiveIndex[CGammaData, flatSpaceLowerGammaScale[mu], mu] /; validGammaIndexQ[mu];


CIGammaUpSparse[mu_Integer] := gammaScaledSparseMatrixAtActiveIndex[CIGammaSparseData, flatSpaceUpperGammaScale[mu], mu] /; validGammaIndexQ[mu];


CIGammaUp[mu_Integer] := gammaScaledDenseMatrixAtActiveIndex[CIGammaData, flatSpaceUpperGammaScale[mu], mu] /; validGammaIndexQ[mu];


CIGammaDownSparse[mu_Integer] := gammaScaledSparseMatrixAtActiveIndex[CIGammaSparseData, flatSpaceLowerGammaScale[mu], mu] /; validGammaIndexQ[mu];


CIGammaDown[mu_Integer] := gammaScaledDenseMatrixAtActiveIndex[CIGammaData, flatSpaceLowerGammaScale[mu], mu] /; validGammaIndexQ[mu];


CGamma[mu_Integer] := CGammaDown[mu] /; validGammaIndexQ[mu];


CGammaSparse[mu_Integer] := CGammaDownSparse[mu] /; validGammaIndexQ[mu];


CIGamma[mu_Integer] := CIGammaDown[mu] /; validGammaIndexQ[mu];


CIGammaSparse[mu_Integer] := CIGammaDownSparse[mu] /; validGammaIndexQ[mu];


GammaUD[mu_Integer] := GammaUDDown[mu] /; validGammaIndexQ[mu];


GammaUDSparse[mu_Integer] := GammaUDDownSparse[mu] /; validGammaIndexQ[mu];


GammaDU[mu_Integer] := GammaDUDown[mu] /; validGammaIndexQ[mu];


GammaDUSparse[mu_Integer] := GammaDUDownSparse[mu] /; validGammaIndexQ[mu];


CUD = CUDData;


CUDSparse = CUDSparseData;


CDU = CDUData;


CDUSparse = CDUSparseData;


Gamma11UUSparse::usage =
  "Gamma11UUSparse is the exact sparse chiral Weyl-block of the SO(10) chirality operator in the canonical TypeII flat-space basis.";
Gamma11UUSparse = gammaSparseIdentityMatrix[gammaSpinorDimension];


Gamma11UU = denseGammaMatrixFromSparse[Gamma11UUSparse];


Gamma11DDSparse::usage =
  "Gamma11DDSparse is the exact sparse antichiral Weyl-block of the SO(10) chirality operator in the canonical TypeII flat-space basis.";
Gamma11DDSparse = -gammaSparseIdentityMatrix[gammaSpinorDimension];


Gamma11DD = denseGammaMatrixFromSparse[Gamma11DDSparse];


Get[FileNameJoin[{DirectoryName[$InputFileName], "GammaProductCache.m"}]];

gammaProductLinkMatrix::usage =
  "gammaProductLinkMatrix[link] returns the exact 16x16 sparse matrix associated with one concrete gamma-link factor.";
gammaProductLinkMatrix[CUDHold] := CUDSparse;
gammaProductLinkMatrix[CDUHold] := CDUSparse;
gammaProductLinkMatrix[GammaUDHold[GammaIndexUp[mu_Integer]]] /; validGammaIndexQ[mu] := GammaUDUpSparse[mu];
gammaProductLinkMatrix[GammaUDHold[GammaIndexDown[mu_Integer]]] /; validGammaIndexQ[mu] := GammaUDDownSparse[mu];
gammaProductLinkMatrix[GammaUDHold[mu_Integer]] /; validGammaIndexQ[mu] := GammaUDDownSparse[mu];
gammaProductLinkMatrix[GammaDUHold[GammaIndexUp[mu_Integer]]] /; validGammaIndexQ[mu] := GammaDUUpSparse[mu];
gammaProductLinkMatrix[GammaDUHold[GammaIndexDown[mu_Integer]]] /; validGammaIndexQ[mu] := GammaDUDownSparse[mu];
gammaProductLinkMatrix[GammaDUHold[mu_Integer]] /; validGammaIndexQ[mu] := GammaDUDownSparse[mu];
gammaProductLinkMatrix[Gamma11UUHold[]] := Gamma11UUSparse;
gammaProductLinkMatrix[Gamma11DDHold[]] := Gamma11DDSparse;
gammaProductLinkMatrix[_] := $Failed;

gammaProductLinkIndex::usage =
  "gammaProductLinkIndex[link] returns the concrete vector index carried by one concrete gamma link, ignoring vector-index variance markers.";
gammaProductLinkIndex[GammaUDHold[GammaIndexUp[mu_]]] := mu;
gammaProductLinkIndex[GammaUDHold[GammaIndexDown[mu_]]] := mu;
gammaProductLinkIndex[GammaUDHold[mu_Integer]] := mu;
gammaProductLinkIndex[GammaDUHold[GammaIndexUp[mu_]]] := mu;
gammaProductLinkIndex[GammaDUHold[GammaIndexDown[mu_]]] := mu;
gammaProductLinkIndex[GammaDUHold[mu_Integer]] := mu;
gammaProductLinkIndex[_] := $Failed;

gammaProductLinkVariance::usage =
  "gammaProductLinkVariance[link] returns \"Up\" or \"Down\" for one concrete gamma vector link.";
gammaProductLinkVariance[GammaUDHold[GammaIndexUp[_]]] := "Up";
gammaProductLinkVariance[GammaDUHold[GammaIndexUp[_]]] := "Up";
gammaProductLinkVariance[_] := "Down";

gammaProductLinkPattern::usage =
  "gammaProductLinkPattern[link] returns the spinor-flow head and vector-index variance carried by one concrete gamma vector link.";
gammaProductLinkPattern[GammaUDHold[idx_]] := {GammaUDHold, gammaProductLinkVariance[GammaUDHold[idx]]};
gammaProductLinkPattern[GammaDUHold[idx_]] := {GammaDUHold, gammaProductLinkVariance[GammaDUHold[idx]]};
gammaProductLinkPattern[_] := $Failed;

gammaProductLinkFromPattern::usage =
  "gammaProductLinkFromPattern[pattern, mu] rebuilds one gamma vector link from a spinor-flow/variance pattern and a concrete vector index.";
gammaProductLinkFromPattern[{head_, "Up"}, mu_] := head[GammaIndexUp[mu]];
gammaProductLinkFromPattern[{head_, "Down"}, mu_] := head[GammaIndexDown[mu]];
gammaProductLinkFromPattern[head_, mu_] /; MemberQ[{GammaUDHold, GammaDUHold}, head] := head[mu];
gammaProductLinkFromPattern[_, _] := $Failed;

gammaProductAntisymmetrizedMatrixFromPattern::usage =
  "gammaProductAntisymmetrizedMatrixFromPattern[linkPatterns, inds] antisymmetrizes vector labels while preserving the ordered spinor-flow and vector-variance pattern.";
gammaProductAntisymmetrizedMatrixFromPattern[{}, {}] := gammaSparseIdentityMatrix[gammaSpinorDimension];
gammaProductAntisymmetrizedMatrixFromPattern[linkPatterns_List, inds_List] /; Length[linkPatterns] === Length[inds] :=
  gammaProductAntisymmetrizedMatrixFromPattern[flatSpaceSignatureName[], linkPatterns, inds];
gammaProductAntisymmetrizedMatrixFromPattern[signature_String, {}, {}] := gammaSparseIdentityMatrix[gammaSpinorDimension];
gammaProductAntisymmetrizedMatrixFromPattern[signature_String, linkPatterns_List, inds_List] /; Length[linkPatterns] === Length[inds] :=
  gammaProductAntisymmetrizedMatrixFromPattern[signature, linkPatterns, inds] = Module[{rank = Length[inds]},
    1/rank Sum[
      (-1)^(pos - 1) gammaProductLinkMatrix[gammaProductLinkFromPattern[First[linkPatterns], inds[[pos]]]] .
        gammaProductAntisymmetrizedMatrixFromPattern[signature, Rest[linkPatterns], Delete[inds, pos]],
      {pos, 1, rank}
    ]
  ];

gammaProductLinkLabelSpec::usage =
  "gammaProductLinkLabelSpec[link] returns {variance, index} for the vector label carried by one concrete gamma link.";
gammaProductLinkLabelSpec[link : GammaUDHold[_]] := {gammaProductLinkVariance[link], gammaProductLinkIndex[link]};
gammaProductLinkLabelSpec[link : GammaDUHold[_]] := {gammaProductLinkVariance[link], gammaProductLinkIndex[link]};
gammaProductLinkLabelSpec[_] := $Failed;

gammaProductAntisymmetrizedMatrixFromLabelSpecs::usage =
  "gammaProductAntisymmetrizedMatrixFromLabelSpecs[heads, labelSpecs] antisymmetrizes vector labels while preserving slot spinor-flow heads and label variances.";
gammaProductAntisymmetrizedMatrixFromLabelSpecs[{}, {}] := gammaSparseIdentityMatrix[gammaSpinorDimension];
gammaProductAntisymmetrizedMatrixFromLabelSpecs[heads_List, labelSpecs_List] /; Length[heads] === Length[labelSpecs] :=
  gammaProductAntisymmetrizedMatrixFromLabelSpecs[flatSpaceSignatureName[], heads, labelSpecs];
gammaProductAntisymmetrizedMatrixFromLabelSpecs[signature_String, {}, {}] := gammaSparseIdentityMatrix[gammaSpinorDimension];
gammaProductAntisymmetrizedMatrixFromLabelSpecs[signature_String, heads_List, labelSpecs_List] /; Length[heads] === Length[labelSpecs] :=
  gammaProductAntisymmetrizedMatrixFromLabelSpecs[signature, heads, labelSpecs] = Module[
    {rank = Length[labelSpecs], linkMatrix, restMatrix, terms, link},
    terms = Table[
      link = gammaProductLinkFromPattern[{First[heads], labelSpecs[[pos, 1]]}, labelSpecs[[pos, 2]]];
      linkMatrix = gammaProductLinkMatrix[link];
      restMatrix = gammaProductAntisymmetrizedMatrixFromLabelSpecs[signature, Rest[heads], Delete[labelSpecs, pos]];
      If[link === $Failed || linkMatrix === $Failed || restMatrix === $Failed, Return[$Failed]];
      (-1)^(pos - 1) linkMatrix . restMatrix,
      {pos, 1, rank}
    ];
    Total[terms]/rank
  ];

gammaProductAntisymmetrizedMatrix::usage =
  "gammaProductAntisymmetrizedMatrix[vectorLinks] returns the exact sparse antisymmetrized gamma matrix for one concrete vector-link list.";
gammaProductAntisymmetrizedMatrix[{}] := gammaSparseIdentityMatrix[gammaSpinorDimension];
gammaProductAntisymmetrizedMatrix[vectorLinks_List] := gammaProductAntisymmetrizedMatrix[flatSpaceSignatureName[], vectorLinks];
gammaProductAntisymmetrizedMatrix[signature_String, {}] := gammaSparseIdentityMatrix[gammaSpinorDimension];
gammaProductAntisymmetrizedMatrix[signature_String, vectorLinks_List] := gammaProductAntisymmetrizedMatrix[signature, vectorLinks] = Module[
  {linkPatterns, heads, labelSpecs},
  If[!AllTrue[vectorLinks, MatchQ[#, GammaUDHold[_] | GammaDUHold[_]] &], Return[$Failed]];
  linkPatterns = gammaProductLinkPattern /@ vectorLinks;
  labelSpecs = gammaProductLinkLabelSpec /@ vectorLinks;
  If[MemberQ[linkPatterns, $Failed] || MemberQ[labelSpecs, $Failed], Return[$Failed]];
  heads = First /@ linkPatterns;
  gammaProductAntisymmetrizedMatrixFromLabelSpecs[signature, heads, labelSpecs]
];

gammaProductFactorMatrixRaw::usage =
  "gammaProductFactorMatrixRaw[links] returns the exact sparse matrix represented by one concrete GammaAntisymmetricProductHold link list.";
gammaProductFactorMatrixRaw[links_List] := Module[
  {cached, cTag, coreLinks, vectorLinks, tailLinks, baseMatrix, cMatrix, tailMatrices},
  cached = gammaProductCacheLookupFromLinks[links];
  If[cached =!= $Failed, Return[cached]];
  cTag = If[links =!= {} && MatchQ[First[links], CUDHold | CDUHold], First[links], None];
  coreLinks = If[cTag === None, links, Rest[links]];
  vectorLinks = Select[coreLinks, MatchQ[#, GammaUDHold[_] | GammaDUHold[_]] &];
  tailLinks = Select[coreLinks, !MatchQ[#, GammaUDHold[_] | GammaDUHold[_]] &];
  baseMatrix = gammaProductAntisymmetrizedMatrix[vectorLinks];
  If[baseMatrix === $Failed, Return[$Failed]];
  If[cTag =!= None,
    cMatrix = gammaProductLinkMatrix[cTag];
    If[cMatrix === $Failed, Return[$Failed]];
    baseMatrix = cMatrix . baseMatrix;
  ];
  tailMatrices = gammaProductLinkMatrix /@ tailLinks;
  If[MemberQ[tailMatrices, $Failed], Return[$Failed]];
  Fold[Dot, baseMatrix, tailMatrices]
];

gammaProductFactorMatrix::usage =
  "gammaProductFactorMatrix[links] returns the memoized exact sparse matrix represented by one concrete GammaAntisymmetricProductHold link list.";
gammaProductFactorMatrix[links_List] := gammaProductFactorMatrix[flatSpaceSignatureName[], links];
gammaProductFactorMatrix[signature_String, links_List] := gammaProductFactorMatrix[signature, links] =
  gammaProductFactorMatrixRaw[links];

GammaAntisymmetricProduct[links_List] /; Head[gammaProductFactorMatrix[links]] === SparseArray :=
  denseGammaMatrixFromSparse[gammaProductFactorMatrix[links]];

GammaAntisymmetricProduct[links_List, alpha_Integer, beta_Integer] /;
    validGammaSpinorIndexQ[alpha] && validGammaSpinorIndexQ[beta] &&
      Head[gammaProductFactorMatrix[links]] === SparseArray :=
  gammaProductFactorMatrix[links][[alpha, beta]];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
