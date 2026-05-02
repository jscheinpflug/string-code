(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`OPE`TypeII`FlatSpace`GammaMatrices`"];
Needs["StringCode`Symbols`"];
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

gammaExternalIndexDomain::usage =
  "gammaExternalIndexDomain[] returns the active public vector-index domain accepted by gamma-matrix accessors.";
gammaExternalIndexDomain[] := flatSpaceVectorIndexDomain[];

gammaCanonicalIndexFromExternal::usage =
  "gammaCanonicalIndexFromExternal[mu] maps one active external vector index to the canonical 1..10 slot used by frozen gamma artifacts.";
gammaCanonicalIndexFromExternal[mu_Integer] := flatSpaceVectorIndexSlot[mu];
gammaCanonicalIndexFromExternal[_] := $Failed;

gammaLorentzianPhase::usage =
  "gammaLorentzianPhase[mu] returns the signature-dependent phase for one gamma index (timelike slot carries I in Lorentzian mode).";
gammaLorentzianPhase[mu_Integer] := If[
  currentSignature[] == "Lorentzian" && mu == First[gammaExternalIndexDomain[]],
  I,
  1
];
gammaLorentzianPhase[_] := 1;


validGammaIndexQ::usage =
  "validGammaIndexQ[mu] checks whether mu is a valid active flat-space vector index in the current signature.";
validGammaIndexQ[mu_Integer] := MemberQ[gammaExternalIndexDomain[], mu];
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

gammaDataFileForSignature::usage =
  "gammaDataFileForSignature[baseName] returns the signature-specific frozen gamma-data file path from the appropriate Euclidean or Lorentzian subdirectory.";
gammaDataFileForSignature[baseName_String] := Module[{dir, sigName},
  dir = DirectoryName[$InputFileName];
  sigName = If[currentSignature[] == "Lorentzian", "Lorentzian", "Euclidean"];
  FileNameJoin[{dir, sigName, baseName}]
];


Get[gammaDataFileForSignature["SpinFieldConventionData.m"]];


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

gammaDenseMatrixAccessor::usage =
  "gammaDenseMatrixAccessor[data, mu] returns one signature-adapted dense gamma matrix from canonical frozen data.";
gammaDenseMatrixAccessor[data_List, mu_Integer] := Module[{slot = gammaCanonicalIndexFromExternal[mu], phase},
  If[slot === $Failed, Return[$Failed]];
  phase = gammaLorentzianPhase[mu];
  phase data[[slot]]
];

gammaSparseMatrixAccessor::usage =
  "gammaSparseMatrixAccessor[data, mu] returns one signature-adapted sparse gamma matrix from canonical frozen data.";
gammaSparseMatrixAccessor[data_List, mu_Integer] := Module[{slot = gammaCanonicalIndexFromExternal[mu], phase},
  If[slot === $Failed, Return[$Failed]];
  phase = gammaLorentzianPhase[mu];
  phase data[[slot]]
];


CGamma[mu_Integer] := gammaDenseMatrixAccessor[CGammaData, mu] /; validGammaIndexQ[mu];


CGammaSparse[mu_Integer] := gammaSparseMatrixAccessor[CGammaSparseData, mu] /; validGammaIndexQ[mu];


CIGamma[mu_Integer] := gammaDenseMatrixAccessor[CIGammaData, mu] /; validGammaIndexQ[mu];


CIGammaSparse[mu_Integer] := gammaSparseMatrixAccessor[CIGammaSparseData, mu] /; validGammaIndexQ[mu];


GammaUD[mu_Integer] := gammaDenseMatrixAccessor[gammaUDData, mu] /; validGammaIndexQ[mu];


GammaUDSparse[mu_Integer] := gammaSparseMatrixAccessor[gammaUDSparseData, mu] /; validGammaIndexQ[mu];


GammaDU[mu_Integer] := gammaDenseMatrixAccessor[gammaDUData, mu] /; validGammaIndexQ[mu];


GammaDUSparse[mu_Integer] := gammaSparseMatrixAccessor[gammaDUSparseData, mu] /; validGammaIndexQ[mu];


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
gammaProductLinkMatrix::invalidindex =
  "Vector index `1` is not valid in `2` mode. Expected index in `3`.";
gammaProductLinkMatrix[CUDHold] := CUDSparse;
gammaProductLinkMatrix[CDUHold] := CDUSparse;
gammaProductLinkMatrix[GammaUDHold[mu_Integer]] /; validGammaIndexQ[mu] := GammaUDSparse[mu];
gammaProductLinkMatrix[GammaDUHold[mu_Integer]] /; validGammaIndexQ[mu] := GammaDUSparse[mu];
gammaProductLinkMatrix[GammaUDHold[mu_Integer]] /; !validGammaIndexQ[mu] := (
  Message[gammaProductLinkMatrix::invalidindex, mu, currentSignature[], gammaExternalIndexDomain[]];
  $Failed
);
gammaProductLinkMatrix[GammaDUHold[mu_Integer]] /; !validGammaIndexQ[mu] := (
  Message[gammaProductLinkMatrix::invalidindex, mu, currentSignature[], gammaExternalIndexDomain[]];
  $Failed
);
gammaProductLinkMatrix[Gamma11UUHold[]] := Gamma11UUSparse;
gammaProductLinkMatrix[Gamma11DDHold[]] := Gamma11DDSparse;
gammaProductLinkMatrix[_] := $Failed;

gammaProductAntisymmetrizedMatrixFromPattern::usage =
  "gammaProductAntisymmetrizedMatrixFromPattern[linkHeads, inds] antisymmetrizes vector labels while preserving the ordered U/D head pattern.";
gammaProductAntisymmetrizedMatrixFromPattern[{}, {}] := gammaSparseIdentityMatrix[gammaSpinorDimension];
gammaProductAntisymmetrizedMatrixFromPattern[linkHeads_List, inds_List] /; Length[linkHeads] === Length[inds] :=
  gammaProductAntisymmetrizedMatrixFromPattern[linkHeads, inds] = Module[{rank = Length[inds]},
    1/rank Sum[
      (-1)^(pos - 1) gammaProductLinkMatrix[linkHeads[[1]][inds[[pos]]]] .
        gammaProductAntisymmetrizedMatrixFromPattern[Rest[linkHeads], Delete[inds, pos]],
      {pos, 1, rank}
    ]
  ];

gammaProductAntisymmetrizedMatrix::usage =
  "gammaProductAntisymmetrizedMatrix[vectorLinks] returns the exact sparse antisymmetrized gamma matrix for one concrete vector-link list.";
gammaProductAntisymmetrizedMatrix[{}] := gammaSparseIdentityMatrix[gammaSpinorDimension];
gammaProductAntisymmetrizedMatrix[vectorLinks_List] := gammaProductAntisymmetrizedMatrix[vectorLinks] = Module[
  {linkHeads, inds},
  linkHeads = Replace[
    vectorLinks,
    {GammaUDHold[_Integer] :> GammaUDHold, GammaDUHold[_Integer] :> GammaDUHold, _ :> $Failed},
    1
  ];
  inds = Replace[
    vectorLinks,
    {GammaUDHold[mu_Integer] :> mu, GammaDUHold[mu_Integer] :> mu, _ :> $Failed},
    1
  ];
  If[MemberQ[linkHeads, $Failed] || MemberQ[inds, $Failed], Return[$Failed]];
  gammaProductAntisymmetrizedMatrixFromPattern[linkHeads, inds]
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
gammaProductFactorMatrix[links_List] := gammaProductFactorMatrix[links] =
  gammaProductFactorMatrixRaw[links];

GammaAntisymmetricProduct[links_List] /; Head[gammaProductFactorMatrix[links]] === SparseArray :=
  GammaAntisymmetricProduct[links] = denseGammaMatrixFromSparse[gammaProductFactorMatrix[links]];

GammaAntisymmetricProduct[links_List, alpha_Integer, beta_Integer] /;
    validGammaSpinorIndexQ[alpha] && validGammaSpinorIndexQ[beta] &&
      Head[gammaProductFactorMatrix[links]] === SparseArray :=
  gammaProductFactorMatrix[links][[alpha, beta]];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
