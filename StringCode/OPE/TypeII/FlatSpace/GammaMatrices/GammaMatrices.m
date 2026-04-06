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
  "validGammaIndexQ[mu] checks whether mu is a valid canonical flat-space vector index between 1 and 10.";
validGammaIndexQ[mu_Integer] := 1 <= mu <= gammaVectorDimension;
validGammaIndexQ[_] := False;


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


CGamma[mu_Integer] := CGammaData[[mu]] /; validGammaIndexQ[mu];


CGammaSparse[mu_Integer] := CGammaSparseData[[mu]] /; validGammaIndexQ[mu];


CIGamma[mu_Integer] := CIGammaData[[mu]] /; validGammaIndexQ[mu];


CIGammaSparse[mu_Integer] := CIGammaSparseData[[mu]] /; validGammaIndexQ[mu];


GammaUD[mu_Integer] := gammaUDData[[mu]] /; validGammaIndexQ[mu];


GammaUDSparse[mu_Integer] := gammaUDSparseData[[mu]] /; validGammaIndexQ[mu];


GammaDU[mu_Integer] := gammaDUData[[mu]] /; validGammaIndexQ[mu];


GammaDUSparse[mu_Integer] := gammaDUSparseData[[mu]] /; validGammaIndexQ[mu];


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


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
