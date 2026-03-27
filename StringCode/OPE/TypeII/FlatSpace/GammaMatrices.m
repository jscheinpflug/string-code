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


CGammaOPEDataRules::usage =
  "CGammaOPEDataRules is the frozen compressed rule data for the ten exact chiral-chiral same-chirality S-S OPE coefficient matrices.";
CGammaOPEDataRules = Uncompress["1:eJzFmt1O20AQhYMhTX9Cm1fos/SWiwr1BagUpJVCgxoqeHvwHNQWZLus6X5zuLCyibODnfWeb2bO5+/788v3i8XicNIfzsrh5nLzbNT9Hp3/2m3/juKzctS/KOv+8Pj+sj98K1fbw+Nw1R++7K+ud9u7sogzj56d+XV/u/1Zuj/vvY0YFzdl/+NiV+77vyefTcSPUVn54h/HrG988eNFWfrixzT6J0zx49brRzDFjwhPzkqPH18pm+r4MWnT+O9i1k+++LFvlY+++B9i1lNf/PVwVaWuv7h03QTT9cdPr0Vgih9LXw+BKX48+toEwPgzacD4NHTzVgNDA8bVcDJvNTA0UK9GDA0Y1Ug0UK9GDA0YaUw0UE9jDA101fGbX79ooD4bYmjAqManw7uaTwPGbFA0UJ8NMjQAZ4MzacDI5p35aRANGNVQNFCvhgwN1NMQQwNGGhINGGlYNGCsTYkGjLUp0YBRjUUDnS++aMCYG4sG6tWYoQEjjYgGjDQuGoBrozNpwJibxcipxqKBehphaMBIY6IB424kGqhXY4YGjDQiGjDmRqIBoxqLBupphKEBY6dKNGCsTYoGjDQqGqhXY4YGjDQiGuiq42fQgFGNY+TMjUUDxkqxaMBII6IBoxqLBoydItGAsTYiGjD6dkQDRhoRDRjVSDRgzA1FA0YaFQ0Ya0OiASONiQZgNf5X/M1wVjcNrF8T40WNX7WedcTxx/j4GHce47ljnHSMP45xvTFeNsahxvjOGDcZ4xFjnF+MnyvNpZXixwJdVil+KtAlBdU8m+9TUy4nqIPZXL+mXEopfiTGZcR4h0BHUJ73B6rkNSfAKe9Oimc35WnuhisMijTlvIEUYqSOCPXPmvPGiEeGcb4wfhbGpcJ4T0BHSYp3hHGEgD6PPEcH1K1pxij/79LI82NAatCcbLTzN8/Wl8PnjswNUrLAEecD42dgXAqg9yDFZcB4B0BHAJQbNM8jpzr6eb37FDVoXj3Vzp+iMVNddigPaK4xU11ySA2a895IlxvsXbe/KyNdaqb3zHSUwT4x5A9L0cip3i+ULzTbt19UiNf0Yx4AXtcpMw=="];


CGammaOPESparseData::usage =
  "CGammaOPESparseData is the exact list of ten sparse 16x16 chiral-chiral same-chirality S-S OPE coefficient matrices in canonical mu-order.";
CGammaOPESparseData = sparseGammaMatrixFromRules /@ CGammaOPEDataRules;


CGammaOPEData::usage =
  "CGammaOPEData is the exact list of ten 16x16 chiral-chiral same-chirality S-S OPE coefficient matrices in canonical mu-order.";
CGammaOPEData = denseGammaMatrixFromSparse /@ CGammaOPESparseData;


CUDSparseData::usage =
  "CUDSparseData is the exact sparse chiral-antichiral spinor pairing matrix used by the frozen TypeII flat-space gamma conventions.";
CUDSparseData = -I gammaSparseIdentityMatrix[gammaSpinorDimension];


CUDData::usage =
  "CUDData is the exact chiral-antichiral spinor pairing matrix used by the frozen TypeII flat-space gamma conventions.";
CUDData = denseGammaMatrixFromSparse[CUDSparseData];


CDUSparseData::usage =
  "CDUSparseData is the exact sparse antichiral-chiral spinor pairing matrix used by the frozen TypeII flat-space gamma conventions.";
CDUSparseData = I gammaSparseIdentityMatrix[gammaSpinorDimension];


CUDInverseSparseData::usage =
  "CUDInverseSparseData is the exact sparse inverse of the chiral-antichiral pairing matrix.";
CUDInverseSparseData = I gammaSparseIdentityMatrix[gammaSpinorDimension];


CDUInverseSparseData::usage =
  "CDUInverseSparseData is the exact sparse inverse of the antichiral-chiral pairing matrix.";
CDUInverseSparseData = -I gammaSparseIdentityMatrix[gammaSpinorDimension];


CDUData::usage =
  "CDUData is the exact antichiral-chiral spinor pairing matrix used by the frozen TypeII flat-space gamma conventions.";
CDUData = denseGammaMatrixFromSparse[CDUSparseData];


CIGammaOPESparseData::usage =
  "CIGammaOPESparseData is the exact list of ten sparse 16x16 antichiral-antichiral same-chirality S-S OPE coefficient matrices derived from the frozen chiral OPE data.";
CIGammaOPESparseData = Table[If[i <= 5, CGammaOPESparseData[[i]], -CGammaOPESparseData[[i]]], {i, 1, gammaVectorDimension}];


CIGammaOPEData::usage =
  "CIGammaOPEData is the exact list of ten antichiral-antichiral same-chirality S-S OPE coefficient matrices derived from the frozen chiral OPE data.";
CIGammaOPEData = denseGammaMatrixFromSparse /@ CIGammaOPESparseData;


sameChiralOPEToMixedGammaPrefactor::usage =
  "sameChiralOPEToMixedGammaPrefactor is the convention-fixed coefficient relating frozen same-chirality S-S OPE data to mixed Clifford-normalized GammaUD and GammaDU matrices.";
sameChiralOPEToMixedGammaPrefactor = -I Sqrt[2];


gammaUDSparseData::usage =
  "gammaUDSparseData is the exact list of ten sparse mixed chiral-to-antichiral gamma matrices derived from the frozen same-chirality OPE data and pairings.";
gammaUDSparseData = Table[
  sameChiralOPEToMixedGammaPrefactor (CGammaOPESparseData[[i]] . CUDInverseSparseData),
  {i, 1, gammaVectorDimension}
];


gammaUDData::usage =
  "gammaUDData is the exact list of ten mixed chiral-to-antichiral gamma matrices derived from the frozen same-chirality OPE data and pairings.";
gammaUDData = denseGammaMatrixFromSparse /@ gammaUDSparseData;


gammaDUSparseData::usage =
  "gammaDUSparseData is the exact list of ten sparse mixed antichiral-to-chiral gamma matrices derived from the frozen same-chirality OPE data and pairings.";
gammaDUSparseData = Table[
  sameChiralOPEToMixedGammaPrefactor (CIGammaOPESparseData[[i]] . CDUInverseSparseData),
  {i, 1, gammaVectorDimension}
];


gammaDUData::usage =
  "gammaDUData is the exact list of ten mixed antichiral-to-chiral gamma matrices derived from the frozen same-chirality OPE data and pairings.";
gammaDUData = denseGammaMatrixFromSparse /@ gammaDUSparseData;


CGammaSparseData::usage =
  "CGammaSparseData is the exact list of ten sparse chiral-chiral charge-conjugated gamma matrices obtained by lowering the mixed GammaUD matrices with CUDSparse.";
CGammaSparseData = Table[gammaUDSparseData[[i]] . CUDSparseData, {i, 1, gammaVectorDimension}];


CGammaData::usage =
  "CGammaData is the exact list of ten chiral-chiral charge-conjugated gamma matrices obtained by lowering the mixed GammaUD matrices with CUD.";
CGammaData = denseGammaMatrixFromSparse /@ CGammaSparseData;


CIGammaSparseData::usage =
  "CIGammaSparseData is the exact list of ten sparse antichiral-antichiral charge-conjugated gamma matrices obtained by lowering the mixed GammaDU matrices with CDUSparse.";
CIGammaSparseData = Table[gammaDUSparseData[[i]] . CDUSparseData, {i, 1, gammaVectorDimension}];


CIGammaData::usage =
  "CIGammaData is the exact list of ten antichiral-antichiral charge-conjugated gamma matrices obtained by lowering the mixed GammaDU matrices with CDU.";
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
