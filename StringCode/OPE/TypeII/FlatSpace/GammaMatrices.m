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


denseGammaMatrixFromRules::usage =
  "denseGammaMatrixFromRules[rules] converts a sparse 16x16 rule list into an exact dense matrix.";
denseGammaMatrixFromRules[rules_List] := Normal[SparseArray[rules, {gammaSpinorDimension, gammaSpinorDimension}]];


CGammaOPEDataRules::usage =
  "CGammaOPEDataRules is the frozen compressed rule data for the ten exact chiral-chiral same-chirality S-S OPE coefficient matrices.";
CGammaOPEDataRules = Uncompress["1:eJzFmt1O20AQhYMhTX9Cm1fos/SWiwr1BagUpJVCgxoqeHvwHNQWZLus6X5zuLCyibODnfWeb2bO5+/788v3i8XicNIfzsrh5nLzbNT9Hp3/2m3/juKzctS/KOv+8Pj+sj98K1fbw+Nw1R++7K+ud9u7sogzj56d+XV/u/1Zuj/vvY0YFzdl/+NiV+77vyefTcSPUVn54h/HrG988eNFWfrixzT6J0zx49brRzDFjwhPzkqPH18pm+r4MWnT+O9i1k+++LFvlY+++B9i1lNf/PVwVaWuv7h03QTT9cdPr0Vgih9LXw+BKX48+toEwPgzacD4NHTzVgNDA8bVcDJvNTA0UK9GDA0Y1Ug0UK9GDA0YaUw0UE9jDA101fGbX79ooD4bYmjAqManw7uaTwPGbFA0UJ8NMjQAZ4MzacDI5p35aRANGNVQNFCvhgwN1NMQQwNGGhINGGlYNGCsTYkGjLUp0YBRjUUDnS++aMCYG4sG6tWYoQEjjYgGjDQuGoBrozNpwJibxcipxqKBehphaMBIY6IB424kGqhXY4YGjDQiGjDmRqIBoxqLBupphKEBY6dKNGCsTYoGjDQqGqhXY4YGjDQiGuiq42fQgFGNY+TMjUUDxkqxaMBII6IBoxqLBoydItGAsTYiGjD6dkQDRhoRDRjVSDRgzA1FA0YaFQ0Ya0OiASONiQZgNf5X/M1wVjcNrF8T40WNX7WedcTxx/j4GHce47ljnHSMP45xvTFeNsahxvjOGDcZ4xFjnF+MnyvNpZXixwJdVil+KtAlBdU8m+9TUy4nqIPZXL+mXEopfiTGZcR4h0BHUJ73B6rkNSfAKe9Oimc35WnuhisMijTlvIEUYqSOCPXPmvPGiEeGcb4wfhbGpcJ4T0BHSYp3hHGEgD6PPEcH1K1pxij/79LI82NAatCcbLTzN8/Wl8PnjswNUrLAEecD42dgXAqg9yDFZcB4B0BHAJQbNM8jpzr6eb37FDVoXj3Vzp+iMVNddigPaK4xU11ySA2a895IlxvsXbe/KyNdaqb3zHSUwT4x5A9L0cip3i+ULzTbt19UiNf0Yx4AXtcpMw=="];


CGammaOPEData::usage =
  "CGammaOPEData is the exact list of ten 16x16 chiral-chiral same-chirality S-S OPE coefficient matrices in canonical mu-order.";
CGammaOPEData = denseGammaMatrixFromRules /@ CGammaOPEDataRules;


CUDData::usage =
  "CUDData is the exact chiral-antichiral spinor pairing matrix used by the frozen TypeII flat-space gamma conventions.";
CUDData = -I IdentityMatrix[gammaSpinorDimension];


CDUData::usage =
  "CDUData is the exact antichiral-chiral spinor pairing matrix used by the frozen TypeII flat-space gamma conventions.";
CDUData = I IdentityMatrix[gammaSpinorDimension];


CIGammaOPEData::usage =
  "CIGammaOPEData is the exact list of ten antichiral-antichiral same-chirality S-S OPE coefficient matrices derived from the frozen chiral OPE data.";
CIGammaOPEData = Table[If[i <= 5, CGammaOPEData[[i]], -CGammaOPEData[[i]]], {i, 1, gammaVectorDimension}];


sameChiralOPEToMixedGammaPrefactor::usage =
  "sameChiralOPEToMixedGammaPrefactor is the convention-fixed coefficient relating frozen same-chirality S-S OPE data to mixed Clifford-normalized GammaUD and GammaDU matrices.";
sameChiralOPEToMixedGammaPrefactor = -I Sqrt[2];


gammaUDData::usage =
  "gammaUDData is the exact list of ten mixed chiral-to-antichiral gamma matrices derived from the frozen same-chirality OPE data and pairings.";
gammaUDData = Table[
  Simplify[sameChiralOPEToMixedGammaPrefactor CGammaOPEData[[i]].Inverse[CUDData]],
  {i, 1, gammaVectorDimension}
];


gammaDUData::usage =
  "gammaDUData is the exact list of ten mixed antichiral-to-chiral gamma matrices derived from the frozen same-chirality OPE data and pairings.";
gammaDUData = Table[
  Simplify[sameChiralOPEToMixedGammaPrefactor CIGammaOPEData[[i]].Inverse[CDUData]],
  {i, 1, gammaVectorDimension}
];


CGammaData::usage =
  "CGammaData is the exact list of ten chiral-chiral charge-conjugated gamma matrices obtained by lowering the mixed GammaUD matrices with CUD.";
CGammaData = Table[Simplify[gammaUDData[[i]] . CUDData], {i, 1, gammaVectorDimension}];


CIGammaData::usage =
  "CIGammaData is the exact list of ten antichiral-antichiral charge-conjugated gamma matrices obtained by lowering the mixed GammaDU matrices with CDU.";
CIGammaData = Table[Simplify[gammaDUData[[i]] . CDUData], {i, 1, gammaVectorDimension}];


CGamma[mu_Integer] := CGammaData[[mu]] /; validGammaIndexQ[mu];


CIGamma[mu_Integer] := CIGammaData[[mu]] /; validGammaIndexQ[mu];


GammaUD[mu_Integer] := gammaUDData[[mu]] /; validGammaIndexQ[mu];


GammaDU[mu_Integer] := gammaDUData[[mu]] /; validGammaIndexQ[mu];


CUD = CUDData;


CDU = CDUData;


Gamma11UU = IdentityMatrix[gammaSpinorDimension];


Gamma11DD = -IdentityMatrix[gammaSpinorDimension];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
