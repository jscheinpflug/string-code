(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Symbols`"]


(* ::Section:: *)
(*Declare public variables and methods*)


bosons::usage = "A list of bosons, including composites";


fermions::usage = "A list of fermions, including composites";


holomorphicFields::usage = "A list of holomorphic fields, expX counted as one";


antiHolomorphicFields::usage = "A list of antiholomorphic fields, expX counted as one";


indexedFields::usage = "A list of fields that carry indices";


allfields::usage = "A list of all bosons and fermions";


regfermions::usage = "A list of fundamental fermions";


simplefields::usage = "A list of fundamental fields";


simplefieldsnotc::usage = "A list of fundamental fields not c-ghost";


compositefields::usage = "A list of composite fields";


Contract::usage = "Contract traced indices";


ContractDelta::usage = "Contract repeated indices";


b::usage = "Holomorphic b-ghost"


bt::usage = "Antiholomorphic b-ghost"


c::usage = "Holomorphic c-ghost"


ct::usage = "Antiholomorphic c-ghost"


isBoson::usage = "Checks if is bosonic field";


isFermion::usage = "Checks if is fermionic field";


isSimple::usage = "Checks if is simple field";


isComposite::usage = "Checks if is composite field";


isField::usage = "Checks if is field";


isHolomorphic::usage = "Checks if is holomorphic";


isAntiHolomorphic::usage = "Checks if is antiholomorphic";


isIndexed::usage = "Checks if is indexed";


(* ::Section:: *)
(*Logic*)


(* ::Subsection:: *)
(*Define index contractions*)


Contract[f_,dim_]:=f /.{\[Delta][\[Mu]_,\[Mu]_]:>dim,\[Delta][\[Mu]_,\[Nu]_]^2:>dim};
Contract[f_]:=Contract[f,10];


ContractDelta[f_]:=f//.{g_ \[Delta][\[Mu]_,\[Mu]1_]:>(g/.{\[Mu]->\[Mu]1})/;!FreeQ[g,\[Mu]],g_ \[Delta][\[Mu]1_,\[Mu]_]:>(g/.{\[Mu]->\[Mu]1})/;!FreeQ[g,\[Mu]]};


Begin["Private`"];


(* ::Subsection:: *)
(*Define symbols*)


bosons={};
fermions={b,bt,c,ct};
regfermions={b,bt,c,ct};
simplefields={b,bt,c,ct};
simplefieldsnotc={b,bt};
compositefields={};
holomorphicFields = {b,c};
antiHolomorphicFields = {bt,ct};
indexedFields = {};
allfields=Join[bosons,fermions];


(* ::Subsection:: *)
(*Define cached lookups*)


isBoson[symbol_]:= isBoson[symbol] = MemberQ[bosons, symbol];
isFermion[symbol_]:= isFermion[symbol] = MemberQ[fermions, symbol];
isSimple[symbol_]:= isSimple[symbol] = MemberQ[simplefields, symbol];
isComposite[symbol_]:= isComposite[symbol] = MemberQ[compositefields, symbol];
isField[symbol_]:= isField[symbol] = MemberQ[allfields, symbol];
isHolomorphic[symbol_]:= isHolomorphic[symbol] = MemberQ[holomorphicFields, symbol];
isAntiHolomorphic[symbol_]:= isAntiHolomorphic[symbol] = MemberQ[antiHolomorphicFields, symbol];
isIndexed[symbol_]:= isIndexed[symbol] = MemberQ[indexedFields, symbol];


(* ::Subsection:: *)
(*Define weight of symbols*)


weightSymbolHolo::usage = "Computes holomorphic weight of a symbol";
weightSymbolAntiHolo::usage = "Computes antiholomorphic weight of a symbol";
weightHolo::usage = "Computes holomorphic weight of a local operator";
weightAntiHolo::usage = "Computes antiholomorphic weight of a local operator";


weightSymbolHolo[symbol_/;!isHolomorphic[symbol]]:= 0;
weightSymbolHolo[c] := - 1;
weightSymbolHolo[b] := 2;

weightHolo[field_/;!isHolomorphic[Head[field]]] := 0;
weightHolo[field_/; isSimple[Head[field]] && isIndexed[Head[field]]] := weightSymbolHolo[Head[field]] + field[[2]];
weightHolo[field_/; isSimple[Head[field]]] := weightSymbolHolo[Head[field]] + field[[1]];

weightSymbolAntiHolo[symbol_/;!isAntiHolomorphic[symbol]]:= 0;
weightSymbolAntiHolo[ct] := - 1;
weightSymbolAntiHolo[bt] := 2;

weightAntiHolo[field_/;!isAntiHolomorphic[Head[field]]] := 0;
weightAntiHolo[field_/; isSimple[Head[field]] && isIndexed[Head[field]]] := weightSymbolAntiHolo[Head[field]] + field[[2]];
weightAntiHolo[field_/; isSimple[Head[field]]] := weightSymbolAntiHolo[Head[field]] + field[[1]];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
