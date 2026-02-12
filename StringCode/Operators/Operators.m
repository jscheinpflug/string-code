(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Operators`"];


Needs["StringCode`Symbols`"];
Needs["StringCode`NormalOrdering`"];


(* ::Section:: *)
(*Declare public variables and methods*)


MultiOp::usage = "A multilocal operator consisting of local operators at different points";


(* ::Section:: *)
(*Logic*)


(* ::Input::Initialization:: *)
Begin["Private`"];


(* ::Subsection:: *)
(*Define MultiOp*)


MultiOp[c___,a_+b_,d___]:=MultiOp[c,a,d]+MultiOp[c,b,d]
MultiOp[c___,0,d___]:=0
MultiOp[c___, s_?nonOperatorQ f_, d___] := s MultiOp[c, f, d];
MultiOp[c___, s_?nonOperatorQ,   d___] := s MultiOp[c, d];

MultiOp[x___, MultiOp[y___], z___] := MultiOp[x, y, z]

nonOperatorQ[expr_]:= FreeQ[expr, R];


(* ::Subsection:: *)
(*Position operators at coordinates*)


RAtPos[Ra_/;RTest[Ra], coordHol_, coordAntiHol_] :=
  mapOp[coordHol, coordAntiHol] /@ Ra;

MultiOpAtPos[Ma_/;MultiOpTest[Ma], coordHol_, coordAntiHol_] :=
  mapOp[coordHol, coordAntiHol] /@ Ma;

OpAtPos[op_/;RTest[op], coordHol_, coordAntiHol_] := RAtPos[op, coordHol, coordAntiHol];
OpAtPos[op_/;MultiOpTest[op], coordHol_, coordAntiHol_] := MultiOpAtPos[op, coordHol, coordAntiHol];


(* ::Subsection:: *)
(*Map operators with conformal weight scaling*)


mapOp[coordHol_, coordAntiHol_][MultiOpa_/;MultiOpTest[MultiOpa]] :=
  mapOp[coordHol, coordAntiHol] /@ MultiOpa;

mapOp[coordHol_, coordAntiHol_][Ra_/;RTest[Ra]] :=
  mapOp[coordHol, coordAntiHol] /@ Ra;

mapOp[coordHol_, coordAntiHol_][a_/;isField[Head[a]] && isHolomorphic[Head[a]] && isAntiHolomorphic[Head[a]]] :=
  Module[{z, zbar, w, wbar},
    {z, zbar} = Take[List @@ a, -2];
    (D[coordHol[w], w] /. {w -> z})^weightHolo[a] *
    (D[coordAntiHol[wbar], wbar] /. {wbar -> zbar})^weightAntiHolo[a] *
    placeOp[coordHol, coordAntiHol][a]
  ];

mapOp[coordHol_, coordAntiHol_][a_/;isHolomorphic[Head[a]]] :=
  Module[{z = Last[a], w},
    (D[coordHol[w], w] /. {w -> z})^weightHolo[a] placeOp[coordHol, coordAntiHol][a]
  ];

mapOp[coordHol_, coordAntiHol_][a_/;isAntiHolomorphic[Head[a]]] :=
  Module[{zbar = Last[a], wbar},
    (D[coordAntiHol[wbar], wbar] /. {wbar -> zbar})^weightAntiHolo[a] placeOp[coordHol, coordAntiHol][a]
  ];


(* ::Subsection:: *)
(*Place operators at coordinates*)


placeOp[coordHol_, coordAntiHol_][b[n_, z_]] := b[n, coordHol[z]];
placeOp[coordHol_, coordAntiHol_][c[n_, z_]] := c[n, coordHol[z]];
placeOp[coordHol_, coordAntiHol_][bt[n_, zbar_]] := bt[n, coordAntiHol[zbar]];
placeOp[coordHol_, coordAntiHol_][ct[n_, zbar_]] := ct[n, coordAntiHol[zbar]];


(* ::Subsection:: *)
(*Factorization helpers*)


splitOperators[operatorList_, f1_, f2_] := Module[{operators1, operators2},
  operators1 = Select[operatorList, f1 @* Head];
  operators2 = Select[operatorList, f2 @* Head];
  {operators1, operators2}
];

fermionPositions[operatorList__, f1_, f2_] := Module[{result, operatorListLength = Length[operatorList], operatorListElem},
  result = Flatten[Reap[
      Do[
        operatorListElem = Head[operatorList[[i]]];
        If[f1[operatorListElem] && isFermion[operatorListElem], Sow[i, "1"]];
        If[f2[operatorListElem] && isFermion[operatorListElem], Sow[i, "2"]];
      , {i, 1, operatorListLength}]
    , {"1", "2"}][[2]], 1];
  result
];

factorizationSign[operatorList__, f1_, f2_] :=
  Module[{fermionPositionLists = fermionPositions[operatorList, f1, f2], swaps, totalSwaps, sign},
    If[Length[fermionPositionLists] == 2,
      swaps = Outer[Boole[#2 < #1] &, fermionPositionLists[[1]], fermionPositionLists[[2]]];
      totalSwaps = Total[swaps, 2];
      sign = (-1)^totalSwaps;,
      sign = 1;
    ];
    sign
  ];


(* ::Subsection:: *)
(*Define parity of MultiOp and R*)


parityOp::usage = "Computes the parity of a local operator";
scalarQ[x_] := FreeQ[x, _MultiOp | _R]
parityOp[expr_Times] := parityOp[SelectFirst[List @@ expr, !scalarQ[#] &]]

parityOp[Ma_/;MultiOpTest[Ma]]:= Mod[Total @ (parityOp /@ List @@ Ma),2];
parityOp[Ra_/;RTest[Ra]]:= Mod[parity[Ra],2];


(* ::Subsection:: *)
(*Define weight of operators*)


totalWeightHolo::usage = "Computes total holomorphic weight of a normal-ordered product";
totalWeightAntiHolo::usage = "Computes total holomorphic weight of a normal-ordered product";
totalWeight::usage = "Computes total weight of a normal-ordered product";

totalWeightHolo[Times[a_, MultiOpa_/;MultiOpTest[MultiOpa]]] := totalWeightHolo[MultiOpa];
totalWeightHolo[MultiOpa_/;MultiOpTest[MultiOpa]] := Total[Map[totalWeightHolo, List @@ MultiOpa]];

totalWeightAntiHolo[Times[a_, MultiOpa_/;MultiOpTest[MultiOpa]]] := totalWeightAntiHolo[MultiOpa];
totalWeightAntiHolo[MultiOpa_/;MultiOpTest[MultiOpa]] := Total[Map[totalWeightAntiHolo, List @@ MultiOpa]];

totalWeightHolo[a_/;NumericQ[a]]:=0;
totalWeightAntiHolo[a_/;NumericQ[a]]:=0;

totalWeight[Times[a_, MultiOpa_/;MultiOpTest[MultiOpa]]] := totalWeight[MultiOpa];
totalWeight[MultiOpa_/;MultiOpTest[MultiOpa]] := {totalWeightHolo[MultiOpa], totalWeightAntiHolo[MultiOpa]};

totalWeight[a_/;NumericQ[a]]:=0;


(* ::Subsection:: *)
(*Test MultiOp and length*)


MultiOpTest::usage = "Test if is MultiOp";
MultiOpTest[f_]:=(Head[f]===MultiOp)

MultiOpLength::usage = "Test if is MultiOp and has nonzero length";
MultiOpLength[f_]:=If[MultiOpTest[f],Length[List @@ f],0]

MultiOpOne::usage = "Test if is MultiOp of length one";
MultiOpOne[f_]:=(MultiOpLength[f]===1)


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
