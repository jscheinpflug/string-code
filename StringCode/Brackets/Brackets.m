(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Brackets`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`StringFields`"];
Needs["StringCode`OPE`"];
Needs["StringCode`Taylor`"];


(* ::Section:: *)
(*Declare public variables and methods*)


Bracket::usage = "Computes the flat string bracket";
actBRST::usage = "Acts with the BRST charge (computes 1-bracket)";


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Define 1-bracket (action of BRST charge)*)


actBRST[SFa_/; SFtest[SFa]]:= actBRSTHolo[SFa] + actBRSTAntiHolo[SFa];

actBRSTAntiHolo[a_+b_]:= actBRSTAntiHolo[a] + actBRSTAntiHolo[b];
actBRSTAntiHolo[a_ b_]:= a actBRSTAntiHolo[b]/;(And @@(FreeQ[a,#]&/@ allfields))
actBRSTAntiHolo[0] := 0;
actBRSTHolo[a_+b_]:= actBRSTHolo[a] +actBRSTHolo[b];
actBRSTHolo[a_ b_]:=a actBRSTHolo[b]/;(And @@(FreeQ[a,#]&/@ allfields))
actBRSTHolo[0] := 0;
actBRST[a_+b_]:=actBRST[a] + actBRST[b];
actBRST[a_ b_]:=a actBRST[b]/;(And @@(FreeQ[a,#]&/@ allfields))
actBRST[0] := 0;


(* ::Subsection:: *)
(*Define 2-bracket*)


Bracket[a___, maxDerivativeOrder_/;NumericQ[maxDerivativeOrder]]:= BracketWithProfileX[a, maxDerivativeOrder];


Bracket[a_+b_,c_]:=Bracket[a,c]+Bracket[b,c]
Bracket[a_,b_+c_]:=Bracket[a,b]+Bracket[a,c]
Bracket[a_ b_,c_]:=a Bracket[b,c]/;(And @@(FreeQ[a,#]&/@ allfields))
Bracket[a_,b_ c_]:=b Bracket[a,c]/;(And @@(FreeQ[b,#]&/@ allfields))


(* ::Subsection:: *)
(*Define action of b0^-*)


b0mHolo[Ra_/;Rtest[Ra]] := Module[{result, RList = List @@ Ra, pos, numberOfPassedFermions},
pos = FirstPosition[RList, c[1, 0], None];
If[pos === None, Return[0]];
numberOfPassedFermions = Count[
    Take[RList, pos[[1]] - 1],
    f_ /; MemberQ[fermions, Head[f]]
  ];
  result = (-1)^numberOfPassedFermions R @@ Delete[RList, pos[[1]]];
result];

b0mAntiHolo[Ra_/;Rtest[Ra]] := Module[{result, RList = List @@ Ra, pos, numberOfPassedFermions},
pos = FirstPosition[RList, ct[1, 0], None];
If[pos === None, Return[0]];
numberOfPassedFermions = Count[
    Take[RList, pos[[1]] - 1],
    f_ /; MemberQ[fermions, Head[f]]
  ];
  result = (-1)^numberOfPassedFermions R @@ Delete[RList, pos[[1]]];
result];

b0m[Ra_/;Rtest[Ra]] := b0mHolo[Ra] - b0mAntiHolo[Ra];
b0m[a_+b_]:=b0m[a] + b0m[b];
b0m[a_ b_]:=a b0m[b]/;(And @@(FreeQ[a,#]&/@ allfields))
b0m[0] := 0;


(* ::Subsection:: *)
(*Determine whether OPE should be computed*)


singularity[b[n_,z_],c[m_,w_]]:= 1 + m + n;
singularity[c[m_,w_],b[n_,z_]]:= 1 + m + n;
singularity[bt[n_,z_],ct[m_,w_]]:= 1 + m + n;
singularity[ct[m_,w_],bt[n_,z_]]:= 1 + m + n;


singularityMatrix[Ra_/;Rtest[Ra], Rb_/; Rtest[Rb]]:= Table[singularity[Ra[[i]], Rb[[j]]], {i, 1, Length[Ra]}, {j, 1, Length[Rb]}];
singularityMatrix[a_ b_, c_]:= singularityMatrix[b,c]/;(And @@(FreeQ[a,#]&/@ allfields));
singularityMatrix[a_, b_ c_]:= singularityMatrix[a,c]/;(And @@(FreeQ[b,#]&/@ allfields));


(* Upper-bounds singularity given singularityMatrix, gets the position of the exp\[Phi] in PCO, on the corresponding row sums up all its entries
since an exponential can contract multiple times (importantly sums up even the negative value) and then adds the maximum from each other row. 
If there are no two operators in the string field contracting with the same operator in the PCO at the same (maximal) singularity order, the upper bound is saturated. *)
upperBoundSingularity[singularityMatrix_?MatrixQ, compositeRowNumber_] := Module[
  {n = Length[singularityMatrix], total = 0, row, negs},
  Do[
    row = singularityMatrix[[i]];
    negs = Select[row, # < 0 &];
    If[i != compositeRowNumber, total = total + Max[row], total = total + Total[row]],
    {i, n}
  ];
  total
];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
