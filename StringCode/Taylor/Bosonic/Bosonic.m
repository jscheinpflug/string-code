(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Taylor`Bosonic`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`Bosonic`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`Bosonic`"];
Needs["StringCode`Taylor`"];


(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Check if field needs expanding*)


isAtPointHolo[dX[\[Mu]_, n_, z_], z0_] := SameQ[z,z0];
isAtPointHolo[X[\[Mu]_,  z_, zbar_], z0_] := SameQ[z,z0];
isAtPointHolo[ProfileX[profile_, ders_, z_, zbar_], z0_] := SameQ[z,z0];
isAtPointHolo[expX[k_, z_, zbar_], z0_] := SameQ[z,z0];
isAtPointHolo[field_, z0_] := False /; isAntiHolomorphic[Head[field]];
isAtPointAntiHolo[dXt[\[Mu]_, n_, zbar_], z0bar_] := SameQ[zbar,z0bar];
isAtPointAntiHolo[X[\[Mu], z_, zbar_], z0bar_] := SameQ[zbar,z0bar];
isAtPointAntiHolo[ProfileX[profile_, ders_, z_, zbar_], z0bar_] := SameQ[zbar,z0bar];
isAtPointAntiHolo[expX[k_, z_, zbar_], z0bar_] := SameQ[zbar,z0bar];
isAtPointAntiHolo[field_, z0bar_] := False /; isHolomorphic[Head[field]];


(* ::Subsection:: *)
(*Define adding derivatives*)


addHoloDerivatives[dX[\[Mu]_,n_,z_], ord_, z0_]:= (z-z0)^ord/Factorial[ord]dX[\[Mu],n+ord,z0];


addHoloDerivatives[X[\[Mu]_,z_,zbar_], ord_, z0_]:= If[ord>0, (z-z0)^ord/Factorial[ord] dX[\[Mu],ord-1,z0], X[\[Mu],z0,zbar]];


addHoloDerivatives[ProfileX[profile_, ders_List, z_, zbar_], ord_, z0_] := 
If[ord > 0, 
Module[{auxDerivativePolynomial},
auxDerivativePolynomial = derivativeOfExponential[1, ord]/.{E^(func[x]) :> 1};
(z-z0)^ord/Factorial[ord]R[auxDerivativePolynomial/.{Power[Derivative[m_][func][x], p_] :>
       Module[{i, interDers = {}, interdX = 1}, 
       Do[Module[{\[Mu]},AppendTo[interDers, \[Mu]]; interdX = interdX dX[\[Mu], m-1,x]], {i,1,p}];
       ProfileX[profile, Join[ders, interDers], x, zbar] interdX ],
       Derivative[m_][func][x] :>
       Module[{\[Mu]}, ProfileX[profile, Append[ders, \[Mu]], x, zbar] dX[\[Mu], m - 1, x]]}/.{x->z0}]
], ProfileX[profile, ders, z0, zbar]];


addHoloDerivatives[expX[k_, z_, zbar_], ord_, z0_] :=
  (z - z0)^ord/Factorial[ord] *
    R[expX[k, z0, zbar] * (expXPoly[k, ord] /. x -> z0)//Expand];


addAntiHoloDerivatives[dXt[\[Mu]_,n_,z_], ord_, z0bar_]:= (z-z0bar)^ord/Factorial[ord]dXt[\[Mu],n+ord,z0bar];


addAntiHoloDerivatives[X[\[Mu]_,z_,zbar_], ord_, z0bar_]:= If[ord > 0, (zbar-z0bar)^ord/Factorial[ord] dXt[\[Mu],ord-1,z0bar], X[\[Mu],z,z0bar]];


addAntiHoloDerivatives[ProfileX[profile_, ders_List, z_, zbar_], ord_, z0bar_] := 
If[ord > 0,
Module[{auxDerivativePolynomial},
auxDerivativePolynomial = derivativeOfExponential[1, ord]/.{E^(func[x]) :> 1};
(zbar-z0bar)^ord/Factorial[ord]R[auxDerivativePolynomial/.{Power[Derivative[m_][func][x], p_] :>
       Module[{i, interDers = {}, interdX = 1}, 
       Do[Module[{\[Mu]},AppendTo[interDers, \[Mu]]; interdX = interdX dXt[\[Mu], m-1,x]], {i,1,p}];
       ProfileX[profile, Join[ders, interDers], z, x] interdX ],
       Derivative[m_][func][x] :>
       Module[{\[Mu]}, ProfileX[profile, Append[ders, \[Mu]], z, x] dXt[\[Mu], m - 1, x]]}/.{x->z0bar}]
], ProfileX[profile, ders, z, z0bar]];


addAntiHoloDerivatives[expX[k_, z_, zbar_], ord_, z0bar_] :=
  (zbar - z0bar)^ord/Factorial[ord] *
    R[expX[k, z, z0bar] * (expXPolyT[k, ord] /. x -> z0bar)//Expand];


(* ::Subsection:: *)
(*Define Taylor expansions of exponentials and profiles*)


derivativeOfExponential[exponent_, n_]:= derivativeOfExponential[exponent, n] = D[E^(exponent func[x]), {x, n}];


Clear[expXPoly]
expXPoly[k_, n_] :=
  expXPoly[k, n] =
   Expand[derivativeOfExponential[I, n] /. {E^(I func[x]) :> 1,
      Power[Derivative[m_][func][x], p_] :>
       Module[{i},Product[Module[{\[Mu]}, k[\[Mu]] dX[\[Mu], m - 1, x]], {i, 1, p}]], 
       Derivative[m_][func][x] :>
       Module[{\[Mu]}, k[\[Mu]] dX[\[Mu], m - 1, x]]}];


Clear[expXPolyT]
expXPolyT[k_, n_] :=
  expXPolyT[k, n] =
   Expand[derivativeOfExponential[I, n]  /. {E^(I func[x]) :> 1,
      Power[Derivative[m_][func][x], p_] :>
       Module[{i},Product[Module[{\[Mu]}, k[\[Mu]] dX[\[Mu], m - 1, x]], {i, 1, p}]], 
       Derivative[m_][func][x] :>
       Module[{\[Mu]}, k[\[Mu]] dX[\[Mu], m - 1, x]]}];


(* ::Subsection:: *)
(*Define Taylor*)


taylorRule[z0_, z0bar_, ord_] := Block[{i,j,x,func,n,z},
{b[n_,z_]:>Sum[If[i==0,1,(z-z0)^i/i!] b[n+i,z0],{i,0,ord}],
c[n_,z_]:>Sum[If[i==0,1,(z-z0)^i/i!] c[n+i,z0],{i,0,ord}],
dX[\[Mu]_,n_,z_]:>Sum[If[i==0,1,(z-z0)^i/i!] dX[\[Mu],n+i,z0],{i,0,ord}],
bt[n_,z_]:>Sum[If[i==0,1,(z-z0bar)^i/i!] bt[n+i,z0bar],{i,0,ord}],
ct[n_,z_]:>Sum[If[i==0,1,(z-z0bar)^i/i!]ct[n+i,z0bar],{i,0,ord}],
dXt[\[Mu]_,n_,z_]:>Sum[If[i==0,1,(z-z0bar)^i/i!] dXt[\[Mu],n+i,z0bar],{i,0,ord}],
X[\[Mu]_,z_,zbar_]:> If[ord >= 1, 1/Factorial[ord] (dX[\[Mu],ord-1,z0] + dXt[\[Mu],ord-1,z0bar]), X[\[Mu],z,zbar]],
expX[k_,z_,zbar_]:>Sum[If[i==0,1,(z-z0)^i/i!]If[j==0,1,(zbar-z0bar)^j/j!] (R[expX[k,z0,z0bar]*(expXPoly[k, i] /. x -> z0)*(expXPolyT[k, j] /. x -> z0bar)//Expand]),{i,0,ord},{j,0,ord}]}];


(* ::Section:: *)
(*End*)


End[];
EndPackage[];
