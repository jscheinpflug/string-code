(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Taylor`TypeII`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`TypeII`"];
Needs["StringCode`Taylor`"];


(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Check if field needs expanding*)


isAtPointHolo[\[Eta][n_, z_], z0_] := SameQ[z,z0];
isAtPointHolo[\[Xi][n_, z_], z0_] := SameQ[z,z0];
isAtPointHolo[d\[Phi][n_, z_], z0_] := SameQ[z,z0];
isAtPointHolo[dX[\[Mu]_, n_, z_], z0_] := SameQ[z,z0];
isAtPointHolo[\[Psi][\[Mu]_, n_, z_], z0_] := SameQ[z,z0];
isAtPointHolo[exp\[Phi]f[n_, z_], z0_] := SameQ[z,z0];
isAtPointHolo[exp\[Phi]b[n_, z_], z0_] := SameQ[z,z0];
isAtPointHolo[X[\[Mu]_,  z_, zbar_], z0_] := SameQ[z,z0];
isAtPointHolo[expX[k_, z_, zbar_], z0_] := SameQ[z,z0];
isAtPointHolo[field_, z0_] := False /; isAntiHolomorphic[Head[field]];
isAtPointAntiHolo[\[Eta]t[n_, zbar_], z0bar_] := SameQ[zbar,z0bar];
isAtPointAntiHolo[\[Xi]t[n_, zbar_], z0bar_] := SameQ[zbar,z0bar];
isAtPointAntiHolo[d\[Phi]t[n_, zbar_], z0bar_] := SameQ[zbar,z0bar];
isAtPointAntiHolo[dXt[\[Mu]_, n_, zbar_], z0bar_] := SameQ[zbar,z0bar];
isAtPointAntiHolo[\[Psi]t[\[Mu]_, n_, zbar_], z0bar_] := SameQ[zbar,z0bar];
isAtPointAntiHolo[exp\[Phi]tf[n_, zbar_], z0bar_] := SameQ[zbar,z0bar];
isAtPointAntiHolo[exp\[Phi]tb[n_, zbar_], z0bar_] := SameQ[zbar,z0bar];
isAtPointAntiHolo[X[\[Mu], z_, zbar_], z0bar_] := SameQ[zbar,z0bar];
isAtPointAntiHolo[expX[k_, z_, zbar_], z0bar_] := SameQ[zbar,z0bar];
isAtPointAntiHolo[field_, z0bar_] := False /; isHolomorphic[Head[field]];


(* ::Subsection:: *)
(*Define adding derivatives*)


addHoloDerivatives[\[Eta][n_,z_], ord_, z0_]:= (z-z0)^ord/Factorial[ord]\[Eta][n+ord,z0];


addHoloDerivatives[\[Xi][n_,z_], ord_, z0_]:= (z-z0)^ord/Factorial[ord]\[Xi][n+ord,z0];


addHoloDerivatives[d\[Phi][n_,z_], ord_, z0_]:= (z-z0)^ord/Factorial[ord]d\[Phi][n+ord,z0];


addHoloDerivatives[\[Psi][\[Mu]_,n_,z_], ord_, z0_]:= (z-z0)^ord/Factorial[ord]\[Psi][\[Mu],n+ord,z0];


addHoloDerivatives[X[\[Mu]_,z_,zbar_], ord_, z0_]:= If[ord>0, (z-z0)^ord/Factorial[ord] dX[\[Mu],ord-1,z0], X[\[Mu],z0,zbar]];


addHoloDerivatives[ProfileX[profile_, ders_List, z_, zbar_], ord_, z0_] := Module[{auxDerivativePolynomial},
auxDerivativePolynomial = derivativeOfExponential[1, ord]/.{E^(func[x]) :> 1};
(z-z0)^ord/Factorial[ord]R[auxDerivativePolynomial/.{Power[Derivative[m_][func][x], p_] :>
       Module[{i, interDers = {}, interdX = 1}, 
       Do[Module[{\[Mu]},AppendTo[interDers, \[Mu]]; interdX = interdX dX[\[Mu], m-1,x]], {i,1,p}];
       ProfileX[profile, Join[ders, interDers], x, zbar] interdX ],
       Derivative[m_][func][x] :>
       Module[{\[Mu]}, ProfileX[profile, Append[ders, \[Mu]], x, zbar] dX[\[Mu], m - 1, x]]}/.{x->z0}]
]


addHoloDerivatives[exp\[Phi]f[a_, z_], ord_, z0_] :=
  (z - z0)^ord/Factorial[ord] * 
    R[exp\[Phi]f[a, z0] * (phiPoly[a, ord] /. x -> z0)//Expand];


addHoloDerivatives[exp\[Phi]b[a_, z_], ord_, z0_] :=
  (z - z0)^ord/Factorial[ord] * 
    R[exp\[Phi]b[a, z0] * (phiPoly[a, ord] /. x -> z0)//Expand];


addAntiHoloDerivatives[\[Eta]t[n_,z_], ord_, z0bar_]:= (z-z0bar)^ord/Factorial[ord]\[Eta]t[n+ord,z0bar];


addAntiHoloDerivatives[\[Xi]t[n_,z_], ord_, z0bar_]:= (z-z0bar)^ord/Factorial[ord]\[Xi]t[n+ord,z0bar];


addAntiHoloDerivatives[d\[Phi]t[n_,z_], ord_, z0bar_]:= (z-z0bar)^ord/Factorial[ord]d\[Phi]t[n+ord,z0bar];


addAntiHoloDerivatives[\[Psi]t[\[Mu]_,n_,z_], ord_, z0bar_]:= (z-z0bar)^ord/Factorial[ord]\[Psi]t[\[Mu],n+ord,z0bar];


addAntiHoloDerivatives[X[\[Mu]_,z_,zbar_], ord_, z0bar_]:= If[ord > 0, (zbar-z0bar)^ord/Factorial[ord] dXt[\[Mu],ord-1,z0bar], X[\[Mu],z,z0bar]];


addAntiHoloDerivatives[ProfileX[profile_, ders_List, z_, zbar_], ord_, z0bar_] := Module[{auxDerivativePolynomial},
auxDerivativePolynomial = derivativeOfExponential[1, ord]/.{E^(func[x]) :> 1};
(zbar-z0bar)^ord/Factorial[ord]R[auxDerivativePolynomial/.{Power[Derivative[m_][func][x], p_] :>
       Module[{i, interDers = {}, interdX = 1}, 
       Do[Module[{\[Mu]},AppendTo[interDers, \[Mu]]; interdX = interdX dXt[\[Mu], m-1,x]], {i,1,p}];
       ProfileX[profile, Join[ders, interDers], z, x] interdX ],
       Derivative[m_][func][x] :>
       Module[{\[Mu]}, ProfileX[profile, Append[ders, \[Mu]], z, x] dXt[\[Mu], m - 1, x]]}/.{x->z0bar}]
]


addAntiHoloDerivatives[exp\[Phi]tf[a_, z_], ord_, z0bar_] :=
  (z - z0bar)^ord/Factorial[ord] *
    R[exp\[Phi]tf[a, z0bar] * (phiPolyT[a, ord] /. x -> z0bar)//Expand];


addAntiHoloDerivatives[exp\[Phi]tb[a_, z_], ord_, z0bar_] :=
  (z - z0bar)^ord/Factorial[ord] *
    R[exp\[Phi]tb[a, z0bar] * (phiPolyT[a, ord] /. x -> z0bar)//Expand];


addHoloDerivatives[dX[\[Mu]_,n_,z_], ord_, z0_]:= (z-z0)^ord/Factorial[ord]dX[\[Mu],n+ord,z0];


addHoloDerivatives[expX[k_, z_, zbar_], ord_, z0_] :=
  (z - z0)^ord/Factorial[ord] *
    R[expX[k, z0, zbar] * (expXPoly[k, ord] /. x -> z0)//Expand];


addAntiHoloDerivatives[dXt[\[Mu]_,n_,z_], ord_, z0bar_]:= (z-z0bar)^ord/Factorial[ord]dXt[\[Mu],n+ord,z0bar];


addAntiHoloDerivatives[expX[k_, z_, zbar_], ord_, z0bar_] :=
  (zbar - z0bar)^ord/Factorial[ord] *
    R[expX[k, z, z0bar] * (expXPolyT[k, ord] /. x -> z0bar)//Expand];


(* ::Subsection:: *)
(*Define Taylor expansions of exponentials*)


derivativeOfExponential[exponent_, n_]:= derivativeOfExponential[exponent, n] = D[E^(exponent func[x]), {x, n}];


phiPoly[a_, n_] := phiPoly[a, n] =
  Expand[
    derivativeOfExponential[a, n] /. {
      E^(a func[x]) :> 1,
      Derivative[m_][func][x] :> d\[Phi][m - 1, x]
    }
  ];


phiPolyT[a_, n_] := phiPolyT[a, n] = 
  Expand[
    derivativeOfExponential[a, n] /. {
      E^(a func[x]) :> 1,
      Derivative[m_][func][x] :> d\[Phi]t[m - 1, x]
    }
  ];


expXPoly[k_, n_] :=
  expXPoly[k, n] =
   Expand[derivativeOfExponential[I, n] /. {E^(I func[x]) :> 1,
      Power[Derivative[m_][func][x], p_] :>
       Module[{i},Product[Module[{\[Mu]}, k[\[Mu]] dX[\[Mu], m - 1, x]], {i, 1, p}]], 
       Derivative[m_][func][x] :>
       Module[{\[Mu]}, k[\[Mu]] dX[\[Mu], m - 1, x]]}];


expXPolyT[k_, n_] :=
  expXPolyT[k, n] =
   Expand[derivativeOfExponential[I, n] /. {E^(I func[x]) :> 1,
      Power[Derivative[m_][func][x], p_] :>
       Module[{i},Product[Module[{\[Mu]}, k[\[Mu]] dX[\[Mu], m - 1, x]], {i, 1, p}]], 
       Derivative[m_][func][x] :>
       Module[{\[Mu]}, k[\[Mu]] dX[\[Mu], m - 1, x]]}];


(* ::Subsection:: *)
(*Define Taylor*)


taylorRule[z0_, z0bar_, ord_] := 
Block[{i,j,x,func,n,z},
{b[n_,z_]:>Sum[If[i==0,1,(z-z0)^i/i!] b[n+i,z0],{i,0,ord}],
c[n_,z_]:>Sum[If[i==0,1,(z-z0)^i/i!] c[n+i,z0],{i,0,ord}],
\[Eta][n_,z_]:>Sum[If[i==0,1,(z-z0)^i/i!] \[Eta][n+i,z0],{i,0,ord}],
\[Xi][n_,z_]:>Sum[If[i==0,1,(z-z0)^i/i!] \[Xi][n+i,z0],{i,0,ord}],
d\[Phi][n_,z_]:>Sum[If[i==0,1,(z-z0)^i/i!] d\[Phi][n+i,z0],{i,0,ord}],
X[\[Mu]_,z_,zbar_]:> If[ord >= 1, 1/Factorial[ord] (dX[\[Mu],ord-1,z0] + dXt[\[Mu],ord-1,z0bar]), X[\[Mu],z,zbar]],
dX[\[Mu]_,n_,z_]:>Sum[If[i==0,1,(z-z0)^i/i!] dX[\[Mu],n+i,z0],{i,0,ord}],
\[Psi][\[Mu]_,n_,z_]:>Sum[If[i==0,1,(z-z0)^i/i!]\[Psi][\[Mu],n+i,z0],{i,0,ord}],
exp\[Phi]f[a_,z_]:>Sum[If[i==0,1,(z-z0)^i/i!](R[exp\[Phi]f[a, z0] * (phiPoly[a, i] /. x -> z0)//Expand]),{i,0,ord}],
exp\[Phi]b[a_,z_]:>Sum[If[i==0,1,(z-z0)^i/i!](R[exp\[Phi]b[a, z0] * (phiPoly[a, i] /. x -> z0)//Expand]),{i,0,ord}],
bt[n_,z_]:>Sum[If[i==0,1,(z-z0bar)^i/i!] bt[n+i,z0bar],{i,0,ord}],
ct[n_,z_]:>Sum[If[i==0,1,(z-z0bar)^i/i!]ct[n+i,z0bar],{i,0,ord}],
\[Eta]t[n_,z_]:>Sum[If[i==0,1,(z-z0bar)^i/i!] \[Eta]t[n+i,z0bar],{i,0,ord}],
\[Xi]t[n_,z_]:>Sum[If[i==0,1,(z-z0bar)^i/i!]\[Xi]t[n+i,z0bar],{i,0,ord}],
d\[Phi]t[n_,z_]:>Sum[If[i==0,1,(z-z0bar)^i/i!] d\[Phi]t[n+i,z0bar],{i,0,ord}],
dXt[\[Mu]_,n_,z_]:>Sum[If[i==0,1,(z-z0bar)^i/i!] dXt[\[Mu],n+i,z0bar],{i,0,ord}],
\[Psi]t[\[Mu]_,n_,z_]:>Sum[If[i==0,1,(z-z0bar)^i/i!] \[Psi]t[\[Mu],n+i,z0bar],{i,0,ord}],
exp\[Phi]tf[a_,z_]:>Sum[If[i==0,1,(z-z0bar)^i/i!](R[exp\[Phi]tf[a, z0bar] * (phiPolyT[a, i] /. x -> z0bar)]//Expand),{i,0,ord}],
exp\[Phi]tb[a_,z_]:>Sum[If[i==0,1,(z-z0bar)^i/i!](R[exp\[Phi]tb[a, z0bar] * (phiPolyT[a, i] /. x -> z0bar)//Expand]),{i,0,ord}],
expX[k_,z_,zbar_]:>Sum[If[i==0,1,(z-z0)^i/i!]If[j==0,1,(zbar-z0bar)^j/j!] (R[expX[k,z0,z0bar]*(expXPoly[k, i] /. x -> z0)*(expXPolyT[k, j] /. x -> z0bar)//Expand]),{i,0,ord},{j,0,ord}]}];


(* ::Section:: *)
(*End*)


End[];
EndPackage[];
