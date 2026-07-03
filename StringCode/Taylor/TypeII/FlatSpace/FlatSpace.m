(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Taylor`TypeII`FlatSpace`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];
Needs["StringCode`Symbols`TypeII`FlatSpace`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`TypeII`"];
Needs["StringCode`Wick`"];
Needs["StringCode`Wick`TypeII`"];
Needs["StringCode`Wick`TypeII`FlatSpace`"];
Needs["StringCode`Taylor`"];
Needs["StringCode`Taylor`TypeII`"];


(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Check if field needs expanding*)


(* ::Subsubsection:: *)
(*Free boson*)


isAtPointHolo[dX[\[Mu]_, n_, z_], z0_] := SameQ[z,z0];
isAtPointHolo[dH[i_, n_, z_], z0_] := SameQ[z,z0];
isAtPointHolo[ProfileX[profile_, ders_, z_, zbar_], z0_] := SameQ[z,z0];
isAtPointHolo[ProfileXHolo[profile_, ders_, z_], z0_] := SameQ[z,z0];
isAtPointHolo[expX[k_, z_, zbar_], z0_] := SameQ[z,z0];
isAtPointHolo[expXHolo[k_, z_], z0_] := SameQ[z,z0];
isAtPointHolo[expH[charges_, z_], z0_] := SameQ[z,z0];

isAtPointAntiHolo[dXt[\[Mu]_, n_, zbar_], z0bar_] := SameQ[zbar,z0bar];
isAtPointAntiHolo[dHt[i_, n_, zbar_], z0bar_] := SameQ[zbar,z0bar];
isAtPointAntiHolo[ProfileX[profile_, ders_, z_, zbar_], z0bar_] := SameQ[zbar,z0bar];
isAtPointAntiHolo[ProfileXAntiHolo[profile_, ders_, zbar_], z0bar_] := SameQ[zbar,z0bar];
isAtPointAntiHolo[expX[k_, z_, zbar_], z0bar_] := SameQ[zbar,z0bar];
isAtPointAntiHolo[expXAntiHolo[k_, zbar_], z0bar_] := SameQ[zbar,z0bar];
isAtPointAntiHolo[expHt[charges_, zbar_], z0bar_] := SameQ[zbar,z0bar];


(* ::Subsubsection:: *)
(*Free fermion*)


isAtPointHolo[\[Psi][\[Mu]_, n_, z_], z0_] := SameQ[z,z0];
isAtPointAntiHolo[\[Psi]t[\[Mu]_, n_, zbar_], z0bar_] := SameQ[zbar,z0bar];
isAtPointHolo[S[{alpha_, chirality : ("chiral" | "antichiral")}, q_, modes_List, der_, z_], z0_] := SameQ[z,z0];
isAtPointAntiHolo[St[{alpha_, chirality : ("chiral" | "antichiral")}, q_, modes_List, der_, zbar_], z0bar_] := SameQ[zbar,z0bar];


(* ::Subsubsection::Closed:: *)
(*Generic*)


isAtPointHolo[field_, z0_] := False /; isAntiHolomorphic[Head[field]] && !isHolomorphic[Head[field]];
isAtPointAntiHolo[field_, z0bar_] := False /; isHolomorphic[Head[field]] && !isAntiHolomorphic[Head[field]];


(* ::Subsection:: *)
(*Define adding derivatives*)


(* ::Subsubsection::Closed:: *)
(*Free boson*)


addHoloDerivatives[dX[\[Mu]_,n_,z_], ord_, z0_]:= taylorDerivativePrefactor[z-z0, ord]dX[\[Mu],n+ord,z0];
addHoloDerivatives[dH[i_,n_,z_], ord_, z0_]:= taylorDerivativePrefactor[z-z0, ord]dH[i,n+ord,z0];


addHoloDerivatives[ProfileX[profile_, ders_, z_, zbar_], ord_, z0_] :=
  taylorDerivativePrefactor[z - z0, ord] *
    ProfileX[profile, ders,  z0, zbar] * (ProfileXPoly[profile, ord] /. x -> z0)//Expand;


addHoloDerivatives[ProfileXHolo[profile_, ders_, z_], ord_, z0_] :=
  taylorDerivativePrefactor[z - z0, ord] *
    ProfileXHolo[profile, ders, z0] * (ProfileXPoly[profile, ord] /. x -> z0)//Expand;


addHoloDerivatives[expX[k_, z_, zbar_], ord_, z0_] :=
  taylorDerivativePrefactor[z - z0, ord] *
    expX[k, z0, zbar] * (expXPoly[k, ord] /. x -> z0)//Expand;


addHoloDerivatives[expXHolo[k_, z_], ord_, z0_] :=
  taylorDerivativePrefactor[z - z0, ord] *
    expXHolo[k, z0] * (expXPoly[k, ord] /. x -> z0)//Expand;


addHoloDerivatives[expH[charges_, z_], ord_, z0_] :=
  Expand[
    taylorDerivativePrefactor[z - z0, ord] *
      bosonizedExponentialDerivative[charges, ord, z0, dH, expH]
  ];


addAntiHoloDerivatives[dXt[\[Mu]_,n_,z_], ord_, z0bar_]:= taylorDerivativePrefactor[z-z0bar, ord]dXt[\[Mu],n+ord,z0bar];
addAntiHoloDerivatives[dHt[i_,n_,z_], ord_, z0bar_]:= taylorDerivativePrefactor[z-z0bar, ord]dHt[i,n+ord,z0bar];


addAntiHoloDerivatives[ProfileX[profile_, ders_, z_, zbar_], ord_, z0bar_] :=
  taylorDerivativePrefactor[zbar - z0bar, ord] *
    ProfileX[profile, ders, z, z0bar] * (ProfileXPolyT[profile, ord] /. x -> z0bar)//Expand;


addAntiHoloDerivatives[ProfileXAntiHolo[profile_, ders_, zbar_], ord_, z0bar_] :=
  taylorDerivativePrefactor[zbar - z0bar, ord] *
    ProfileXAntiHolo[profile, ders, z0bar] * (ProfileXPolyT[profile, ord] /. x -> z0bar)//Expand;


addAntiHoloDerivatives[expX[k_, z_, zbar_], ord_, z0bar_] :=
  taylorDerivativePrefactor[zbar - z0bar, ord] *
    expX[k, z, z0bar] * (expXPolyT[k, ord] /. x -> z0bar)//Expand;


addAntiHoloDerivatives[expXAntiHolo[k_, zbar_], ord_, z0bar_] :=
  taylorDerivativePrefactor[zbar - z0bar, ord] *
    expXAntiHolo[k, z0bar] * (expXPolyT[k, ord] /. x -> z0bar)//Expand;


addAntiHoloDerivatives[expHt[charges_, zbar_], ord_, z0bar_] :=
  Expand[
    taylorDerivativePrefactor[zbar - z0bar, ord] *
      bosonizedExponentialDerivative[charges, ord, z0bar, dHt, expHt]
  ];


(* ::Subsubsection::Closed:: *)
(*Free fermion*)


addHoloDerivatives[\[Psi][\[Mu]_,n_,z_], ord_, z0_]:= taylorDerivativePrefactor[z-z0, ord]\[Psi][\[Mu],n+ord,z0];
addAntiHoloDerivatives[\[Psi]t[\[Mu]_,n_,z_], ord_, z0bar_]:= taylorDerivativePrefactor[z-z0bar, ord]\[Psi]t[\[Mu],n+ord,z0bar];
addHoloDerivatives[S[{alpha_, chirality : ("chiral" | "antichiral")}, q_, modes_List, der_, z_], ord_, z0_] := taylorDerivativePrefactor[z-z0, ord] S[{alpha, chirality}, q, modes, der + ord, z0];
addAntiHoloDerivatives[St[{alpha_, chirality : ("chiral" | "antichiral")}, q_, modes_List, der_, zbar_], ord_, z0bar_] := taylorDerivativePrefactor[zbar-z0bar, ord] St[{alpha, chirality}, q, modes, der + ord, z0bar];


(* ::Subsection:: *)
(*Define Taylor expansions of exponentials*)


ProfileXPoly::usage = "Computes the polynomial in holomorphic derivatives of X one needs when differentiating Profiles in X";
ProfileXPolyT::usage = "Computes the polynomial in antiholomorphic derivatives of X one needs when differentiating Profiles in X";

profileXPolyCached::usage = "profileXPolyCached[profile, n] is the cached symbolic Taylor template behind ProfileXPoly; its Module dummy indices are frozen in the cache and must be freshened on retrieval (see ProfileXPoly).";
profileXPolyCached[profile_, n_] := profileXPolyCached[profile, n] =
   Expand[derivativeOfExponential[1, n] /. {E^(func[x]) :> 1,
      Power[Derivative[m_][func][x], p_] :>
       Module[{i},Product[Module[{\[Mu]}, der[profile][\[Mu]] dX[\[Mu], m - 1, x]], {i, 1, p}]],
       Derivative[m_][func][x] :>
       Module[{\[Mu]}, der[profile][\[Mu]] dX[\[Mu], m - 1, x]]}];

ProfileXPoly[profile_, n_] := Module[{cached, oldNames, newNames},
  cached = profileXPolyCached[profile, n];
  oldNames = DeleteDuplicates @ Cases[cached,
     s_Symbol /; StringContainsQ[SymbolName[s], "$" ~~ DigitCharacter ..],
     {0, Infinity}, Heads -> True];
  newNames = Table[Unique["\[Mu]"], Length[oldNames]];
  cached /. Thread[oldNames -> newNames]
];
       
profileXPolyTCached::usage = "profileXPolyTCached[profile, n] is the cached symbolic anti-holomorphic Taylor template behind ProfileXPolyT; its Module dummy indices are frozen in the cache and must be freshened on retrieval (see ProfileXPolyT).";
profileXPolyTCached[profile_, n_] := profileXPolyTCached[profile, n] =
   Expand[derivativeOfExponential[1, n] /. {E^(func[x]) :> 1,
      Power[Derivative[m_][func][x], p_] :>
       Module[{i},Product[Module[{\[Mu]}, der[profile][\[Mu]] dXt[\[Mu], m - 1, x]], {i, 1, p}]],
       Derivative[m_][func][x] :>
       Module[{\[Mu]}, der[profile][\[Mu]] dXt[\[Mu], m - 1, x]]}];

ProfileXPolyT[profile_, n_] := Module[{cached, oldNames, newNames},
  cached = profileXPolyTCached[profile, n];
  oldNames = DeleteDuplicates @ Cases[cached,
     s_Symbol /; StringContainsQ[SymbolName[s], "$" ~~ DigitCharacter ..],
     {0, Infinity}, Heads -> True];
  newNames = Table[Unique["\[Mu]"], Length[oldNames]];
  cached /. Thread[oldNames -> newNames]
];


expXPoly::usage = "Computes the polynomial in holomorphic derivatives of X one needs when differentiating exponentials in X";
expXPolyT::usage = "Computes the polynomial in antiholomorphic derivatives of X one needs when differentiating exponentials in X";

expXPoly[k_, n_] := expXPoly[k, n] =
   Expand[derivativeOfExponential[I, n] /. {E^(I func[x]) :> 1,
      Power[Derivative[m_][func][x], p_] :>
       Module[{i},Product[Module[{\[Mu]}, k[\[Mu]] dX[\[Mu], m - 1, x]], {i, 1, p}]], 
       Derivative[m_][func][x] :>
       Module[{\[Mu]}, k[\[Mu]] dX[\[Mu], m - 1, x]]}];
       
expXPolyT[k_, n_] := expXPolyT[k, n] =
   Expand[derivativeOfExponential[I, n] /. {E^(I func[x]) :> 1,
      Power[Derivative[m_][func][x], p_] :>
       Module[{i},Product[Module[{\[Mu]}, k[\[Mu]] dXt[\[Mu], m - 1, x]], {i, 1, p}]], 
       Derivative[m_][func][x] :>
       Module[{\[Mu]}, k[\[Mu]] dXt[\[Mu], m - 1, x]]}];       

(* ::Section:: *)
(*End*)


End[];
EndPackage[];
