(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Taylor`TypeII`FlatSpace`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];
Needs["StringCode`Symbols`TypeII`FlatSpace`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`TypeII`"];
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
isAtPointHolo[ProfileX[profile_, ders_, z_, zbar_], z0_] := SameQ[z,z0];
isAtPointHolo[ProfileXHolo[profile_, ders_, z_], z0_] := SameQ[z,z0];
isAtPointHolo[expX[k_, z_, zbar_], z0_] := SameQ[z,z0];
isAtPointHolo[expXHolo[k_, z_], z0_] := SameQ[z,z0];

isAtPointAntiHolo[dXt[\[Mu]_, n_, zbar_], z0bar_] := SameQ[zbar,z0bar];
isAtPointAntiHolo[ProfileX[profile_, ders_, z_, zbar_], z0bar_] := SameQ[zbar,z0bar];
isAtPointAntiHolo[ProfileXAntiHolo[profile_, ders_, zbar_], z0bar_] := SameQ[zbar,z0bar];
isAtPointAntiHolo[expX[k_, z_, zbar_], z0bar_] := SameQ[zbar,z0bar];
isAtPointAntiHolo[expXAntiHolo[k_, zbar_], z0bar_] := SameQ[zbar,z0bar];


(* ::Subsubsection:: *)
(*Free fermion*)


isAtPointHolo[\[Psi][\[Mu]_, n_, z_], z0_] := SameQ[z,z0];
isAtPointAntiHolo[\[Psi]t[\[Mu]_, n_, zbar_], z0bar_] := SameQ[zbar,z0bar];


(* ::Subsubsection::Closed:: *)
(*Generic*)


isAtPointHolo[field_, z0_] := False /; isAntiHolomorphic[Head[field]];
isAtPointAntiHolo[field_, z0bar_] := False /; isHolomorphic[Head[field]];


(* ::Subsection:: *)
(*Define adding derivatives*)


(* ::Subsubsection::Closed:: *)
(*Free boson*)


addHoloDerivatives[dX[\[Mu]_,n_,z_], ord_, z0_]:= (z-z0)^ord/Factorial[ord]dX[\[Mu],n+ord,z0];


addHoloDerivatives[ProfileX[profile_, ders_, z_, zbar_], ord_, z0_] :=
  (z - z0)^ord/Factorial[ord] *
    ProfileX[profile, ders,  z0, zbar] * (ProfileXPoly[profile, ord] /. x -> z0)//Expand;


addHoloDerivatives[ProfileXHolo[profile_, ders_, z_], ord_, z0_] :=
  (z - z0)^ord/Factorial[ord] *
    ProfileXHolo[profile, ders, z0] * (ProfileXPoly[profile, ord] /. x -> z0)//Expand;


addHoloDerivatives[expX[k_, z_, zbar_], ord_, z0_] :=
  (z - z0)^ord/Factorial[ord] *
    expX[k, z0, zbar] * (expXPoly[k, ord] /. x -> z0)//Expand;


addHoloDerivatives[expXHolo[k_, z_], ord_, z0_] :=
  (z - z0)^ord/Factorial[ord] *
    expXHolo[k, z0] * (expXPoly[k, ord] /. x -> z0)//Expand;


addAntiHoloDerivatives[dXt[\[Mu]_,n_,z_], ord_, z0bar_]:= (z-z0bar)^ord/Factorial[ord]dXt[\[Mu],n+ord,z0bar];


addAntiHoloDerivatives[ProfileX[profile_, ders_, z_, zbar_], ord_, z0bar_] :=
  (zbar - z0bar)^ord/Factorial[ord] *
    ProfileX[profile, ders, z, z0bar] * (ProfileXPolyT[profile, ord] /. x -> z0bar)//Expand;


addAntiHoloDerivatives[ProfileXAntiHolo[profile_, ders_, zbar_], ord_, z0bar_] :=
  (zbar - z0bar)^ord/Factorial[ord] *
    ProfileXAntiHolo[profile, ders, z0bar] * (ProfileXPolyT[profile, ord] /. x -> z0bar)//Expand;


addAntiHoloDerivatives[expX[k_, z_, zbar_], ord_, z0bar_] :=
  (zbar - z0bar)^ord/Factorial[ord] *
    expX[k, z, z0bar] * (expXPolyT[k, ord] /. x -> z0bar)//Expand;


addAntiHoloDerivatives[expXAntiHolo[k_, zbar_], ord_, z0bar_] :=
  (zbar - z0bar)^ord/Factorial[ord] *
    expXAntiHolo[k, z0bar] * (expXPolyT[k, ord] /. x -> z0bar)//Expand;


(* ::Subsubsection::Closed:: *)
(*Free fermion*)


addHoloDerivatives[\[Psi][\[Mu]_,n_,z_], ord_, z0_]:= (z-z0)^ord/Factorial[ord]\[Psi][\[Mu],n+ord,z0];
addAntiHoloDerivatives[\[Psi]t[\[Mu]_,n_,z_], ord_, z0bar_]:= (z-z0bar)^ord/Factorial[ord]\[Psi]t[\[Mu],n+ord,z0bar];


(* ::Subsection:: *)
(*Define Taylor expansions of exponentials*)


ProfileXPoly::usage = "Computes the polynomial in holomorphic derivatives of X one needs when differentiating Profiles in X";
ProfileXPolyT::usage = "Computes the polynomial in antiholomorphic derivatives of X one needs when differentiating Profiles in X";

ProfileXPoly[profile_, n_] := ProfileXPoly[profile, n] =
   Expand[derivativeOfExponential[1, n] /. {E^(func[x]) :> 1,
      Power[Derivative[m_][func][x], p_] :>
       Module[{i},Product[Module[{\[Mu]}, der[profile][\[Mu]] dX[\[Mu], m - 1, x]], {i, 1, p}]], 
       Derivative[m_][func][x] :>
       Module[{\[Mu]}, der[profile][\[Mu]] dX[\[Mu], m - 1, x]]}];
       
ProfileXPolyT[profile_, n_] := ProfileXPolyT[profile, n] =
   Expand[derivativeOfExponential[1, n] /. {E^(func[x]) :> 1,
      Power[Derivative[m_][func][x], p_] :>
       Module[{i},Product[Module[{\[Mu]}, der[profile][\[Mu]] dXt[\[Mu], m - 1, x]], {i, 1, p}]], 
       Derivative[m_][func][x] :>
       Module[{\[Mu]}, der[profile][\[Mu]] dXt[\[Mu], m - 1, x]]}];


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
