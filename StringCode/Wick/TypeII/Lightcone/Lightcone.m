(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Wick`TypeII`Lightcone`"]
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];
Needs["StringCode`Symbols`TypeII`FlatSpace`"];
Needs["StringCode`Symbols`TypeII`Lightcone`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`TypeII`"];
Needs["StringCode`Wick`"];
Needs["StringCode`Wick`TypeII`"];
Needs["StringCode`Conventions`TypeII`"];


(* ::Section:: *)
(*Declare public methods*)


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Define Wick contractions for lightcone indices*)


(* ::Subsubsection:: *)
(*Free boson with lightcone indices*)


(* Lightcone-lightcone contractions produce eta metric factors *)
Wick[dX[p, n_, z_], dX[m, m_, w_]] := Wick[dX[p, n, z], dX[m, m, w]] =
  Module[{zd}, \[Eta][p, m] (-1)^m D[(-1/2)*\[Alpha]p/(zd - w)^2, {zd, n + m}] /. {zd -> z}];
Wick[dX[m, n_, z_], dX[p, m_, w_]] := Wick[dX[m, n, z], dX[p, m, w]] =
  Module[{zd}, \[Eta][m, p] (-1)^m D[(-1/2)*\[Alpha]p/(zd - w)^2, {zd, n + m}] /. {zd -> z}];
Wick[dX[p, n_, z_], dX[p, m_, w_]] := 0;  (* \[Eta][p,p] = 0 *)
Wick[dX[m, n_, z_], dX[m, m_, w_]] := 0;  (* \[Eta][m,m] = 0 *)

(* Transverse contractions produce deltaT - any non-lightcone symbol is transverse *)
Wick[dX[i_, n_, z_], dX[j_, mm_, w_]] /; transverseIndexQ[i] && transverseIndexQ[j] :=
  Module[{zd}, \[Delta]T[i, j] (-1)^mm D[(-1/2)*\[Alpha]p/(zd - w)^2, {zd, n + mm}] /. {zd -> z}];

(* Mixed lightcone-transverse vanish *)
Wick[dX[p, n_, z_], dX[i_, mm_, w_]] /; transverseIndexQ[i] := 0;
Wick[dX[m, n_, z_], dX[i_, mm_, w_]] /; transverseIndexQ[i] := 0;
Wick[dX[i_, n_, z_], dX[p, mm_, w_]] /; transverseIndexQ[i] := 0;
Wick[dX[i_, n_, z_], dX[m, mm_, w_]] /; transverseIndexQ[i] := 0;

(* Antiholomorphic dXt with lightcone indices *)
Wick[dXt[p, n_, z_], dXt[m, m_, w_]] := Wick[dXt[p, n, z], dXt[m, m, w]] =
  Module[{zd}, \[Eta][p, m] (-1)^m D[(-1/2)*\[Alpha]p/(zd - w)^2, {zd, n + m}] /. {zd -> z}];
Wick[dXt[m, n_, z_], dXt[p, m_, w_]] := Wick[dXt[m, n, z], dXt[p, m, w]] =
  Module[{zd}, \[Eta][m, p] (-1)^m D[(-1/2)*\[Alpha]p/(zd - w)^2, {zd, n + m}] /. {zd -> z}];
Wick[dXt[p, n_, z_], dXt[p, m_, w_]] := 0;
Wick[dXt[m, n_, z_], dXt[m, m_, w_]] := 0;

Wick[dXt[i_, n_, z_], dXt[j_, mm_, w_]] /; transverseIndexQ[i] && transverseIndexQ[j] :=
  Module[{zd}, \[Delta]T[i, j] (-1)^mm D[(-1/2)*\[Alpha]p/(zd - w)^2, {zd, n + mm}] /. {zd -> z}];

Wick[dXt[p, n_, z_], dXt[i_, mm_, w_]] /; transverseIndexQ[i] := 0;
Wick[dXt[m, n_, z_], dXt[i_, mm_, w_]] /; transverseIndexQ[i] := 0;
Wick[dXt[i_, n_, z_], dXt[p, mm_, w_]] /; transverseIndexQ[i] := 0;
Wick[dXt[i_, n_, z_], dXt[m, mm_, w_]] /; transverseIndexQ[i] := 0;


(* ::Subsubsection:: *)
(*Free fermion with lightcone indices*)


(* Lightcone-lightcone contractions *)
Wick[\[Psi][p, n_, z_], \[Psi][m, m_, w_]] := Wick[\[Psi][p, n, z], \[Psi][m, m, w]] =
  Module[{zd}, \[Eta][p, m] (-1)^m D[fermionToBosonWickRatio/(zd - w), {zd, n + m}] /. {zd -> z}];
Wick[\[Psi][m, n_, z_], \[Psi][p, m_, w_]] := Wick[\[Psi][m, n, z], \[Psi][p, m, w]] =
  Module[{zd}, \[Eta][m, p] (-1)^m D[fermionToBosonWickRatio/(zd - w), {zd, n + m}] /. {zd -> z}];
Wick[\[Psi][p, n_, z_], \[Psi][p, m_, w_]] := 0;  (* \[Eta][p,p] = 0 *)
Wick[\[Psi][m, n_, z_], \[Psi][m, m_, w_]] := 0;  (* \[Eta][m,m] = 0 *)

(* Transverse contractions - any non-lightcone symbol is transverse *)
Wick[\[Psi][i_, n_, z_], \[Psi][j_, mm_, w_]] /; transverseIndexQ[i] && transverseIndexQ[j] :=
  Module[{zd}, \[Delta]T[i, j] (-1)^mm D[fermionToBosonWickRatio/(zd - w), {zd, n + mm}] /. {zd -> z}];

(* Mixed lightcone-transverse vanish *)
Wick[\[Psi][p, n_, z_], \[Psi][i_, mm_, w_]] /; transverseIndexQ[i] := 0;
Wick[\[Psi][m, n_, z_], \[Psi][i_, mm_, w_]] /; transverseIndexQ[i] := 0;
Wick[\[Psi][i_, n_, z_], \[Psi][p, mm_, w_]] /; transverseIndexQ[i] := 0;
Wick[\[Psi][i_, n_, z_], \[Psi][m, mm_, w_]] /; transverseIndexQ[i] := 0;

(* Antiholomorphic psit with lightcone indices *)
Wick[\[Psi]t[p, n_, z_], \[Psi]t[m, m_, w_]] := Wick[\[Psi]t[p, n, z], \[Psi]t[m, m, w]] =
  Module[{zd}, \[Eta][p, m] (-1)^m D[fermionToBosonWickRatio/(zd - w), {zd, n + m}] /. {zd -> z}];
Wick[\[Psi]t[m, n_, z_], \[Psi]t[p, m_, w_]] := Wick[\[Psi]t[m, n, z], \[Psi]t[p, m, w]] =
  Module[{zd}, \[Eta][m, p] (-1)^m D[fermionToBosonWickRatio/(zd - w), {zd, n + m}] /. {zd -> z}];
Wick[\[Psi]t[p, n_, z_], \[Psi]t[p, m_, w_]] := 0;
Wick[\[Psi]t[m, n_, z_], \[Psi]t[m, m_, w_]] := 0;

Wick[\[Psi]t[i_, n_, z_], \[Psi]t[j_, mm_, w_]] /; transverseIndexQ[i] && transverseIndexQ[j] :=
  Module[{zd}, \[Delta]T[i, j] (-1)^mm D[fermionToBosonWickRatio/(zd - w), {zd, n + mm}] /. {zd -> z}];

Wick[\[Psi]t[p, n_, z_], \[Psi]t[i_, mm_, w_]] /; transverseIndexQ[i] := 0;
Wick[\[Psi]t[m, n_, z_], \[Psi]t[i_, mm_, w_]] /; transverseIndexQ[i] := 0;
Wick[\[Psi]t[i_, n_, z_], \[Psi]t[p, mm_, w_]] /; transverseIndexQ[i] := 0;
Wick[\[Psi]t[i_, n_, z_], \[Psi]t[m, mm_, w_]] /; transverseIndexQ[i] := 0;


(* ::Subsection:: *)
(*SWick for profiles with lightcone indices*)


(* ProfileX with lightcone derivatives *)
SWick[dX[p, n_, z_], ProfileX[profile_, ders_, w_, wbar_]] :=
  SWick[dX[p, n, z], ProfileX[profile, ders, w, wbar]] =
  Module[{zd}, (-\[Alpha]p/2 der[profile][p]) D[1/(zd - w), {zd, n}] /. {zd -> z}];
SWick[ProfileX[profile_, ders_, w_, wbar_], dX[p, n_, z_]] :=
  SWick[ProfileX[profile, ders, w, wbar], dX[p, n, z]] =
  Module[{zd}, (-\[Alpha]p/2 der[profile][p]) D[1/(zd - w), {zd, n}] /. {zd -> z}];

SWick[dX[m, n_, z_], ProfileX[profile_, ders_, w_, wbar_]] :=
  SWick[dX[m, n, z], ProfileX[profile, ders, w, wbar]] =
  Module[{zd}, (-\[Alpha]p/2 der[profile][m]) D[1/(zd - w), {zd, n}] /. {zd -> z}];
SWick[ProfileX[profile_, ders_, w_, wbar_], dX[m, n_, z_]] :=
  SWick[ProfileX[profile, ders, w, wbar], dX[m, n, z]] =
  Module[{zd}, (-\[Alpha]p/2 der[profile][m]) D[1/(zd - w), {zd, n}] /. {zd -> z}];

SWick[dX[i_, n_, z_], ProfileX[profile_, ders_, w_, wbar_]] /; transverseIndexQ[i] :=
  SWick[dX[i, n, z], ProfileX[profile, ders, w, wbar]] =
  Module[{zd}, (-\[Alpha]p/2 der[profile][i]) D[1/(zd - w), {zd, n}] /. {zd -> z}];
SWick[ProfileX[profile_, ders_, w_, wbar_], dX[i_, n_, z_]] /; transverseIndexQ[i] :=
  SWick[ProfileX[profile, ders, w, wbar], dX[i, n, z]] =
  Module[{zd}, (-\[Alpha]p/2 der[profile][i]) D[1/(zd - w), {zd, n}] /. {zd -> z}];

(* Antiholomorphic dXt with profiles *)
SWick[dXt[p, n_, z_], ProfileX[profile_, ders_, w_, wbar_]] :=
  SWick[dXt[p, n, z], ProfileX[profile, ders, w, wbar]] =
  Module[{zd}, (-\[Alpha]p/2 der[profile][p]) D[1/(zd - wbar), {zd, n}] /. {zd -> z}];
SWick[ProfileX[profile_, ders_, w_, wbar_], dXt[p, n_, z_]] :=
  SWick[ProfileX[profile, ders, w, wbar], dXt[p, n, z]] =
  Module[{zd}, (-\[Alpha]p/2 der[profile][p]) D[1/(zd - wbar), {zd, n}] /. {zd -> z}];

SWick[dXt[m, n_, z_], ProfileX[profile_, ders_, w_, wbar_]] :=
  SWick[dXt[m, n, z], ProfileX[profile, ders, w, wbar]] =
  Module[{zd}, (-\[Alpha]p/2 der[profile][m]) D[1/(zd - wbar), {zd, n}] /. {zd -> z}];
SWick[ProfileX[profile_, ders_, w_, wbar_], dXt[m, n_, z_]] :=
  SWick[ProfileX[profile, ders, w, wbar], dXt[m, n, z]] =
  Module[{zd}, (-\[Alpha]p/2 der[profile][m]) D[1/(zd - wbar), {zd, n}] /. {zd -> z}];

SWick[dXt[i_, n_, z_], ProfileX[profile_, ders_, w_, wbar_]] /; transverseIndexQ[i] :=
  SWick[dXt[i, n, z], ProfileX[profile, ders, w, wbar]] =
  Module[{zd}, (-\[Alpha]p/2 der[profile][i]) D[1/(zd - wbar), {zd, n}] /. {zd -> z}];
SWick[ProfileX[profile_, ders_, w_, wbar_], dXt[i_, n_, z_]] /; transverseIndexQ[i] :=
  SWick[ProfileX[profile, ders, w, wbar], dXt[i, n, z]] =
  Module[{zd}, (-\[Alpha]p/2 der[profile][i]) D[1/(zd - wbar), {zd, n}] /. {zd -> z}];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
