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
(* Note: use nn_ for derivative order to avoid shadowing lightcone index m *)
Wick[dX[p, n_, z_], dX[m, nn_, w_]] := Wick[dX[p, n, z], dX[m, nn, w]] =
  Module[{zd}, \[Eta]LC[p, m] (-1)^nn D[(-1/2)*\[Alpha]p/(zd - w)^2, {zd, n + nn}] /. {zd -> z}];
Wick[dX[m, n_, z_], dX[p, nn_, w_]] := Wick[dX[m, n, z], dX[p, nn, w]] =
  Module[{zd}, \[Eta]LC[m, p] (-1)^nn D[(-1/2)*\[Alpha]p/(zd - w)^2, {zd, n + nn}] /. {zd -> z}];
Wick[dX[p, n_, z_], dX[p, nn_, w_]] := 0;  (* \[Eta]LC[p,p] = 0 *)
Wick[dX[m, n_, z_], dX[m, nn_, w_]] := 0;  (* \[Eta]LC[m,m] = 0 *)

(* Transverse contractions produce deltaT - any non-lightcone symbol is transverse *)
Wick[dX[i_, n_, z_], dX[j_, mm_, w_]] /; transverseIndexQ[i] && transverseIndexQ[j] :=
  Module[{zd}, \[Delta]T[i, j] (-1)^mm D[(-1/2)*\[Alpha]p/(zd - w)^2, {zd, n + mm}] /. {zd -> z}];

(* Mixed lightcone-transverse vanish *)
Wick[dX[p, n_, z_], dX[i_, mm_, w_]] /; transverseIndexQ[i] := 0;
Wick[dX[m, n_, z_], dX[i_, mm_, w_]] /; transverseIndexQ[i] := 0;
Wick[dX[i_, n_, z_], dX[p, mm_, w_]] /; transverseIndexQ[i] := 0;
Wick[dX[i_, n_, z_], dX[m, mm_, w_]] /; transverseIndexQ[i] := 0;

(* Antiholomorphic dXt with lightcone indices *)
Wick[dXt[p, n_, z_], dXt[m, nn_, w_]] := Wick[dXt[p, n, z], dXt[m, nn, w]] =
  Module[{zd}, \[Eta]LC[p, m] (-1)^nn D[(-1/2)*\[Alpha]p/(zd - w)^2, {zd, n + nn}] /. {zd -> z}];
Wick[dXt[m, n_, z_], dXt[p, nn_, w_]] := Wick[dXt[m, n, z], dXt[p, nn, w]] =
  Module[{zd}, \[Eta]LC[m, p] (-1)^nn D[(-1/2)*\[Alpha]p/(zd - w)^2, {zd, n + nn}] /. {zd -> z}];
Wick[dXt[p, n_, z_], dXt[p, nn_, w_]] := 0;
Wick[dXt[m, n_, z_], dXt[m, nn_, w_]] := 0;

Wick[dXt[i_, n_, z_], dXt[j_, mm_, w_]] /; transverseIndexQ[i] && transverseIndexQ[j] :=
  Module[{zd}, \[Delta]T[i, j] (-1)^mm D[(-1/2)*\[Alpha]p/(zd - w)^2, {zd, n + mm}] /. {zd -> z}];

Wick[dXt[p, n_, z_], dXt[i_, mm_, w_]] /; transverseIndexQ[i] := 0;
Wick[dXt[m, n_, z_], dXt[i_, mm_, w_]] /; transverseIndexQ[i] := 0;
Wick[dXt[i_, n_, z_], dXt[p, mm_, w_]] /; transverseIndexQ[i] := 0;
Wick[dXt[i_, n_, z_], dXt[m, mm_, w_]] /; transverseIndexQ[i] := 0;


(* ::Subsubsection:: *)
(*Free fermion with lightcone indices*)


(* Lightcone-lightcone contractions *)
Wick[\[Psi][p, n_, z_], \[Psi][m, nn_, w_]] := Wick[\[Psi][p, n, z], \[Psi][m, nn, w]] =
  Module[{zd}, \[Eta]LC[p, m] (-1)^nn D[fermionToBosonWickRatio/(zd - w), {zd, n + nn}] /. {zd -> z}];
Wick[\[Psi][m, n_, z_], \[Psi][p, nn_, w_]] := Wick[\[Psi][m, n, z], \[Psi][p, nn, w]] =
  Module[{zd}, \[Eta]LC[m, p] (-1)^nn D[fermionToBosonWickRatio/(zd - w), {zd, n + nn}] /. {zd -> z}];
Wick[\[Psi][p, n_, z_], \[Psi][p, nn_, w_]] := 0;  (* \[Eta]LC[p,p] = 0 *)
Wick[\[Psi][m, n_, z_], \[Psi][m, nn_, w_]] := 0;  (* \[Eta]LC[m,m] = 0 *)

(* Transverse contractions - any non-lightcone symbol is transverse *)
Wick[\[Psi][i_, n_, z_], \[Psi][j_, mm_, w_]] /; transverseIndexQ[i] && transverseIndexQ[j] :=
  Module[{zd}, \[Delta]T[i, j] (-1)^mm D[fermionToBosonWickRatio/(zd - w), {zd, n + mm}] /. {zd -> z}];

(* Mixed lightcone-transverse vanish *)
Wick[\[Psi][p, n_, z_], \[Psi][i_, mm_, w_]] /; transverseIndexQ[i] := 0;
Wick[\[Psi][m, n_, z_], \[Psi][i_, mm_, w_]] /; transverseIndexQ[i] := 0;
Wick[\[Psi][i_, n_, z_], \[Psi][p, mm_, w_]] /; transverseIndexQ[i] := 0;
Wick[\[Psi][i_, n_, z_], \[Psi][m, mm_, w_]] /; transverseIndexQ[i] := 0;

(* Antiholomorphic psit with lightcone indices *)
Wick[\[Psi]t[p, n_, z_], \[Psi]t[m, nn_, w_]] := Wick[\[Psi]t[p, n, z], \[Psi]t[m, nn, w]] =
  Module[{zd}, \[Eta]LC[p, m] (-1)^nn D[fermionToBosonWickRatio/(zd - w), {zd, n + nn}] /. {zd -> z}];
Wick[\[Psi]t[m, n_, z_], \[Psi]t[p, nn_, w_]] := Wick[\[Psi]t[m, n, z], \[Psi]t[p, nn, w]] =
  Module[{zd}, \[Eta]LC[m, p] (-1)^nn D[fermionToBosonWickRatio/(zd - w), {zd, n + nn}] /. {zd -> z}];
Wick[\[Psi]t[p, n_, z_], \[Psi]t[p, nn_, w_]] := 0;
Wick[\[Psi]t[m, n_, z_], \[Psi]t[m, nn_, w_]] := 0;

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

(* ProfileXHolo with dX - lightcone indices *)
SWick[dX[p, n_, z_], ProfileXHolo[profile_, ders_, w_]] :=
  SWick[dX[p, n, z], ProfileXHolo[profile, ders, w]] =
  Module[{zd}, (-\[Alpha]p/2 der[profile][p]) D[1/(zd - w), {zd, n}] /. {zd -> z}];
SWick[ProfileXHolo[profile_, ders_, w_], dX[p, n_, z_]] :=
  SWick[ProfileXHolo[profile, ders, w], dX[p, n, z]] =
  Module[{zd}, (-\[Alpha]p/2 der[profile][p]) D[1/(zd - w), {zd, n}] /. {zd -> z}];

SWick[dX[m, n_, z_], ProfileXHolo[profile_, ders_, w_]] :=
  SWick[dX[m, n, z], ProfileXHolo[profile, ders, w]] =
  Module[{zd}, (-\[Alpha]p/2 der[profile][m]) D[1/(zd - w), {zd, n}] /. {zd -> z}];
SWick[ProfileXHolo[profile_, ders_, w_], dX[m, n_, z_]] :=
  SWick[ProfileXHolo[profile, ders, w], dX[m, n, z]] =
  Module[{zd}, (-\[Alpha]p/2 der[profile][m]) D[1/(zd - w), {zd, n}] /. {zd -> z}];

SWick[dX[i_, n_, z_], ProfileXHolo[profile_, ders_, w_]] /; transverseIndexQ[i] :=
  SWick[dX[i, n, z], ProfileXHolo[profile, ders, w]] =
  Module[{zd}, (-\[Alpha]p/2 der[profile][i]) D[1/(zd - w), {zd, n}] /. {zd -> z}];
SWick[ProfileXHolo[profile_, ders_, w_], dX[i_, n_, z_]] /; transverseIndexQ[i] :=
  SWick[ProfileXHolo[profile, ders, w], dX[i, n, z]] =
  Module[{zd}, (-\[Alpha]p/2 der[profile][i]) D[1/(zd - w), {zd, n}] /. {zd -> z}];

(* ProfileXAntiHolo with dXt - lightcone indices *)
SWick[dXt[p, n_, z_], ProfileXAntiHolo[profile_, ders_, wbar_]] :=
  SWick[dXt[p, n, z], ProfileXAntiHolo[profile, ders, wbar]] =
  Module[{zd}, (-\[Alpha]p/2 der[profile][p]) D[1/(zd - wbar), {zd, n}] /. {zd -> z}];
SWick[ProfileXAntiHolo[profile_, ders_, wbar_], dXt[p, n_, z_]] :=
  SWick[ProfileXAntiHolo[profile, ders, wbar], dXt[p, n, z]] =
  Module[{zd}, (-\[Alpha]p/2 der[profile][p]) D[1/(zd - wbar), {zd, n}] /. {zd -> z}];

SWick[dXt[m, n_, z_], ProfileXAntiHolo[profile_, ders_, wbar_]] :=
  SWick[dXt[m, n, z], ProfileXAntiHolo[profile, ders, wbar]] =
  Module[{zd}, (-\[Alpha]p/2 der[profile][m]) D[1/(zd - wbar), {zd, n}] /. {zd -> z}];
SWick[ProfileXAntiHolo[profile_, ders_, wbar_], dXt[m, n_, z_]] :=
  SWick[ProfileXAntiHolo[profile, ders, wbar], dXt[m, n, z]] =
  Module[{zd}, (-\[Alpha]p/2 der[profile][m]) D[1/(zd - wbar), {zd, n}] /. {zd -> z}];

SWick[dXt[i_, n_, z_], ProfileXAntiHolo[profile_, ders_, wbar_]] /; transverseIndexQ[i] :=
  SWick[dXt[i, n, z], ProfileXAntiHolo[profile, ders, wbar]] =
  Module[{zd}, (-\[Alpha]p/2 der[profile][i]) D[1/(zd - wbar), {zd, n}] /. {zd -> z}];
SWick[ProfileXAntiHolo[profile_, ders_, wbar_], dXt[i_, n_, z_]] /; transverseIndexQ[i] :=
  SWick[ProfileXAntiHolo[profile, ders, wbar], dXt[i, n, z]] =
  Module[{zd}, (-\[Alpha]p/2 der[profile][i]) D[1/(zd - wbar), {zd, n}] /. {zd -> z}];


(* ::Subsection:: *)
(*SWick for expX with lightcone indices*)


(* expX with holomorphic dX - lightcone indices *)
SWick[dX[p, n_, z_], expX[k_, w_, wbar_]] := SWick[dX[p, n, z], expX[k, w, wbar]] =
  Module[{zd}, (-\[Alpha]p/2 I k[p]) D[1/(zd - w), {zd, n}] /. {zd -> z}];
SWick[expX[k_, w_, wbar_], dX[p, n_, z_]] := SWick[expX[k, w, wbar], dX[p, n, z]] =
  Module[{zd}, (-\[Alpha]p/2 I k[p]) D[1/(zd - w), {zd, n}] /. {zd -> z}];

SWick[dX[m, n_, z_], expX[k_, w_, wbar_]] := SWick[dX[m, n, z], expX[k, w, wbar]] =
  Module[{zd}, (-\[Alpha]p/2 I k[m]) D[1/(zd - w), {zd, n}] /. {zd -> z}];
SWick[expX[k_, w_, wbar_], dX[m, n_, z_]] := SWick[expX[k, w, wbar], dX[m, n, z]] =
  Module[{zd}, (-\[Alpha]p/2 I k[m]) D[1/(zd - w), {zd, n}] /. {zd -> z}];

SWick[dX[i_, n_, z_], expX[k_, w_, wbar_]] /; transverseIndexQ[i] :=
  Module[{zd}, (-\[Alpha]p/2 I k[i]) D[1/(zd - w), {zd, n}] /. {zd -> z}];
SWick[expX[k_, w_, wbar_], dX[i_, n_, z_]] /; transverseIndexQ[i] :=
  Module[{zd}, (-\[Alpha]p/2 I k[i]) D[1/(zd - w), {zd, n}] /. {zd -> z}];

(* expX with antiholomorphic dXt - lightcone indices *)
SWick[dXt[p, n_, z_], expX[k_, w_, wbar_]] := SWick[dXt[p, n, z], expX[k, w, wbar]] =
  Module[{zd}, (-\[Alpha]p/2 I k[p]) D[1/(zd - wbar), {zd, n}] /. {zd -> z}];
SWick[expX[k_, w_, wbar_], dXt[p, n_, z_]] := SWick[expX[k, w, wbar], dXt[p, n, z]] =
  Module[{zd}, (-\[Alpha]p/2 I k[p]) D[1/(zd - wbar), {zd, n}] /. {zd -> z}];

SWick[dXt[m, n_, z_], expX[k_, w_, wbar_]] := SWick[dXt[m, n, z], expX[k, w, wbar]] =
  Module[{zd}, (-\[Alpha]p/2 I k[m]) D[1/(zd - wbar), {zd, n}] /. {zd -> z}];
SWick[expX[k_, w_, wbar_], dXt[m, n_, z_]] := SWick[expX[k, w, wbar], dXt[m, n, z]] =
  Module[{zd}, (-\[Alpha]p/2 I k[m]) D[1/(zd - wbar), {zd, n}] /. {zd -> z}];

SWick[dXt[i_, n_, z_], expX[k_, w_, wbar_]] /; transverseIndexQ[i] :=
  Module[{zd}, (-\[Alpha]p/2 I k[i]) D[1/(zd - wbar), {zd, n}] /. {zd -> z}];
SWick[expX[k_, w_, wbar_], dXt[i_, n_, z_]] /; transverseIndexQ[i] :=
  Module[{zd}, (-\[Alpha]p/2 I k[i]) D[1/(zd - wbar), {zd, n}] /. {zd -> z}];

(* expXHolo with dX - lightcone indices *)
SWick[dX[p, n_, z_], expXHolo[k_, w_]] := SWick[dX[p, n, z], expXHolo[k, w]] =
  Module[{zd}, (-\[Alpha]p/2 I k[p]) D[1/(zd - w), {zd, n}] /. {zd -> z}];
SWick[expXHolo[k_, w_], dX[p, n_, z_]] := SWick[expXHolo[k, w], dX[p, n, z]] =
  Module[{zd}, (-\[Alpha]p/2 I k[p]) D[1/(zd - w), {zd, n}] /. {zd -> z}];

SWick[dX[m, n_, z_], expXHolo[k_, w_]] := SWick[dX[m, n, z], expXHolo[k, w]] =
  Module[{zd}, (-\[Alpha]p/2 I k[m]) D[1/(zd - w), {zd, n}] /. {zd -> z}];
SWick[expXHolo[k_, w_], dX[m, n_, z_]] := SWick[expXHolo[k, w], dX[m, n, z]] =
  Module[{zd}, (-\[Alpha]p/2 I k[m]) D[1/(zd - w), {zd, n}] /. {zd -> z}];

SWick[dX[i_, n_, z_], expXHolo[k_, w_]] /; transverseIndexQ[i] :=
  Module[{zd}, (-\[Alpha]p/2 I k[i]) D[1/(zd - w), {zd, n}] /. {zd -> z}];
SWick[expXHolo[k_, w_], dX[i_, n_, z_]] /; transverseIndexQ[i] :=
  Module[{zd}, (-\[Alpha]p/2 I k[i]) D[1/(zd - w), {zd, n}] /. {zd -> z}];

(* expXAntiHolo with dXt - lightcone indices *)
SWick[dXt[p, n_, z_], expXAntiHolo[k_, wbar_]] := SWick[dXt[p, n, z], expXAntiHolo[k, wbar]] =
  Module[{zd}, (-\[Alpha]p/2 I k[p]) D[1/(zd - wbar), {zd, n}] /. {zd -> z}];
SWick[expXAntiHolo[k_, wbar_], dXt[p, n_, z_]] := SWick[expXAntiHolo[k, wbar], dXt[p, n, z]] =
  Module[{zd}, (-\[Alpha]p/2 I k[p]) D[1/(zd - wbar), {zd, n}] /. {zd -> z}];

SWick[dXt[m, n_, z_], expXAntiHolo[k_, wbar_]] := SWick[dXt[m, n, z], expXAntiHolo[k, wbar]] =
  Module[{zd}, (-\[Alpha]p/2 I k[m]) D[1/(zd - wbar), {zd, n}] /. {zd -> z}];
SWick[expXAntiHolo[k_, wbar_], dXt[m, n_, z_]] := SWick[expXAntiHolo[k, wbar], dXt[m, n, z]] =
  Module[{zd}, (-\[Alpha]p/2 I k[m]) D[1/(zd - wbar), {zd, n}] /. {zd -> z}];

SWick[dXt[i_, n_, z_], expXAntiHolo[k_, wbar_]] /; transverseIndexQ[i] :=
  Module[{zd}, (-\[Alpha]p/2 I k[i]) D[1/(zd - wbar), {zd, n}] /. {zd -> z}];
SWick[expXAntiHolo[k_, wbar_], dXt[i_, n_, z_]] /; transverseIndexQ[i] :=
  Module[{zd}, (-\[Alpha]p/2 I k[i]) D[1/(zd - wbar), {zd, n}] /. {zd -> z}];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
