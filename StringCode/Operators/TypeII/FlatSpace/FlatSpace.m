(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Operators`TypeII`FlatSpace`"];


Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];
Needs["StringCode`Symbols`TypeII`FlatSpace`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`TypeII`"];
Needs["StringCode`Operators`"];
Needs["StringCode`Operators`TypeII`"];


(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsubsection:: *)
(*Free boson*)


placeOp[coordinateHol_, coordinateAntiHol_][ProfileX[profile_, ders_List, z_, zbar_]]:= ProfileX[profile, ders, coordinateHol[z], coordinateAntiHol[zbar]];
placeOp[coordinateHol_, coordinateAntiHol_][ProfileXHolo[profile_, ders_List, z_]]:= ProfileXHolo[profile, ders, coordinateHol[z]];
placeOp[coordinateHol_, coordinateAntiHol_][ProfileXAntiHolo[profile_, ders_List, zbar_]]:= ProfileXAntiHolo[profile, ders, coordinateAntiHol[zbar]];
placeOp[coordinateHol_, coordinateAntiHol_][dX[\[Mu]_, n_, z_]]:= dX[\[Mu], n, coordinateHol[z]];
placeOp[coordinateHol_, coordinateAntiHol_][dXt[\[Mu]_, n_, zbar_]]:= dXt[\[Mu], n, coordinateAntiHol[zbar]];
placeOp[coordinateHol_, coordinateAntiHol_][dH[i_, n_, z_]]:= dH[i, n, coordinateHol[z]];
placeOp[coordinateHol_, coordinateAntiHol_][dHt[i_, n_, zbar_]]:= dHt[i, n, coordinateAntiHol[zbar]];
placeOp[coordinateHol_, coordinateAntiHol_][expX[n_, z_, zbar_]]:= expX[n, coordinateHol[z], coordinateAntiHol[zbar]];
placeOp[coordinateHol_, coordinateAntiHol_][expXHolo[n_, z_]]:= expXHolo[n, coordinateHol[z]];
placeOp[coordinateHol_, coordinateAntiHol_][expXAntiHolo[n_, zbar_]]:= expXAntiHolo[n, coordinateAntiHol[zbar]];
placeOp[coordinateHol_, coordinateAntiHol_][expH[charges_, z_]]:= expH[charges, coordinateHol[z]];
placeOp[coordinateHol_, coordinateAntiHol_][expHt[charges_, zbar_]]:= expHt[charges, coordinateAntiHol[zbar]];


(* ::Subsubsection:: *)
(*Free fermion*)


placeOp[coordinateHol_, coordinateAntiHol_][\[Psi][\[Mu]_, n_, z_]]:= \[Psi][\[Mu], n, coordinateHol[z]];
placeOp[coordinateHol_, coordinateAntiHol_][\[Psi]t[\[Mu]_, n_, zbar_]]:= \[Psi]t[\[Mu], n, coordinateAntiHol[zbar]];
placeOp[coordinateHol_, coordinateAntiHol_][S[{alpha_, chirality : ("chiral" | "antichiral")}, q_, modes_List, der_, z_]] := S[{alpha, chirality}, q, modes, der, coordinateHol[z]];
placeOp[coordinateHol_, coordinateAntiHol_][St[{alpha_, chirality : ("chiral" | "antichiral")}, q_, modes_List, der_, zbar_]] := St[{alpha, chirality}, q, modes, der, coordinateAntiHol[zbar]];

mapOp[coordinateHol_, coordinateAntiHol_][op:S[{alpha_, chirality : ("chiral" | "antichiral")}, q_, modes_List, der_, z_]] := Module[{w},
  (D[coordinateHol[w], w] /. {w -> z})^weightHolo[op] placeOp[coordinateHol, coordinateAntiHol][op]
];

mapOp[coordinateHol_, coordinateAntiHol_][op:St[{alpha_, chirality : ("chiral" | "antichiral")}, q_, modes_List, der_, zbar_]] := Module[{wbar},
  (D[coordinateAntiHol[wbar], wbar] /. {wbar -> zbar})^weightAntiHolo[op] placeOp[coordinateHol, coordinateAntiHol][op]
];


(* ::Subsubsection:: *)
(*Exponentials of phi*)


placeOp[coordinateHol_, coordinateAntiHol_][exp\[Phi]f[q_, z_]]:= exp\[Phi]f[q, coordinateHol[z]];
placeOp[coordinateHol_, coordinateAntiHol_][exp\[Phi]b[q_, z_]]:= exp\[Phi]b[q, coordinateHol[z]];
placeOp[coordinateHol_, coordinateAntiHol_][exp\[Phi]tf[q_, zbar_]]:= exp\[Phi]tf[q, coordinateAntiHol[zbar]];
placeOp[coordinateHol_, coordinateAntiHol_][exp\[Phi]tb[q_, zbar_]]:= exp\[Phi]tb[q, coordinateAntiHol[zbar]];


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
