(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`Brackets`TypeII`SL2C`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`NormalOrdering`TypeII`"];
Needs["StringCode`Taylor`"];
Needs["StringCode`Taylor`TypeII`"];
Needs["StringCode`Conventions`TypeII`"];
Needs["StringCode`OPE`"];
Needs["StringCode`Brackets`"];
Needs["StringCode`Brackets`TypeII`"];


(* ::Section:: *)
(*Declare public variables and methods*)


sl2cR::usage = "sl2cR is the SL(2,C) integration-slice parameter r of Cho-Collier-Yin (arXiv:1811.00032) eq. (2.11), where the three-punctured vertex has q1 = -q2 = q3 = r. Deforming the slice is a field redefinition, so on-shell quantities must not depend on sl2cR; that independence is the intended regression test. Kept public so it can be substituted or fixed numerically from a notebook. Only one bracket module is loaded per session (InitStringCode selects it), so this never coexists with the Bosonic SL2C symbol of the same name.";


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Local coordinate family*)


(* Cho-Collier-Yin eq. (2.8) gives the local coordinate at each puncture as the
   Mobius map  z = f_i(w) = z_i + q_i w / (1 + s_i q_i w),  with f_i'(0) = q_i and
   f_i''(0) = -2 s_i q_i^2. This module implements the s_i = 0 slice, where the map
   is affine and f_i''(0) = 0.

   That restriction is what makes the module data-only. StringCode's conformal
   placement (mapOp, Operators.m:85-108) applies the primary transformation law
   (f'(w))^h Phi(f(w)) and nothing else, which is exact precisely when f'' = 0.
   A nonzero s_i additionally requires the operator exp[-s_i L_1] of CCY eq. (2.9),
   which has no counterpart anywhere in the package; do not set s_i nonzero here
   without implementing it.

   The b-ghost side needs nothing: bgGhostModeCoefficients (Brackets.m:348) inverts
   the map with InverseSeries and series-expands -Differential[f[w], moduli] about
   f(0), which is CCY eq. (2.9)'s contour for an arbitrary f.

   Symbol naming: deliberately NOT the q/z of the Flat module. Private`q and
   Private`z already carry SubValues from ModuliIntegration.m:356-358
   (q[2,i_][_] := r0, z[2,1][_] := -z0, z[2,2][_] := z0), so a module reusing those
   heads silently inherits the plumbing values instead of its own. The dedicated
   sl2c* heads below are collision-free. *)


sl2cQ::usage = "sl2cQ[order, i][moduli] is the holomorphic scale q_i = f_i'(0) of the i-th puncture of the SL(2,C) order-bracket vertex. Left symbolic when no slice has been fixed for that order.";

sl2cZ::usage = "sl2cZ[order, i][moduli] is the holomorphic insertion point z_i = f_i(0) of the i-th puncture of the SL(2,C) order-bracket vertex.";

sl2cQbar::usage = "sl2cQbar[order, i][moduli] is the antiholomorphic scale qbar_i of the i-th puncture.";

sl2cZbar::usage = "sl2cZbar[order, i][moduli] is the antiholomorphic insertion point zbar_i of the i-th puncture.";


sl2cLocalCoordinate::usage = "sl2cLocalCoordinate[order, i][moduli][w] is the i-th holomorphic SL(2,C) local coordinate map, f_i(w) = z_i + q_i w (CCY eq. (2.8) at s_i = 0).";
sl2cLocalCoordinate[order_, i_][moduli___][w_] := w sl2cQ[order, i][moduli] + sl2cZ[order, i][moduli];

sl2cLocalCoordinateBar::usage = "sl2cLocalCoordinateBar[order, i][moduli][wbar] is the i-th antiholomorphic SL(2,C) local coordinate map.";
sl2cLocalCoordinateBar[order_, i_][moduli___][wbar_] := wbar sl2cQbar[order, i][moduli] + sl2cZbar[order, i][moduli];


(* ::Subsection:: *)
(*Abstract n-bracket data*)


(* The returned replacement list is intentionally empty. BracketBosonic
   (Brackets.m:72-93) destructures the sixth payload slot into
   localCoordinateReplacement and then never applies it, so the indirection
   q -> qR that the Flat module carries is dead code. This module instead puts the
   slice values directly on sl2cQ/sl2cZ, which is what actually reaches the
   bracket. *)

getLocalCoordinateData::usage = "getLocalCoordinateData[order] gives the SL(2,C) local coordinate data for an order-bracket: {holomorphic maps, antiholomorphic maps, w, wbar, moduli, replacement rules}. An order-n bracket has n input punctures plus the output puncture, i.e. an (n+1)-punctured sphere, and therefore n-2 complex moduli -- listed here as 2(n-2) entries, one t and one tbar per complex modulus, matching the moduliLength/2 normalization in BracketBosonic.";
getLocalCoordinateData[order_] := Module[
  {moduli = {}, w, wbar, localCoordinateFunctionsHol = {}, localCoordinateFunctionsAntiHol = {}},

  (*One {t, tbar} pair per complex modulus*)
  Do[Module[{t, tbar}, AppendTo[moduli, t]; AppendTo[moduli, tbar]], order - 2];

  {localCoordinateFunctionsHol, localCoordinateFunctionsAntiHol} =
    Reap[
      Do[
        Sow[sl2cLocalCoordinate[order, i][moduli], "Holo"];
        Sow[sl2cLocalCoordinateBar[order, i][moduli], "AntiHolo"],
        {i, 1, order}
      ]
    ][[2]];

  {localCoordinateFunctionsHol, localCoordinateFunctionsAntiHol, w, wbar, moduli, {}}
];


(* ::Subsection:: *)
(*SL(2,C) 2-bracket data = CCY's three-punctured vertex, eq. (2.11)*)


(* Two inputs plus the output puncture make three punctures and zero moduli, so
   BracketBosonic takes its moduliLength == 0 branch: no b-ghost insertions and
   unit normalization, matching CCY eq. (2.10), which carries no b's.

   CCY put the punctures at z = 0, 1, infinity with q1 = -q2 = q3 = r. The puncture
   at infinity is the bracket's OUTPUT leg, which is never assigned a local
   coordinate -- BracketBosonic builds one map per INPUT (Brackets.m:74-78) and
   returns a state. So only f_1(w) = r w and f_2(w) = 1 - r w are needed here, and
   the infinity chart never arises.

   r is real in CCY's slice, so the antiholomorphic data is the complex conjugate
   of the holomorphic data and coincides with it entrywise. *)

sl2cZ[2, 1][{}] := 0;
sl2cZ[2, 2][{}] := 1;
sl2cQ[2, 1][{}] := sl2cR;
sl2cQ[2, 2][{}] := -sl2cR;

sl2cZbar[2, 1][{}] := 0;
sl2cZbar[2, 2][{}] := 1;
sl2cQbar[2, 1][{}] := sl2cR;
sl2cQbar[2, 2][{}] := -sl2cR;


(* Order >= 3 is deliberately left symbolic: it needs a choice of integration
   slice S_n (the moduli-dependence of z_i and q_i), which CCY do not fix in closed
   form -- any slice that glues consistently under plumbing is admissible. *)


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
