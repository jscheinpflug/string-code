Spin Fields

(*Function that computes spinField associated with NSNS operator*)

Sb::usage = "Bosonized holomorphic spin field"
Stb::usage = "Bosonized anti-holomorphic spin field"

DefineField[Sb,
  "Statistics" -> "Fermion",
  "Simple" -> True,
  "Composite" -> False,
  "Holomorphic" -> True,
  "AntiHolomorphic" -> False,
  "Indexed" -> True,
  "Collapsable" -> False,
  "Factorizable" -> False,
  "RegularFermion" -> True,
  "PairsWith" -> {},
  "WeightHolo" -> Function[
    field,
    5/8 - field[[2]] (field[[2]] + 2)/2 + field[[4]] +
      Total[
        Join[
          Cases[field[[3]], {_, mode_?NumericQ} :> mode],
          Cases[field[[3]], {mode_?NumericQ, _} :> mode]
        ]
      ]
  ],
  "WeightAntiHolo" -> 0,
  "GSOParityHolo" -> Function[field, spinAlphaChiralitySign[field[[1, 2]]] (-1)^(field[[2]] + 1/2 + Length[field[[3]]])],
  "GSOParityAntiHolo" -> 1
];

DefineField[Stb,
  "Statistics" -> "Fermion",
  "Simple" -> True,
  "Composite" -> False,
  "Holomorphic" -> False,
  "AntiHolomorphic" -> True,
  "Indexed" -> True,
  "Collapsable" -> False,
  "Factorizable" -> False,
  "RegularFermion" -> True,
  "PairsWith" -> {},
  "WeightHolo" -> 0,
  "WeightAntiHolo" -> Function[
    field,
    5/8 - field[[2]] (field[[2]] + 2)/2 + field[[4]] +
      Total[
        Join[
          Cases[field[[3]], {_, mode_?NumericQ} :> mode],
          Cases[field[[3]], {mode_?NumericQ, _} :> mode]
        ]
      ]
  ],
  "GSOParityHolo" -> 1,
  "GSOParityAntiHolo" -> Function[field, spinAlphaChiralitySign[field[[1, 2]]] (-1)^(field[[2]] + 1/2 + Length[field[[3]]])]
];



(*
spinFieldPsiHolo[\[Mu]_ /; NumberQ[\[Mu]], d_, z_] :=
 Which[\[Mu] <= 1, 1/Sqrt[2] (Sb[0, 1, 0, 0, 0, 0, z] + (-1)^\[Mu] Sb[0, -1, 0, 0, 0, 0, z]),
  \[Mu] == 2, 1/Sqrt[2] (Sb[0, 0, 1, 0, 0, 0, z] + Sb[0, 0, -1, 0, 0, 0, z]), 
  \[Mu] == 3, -I/Sqrt[2] (Sb[0, 0, 1, 0, 0, 0, z] - Sb[0, 0, -1, 0, 0, 0, z]), 
  \[Mu] == 4, 1/Sqrt[2] (Sb[0, 0, 0, 1, 0, 0, z] + Sb[0, 0, 0, -1, 0, 0, z]), 
  \[Mu] == 5, -I/Sqrt[2] (Sb[0, 0, 0, 1, 0, 0, z] - Sb[0, 0, 0, -1, 0, 0, z]), 
  \[Mu] == 6, 1/Sqrt[2] (Sb[0, 0, 0, 0, 1, 0, z] + Sb[0, 0, 0, 0, -1, 0, z]), 
  \[Mu] == 7, -I/Sqrt[2] (Sb[0, 0, 0, 0, 1, 0, z] - Sb[0, 0, 0, 0, -1, 0, z]), 
  \[Mu] == 8, 1/Sqrt[2] (Sb[0, 0, 0, 0, 0, 1, z] + Sb[0, 0, 0, 0, 0, -1, z]), 
  \[Mu] == 9, -I/Sqrt[2] (Sb[0, 0, 0, 0, 0, 1, z] - Sb[0, 0, 0, 0, 0, -1, z])]

spinFieldPsiAntiHolo[\[Mu]_ /; NumberQ[\[Mu]], d_, z_] := 
 Which[\[Mu] <= 1, 1/Sqrt[2] (Stb[0, 1, 0, 0, 0, 0, z] + (-1)^\[Mu] Stb[0, -1, 0, 0, 0, 0, z]), 
  \[Mu] == 2, 1/Sqrt[2] (Stb[0, 0, 1, 0, 0, 0, z] + Stb[0, 0, -1, 0, 0, 0, z]), 
  \[Mu] == 3, -I/Sqrt[2] (Stb[0, 0, 1, 0, 0, 0, z] - Stb[0, 0, -1, 0, 0, 0, z]), 
  \[Mu] == 4, 1/Sqrt[2] (Stb[0, 0, 0, 1, 0, 0, z] + Stb[0, 0, 0, -1, 0, 0, z]), 
  \[Mu] == 5, -I/Sqrt[2] (Stb[0, 0, 0, 1, 0, 0, z] - Stb[0, 0, 0, -1, 0, 0, z]), 
  \[Mu] == 6, 1/Sqrt[2] (Stb[0, 0, 0, 0, 1, 0, z] + Stb[0, 0, 0, 0, -1, 0, z]), 
  \[Mu] == 7, -I/Sqrt[2] (Stb[0, 0, 0, 0, 1, 0, z] - Stb[0, 0, 0, 0, -1, 0, z]), 
  \[Mu] == 8, 1/Sqrt[2] (Stb[0, 0, 0, 0, 0, 1, z] + Stb[0, 0, 0, 0, 0, -1, z]), 
  \[Mu] == 9, -I/Sqrt[2] (Stb[0, 0, 0, 0, 0, 1, z] - Stb[0, 0, 0, 0, 0, -1, z])]
*)
 
(*Necessary for the bosonization of \[Psi]'s*)
spinFieldHoloExp[\[Mu]_ /; NumberQ[\[Mu]], d_, z_] := 
 Which[\[Mu] <= 1, 1/Sqrt[2] D[(Exp[I H0[0, z]] + (-1)^(\[Mu] + 1) Exp[-I H0[0, z]]), {z, d}],
  \[Mu] == 2, 1/Sqrt[2] D[(Exp[I H1[0, z]] + Exp[-I H1[0, z]]), {z, d}],
  \[Mu] == 3, -I/Sqrt[2] D[(Exp[I H1[0, z]] - Exp[-I H1[0, z]]), {z, d}],
  \[Mu] == 4, 1/Sqrt[2] D[(Exp[I H2[0, z]] + Exp[-I H2[0, z]]), {z, d}],
  \[Mu] == 5, -I/Sqrt[2] D[(Exp[I H2[0, z]] - Exp[-I H2[0, z]]), {z, d}],
  \[Mu] == 6, 1/Sqrt[2] D[(Exp[I H3[0, z]] + Exp[-I H3[0, z]]), {z, d}],
  \[Mu] == 7, -I/Sqrt[2] D[(Exp[I H3[0, z]] - Exp[-I H3[0, z]]), {z, d}],
  \[Mu] == 8, 1/Sqrt[2] D[(Exp[I H4[0, z]] + Exp[-I H4[0, z]]), {z, d}],
  \[Mu] == 9, -I/Sqrt[2] D[(Exp[I H4[0, z]] - Exp[-I H4[0, z]]), {z, d}]]

spinFieldAntiHoloExp[\[Mu]_ /; NumberQ[\[Mu]], d_, z_] := 
 Which[\[Mu] <= 1, 1/Sqrt[2] D[(Exp[I Ht0[0, z]] + (-1)^(\[Mu] + 1) Exp[-I Ht0[0, z]]), {z, d}],
  \[Mu] == 2, 1/Sqrt[2] D[(Exp[I Ht1[0, z]] + Exp[-I Ht1[0, z]]), {z, d}],
  \[Mu] == 3, -I/Sqrt[2] D[(Exp[I Ht1[0, z]] - Exp[-I Ht1[0, z]]), {z, d}],
  \[Mu] == 4, 1/Sqrt[2] D[(Exp[I Ht2[0, z]] + Exp[-I Ht2[0, z]]), {z, d}],
  \[Mu] == 5, -I/Sqrt[2] D[(Exp[I Ht2[0, z]] - Exp[-I Ht2[0, z]]), {z, d}],
  \[Mu] == 6, 1/Sqrt[2] D[(Exp[I Ht3[0, z]] + Exp[-I Ht3[0, z]]), {z, d}],
  \[Mu] == 7, -I/Sqrt[2] D[(Exp[I Ht3[0, z]] - Exp[-I Ht3[0, z]]), {z, d}],
  \[Mu] == 8, 1/Sqrt[2] D[(Exp[I Ht4[0, z]] + Exp[-I Ht4[0, z]]), {z, d}],
  \[Mu] == 9, -I/Sqrt[2] D[(Exp[I Ht4[0, z]] - Exp[-I Ht4[0, z]]), {z, d}]]

replaceDerHoloH = {Derivative[0, d_][H0][0, z_] :> dH0[d - 1, z],
   Derivative[0, d_][H1][0, z_] :> dH1[d - 1, z],
   Derivative[0, d_][H2][0, z_] :> dH2[d - 1, z],
   Derivative[0, d_][H3][0, z_] :> dH3[d - 1, z],
   Derivative[0, d_][H4][0, z_] :> dH4[d - 1, z]};
replaceDerAntiHoloH = {Derivative[0, d_][Ht0][0, z_] :> dHt0[d - 1, z],
   Derivative[0, d_][Ht1][0, z_] :> dHt1[d - 1, z],
   Derivative[0, d_][Ht2][0, z_] :> dHt2[d - 1, z],
   Derivative[0, d_][Ht3][0, z_] :> dHt3[d - 1, z],
   Derivative[0, d_][Ht4][0, z_] :> dHt4[d - 1, z]};

replaceHoloExpH = {Exp[Times[a_, H0[0, z_]]] :> spinFieldHolo[0, a, 0, 0, 0, 0, z],
   Exp[Times[a_, H1[0, z_]]] :> spinFieldHolo[0, 0, a, 0, 0, 0, z],
   Exp[Times[a_, H2[0, z_]]] :> spinFieldHolo[0, 0, 0, a, 0, 0, z],
   Exp[Times[a_, H3[0, z_]]] :> spinFieldHolo[0, 0, 0, 0, a, 0, z],
   Exp[Times[a_, H4[0, z_]]] :> spinFieldHolo[0, 0, 0, 0, 0, a, z]};

replaceAntiHoloExpH = {Exp[Times[a_, Ht0[0, z_]]] :> spinFieldAntiHolo[0, a, 0, 0, 0, 0, z],
   Exp[Times[a_, Ht1[0, z_]]] :> spinFieldAntiHolo[0, 0, a, 0, 0, 0, z],
   Exp[Times[a_, Ht2[0, z_]]] :> spinFieldAntiHolo[0, 0, 0, a, 0, 0, z],
   Exp[Times[a_, Ht3[0, z_]]] :> spinFieldAntiHolo[0, 0, 0, 0, a, 0, z],
   Exp[Times[a_, Ht4[0, z_]]] :> spinFieldAntiHolo[0, 0, 0, 0, 0, a, z]};


(*Defines bosonization of \[Psi]'s as a spin Field*)
spinFieldPsiHolo[\[Mu]_ /; NumberQ[\[Mu]], d_, z_] := (spinFieldHoloExp[\[Mu], d, z] /. replaceDerHoloH) /. 
  replaceHoloExpH
spinFieldPsiAntiHolo[\[Mu]_ /; NumberQ[\[Mu]], d_, z_] := (spinFieldAntiHoloExp[\[Mu], d, z] /. replaceDerAntiHoloH) /. 
  replaceAntiHoloExpH

(*Turns \[Psi]^\[Mu] into bosonized form and exp\[Phi]\
 into spin Field representation.*)
spinFieldNS[op_ /; RTestUpToConstant[op]] := Module[{list}, list = List @@ op;
  list = list /. {exp\[Phi]b[a_, z_] :> Sb[a, 0, 0, 0, 0, 0, z], 
     exp\[Phi]f[a_, z_] :> Sb[a, 0, 0, 0, 0, 0, z], 
     exp\[Phi]tb[a_, zbar_] :> Stb[a, 0, 0, 0, 0, 0, zbar], 
     exp\[Phi]tf[a_, zbar_] :> Stb[a, 0, 0, 0, 0, 0, zbar], 
     \[Psi][\[Mu]_ /; NumberQ[\[Mu]], d_, z_] :> spinFieldPsiHolo[\[Mu], d, z], 
     \[Psi]t[\[Mu]_ /; NumberQ[\[Mu]], dbar_, zbar_] :> spinFieldPsiAntiHolo[\[Mu], dbar, zbar]};
  R @@ list]


(*Picks out random component for \[Psi]^\[Mu].*)
compPickerNS[op_ /; RTestUpToConstant[op]] := Module[{list}, list = List @@ op;
  list = list /. {\[Psi][\[Mu]_, d_, z_] :> \[Psi][RandomInteger[{0, 9}], d, z], 
  \[Psi]t[\[Mu]_, dbar_, zbar_] :> \[Psi]t[RandomInteger[{0, 9}], d, z]};
  R @@ list]

(*NS sector bosonization*)

bosonizeNS[op_ /; RTestUpToConstant[op]]:= spinFieldNS[compPickerNS[op]]

(*Generate all possible combinations of signs*)
signs = Tuples[{-1, 1}, 5];

(*Filter for even number of positive signs (0,2,or 4)*)
evenSigns = Select[signs, EvenQ[Count[#, 1]] &];
oddSigns = Select[signs, OddQ[Count[#, 1]] &];
(*Create the matrix with first column 0 and rest\[PlusMinus]i/2*)
matrixChiral = Table[Join[{0}, oddSigns[[i]]*I/2], {i, Length[oddSigns]}];
matrixAntiChiral = Table[Join[{0}, evenSigns[[i]]*I/2], {i, Length[evenSigns]}];

(*Given an operator with \[CapitalTheta]^\[Alpha], \
picks out a random component for \[Alpha] to perform computations.*)
compPickerR[op_ /; RTestUpToConstant[op]] := Module[{list}, list = List @@ op;
  list = list /. {S[\[Alpha]_, chirality_, q_, modes_, d_, z_] :> S[RandomInteger[{1, 16}], chirality , q, modes, d, z], 
     St[\[Alpha]_, chirality_, q_, modes_, dbar_, zbar_] :> St[RandomInteger[{1, 16}], chirality , q, modes, d, z]};
  R @@ list]

(*Turns particular component of S or St
 into spinField in bosonized form.*)
spinFieldR[op_ /; RTestUpToConstant[op]] := Module[{list}, list = List @@ op;
  list = list /. {S[\[Alpha]_ /; NumberQ[\[Alpha]], chirality_ /; (chirality=="chiral"),q_,modes_, d_, z_] :> Sb[q, ##, modes, d, z] & @@ matrixChiral[[\[Alpha]]],
  S[\[Alpha]_ /; NumberQ[\[Alpha]], chirality_ /; (chirality=="antichiral"),q_, modes_, d_, z_] :> Sb[q, ##, modes, d, z] & @@ matrixAntiChiral[[\[Alpha]]],
  St[\[Alpha]_ /; NumberQ[\[Alpha]], chirality_ /; (chirality=="chiral"),q_,modes_, d_, z_] :> Sbt[q, ##, modes, d, z] & @@ matrixChiral[[\[Alpha]]],
  St[\[Alpha]_ /; NumberQ[\[Alpha]], chirality_ /; (chirality=="antichiral"),q_, modes_, d_, z_] :> Sbt[q, ##, modes, d, z] & @@ matrixAntiChiral[[\[Alpha]]]};
  R @@ list]

(*Still have to extend definition of R such that spin fields are combined (making use of cocyle phases?).
Not sure about what's the best way to proceed with the modes.*)

(*
pGSOHolo[field_ /; isField[Head[field]]] := Which[
  Head[field] === \[Psi], 1,

  MemberQ[{exp\[Phi]f, exp\[Phi]b}, Head[field]], field[[1]],

  Head[field] === S &&
   !((EvenQ[field[[1]] + 1/2] && field[[3]] === d) ||
     (OddQ[field[[1]] + 1/2] && field[[3]] === u)), 1,

  True, 0
]


pGSOAntiHolo[field_ /; isField[Head[field]]] := Which[
  Head[field] === \[Psi]t, 1,

  MemberQ[{exp\[Phi]tf, exp\[Phi]tb}, Head[field]], field[[1]],

  Head[field] === St &&
   !((EvenQ[field[[1]] + 1/2] && field[[3]] === d) ||
     (OddQ[field[[1]] + 1/2] && field[[3]] === u)), 1,

  True, 0
]

pGSOHoloT[field_ /; isField[Head[field]]] := Which[
  Head[field] === \[Psi], 1,

  MemberQ[{exp\[Phi]f, exp\[Phi]b}, Head[field]], field[[1]],

  Head[field] === S &&
   !((EvenQ[field[[1]] + 1/2] && field[[3]] === u) ||
     (OddQ[field[[1]] + 1/2] && field[[3]] === d)), 1,

  True, 0
]


pGSOAntiHoloT[field_ /; isField[Head[field]]] := Which[
  Head[field] === \[Psi]t, 1,

  MemberQ[{exp\[Phi]tf, exp\[Phi]tb}, Head[field]], field[[1]],

  Head[field] === St &&
   !((EvenQ[field[[1]] + 1/2] && field[[3]] === u) ||
     (OddQ[field[[1]] + 1/2] && field[[3]] === d)), 1,

  True, 0
]


projGSOIIA[Ra_ /; RTestUpToConstant[Ra]]:= projGSOHolo[Ra] && projGSOAntiHoloT[Ra];
projGSOIIB[Ra_ /; RTestUpToConstant[Ra]]:= projGSOHolo[Ra] && projGSOAntiHolo[Ra];
*)
