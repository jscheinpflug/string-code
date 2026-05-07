Needs["StringCode`"];

InitStringCode[<| "theory" -> "TypeII", "CFT" -> "FlatSpace", "conventions" -> "TypeII-Ashoke", "bracket" -> "Flat"|>];

(*Setup*)

canonicalizeDummies[expr_] := Module[{terms, canonicalize},
  canonicalize[term_] := Module[{indices, rules},
    (* Find all module-generated indices *)
    indices = DeleteDuplicates[
      Cases[term, s_Symbol /; StringMatchQ[SymbolName[s], __ ~~ "$" ~~ DigitCharacter..], Infinity]
    ];
    (* Replace with canonical names in order of appearance *)
    rules = Thread[indices -> Take[{\[Mu], \[Nu], \[Rho], \[Sigma], \[Tau], \[Lambda]}, Length[indices]]];
    term /. rules
  ];
  
  (* Apply to each term in the sum *)
  If[Head[expr] === Plus,
    Total[canonicalize /@ (List @@ expr)],
    canonicalize[expr]
  ]
]

twoBracketReplRule = {Private`z[2,1][{}] :> z, Private`z[2,2][{}] :> -z, Private`q[2,1][{}]:> Private`r0,Private`q[2,2][{}] :> Private`r0, Private`zbar[2,1][{}] :> z, Private`zbar[2,2][{}] :> -z, Private`qbar[2,1][{}]:> Private`r0, Private`qbar[2,2][{}] :> Private`r0};


(*Defining general string fields*)

stringFieldRR[F_,\[Alpha]_,\[Beta]_, z_, zbar_] := R[ProfileX[F, {}, z, zbar],c[0,z], ct[0,zbar], S[{\[Alpha], "chiral"}, -1/2, {}, 0, z], St[{\[Beta], "chiral"}, -1/2, {}, 0, zbar]];

stringFieldGrav[h_,\[Mu]_, \[Nu]_, z_, zbar_] := R[ProfileX[h[\[Mu],\[Nu]], {}, z, zbar], c[0,z], ct[0,zbar], exp\[Phi]f[-1,z], \[Psi][\[Mu],0,z], exp\[Phi]tf[-1,zbar], \[Psi]t[\[Nu],0,zbar]];

stringFieldGD[Dil_ , z_, zbar_] := R[ProfileX[Dil,{},z,zbar],c[0,z], ct[0,zbar], \[Eta][0,z],exp\[Phi]tb[-2,zbar],\[Xi]t[1,zbar]] - R[ProfileX[Dil,{},z,zbar],c[0,z], ct[0,zbar],exp\[Phi]b[-2,z],\[Xi][1,z],\[Eta]t[0,zbar]];

symRNS[\[Lambda]_ ,\[Alpha]_, z_, zbar_] := R[ProfileX[\[Lambda][\[Alpha]],{},z,zbar],c[0,z],ct[0,zbar],S[{\[Alpha], "chiral"}, -1/2, {}, 0, z],exp\[Phi]tb[-2,zbar],\[Xi]t[1,zbar]];

symNSR[\[Lambda]_,\[Alpha]_,z_,zbar_] := R[ProfileX[\[Lambda][\[Alpha]],{},z,zbar],c[0,z],ct[0,zbar],exp\[Phi]b[-2,z],\[Xi][1,z],St[{\[Alpha], "chiral"}, -1/2, {}, 0, zbar]];

symNSNS[V_,\[Mu]_, z_, zbar_] := R[ProfileX[V[\[Mu]],{},z,zbar],c[0,z],ct[0,zbar],exp\[Phi]f[-1,z],\[Psi][\[Mu],0,z],exp\[Phi]tb[-2,zbar],\[Xi]t[1,zbar]]+R[ProfileX[V[\[Mu]],{},z,zbar],c[0,z],ct[0,zbar],exp\[Phi]b[-2,z],\[Xi][1,z],exp\[Phi]tf[-1,zbar],\[Psi]t[\[Mu],0,zbar]];

AuxNSNS[Aux_, \[Mu]_, z_, zbar_] := (1/2)*R[c[1,z]+ct[1,zbar], ProfileX[Aux[\[Mu]],{},z,zbar],c[0,z],ct[0,zbar],exp\[Phi]f[-1,z],\[Psi][\[Mu],0,z],exp\[Phi]tb[-2,zbar],\[Xi]t[1,zbar]]+(1/2)*R[c[1,z]+ct[1,zbar], ProfileX[Aux[\[Mu]],{},z,zbar],c[0,z],ct[0,zbar],exp\[Phi]b[-2,z],\[Xi][1,z],exp\[Phi]tf[-1,zbar],\[Psi]t[\[Mu],0,zbar]];



(*Brackets*)

(*Simplest RR-RR 2-bracket works. No PCO shenanigans.*)
(BracketProjected[stringFieldRR[F1,\[Alpha]1,\[Beta]1,z1,z1bar],stringFieldRR[F2,\[Alpha]2,\[Beta]2,z2,z2bar],0,0]//Private`CollapseB0m)//.{_der:>0, dot[0,0]:>0}//.twoBracketReplRule//Simplify


(*This RR-NSNS 2-bracket already fails: needs PCO action, which doesn't seem to handle the following simple R picture-raising. Why do such simple OPE's give $Failed?*)
test1 = ((BracketProjected[stringFieldRR[F1,\[Alpha],\[Beta],z,zbar],stringFieldGrav[H,\[Mu],\[Nu],-z,-zbar],0,0]//Private`CollapseB0m)//.{_der:>0, dot[0,0]:>0})//.twoBracketReplRule//Simplify

Private`actPCOHolo[R[ProfileX[F, {}, z, zbar],c[0,z], S[{\[Alpha], "antichiral"}, -3/2, {}, 0, z]]]

(*Understand why bracket result gives zero, whereas OPEProjected yields non-zero result. Gotta check factorization -> OPEProjectedHolo/AntiHolo*)

result = (BracketProjected[R[c[0,z1],S[{\[Alpha]1,"chiral"},-1/2,{},0,z1],ct[0,z1bar],St[{\[Beta]1,"chiral"},-1/2,{},0,z1bar]],R[c[0,z2],S[{\[Alpha]2,"chiral"},-1/2,{},0,z2],ct[0,z2bar],St[{\[Beta]2,"chiral"},-1/2,{},0,z2bar]],R[ProfileX[h[\[Mu],\[Nu]], {}, z3, z3bar], c[0,z3], ct[0,z3bar], exp\[Phi]f[-1,z3], \[Psi][\[Mu],0,z3], exp\[Phi]tf[-1,z3bar], \[Psi]t[\[Nu],0,z3bar]],0,0])//Private`CollapseB0m//.{der[F1]:>0, der[F2]:>0, dot[0,_]:>0}

(OPEProjected[0,0][R[c[0,z1],S[{\[Alpha]1,"chiral"},-1/2,{},0,z1],ct[0,z1bar],St[{\[Beta]1,"chiral"},-1/2,{},0,z1bar]],R[c[0,z2],S[{\[Alpha]2,"chiral"},-1/2,{},0,z2],ct[0,z2bar],St[{\[Beta]2,"chiral"},-1/2,{},0,z2bar]],R[ProfileX[h[\[Mu],\[Nu]], {}, z3, z3bar], c[0,z3], ct[0,z3bar], exp\[Phi]f[-1,z3], \[Psi][\[Mu],0,z3], exp\[Phi]tf[-1,z3bar], \[Psi]t[\[Nu],0,z3bar]]]//Simplify)//.{der[F1]:>0, der[F2]:>0, dot[0,_]:>0}

(*Clearly OPEProjectedHolo + actPCOHolo works fine... and gives non-zero result.*)

OPEProjectedHolo[0][R[c[0,z1],S[{\[Alpha]1,"chiral"},-1/2,{},0,z1]],R[c[0,z2],S[{\[Alpha]2,"chiral"},-1/2,{},0,z2]],R[ProfileXHolo[h[\[Mu],\[Nu]], {}, z3], c[0,z3], exp\[Phi]f[-1,z3], \[Psi][\[Mu],0,z3]]]//Simplify

Private`actPCOHolo[R[c[0, 0], c[1, 0], c[2, 0], exp\[Phi]b[-2, 0], ProfileXHolo[h[\[Mu], \[Nu]], {}, 0]]]

Put[result, "~/Desktop/OPEresult.m"]


(*NSNS-NSNS 2-bracket also has problematic output with mysterious 0[\[Mu]] factor*)
(BracketProjected[R[ProfileX[h1[\[Mu]1,\[Nu]1], {}, z, zbar], c[0,z], ct[0,zbar], exp\[Phi]f[-1,z], \[Psi][\[Mu]1,0,z], exp\[Phi]tf[-1,zbar], \[Psi]t[\[Nu]1,0,zbar]],R[ProfileX[h2[\[Mu]2,\[Nu]2], {}, -z, -zbar], c[0,-z], ct[0,-zbar], exp\[Phi]f[-1,-z], \[Psi][\[Mu]2,0,-z], exp\[Phi]tf[-1,-zbar], \[Psi]t[\[Nu]2,0,-zbar]],0,0]//Private`CollapseB0m)//.{_der:>0, dot[0,0]:>0}//.twoBracketReplRule//Simplify