(* Evaluate every surviving polynomial-profile contraction in the native
   binary expression after separating the two scalar heat operators. *)
auditWordSlots[term_] := Flatten[Join[
  Cases[term, ProfileX[f_,ds_List,_,_] :> Join[If[AtomQ[f],{},List@@f],ds], Infinity],
  Cases[term, (dX|dXt|\[Psi]|\[Psi]t)[i_,_,_] :> {i}, Infinity],
  Cases[term, \[Delta][i_,j_] :> {i,j}, Infinity]]];
auditSourceJet[d_, key_, indices_List, derivatives_List] := auditSourceJet[d,key,indices,derivatives] =
  Module[{array = auditBackground[d,key], subs, vec, tensor},
    vec[i_Integer] := UnitVector[10,i+1];
    vec[p] := {0,1,I,0,0,0,0,0,0,0}; vec[m] := {0,1,-I,0,0,0,0,0,0,0};
    tensor = Switch[key, "metric", vec[indices[[1]]].array.vec[indices[[2]]],
      "A", vec[First[indices]].array, "phi", array];
    auditProfileDerivative[tensor,derivatives,0]
  ];
auditSpecializeSourceTerm[raw_, n_, d_] := Module[
  {term=raw, jets, indices, force, result, field, heads={h,av,ph}, e=2Sqrt[n]},
  jets = Cases[term, ProfileX[seed,ds_List,_,_] :> ds, Infinity];
  If[Length[jets] =!= 1, Print["Expected one seed profile in ",InputForm[Short[term,2]]]; Return[$Failed]];
  If[AnyTrue[First[jets], #===p || #===m || (IntegerQ[#] && #=!=0)&], Return[0]];
  force = Thread[DeleteDuplicates[Select[First[jets], Head[#]===Symbol &]] -> 0];
  term = Expand[term /. force /. ProfileX[seed,ds_List,_,_] :> (-e)^Length[ds]];
  term = auditProjectionCleanup[term];
  If[term === 0,Return[0]];
  If[Head[term]===Plus, Return[Total[auditSpecializeSourceTermAfterSeed[#,d]& /@ List@@term]]];
  auditSpecializeSourceTermAfterSeed[term,d]
];
auditChiralSeed[expr_,n_] := Module[{term, e=2 Sqrt[n]},
  term = Expand[expr /. {
    HoldPattern[der[f_][j_] /; f === seed] :> -e \[Delta][j,0],
    HoldPattern[(head_Symbol)[f_,ds_List,z_] /;
      f === seed && MemberQ[{"ProfileXHolo","ProfileXAntiHolo"},SymbolName[head]]] :>
      (-e)^Length[ds] (Times@@(\[Delta][#,0]& /@ ds)) head[seed,{},z]
  }];
  auditProjectionCleanup[term]
];
auditSpecializeSourceTermAfterSeed[term_,d_] := Module[{indices, jets, parts, word, tag, stripped},
  jets = Cases[term, ProfileX[f_,ds_List,_,_] :> {f,ds}, Infinity];
  If[Length[jets]=!=1,Print["Expected one background profile in ",InputForm[Short[term,2]]];Return[$Failed]];
  {word,parts}=First[jets];
  tag=Which[Head[word]===h,"metric",Head[word]===av,"A",word===ph,"phi",True,Return[$Failed]];
  indices=DeleteDuplicates[Select[auditWordSlots[term],Head[#]===Symbol && !MemberQ[{p,m},#]&]];
  stripped=term /. _ProfileX -> 1;
  Total[Table[
    Module[{rule=Thread[indices->values], value},
      value=auditSourceJet[d,tag,If[AtomQ[word],{},List@@(word/.rule)],parts/.rule];
      If[value === 0,0,(stripped /. rule /. auditNullRules) value]],
    {values,Tuples[Range[0,9],Length[indices]]}]]
];
auditEvaluateSource[expr_,n_,d_] := auditProjectionCleanup[auditNumericWord[
  Total[auditSpecializeSourceTerm[#,n,d]& /@ auditTerms[Expand[expr]]]]];

