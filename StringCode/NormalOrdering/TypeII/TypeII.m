(* ::Package:: *)

(* ::Section:: *)
(*Init*)


BeginPackage["StringCode`NormalOrdering`TypeII`"];


Needs["StringCode`Symbols`"];
Needs["StringCode`Symbols`TypeII`"];
Needs["StringCode`NormalOrdering`"]


(* ::Section:: *)
(*Declare public variables and methods*)


(* ::Section:: *)
(*Logic*)


Begin["Private`"];


(* ::Subsection:: *)
(*Define Grassmann parity*)


regcomm::usage = "Give Grassmann sign under commutation";
regcomm[f_,g_]:=(-1)^(parity[f] parity[g])(-1)^(exp\[Phi]parity[f] exp\[Phi]parity[g])(-1)^(exp\[Phi]tparity[f] exp\[Phi]tparity[g])

exp\[Phi]parity::usage = "Compute Grassmann parity of exp\[Phi]";
exp\[Phi]parity[f_]:=0/;(And @@(FreeQ[f,#]&/@ exp\[Phi]fermions))
exp\[Phi]parity[f_]:=1/;(!(And @@(FreeQ[f,#]&/@ exp\[Phi]fermions)))
exp\[Phi]parity[R[f__,g__]]:=Mod[exp\[Phi]parity[R[f]]+exp\[Phi]parity[R[g]],2]
exp\[Phi]parity[R[f_]]:=exp\[Phi]parity[f]

exp\[Phi]tparity::usage = "Compute Grassmann parity of exp\[Phi]t";
exp\[Phi]tparity[f_]:=0/;(And @@(FreeQ[f,#]&/@ exp\[Phi]tfermions))
exp\[Phi]tparity[f_]:=1/;(!(And @@(FreeQ[f,#]&/@ exp\[Phi]tfermions)))
exp\[Phi]tparity[R[f__,g__]]:=Mod[exp\[Phi]tparity[R[f]]+exp\[Phi]tparity[R[g]],2]
exp\[Phi]tparity[R[f_]]:=exp\[Phi]tparity[f]


(* ::Subsection::Closed:: *)
(*Define normal-ordered product*)


R[ c___,a_,a_,d___]:=R[c,exp\[Phi]b[2a[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]f)
R[ c___,a_,a_,d___]:=R[c,exp\[Phi]tb[2a[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]tf)
R[ c___,a_,b_,d___]:=R[c,exp\[Phi]b[a[[1]]+b[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]b && Head[b]==exp\[Phi]b && a[[2]]==b[[2]])
R[ c___,a_,b_,d___]:=R[c,exp\[Phi]tb[a[[1]]+b[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]tb && Head[b]==exp\[Phi]tb && a[[2]]==b[[2]])
R[ c___,a_,b_,d___]:=R[c,exp\[Phi]b[a[[1]]+b[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]f && Head[b]==exp\[Phi]f && a[[2]]==b[[2]])
R[ c___,a_,b_,d___]:=R[c,exp\[Phi]tb[a[[1]]+b[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]tf && Head[b]==exp\[Phi]tf && a[[2]]==b[[2]])
R[ c___,a_,b_,d___]:=R[c,exp\[Phi]f[a[[1]]+b[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]b && Head[b]==exp\[Phi]f && a[[2]]==b[[2]])
R[ c___,a_,b_,d___]:=R[c,exp\[Phi]tf[a[[1]]+b[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]tb && Head[b]==exp\[Phi]tf && a[[2]]==b[[2]])


(* ::Subsection:: *)
(*Convert list of symbols to normal-ordered product*)


simplifying[list_] :=
  Module[{listofall, listFree\[CapitalPhi], listNoBoson, listSimpleF,
    list\[CapitalPhi], list\[CapitalPhi]t, positions\[CapitalPhi],
    positions\[CapitalPhi]t, positionsN\[CapitalPhi]t, positionsrest,
    count\[CapitalPhi]t, count\[CapitalPhi], factor\[CapitalPhi]s},
   listofall = Flatten[TimesToList[#] & /@ list, 1];
   listFree\[CapitalPhi] =
    Select[listofall, (Head[#] =!= exp\[Phi]f &&
        Head[#] =!= exp\[Phi]tf) &];
   listNoBoson = Select[listofall, isFermion[Head[#]] &];
   listSimpleF =
    Select[listNoBoson, (Head[#] =!= exp\[Phi]f &&
        Head[#] =!= exp\[Phi]tf) &];
   list\[CapitalPhi] =
    Select[listofall, (Head[FieldReturn[#]] === exp\[Phi]f) &];
   list\[CapitalPhi]t =
    Select[listofall, (Head[FieldReturn[#]] === exp\[Phi]tf) &];
   positions\[CapitalPhi] =
    If[list\[CapitalPhi] =!= {},
     Flatten[Position[listNoBoson,
       elem_ /; Head[elem] === exp\[Phi]f, {1},
       Heads -> False]], {}];
   positions\[CapitalPhi]t =
    If[list\[CapitalPhi]t =!= {},
     Flatten[Position[listNoBoson,
       elem_ /; Head[elem] === exp\[Phi]tf, {1}, Heads -> False]], {}];
   positionsN\[CapitalPhi]t =
    Flatten[Position[listNoBoson,
      elem_ /; Head[elem] =!= exp\[Phi]tf, {1}, Heads -> False]];
   positionsrest =
    Flatten[Position[listNoBoson,
      elem_ /; (Head[elem] =!= exp\[Phi]f &&
         Head[elem] =!= exp\[Phi]tf), {1}, Heads -> False]];
   count\[CapitalPhi]t =
    If[positions\[CapitalPhi]t =!= {},
     Total[Boole@
       Flatten@Table[
         a > b, {a, positionsN\[CapitalPhi]t}, {b,
          positions\[CapitalPhi]t}]], 0];
   count\[CapitalPhi] =
    If[positions\[CapitalPhi] =!= {},
     Total[Boole@
       Flatten@Table[
         a > b, {a, positionsrest}, {b, positions\[CapitalPhi]}]],
     0];
   factor\[CapitalPhi]s =
    Power[-1, count\[CapitalPhi] + count\[CapitalPhi]t];
   {factor\[CapitalPhi]s, listFree\[CapitalPhi], listSimpleF,
    list\[CapitalPhi], list\[CapitalPhi]t}];


(* ::Subsection:: *)
(*Define total picture number*)


totalHolPicture::usage = "Computes total holomorphic picture";
totalAntiHolPicture::usage = "Computes total antiholomorphic picture";

totalHolPicture[Ra_/;Rtest[Ra]]:= Map[pictureHol, List @@ Ra]//Total;
totalHolPicture[Times[a_, Ra_/;Rtest[Ra]]] := totalHolPicture[Ra];

totalAntiHolPicture[Ra_/;Rtest[Ra]]:= Map[pictureAntiHol, List @@ Ra]//Total;
totalAntiHolPicture[Times[a_, Ra_/;Rtest[Ra]]] := totalAntiHolPicture[Ra];


(* ::Subsection::Closed:: *)
(*Define CR*)


CR[ c___,a_,a_,d___]:=CR[c,exp\[Phi]b[2a[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]f)
CR[ c___,a_,a_,d___]:=CR[c,exp\[Phi]tb[2a[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]tf)
CR[ c___,a_,b_,d___]:=CR[c,exp\[Phi]b[a[[1]]+b[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]f && Head[b]==exp\[Phi]f && a[[2]]==b[[2]])
CR[ c___,a_,b_,d___]:=CR[c,exp\[Phi]tb[a[[1]]+b[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]tf && Head[b]==exp\[Phi]tf && a[[2]]==b[[2]])
CR[ c___,a_,b_,d___]:=CR[c,exp\[Phi]f[a[[1]]+b[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]b && Head[b]==exp\[Phi]f && a[[2]]==b[[2]])
CR[ c___,a_,b_,d___]:=CR[c,exp\[Phi]tf[a[[1]]+b[[1]],a[[2]]],d]/;(Head[a]==exp\[Phi]tb && Head[b]==exp\[Phi]tf && a[[2]]==b[[2]])


(* ::Section:: *)
(*End*)


End[];


EndPackage[];
